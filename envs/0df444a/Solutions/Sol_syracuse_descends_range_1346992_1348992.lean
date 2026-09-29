-- Prove2me | solution 1 for syracuse_descends_range_1346992_1348992
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:48.335742+00:00
-- url     : https://prove2.me/submissions/0156f02c-ca14-461b-be4e-22e09542e18f

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


theorem B1515541 : Blo 1346992 1515541 := bbase (se 6 (by rfl) ⟨35520, by rfl⟩ : syracuseStep 1515541 = 71041) (by norm_num)
theorem B2023445 : Blo 1346992 2023445 := bbase (se 6 (by rfl) ⟨47424, by rfl⟩ : syracuseStep 2023445 = 94849) (by norm_num)
theorem B2023469 : Blo 1346992 2023469 := bbase (se 3 (by rfl) ⟨379400, by rfl⟩ : syracuseStep 2023469 = 758801) (by norm_num)
theorem B12959797 : Blo 1346992 12959797 := bbase (se 5 (by rfl) ⟨607490, by rfl⟩ : syracuseStep 12959797 = 1214981) (by norm_num)
theorem B1515577 : Blo 1346992 1515577 := bbase (se 2 (by rfl) ⟨568341, by rfl⟩ : syracuseStep 1515577 = 1136683) (by norm_num)
theorem B3031109 : Blo 1346992 3031109 := bbase (se 4 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 3031109 = 568333) (by norm_num)
theorem B1515613 : Blo 1346992 1515613 := bbase (se 3 (by rfl) ⟨284177, by rfl⟩ : syracuseStep 1515613 = 568355) (by norm_num)
theorem B5120117 : Blo 1346992 5120117 := bbase (se 5 (by rfl) ⟨240005, by rfl⟩ : syracuseStep 5120117 = 480011) (by norm_num)
theorem B1515649 : Blo 1346992 1515649 := bbase (se 2 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 1515649 = 1136737) (by norm_num)
theorem B3031181 : Blo 1346992 3031181 := bbase (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) (by norm_num)
theorem B1515685 : Blo 1346992 1515685 := bbase (se 4 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 1515685 = 284191) (by norm_num)
theorem B1515721 : Blo 1346992 1515721 := bbase (se 2 (by rfl) ⟨568395, by rfl⟩ : syracuseStep 1515721 = 1136791) (by norm_num)
theorem B3031253 : Blo 1346992 3031253 := bbase (se 7 (by rfl) ⟨35522, by rfl⟩ : syracuseStep 3031253 = 71045) (by norm_num)
theorem B1515757 : Blo 1346992 1515757 := bbase (se 3 (by rfl) ⟨284204, by rfl⟩ : syracuseStep 1515757 = 568409) (by norm_num)
theorem B4497653 : Blo 1346992 4497653 := bbase (se 5 (by rfl) ⟨210827, by rfl⟩ : syracuseStep 4497653 = 421655) (by norm_num)
theorem B1515793 : Blo 1346992 1515793 := bbase (se 2 (by rfl) ⟨568422, by rfl⟩ : syracuseStep 1515793 = 1136845) (by norm_num)
theorem B3031325 : Blo 1346992 3031325 := bbase (se 3 (by rfl) ⟨568373, by rfl⟩ : syracuseStep 3031325 = 1136747) (by norm_num)
theorem B4546853 : Blo 1346992 4546853 := bbase (se 4 (by rfl) ⟨426267, by rfl⟩ : syracuseStep 4546853 = 852535) (by norm_num)
theorem B1515829 : Blo 1346992 1515829 := bbase (se 5 (by rfl) ⟨71054, by rfl⟩ : syracuseStep 1515829 = 142109) (by norm_num)
theorem B1515865 : Blo 1346992 1515865 := bbase (se 2 (by rfl) ⟨568449, by rfl⟩ : syracuseStep 1515865 = 1136899) (by norm_num)
theorem B3031397 : Blo 1346992 3031397 := bbase (se 4 (by rfl) ⟨284193, by rfl⟩ : syracuseStep 3031397 = 568387) (by norm_num)
theorem B1515901 : Blo 1346992 1515901 := bbase (se 3 (by rfl) ⟨284231, by rfl⟩ : syracuseStep 1515901 = 568463) (by norm_num)
theorem B5120405 : Blo 1346992 5120405 := bbase (se 6 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 5120405 = 240019) (by norm_num)
theorem B6152597 : Blo 1346992 6152597 := bbase (se 6 (by rfl) ⟨144201, by rfl⟩ : syracuseStep 6152597 = 288403) (by norm_num)
theorem B1515937 : Blo 1346992 1515937 := bbase (se 2 (by rfl) ⟨568476, by rfl⟩ : syracuseStep 1515937 = 1136953) (by norm_num)
theorem B3031469 : Blo 1346992 3031469 := bbase (se 3 (by rfl) ⟨568400, by rfl⟩ : syracuseStep 3031469 = 1136801) (by norm_num)
theorem B1515973 : Blo 1346992 1515973 := bbase (se 4 (by rfl) ⟨142122, by rfl⟩ : syracuseStep 1515973 = 284245) (by norm_num)
theorem B2769365 : Blo 1346992 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B1516009 : Blo 1346992 1516009 := bbase (se 2 (by rfl) ⟨568503, by rfl⟩ : syracuseStep 1516009 = 1137007) (by norm_num)
theorem B3031541 : Blo 1346992 3031541 := bbase (se 5 (by rfl) ⟨142103, by rfl⟩ : syracuseStep 3031541 = 284207) (by norm_num)
theorem B8634869 : Blo 1346992 8634869 := bbase (se 5 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 8634869 = 809519) (by norm_num)
theorem B1516045 : Blo 1346992 1516045 := bbase (se 3 (by rfl) ⟨284258, by rfl⟩ : syracuseStep 1516045 = 568517) (by norm_num)
theorem B1516081 : Blo 1346992 1516081 := bbase (se 2 (by rfl) ⟨568530, by rfl⟩ : syracuseStep 1516081 = 1137061) (by norm_num)
theorem B3031613 : Blo 1346992 3031613 := bbase (se 3 (by rfl) ⟨568427, by rfl⟩ : syracuseStep 3031613 = 1136855) (by norm_num)
theorem B1516117 : Blo 1346992 1516117 := bbase (se 8 (by rfl) ⟨8883, by rfl⟩ : syracuseStep 1516117 = 17767) (by norm_num)
theorem B1516153 : Blo 1346992 1516153 := bbase (se 2 (by rfl) ⟨568557, by rfl⟩ : syracuseStep 1516153 = 1137115) (by norm_num)
theorem B3031685 : Blo 1346992 3031685 := bbase (se 4 (by rfl) ⟨284220, by rfl⟩ : syracuseStep 3031685 = 568441) (by norm_num)
theorem B1516189 : Blo 1346992 1516189 := bbase (se 3 (by rfl) ⟨284285, by rfl⟩ : syracuseStep 1516189 = 568571) (by norm_num)
theorem B1516225 : Blo 1346992 1516225 := bbase (se 2 (by rfl) ⟨568584, by rfl⟩ : syracuseStep 1516225 = 1137169) (by norm_num)
theorem B3031757 : Blo 1346992 3031757 := bbase (se 3 (by rfl) ⟨568454, by rfl⟩ : syracuseStep 3031757 = 1136909) (by norm_num)
theorem B4547285 : Blo 1346992 4547285 := bbase (se 7 (by rfl) ⟨53288, by rfl⟩ : syracuseStep 4547285 = 106577) (by norm_num)
theorem B13837013 : Blo 1346992 13837013 := bbase (se 7 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 13837013 = 324305) (by norm_num)
theorem B4096741 : Blo 1346992 4096741 := bbase (se 4 (by rfl) ⟨384069, by rfl⟩ : syracuseStep 4096741 = 768139) (by norm_num)
theorem B1516261 : Blo 1346992 1516261 := bbase (se 4 (by rfl) ⟨142149, by rfl⟩ : syracuseStep 1516261 = 284299) (by norm_num)
theorem B1516297 : Blo 1346992 1516297 := bbase (se 2 (by rfl) ⟨568611, by rfl⟩ : syracuseStep 1516297 = 1137223) (by norm_num)
theorem B3031829 : Blo 1346992 3031829 := bbase (se 6 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 3031829 = 142117) (by norm_num)
theorem B5464853 : Blo 1346992 5464853 := bbase (se 6 (by rfl) ⟨128082, by rfl⟩ : syracuseStep 5464853 = 256165) (by norm_num)
theorem B1516333 : Blo 1346992 1516333 := bbase (se 3 (by rfl) ⟨284312, by rfl⟩ : syracuseStep 1516333 = 568625) (by norm_num)
theorem B1516369 : Blo 1346992 1516369 := bbase (se 2 (by rfl) ⟨568638, by rfl⟩ : syracuseStep 1516369 = 1137277) (by norm_num)
theorem B3236701 : Blo 1346992 3236701 := bbase (se 3 (by rfl) ⟨606881, by rfl⟩ : syracuseStep 3236701 = 1213763) (by norm_num)
theorem B3031901 : Blo 1346992 3031901 := bbase (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) (by norm_num)
theorem B1704817 : Blo 1346992 1704817 := bbase (se 2 (by rfl) ⟨639306, by rfl⟩ : syracuseStep 1704817 = 1278613) (by norm_num)
theorem B1516405 : Blo 1346992 1516405 := bbase (se 5 (by rfl) ⟨71081, by rfl⟩ : syracuseStep 1516405 = 142163) (by norm_num)
theorem B1516441 : Blo 1346992 1516441 := bbase (se 2 (by rfl) ⟨568665, by rfl⟩ : syracuseStep 1516441 = 1137331) (by norm_num)
theorem B3031973 : Blo 1346992 3031973 := bbase (se 4 (by rfl) ⟨284247, by rfl⟩ : syracuseStep 3031973 = 568495) (by norm_num)
theorem B1516477 : Blo 1346992 1516477 := bbase (se 3 (by rfl) ⟨284339, by rfl⟩ : syracuseStep 1516477 = 568679) (by norm_num)
theorem B1516513 : Blo 1346992 1516513 := bbase (se 2 (by rfl) ⟨568692, by rfl⟩ : syracuseStep 1516513 = 1137385) (by norm_num)
theorem B3032045 : Blo 1346992 3032045 := bbase (se 3 (by rfl) ⟨568508, by rfl⟩ : syracuseStep 3032045 = 1137017) (by norm_num)
theorem B1663997 : Blo 1346992 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B1516549 : Blo 1346992 1516549 := bbase (se 4 (by rfl) ⟨142176, by rfl⟩ : syracuseStep 1516549 = 284353) (by norm_num)
theorem B1917965 : Blo 1346992 1917965 := bbase (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) (by norm_num)
theorem B1704989 : Blo 1346992 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B1516585 : Blo 1346992 1516585 := bbase (se 2 (by rfl) ⟨568719, by rfl⟩ : syracuseStep 1516585 = 1137439) (by norm_num)
theorem B3032117 : Blo 1346992 3032117 := bbase (se 5 (by rfl) ⟨142130, by rfl⟩ : syracuseStep 3032117 = 284261) (by norm_num)
theorem B1516621 : Blo 1346992 1516621 := bbase (se 3 (by rfl) ⟨284366, by rfl⟩ : syracuseStep 1516621 = 568733) (by norm_num)
theorem B1705045 : Blo 1346992 1705045 := bbase (se 8 (by rfl) ⟨9990, by rfl⟩ : syracuseStep 1705045 = 19981) (by norm_num)
theorem B10937429 : Blo 1346992 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B1516657 : Blo 1346992 1516657 := bbase (se 2 (by rfl) ⟨568746, by rfl⟩ : syracuseStep 1516657 = 1137493) (by norm_num)
theorem B3032189 : Blo 1346992 3032189 := bbase (se 3 (by rfl) ⟨568535, by rfl⟩ : syracuseStep 3032189 = 1137071) (by norm_num)
theorem B4547717 : Blo 1346992 4547717 := bbase (se 4 (by rfl) ⟨426348, by rfl⟩ : syracuseStep 4547717 = 852697) (by norm_num)
theorem B1729669 : Blo 1346992 1729669 := bbase (se 4 (by rfl) ⟨162156, by rfl⟩ : syracuseStep 1729669 = 324313) (by norm_num)
theorem B3458189 : Blo 1346992 3458189 := bbase (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) (by norm_num)
theorem B6915221 : Blo 1346992 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B1516693 : Blo 1346992 1516693 := bbase (se 6 (by rfl) ⟨35547, by rfl⟩ : syracuseStep 1516693 = 71095) (by norm_num)
theorem B3237029 : Blo 1346992 3237029 := bbase (se 4 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 3237029 = 606943) (by norm_num)
theorem B1705141 : Blo 1346992 1705141 := bbase (se 5 (by rfl) ⟨79928, by rfl⟩ : syracuseStep 1705141 = 159857) (by norm_num)
theorem B1516729 : Blo 1346992 1516729 := bbase (se 2 (by rfl) ⟨568773, by rfl⟩ : syracuseStep 1516729 = 1137547) (by norm_num)
theorem B3032261 : Blo 1346992 3032261 := bbase (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) (by norm_num)
theorem B3237085 : Blo 1346992 3237085 := bbase (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) (by norm_num)
theorem B1516765 : Blo 1346992 1516765 := bbase (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) (by norm_num)
theorem B1516801 : Blo 1346992 1516801 := bbase (se 2 (by rfl) ⟨568800, by rfl⟩ : syracuseStep 1516801 = 1137601) (by norm_num)
theorem B6825221 : Blo 1346992 6825221 := bbase (se 4 (by rfl) ⟨639864, by rfl⟩ : syracuseStep 6825221 = 1279729) (by norm_num)
theorem B3032333 : Blo 1346992 3032333 := bbase (se 3 (by rfl) ⟨568562, by rfl⟩ : syracuseStep 3032333 = 1137125) (by norm_num)
theorem B1516837 : Blo 1346992 1516837 := bbase (se 4 (by rfl) ⟨142203, by rfl⟩ : syracuseStep 1516837 = 284407) (by norm_num)
theorem B1516873 : Blo 1346992 1516873 := bbase (se 2 (by rfl) ⟨568827, by rfl⟩ : syracuseStep 1516873 = 1137655) (by norm_num)
theorem B3032405 : Blo 1346992 3032405 := bbase (se 12 (by rfl) ⟨1110, by rfl⟩ : syracuseStep 3032405 = 2221) (by norm_num)
theorem B1705313 : Blo 1346992 1705313 := bbase (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) (by norm_num)
theorem B1516909 : Blo 1346992 1516909 := bbase (se 3 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 1516909 = 568841) (by norm_num)
theorem B4097413 : Blo 1346992 4097413 := bbase (se 4 (by rfl) ⟨384132, by rfl⟩ : syracuseStep 4097413 = 768265) (by norm_num)
theorem B2557325 : Blo 1346992 2557325 := bbase (se 3 (by rfl) ⟨479498, by rfl⟩ : syracuseStep 2557325 = 958997) (by norm_num)
theorem B1516945 : Blo 1346992 1516945 := bbase (se 2 (by rfl) ⟨568854, by rfl⟩ : syracuseStep 1516945 = 1137709) (by norm_num)
theorem B1705369 : Blo 1346992 1705369 := bbase (se 2 (by rfl) ⟨639513, by rfl⟩ : syracuseStep 1705369 = 1279027) (by norm_num)
theorem B3032477 : Blo 1346992 3032477 := bbase (se 3 (by rfl) ⟨568589, by rfl⟩ : syracuseStep 3032477 = 1137179) (by norm_num)
theorem B1516981 : Blo 1346992 1516981 := bbase (se 5 (by rfl) ⟨71108, by rfl⟩ : syracuseStep 1516981 = 142217) (by norm_num)
theorem B3237317 : Blo 1346992 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B1517017 : Blo 1346992 1517017 := bbase (se 2 (by rfl) ⟨568881, by rfl⟩ : syracuseStep 1517017 = 1137763) (by norm_num)
theorem B3032549 : Blo 1346992 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B6481397 : Blo 1346992 6481397 := bbase (se 5 (by rfl) ⟨303815, by rfl⟩ : syracuseStep 6481397 = 607631) (by norm_num)
theorem B1705465 : Blo 1346992 1705465 := bbase (se 2 (by rfl) ⟨639549, by rfl⟩ : syracuseStep 1705465 = 1279099) (by norm_num)
theorem B1517053 : Blo 1346992 1517053 := bbase (se 3 (by rfl) ⟨284447, by rfl⟩ : syracuseStep 1517053 = 568895) (by norm_num)
theorem B2336261 : Blo 1346992 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B2557469 : Blo 1346992 2557469 := bbase (se 3 (by rfl) ⟨479525, by rfl⟩ : syracuseStep 2557469 = 959051) (by norm_num)
theorem B1517089 : Blo 1346992 1517089 := bbase (se 2 (by rfl) ⟨568908, by rfl⟩ : syracuseStep 1517089 = 1137817) (by norm_num)
theorem B3032621 : Blo 1346992 3032621 := bbase (se 3 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 3032621 = 1137233) (by norm_num)
theorem B4548149 : Blo 1346992 4548149 := bbase (se 5 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 4548149 = 426389) (by norm_num)
theorem B5121589 : Blo 1346992 5121589 := bbase (se 5 (by rfl) ⟨240074, by rfl⟩ : syracuseStep 5121589 = 480149) (by norm_num)
theorem B1517125 : Blo 1346992 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1517161 : Blo 1346992 1517161 := bbase (se 2 (by rfl) ⟨568935, by rfl⟩ : syracuseStep 1517161 = 1137871) (by norm_num)
theorem B1730161 : Blo 1346992 1730161 := bbase (se 2 (by rfl) ⟨648810, by rfl⟩ : syracuseStep 1730161 = 1297621) (by norm_num)
theorem B3032693 : Blo 1346992 3032693 := bbase (se 5 (by rfl) ⟨142157, by rfl⟩ : syracuseStep 3032693 = 284315) (by norm_num)
theorem B3237509 : Blo 1346992 3237509 := bbase (se 4 (by rfl) ⟨303516, by rfl⟩ : syracuseStep 3237509 = 607033) (by norm_num)
theorem B1517197 : Blo 1346992 1517197 := bbase (se 3 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 1517197 = 568949) (by norm_num)
theorem B21849749 : Blo 1346992 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B1705637 : Blo 1346992 1705637 := bbase (se 4 (by rfl) ⟨159903, by rfl⟩ : syracuseStep 1705637 = 319807) (by norm_num)
theorem B2049709 : Blo 1346992 2049709 := bbase (se 3 (by rfl) ⟨384320, by rfl⟩ : syracuseStep 2049709 = 768641) (by norm_num)
theorem B1517233 : Blo 1346992 1517233 := bbase (se 2 (by rfl) ⟨568962, by rfl⟩ : syracuseStep 1517233 = 1137925) (by norm_num)
theorem B3032765 : Blo 1346992 3032765 := bbase (se 3 (by rfl) ⟨568643, by rfl⟩ : syracuseStep 3032765 = 1137287) (by norm_num)
theorem B2049733 : Blo 1346992 2049733 := bbase (se 4 (by rfl) ⟨192162, by rfl⟩ : syracuseStep 2049733 = 384325) (by norm_num)
theorem B4318933 : Blo 1346992 4318933 := bbase (se 7 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 4318933 = 101225) (by norm_num)
theorem B1517269 : Blo 1346992 1517269 := bbase (se 7 (by rfl) ⟨17780, by rfl⟩ : syracuseStep 1517269 = 35561) (by norm_num)
theorem B24610517 : Blo 1346992 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B1705693 : Blo 1346992 1705693 := bbase (se 3 (by rfl) ⟨319817, by rfl⟩ : syracuseStep 1705693 = 639635) (by norm_num)
theorem B1517305 : Blo 1346992 1517305 := bbase (se 2 (by rfl) ⟨568989, by rfl⟩ : syracuseStep 1517305 = 1137979) (by norm_num)
theorem B3032837 : Blo 1346992 3032837 := bbase (se 4 (by rfl) ⟨284328, by rfl⟩ : syracuseStep 3032837 = 568657) (by norm_num)
theorem B3409685 : Blo 1346992 3409685 := bbase (se 6 (by rfl) ⟨79914, by rfl⟩ : syracuseStep 3409685 = 159829) (by norm_num)
theorem B1517341 : Blo 1346992 1517341 := bbase (se 3 (by rfl) ⟨284501, by rfl⟩ : syracuseStep 1517341 = 569003) (by norm_num)
theorem B2877221 : Blo 1346992 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B2557757 : Blo 1346992 2557757 := bbase (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) (by norm_num)
theorem B1705789 : Blo 1346992 1705789 := bbase (se 3 (by rfl) ⟨319835, by rfl⟩ : syracuseStep 1705789 = 639671) (by norm_num)
theorem B1517377 : Blo 1346992 1517377 := bbase (se 2 (by rfl) ⟨569016, by rfl⟩ : syracuseStep 1517377 = 1138033) (by norm_num)
theorem B3032909 : Blo 1346992 3032909 := bbase (se 3 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 3032909 = 1137341) (by norm_num)
theorem B1517413 : Blo 1346992 1517413 := bbase (se 4 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 1517413 = 284515) (by norm_num)
theorem B5121893 : Blo 1346992 5121893 := bbase (se 4 (by rfl) ⟨480177, by rfl⟩ : syracuseStep 5121893 = 960355) (by norm_num)
theorem B3073909 : Blo 1346992 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B1517449 : Blo 1346992 1517449 := bbase (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) (by norm_num)
theorem B3032981 : Blo 1346992 3032981 := bbase (se 6 (by rfl) ⟨71085, by rfl⟩ : syracuseStep 3032981 = 142171) (by norm_num)
theorem B2770861 : Blo 1346992 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B1517485 : Blo 1346992 1517485 := bbase (se 3 (by rfl) ⟨284528, by rfl⟩ : syracuseStep 1517485 = 569057) (by norm_num)
theorem B1517521 : Blo 1346992 1517521 := bbase (se 2 (by rfl) ⟨569070, by rfl⟩ : syracuseStep 1517521 = 1138141) (by norm_num)
theorem B3409877 : Blo 1346992 3409877 := bbase (se 7 (by rfl) ⟨39959, by rfl⟩ : syracuseStep 3409877 = 79919) (by norm_num)
theorem B2557909 : Blo 1346992 2557909 := bbase (se 7 (by rfl) ⟨29975, by rfl⟩ : syracuseStep 2557909 = 59951) (by norm_num)
theorem B3033053 : Blo 1346992 3033053 := bbase (se 3 (by rfl) ⟨568697, by rfl⟩ : syracuseStep 3033053 = 1137395) (by norm_num)
theorem B4548581 : Blo 1346992 4548581 := bbase (se 4 (by rfl) ⟨426429, by rfl⟩ : syracuseStep 4548581 = 852859) (by norm_num)
theorem B1705961 : Blo 1346992 1705961 := bbase (se 2 (by rfl) ⟨639735, by rfl⟩ : syracuseStep 1705961 = 1279471) (by norm_num)
theorem B1517557 : Blo 1346992 1517557 := bbase (se 5 (by rfl) ⟨71135, by rfl⟩ : syracuseStep 1517557 = 142271) (by norm_num)
theorem B1517593 : Blo 1346992 1517593 := bbase (se 2 (by rfl) ⟨569097, by rfl⟩ : syracuseStep 1517593 = 1138195) (by norm_num)
theorem B1706017 : Blo 1346992 1706017 := bbase (se 2 (by rfl) ⟨639756, by rfl⟩ : syracuseStep 1706017 = 1279513) (by norm_num)
theorem B3033125 : Blo 1346992 3033125 := bbase (se 4 (by rfl) ⟨284355, by rfl⟩ : syracuseStep 3033125 = 568711) (by norm_num)
theorem B5187685 : Blo 1346992 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B3033197 : Blo 1346992 3033197 := bbase (se 3 (by rfl) ⟨568724, by rfl⟩ : syracuseStep 3033197 = 1137449) (by norm_num)
theorem B1706113 : Blo 1346992 1706113 := bbase (se 2 (by rfl) ⟨639792, by rfl⟩ : syracuseStep 1706113 = 1279585) (by norm_num)
theorem B14567573 : Blo 1346992 14567573 := bbase (se 6 (by rfl) ⟨341427, by rfl⟩ : syracuseStep 14567573 = 682855) (by norm_num)
theorem B2959517 : Blo 1346992 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B3033269 : Blo 1346992 3033269 := bbase (se 5 (by rfl) ⟨142184, by rfl⟩ : syracuseStep 3033269 = 284369) (by norm_num)
theorem B44902613 : Blo 1346992 44902613 := bbase (se 7 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 44902613 = 1052405) (by norm_num)
theorem B3033341 : Blo 1346992 3033341 := bbase (se 3 (by rfl) ⟨568751, by rfl⟩ : syracuseStep 3033341 = 1137503) (by norm_num)
theorem B2558213 : Blo 1346992 2558213 := bbase (se 4 (by rfl) ⟨239832, by rfl⟩ : syracuseStep 2558213 = 479665) (by norm_num)
theorem B3410221 : Blo 1346992 3410221 := bbase (se 3 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 3410221 = 1278833) (by norm_num)
theorem B1706285 : Blo 1346992 1706285 := bbase (se 3 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 1706285 = 639857) (by norm_num)
theorem B3033413 : Blo 1346992 3033413 := bbase (se 4 (by rfl) ⟨284382, by rfl⟩ : syracuseStep 3033413 = 568765) (by norm_num)
theorem B15354197 : Blo 1346992 15354197 := bbase (se 10 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 15354197 = 44983) (by norm_num)
theorem B3836261 : Blo 1346992 3836261 := bbase (se 4 (by rfl) ⟨359649, by rfl⟩ : syracuseStep 3836261 = 719299) (by norm_num)
theorem B1706341 : Blo 1346992 1706341 := bbase (se 4 (by rfl) ⟨159969, by rfl⟩ : syracuseStep 1706341 = 319939) (by norm_num)
theorem B4098421 : Blo 1346992 4098421 := bbase (se 5 (by rfl) ⟨192113, by rfl⟩ : syracuseStep 4098421 = 384227) (by norm_num)
theorem B3033485 : Blo 1346992 3033485 := bbase (se 3 (by rfl) ⟨568778, by rfl⟩ : syracuseStep 3033485 = 1137557) (by norm_num)
theorem B4549013 : Blo 1346992 4549013 := bbase (se 6 (by rfl) ⟨106617, by rfl⟩ : syracuseStep 4549013 = 213235) (by norm_num)
theorem B3410333 : Blo 1346992 3410333 := bbase (se 3 (by rfl) ⟨639437, by rfl⟩ : syracuseStep 3410333 = 1278875) (by norm_num)
theorem B1919389 : Blo 1346992 1919389 := bbase (se 3 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 1919389 = 719771) (by norm_num)
theorem B1706437 : Blo 1346992 1706437 := bbase (se 4 (by rfl) ⟨159978, by rfl⟩ : syracuseStep 1706437 = 319957) (by norm_num)
theorem B7678421 : Blo 1346992 7678421 := bbase (se 7 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 7678421 = 179963) (by norm_num)
theorem B3033557 : Blo 1346992 3033557 := bbase (se 7 (by rfl) ⟨35549, by rfl⟩ : syracuseStep 3033557 = 71099) (by norm_num)
theorem B3893717 : Blo 1346992 3893717 := bbase (se 7 (by rfl) ⟨45629, by rfl⟩ : syracuseStep 3893717 = 91259) (by norm_num)
theorem B6826517 : Blo 1346992 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B3033629 : Blo 1346992 3033629 := bbase (se 3 (by rfl) ⟨568805, by rfl⟩ : syracuseStep 3033629 = 1137611) (by norm_num)
theorem B1944101 : Blo 1346992 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B3238469 : Blo 1346992 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B3410525 : Blo 1346992 3410525 := bbase (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) (by norm_num)
theorem B3033701 : Blo 1346992 3033701 := bbase (se 4 (by rfl) ⟨284409, by rfl⟩ : syracuseStep 3033701 = 568819) (by norm_num)
theorem B5761637 : Blo 1346992 5761637 := bbase (se 4 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 5761637 = 1080307) (by norm_num)
theorem B1706609 : Blo 1346992 1706609 := bbase (se 2 (by rfl) ⟨639978, by rfl⟩ : syracuseStep 1706609 = 1279957) (by norm_num)
theorem B2878085 : Blo 1346992 2878085 := bbase (se 4 (by rfl) ⟨269820, by rfl⟩ : syracuseStep 2878085 = 539641) (by norm_num)
theorem B1706665 : Blo 1346992 1706665 := bbase (se 2 (by rfl) ⟨639999, by rfl⟩ : syracuseStep 1706665 = 1279999) (by norm_num)
theorem B3033773 : Blo 1346992 3033773 := bbase (se 3 (by rfl) ⟨568832, by rfl⟩ : syracuseStep 3033773 = 1137665) (by norm_num)
theorem B3033845 : Blo 1346992 3033845 := bbase (se 5 (by rfl) ⟨142211, by rfl⟩ : syracuseStep 3033845 = 284423) (by norm_num)
theorem B1706761 : Blo 1346992 1706761 := bbase (se 2 (by rfl) ⟨640035, by rfl⟩ : syracuseStep 1706761 = 1280071) (by norm_num)
theorem B2878229 : Blo 1346992 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B3033917 : Blo 1346992 3033917 := bbase (se 3 (by rfl) ⟨568859, by rfl⟩ : syracuseStep 3033917 = 1137719) (by norm_num)
theorem B1821509 : Blo 1346992 1821509 := bbase (se 4 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 1821509 = 341533) (by norm_num)
theorem B4549445 : Blo 1346992 4549445 := bbase (se 4 (by rfl) ⟨426510, by rfl⟩ : syracuseStep 4549445 = 853021) (by norm_num)
theorem B3033989 : Blo 1346992 3033989 := bbase (se 4 (by rfl) ⟨284436, by rfl⟩ : syracuseStep 3033989 = 568873) (by norm_num)
theorem B4860805 : Blo 1346992 4860805 := bbase (se 4 (by rfl) ⟨455700, by rfl⟩ : syracuseStep 4860805 = 911401) (by norm_num)
theorem B5761925 : Blo 1346992 5761925 := bbase (se 4 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 5761925 = 1080361) (by norm_num)
theorem B3410869 : Blo 1346992 3410869 := bbase (se 5 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 3410869 = 319769) (by norm_num)
theorem B1706933 : Blo 1346992 1706933 := bbase (se 5 (by rfl) ⟨80012, by rfl⟩ : syracuseStep 1706933 = 160025) (by norm_num)
theorem B3034061 : Blo 1346992 3034061 := bbase (se 3 (by rfl) ⟨568886, by rfl⟩ : syracuseStep 3034061 = 1137773) (by norm_num)
theorem B1919981 : Blo 1346992 1919981 := bbase (se 3 (by rfl) ⟨359996, by rfl⟩ : syracuseStep 1919981 = 719993) (by norm_num)
theorem B1706989 : Blo 1346992 1706989 := bbase (se 3 (by rfl) ⟨320060, by rfl⟩ : syracuseStep 1706989 = 640121) (by norm_num)
theorem B2558965 : Blo 1346992 2558965 := bbase (se 5 (by rfl) ⟨119951, by rfl⟩ : syracuseStep 2558965 = 239903) (by norm_num)
theorem B5753861 : Blo 1346992 5753861 := bbase (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) (by norm_num)
theorem B3836933 : Blo 1346992 3836933 := bbase (se 4 (by rfl) ⟨359712, by rfl⟩ : syracuseStep 3836933 = 719425) (by norm_num)
theorem B3075077 : Blo 1346992 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B3034133 : Blo 1346992 3034133 := bbase (se 6 (by rfl) ⟨71112, by rfl⟩ : syracuseStep 3034133 = 142225) (by norm_num)
theorem B3410981 : Blo 1346992 3410981 := bbase (se 4 (by rfl) ⟨319779, by rfl⟩ : syracuseStep 3410981 = 639559) (by norm_num)
theorem B1920061 : Blo 1346992 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B1707085 : Blo 1346992 1707085 := bbase (se 3 (by rfl) ⟨320078, by rfl⟩ : syracuseStep 1707085 = 640157) (by norm_num)
theorem B3034205 : Blo 1346992 3034205 := bbase (se 3 (by rfl) ⟨568913, by rfl⟩ : syracuseStep 3034205 = 1137827) (by norm_num)
theorem B2559109 : Blo 1346992 2559109 := bbase (se 4 (by rfl) ⟨239916, by rfl⟩ : syracuseStep 2559109 = 479833) (by norm_num)
theorem B3034277 : Blo 1346992 3034277 := bbase (se 4 (by rfl) ⟨284463, by rfl⟩ : syracuseStep 3034277 = 568927) (by norm_num)
theorem B1920181 : Blo 1346992 1920181 := bbase (se 5 (by rfl) ⟨90008, by rfl⟩ : syracuseStep 1920181 = 180017) (by norm_num)
theorem B3411173 : Blo 1346992 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B3034349 : Blo 1346992 3034349 := bbase (se 3 (by rfl) ⟨568940, by rfl⟩ : syracuseStep 3034349 = 1137881) (by norm_num)
theorem B4549877 : Blo 1346992 4549877 := bbase (se 5 (by rfl) ⟨213275, by rfl⟩ : syracuseStep 4549877 = 426551) (by norm_num)
theorem B1707257 : Blo 1346992 1707257 := bbase (se 2 (by rfl) ⟨640221, by rfl⟩ : syracuseStep 1707257 = 1280443) (by norm_num)
theorem B1920277 : Blo 1346992 1920277 := bbase (se 6 (by rfl) ⟨45006, by rfl⟩ : syracuseStep 1920277 = 90013) (by norm_num)
theorem B2559269 : Blo 1346992 2559269 := bbase (se 4 (by rfl) ⟨239931, by rfl⟩ : syracuseStep 2559269 = 479863) (by norm_num)
theorem B1707313 : Blo 1346992 1707313 := bbase (se 2 (by rfl) ⟨640242, by rfl⟩ : syracuseStep 1707313 = 1280485) (by norm_num)
theorem B3034421 : Blo 1346992 3034421 := bbase (se 5 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 3034421 = 284477) (by norm_num)
theorem B3034493 : Blo 1346992 3034493 := bbase (se 3 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 3034493 = 1137935) (by norm_num)
theorem B3837365 : Blo 1346992 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B2559413 : Blo 1346992 2559413 := bbase (se 5 (by rfl) ⟨119972, by rfl⟩ : syracuseStep 2559413 = 239945) (by norm_num)
theorem B3034565 : Blo 1346992 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B25898453 : Blo 1346992 25898453 := bbase (se 7 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 25898453 = 606995) (by norm_num)
theorem B2878973 : Blo 1346992 2878973 := bbase (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) (by norm_num)
theorem B1822213 : Blo 1346992 1822213 := bbase (se 4 (by rfl) ⟨170832, by rfl⟩ : syracuseStep 1822213 = 341665) (by norm_num)
theorem B3034637 : Blo 1346992 3034637 := bbase (se 3 (by rfl) ⟨568994, by rfl⟩ : syracuseStep 3034637 = 1137989) (by norm_num)
theorem B2592317 : Blo 1346992 2592317 := bbase (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) (by norm_num)
theorem B3411517 : Blo 1346992 3411517 := bbase (se 3 (by rfl) ⟨639659, by rfl⟩ : syracuseStep 3411517 = 1279319) (by norm_num)
theorem B10923605 : Blo 1346992 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B3034709 : Blo 1346992 3034709 := bbase (se 8 (by rfl) ⟨17781, by rfl⟩ : syracuseStep 3034709 = 35563) (by norm_num)
theorem B11513461 : Blo 1346992 11513461 := bbase (se 5 (by rfl) ⟨539693, by rfl⟩ : syracuseStep 11513461 = 1079387) (by norm_num)
theorem B3034781 : Blo 1346992 3034781 := bbase (se 3 (by rfl) ⟨569021, by rfl⟩ : syracuseStep 3034781 = 1138043) (by norm_num)
theorem B4550309 : Blo 1346992 4550309 := bbase (se 4 (by rfl) ⟨426591, by rfl⟩ : syracuseStep 4550309 = 853183) (by norm_num)
theorem B3411629 : Blo 1346992 3411629 := bbase (se 3 (by rfl) ⟨639680, by rfl⟩ : syracuseStep 3411629 = 1279361) (by norm_num)
theorem B2920133 : Blo 1346992 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B2559701 : Blo 1346992 2559701 := bbase (se 7 (by rfl) ⟨29996, by rfl⟩ : syracuseStep 2559701 = 59993) (by norm_num)
theorem B1822429 : Blo 1346992 1822429 := bbase (se 3 (by rfl) ⟨341705, by rfl⟩ : syracuseStep 1822429 = 683411) (by norm_num)
theorem B3034853 : Blo 1346992 3034853 := bbase (se 4 (by rfl) ⟨284517, by rfl⟩ : syracuseStep 3034853 = 569035) (by norm_num)
theorem B6827813 : Blo 1346992 6827813 := bbase (se 4 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 6827813 = 1280215) (by norm_num)
theorem B2273069 : Blo 1346992 2273069 := bbase (se 3 (by rfl) ⟨426200, by rfl⟩ : syracuseStep 2273069 = 852401) (by norm_num)
theorem B3034925 : Blo 1346992 3034925 := bbase (se 3 (by rfl) ⟨569048, by rfl⟩ : syracuseStep 3034925 = 1138097) (by norm_num)
theorem B2158429 : Blo 1346992 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B3411821 : Blo 1346992 3411821 := bbase (se 3 (by rfl) ⟨639716, by rfl⟩ : syracuseStep 3411821 = 1279433) (by norm_num)
theorem B2559853 : Blo 1346992 2559853 := bbase (se 3 (by rfl) ⟨479972, by rfl⟩ : syracuseStep 2559853 = 959945) (by norm_num)
theorem B3034997 : Blo 1346992 3034997 := bbase (se 5 (by rfl) ⟨142265, by rfl⟩ : syracuseStep 3034997 = 284531) (by norm_num)
theorem B2273197 : Blo 1346992 2273197 := bbase (se 3 (by rfl) ⟨426224, by rfl⟩ : syracuseStep 2273197 = 852449) (by norm_num)
theorem B3035069 : Blo 1346992 3035069 := bbase (se 3 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 3035069 = 1138151) (by norm_num)
theorem B16404437 : Blo 1346992 16404437 := bbase (se 7 (by rfl) ⟨192239, by rfl⟩ : syracuseStep 16404437 = 384479) (by norm_num)
theorem B2732005 : Blo 1346992 2732005 := bbase (se 4 (by rfl) ⟨256125, by rfl⟩ : syracuseStep 2732005 = 512251) (by norm_num)
theorem B2273285 : Blo 1346992 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B3035141 : Blo 1346992 3035141 := bbase (se 4 (by rfl) ⟨284544, by rfl⟩ : syracuseStep 3035141 = 569089) (by norm_num)
theorem B3035213 : Blo 1346992 3035213 := bbase (se 3 (by rfl) ⟨569102, by rfl⟩ : syracuseStep 3035213 = 1138205) (by norm_num)
theorem B4550741 : Blo 1346992 4550741 := bbase (se 8 (by rfl) ⟨26664, by rfl⟩ : syracuseStep 4550741 = 53329) (by norm_num)
theorem B2273413 : Blo 1346992 2273413 := bbase (se 4 (by rfl) ⟨213132, by rfl⟩ : syracuseStep 2273413 = 426265) (by norm_num)
theorem B12963989 : Blo 1346992 12963989 := bbase (se 6 (by rfl) ⟨303843, by rfl⟩ : syracuseStep 12963989 = 607687) (by norm_num)
theorem B2560157 : Blo 1346992 2560157 := bbase (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) (by norm_num)
theorem B3838117 : Blo 1346992 3838117 := bbase (se 4 (by rfl) ⟨359823, by rfl⟩ : syracuseStep 3838117 = 719647) (by norm_num)
theorem B6820037 : Blo 1346992 6820037 := bbase (se 4 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 6820037 = 1278757) (by norm_num)
theorem B3412165 : Blo 1346992 3412165 := bbase (se 4 (by rfl) ⟨319890, by rfl⟩ : syracuseStep 3412165 = 639781) (by norm_num)
theorem B2273501 : Blo 1346992 2273501 := bbase (se 3 (by rfl) ⟨426281, by rfl⟩ : syracuseStep 2273501 = 852563) (by norm_num)
theorem B2879725 : Blo 1346992 2879725 := bbase (se 3 (by rfl) ⟨539948, by rfl⟩ : syracuseStep 2879725 = 1079897) (by norm_num)
theorem B1822981 : Blo 1346992 1822981 := bbase (se 4 (by rfl) ⟨170904, by rfl⟩ : syracuseStep 1822981 = 341809) (by norm_num)
theorem B2158877 : Blo 1346992 2158877 := bbase (se 3 (by rfl) ⟨404789, by rfl⟩ : syracuseStep 2158877 = 809579) (by norm_num)
theorem B3412277 : Blo 1346992 3412277 := bbase (se 5 (by rfl) ⟨159950, by rfl⟩ : syracuseStep 3412277 = 319901) (by norm_num)
theorem B5116229 : Blo 1346992 5116229 := bbase (se 4 (by rfl) ⟨479646, by rfl⟩ : syracuseStep 5116229 = 959293) (by norm_num)
theorem B2273629 : Blo 1346992 2273629 := bbase (se 3 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 2273629 = 852611) (by norm_num)
theorem B2879869 : Blo 1346992 2879869 := bbase (se 3 (by rfl) ⟨539975, by rfl⟩ : syracuseStep 2879869 = 1079951) (by norm_num)
theorem B3641765 : Blo 1346992 3641765 := bbase (se 4 (by rfl) ⟨341415, by rfl⟩ : syracuseStep 3641765 = 682831) (by norm_num)
theorem B2273717 : Blo 1346992 2273717 := bbase (se 5 (by rfl) ⟨106580, by rfl⟩ : syracuseStep 2273717 = 213161) (by norm_num)
theorem B2429365 : Blo 1346992 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B3076589 : Blo 1346992 3076589 := bbase (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) (by norm_num)
theorem B3412469 : Blo 1346992 3412469 := bbase (se 5 (by rfl) ⟨159959, by rfl⟩ : syracuseStep 3412469 = 319919) (by norm_num)
theorem B4551173 : Blo 1346992 4551173 := bbase (se 4 (by rfl) ⟨426672, by rfl⟩ : syracuseStep 4551173 = 853345) (by norm_num)
theorem B13824533 : Blo 1346992 13824533 := bbase (se 6 (by rfl) ⟨324012, by rfl⟩ : syracuseStep 13824533 = 648025) (by norm_num)
theorem B2273845 : Blo 1346992 2273845 := bbase (se 5 (by rfl) ⟨106586, by rfl⟩ : syracuseStep 2273845 = 213173) (by norm_num)
theorem B5116517 : Blo 1346992 5116517 := bbase (se 4 (by rfl) ⟨479673, by rfl⟩ : syracuseStep 5116517 = 959347) (by norm_num)
theorem B2273933 : Blo 1346992 2273933 := bbase (se 3 (by rfl) ⟨426362, by rfl⟩ : syracuseStep 2273933 = 852725) (by norm_num)
theorem B5755637 : Blo 1346992 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B2880245 : Blo 1346992 2880245 := bbase (se 5 (by rfl) ⟨135011, by rfl⟩ : syracuseStep 2880245 = 270023) (by norm_num)
theorem B2274061 : Blo 1346992 2274061 := bbase (se 3 (by rfl) ⟨426386, by rfl⟩ : syracuseStep 2274061 = 852773) (by norm_num)
theorem B3412813 : Blo 1346992 3412813 := bbase (se 3 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 3412813 = 1279805) (by norm_num)
theorem B2274149 : Blo 1346992 2274149 := bbase (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) (by norm_num)
theorem B2560909 : Blo 1346992 2560909 := bbase (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) (by norm_num)
theorem B4551605 : Blo 1346992 4551605 := bbase (se 5 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 4551605 = 426713) (by norm_num)
theorem B3412925 : Blo 1346992 3412925 := bbase (se 3 (by rfl) ⟨639923, by rfl⟩ : syracuseStep 3412925 = 1279847) (by norm_num)
theorem B14578645 : Blo 1346992 14578645 := bbase (se 7 (by rfl) ⟨170843, by rfl⟩ : syracuseStep 14578645 = 341687) (by norm_num)
theorem B2593757 : Blo 1346992 2593757 := bbase (se 3 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 2593757 = 972659) (by norm_num)
theorem B2274277 : Blo 1346992 2274277 := bbase (se 4 (by rfl) ⟨213213, by rfl⟩ : syracuseStep 2274277 = 426427) (by norm_num)
theorem B1618961 : Blo 1346992 1618961 := bbase (se 2 (by rfl) ⟨607110, by rfl⟩ : syracuseStep 1618961 = 1214221) (by norm_num)
theorem B1618985 : Blo 1346992 1618985 := bbase (se 2 (by rfl) ⟨607119, by rfl⟩ : syracuseStep 1618985 = 1214239) (by norm_num)
theorem B1438769 : Blo 1346992 1438769 := bbase (se 2 (by rfl) ⟨539538, by rfl⟩ : syracuseStep 1438769 = 1079077) (by norm_num)
theorem B2430005 : Blo 1346992 2430005 := bbase (se 5 (by rfl) ⟨113906, by rfl⟩ : syracuseStep 2430005 = 227813) (by norm_num)
theorem B6829109 : Blo 1346992 6829109 := bbase (se 5 (by rfl) ⟨320114, by rfl⟩ : syracuseStep 6829109 = 640229) (by norm_num)
theorem B2274365 : Blo 1346992 2274365 := bbase (se 3 (by rfl) ⟨426443, by rfl⟩ : syracuseStep 2274365 = 852887) (by norm_num)
theorem B1971301 : Blo 1346992 1971301 := bbase (se 4 (by rfl) ⟨184809, by rfl⟩ : syracuseStep 1971301 = 369619) (by norm_num)
theorem B2880613 : Blo 1346992 2880613 := bbase (se 4 (by rfl) ⟨270057, by rfl⟩ : syracuseStep 2880613 = 540115) (by norm_num)
theorem B1438841 : Blo 1346992 1438841 := bbase (se 2 (by rfl) ⟨539565, by rfl⟩ : syracuseStep 1438841 = 1079131) (by norm_num)
theorem B3413117 : Blo 1346992 3413117 := bbase (se 3 (by rfl) ⟨639959, by rfl⟩ : syracuseStep 3413117 = 1279919) (by norm_num)
theorem B2020493 : Blo 1346992 2020493 := bbase (se 3 (by rfl) ⟨378842, by rfl⟩ : syracuseStep 2020493 = 757685) (by norm_num)
theorem B2020517 : Blo 1346992 2020517 := bbase (se 4 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 2020517 = 378847) (by norm_num)
theorem B2020541 : Blo 1346992 2020541 := bbase (se 3 (by rfl) ⟨378851, by rfl⟩ : syracuseStep 2020541 = 757703) (by norm_num)
theorem B2274493 : Blo 1346992 2274493 := bbase (se 3 (by rfl) ⟨426467, by rfl⟩ : syracuseStep 2274493 = 852935) (by norm_num)
theorem B2020565 : Blo 1346992 2020565 := bbase (se 7 (by rfl) ⟨23678, by rfl⟩ : syracuseStep 2020565 = 47357) (by norm_num)
theorem B2495701 : Blo 1346992 2495701 := bbase (se 7 (by rfl) ⟨29246, by rfl⟩ : syracuseStep 2495701 = 58493) (by norm_num)
theorem B2020589 : Blo 1346992 2020589 := bbase (se 3 (by rfl) ⟨378860, by rfl⟩ : syracuseStep 2020589 = 757721) (by norm_num)
theorem B2020613 : Blo 1346992 2020613 := bbase (se 4 (by rfl) ⟨189432, by rfl⟩ : syracuseStep 2020613 = 378865) (by norm_num)
theorem B2274581 : Blo 1346992 2274581 := bbase (se 6 (by rfl) ⟨53310, by rfl⟩ : syracuseStep 2274581 = 106621) (by norm_num)
theorem B3241237 : Blo 1346992 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B2020637 : Blo 1346992 2020637 := bbase (se 3 (by rfl) ⟨378869, by rfl⟩ : syracuseStep 2020637 = 757739) (by norm_num)
theorem B2020661 : Blo 1346992 2020661 := bbase (se 5 (by rfl) ⟨94718, by rfl⟩ : syracuseStep 2020661 = 189437) (by norm_num)
theorem B1439029 : Blo 1346992 1439029 := bbase (se 5 (by rfl) ⟨67454, by rfl⟩ : syracuseStep 1439029 = 134909) (by norm_num)
theorem B2020685 : Blo 1346992 2020685 := bbase (se 3 (by rfl) ⟨378878, by rfl⟩ : syracuseStep 2020685 = 757757) (by norm_num)
theorem B1619293 : Blo 1346992 1619293 := bbase (se 3 (by rfl) ⟨303617, by rfl⟩ : syracuseStep 1619293 = 607235) (by norm_num)
theorem B2020709 : Blo 1346992 2020709 := bbase (se 4 (by rfl) ⟨189441, by rfl⟩ : syracuseStep 2020709 = 378883) (by norm_num)
theorem B4552037 : Blo 1346992 4552037 := bbase (se 4 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 4552037 = 853507) (by norm_num)
theorem B2020733 : Blo 1346992 2020733 := bbase (se 3 (by rfl) ⟨378887, by rfl⟩ : syracuseStep 2020733 = 757775) (by norm_num)
theorem B2020757 : Blo 1346992 2020757 := bbase (se 6 (by rfl) ⟨47361, by rfl⟩ : syracuseStep 2020757 = 94723) (by norm_num)
theorem B2274709 : Blo 1346992 2274709 := bbase (se 6 (by rfl) ⟨53313, by rfl⟩ : syracuseStep 2274709 = 106627) (by norm_num)
theorem B2020781 : Blo 1346992 2020781 := bbase (se 3 (by rfl) ⟨378896, by rfl⟩ : syracuseStep 2020781 = 757793) (by norm_num)
theorem B2020805 : Blo 1346992 2020805 := bbase (se 4 (by rfl) ⟨189450, by rfl⟩ : syracuseStep 2020805 = 378901) (by norm_num)
theorem B6821333 : Blo 1346992 6821333 := bbase (se 7 (by rfl) ⟨79937, by rfl⟩ : syracuseStep 6821333 = 159875) (by norm_num)
theorem B3413461 : Blo 1346992 3413461 := bbase (se 7 (by rfl) ⟨40001, by rfl⟩ : syracuseStep 3413461 = 80003) (by norm_num)
theorem B2020829 : Blo 1346992 2020829 := bbase (se 3 (by rfl) ⟨378905, by rfl⟩ : syracuseStep 2020829 = 757811) (by norm_num)
theorem B1439213 : Blo 1346992 1439213 := bbase (se 3 (by rfl) ⟨269852, by rfl⟩ : syracuseStep 1439213 = 539705) (by norm_num)
theorem B2274797 : Blo 1346992 2274797 := bbase (se 3 (by rfl) ⟨426524, by rfl⟩ : syracuseStep 2274797 = 853049) (by norm_num)
theorem B2020853 : Blo 1346992 2020853 := bbase (se 5 (by rfl) ⟨94727, by rfl⟩ : syracuseStep 2020853 = 189455) (by norm_num)
theorem B1619465 : Blo 1346992 1619465 := bbase (se 2 (by rfl) ⟨607299, by rfl⟩ : syracuseStep 1619465 = 1214599) (by norm_num)
theorem B2020877 : Blo 1346992 2020877 := bbase (se 3 (by rfl) ⟨378914, by rfl⟩ : syracuseStep 2020877 = 757829) (by norm_num)
theorem B2020901 : Blo 1346992 2020901 := bbase (se 4 (by rfl) ⟨189459, by rfl⟩ : syracuseStep 2020901 = 378919) (by norm_num)
theorem B11515445 : Blo 1346992 11515445 := bbase (se 5 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 11515445 = 1079573) (by norm_num)
theorem B2020925 : Blo 1346992 2020925 := bbase (se 3 (by rfl) ⟨378923, by rfl⟩ : syracuseStep 2020925 = 757847) (by norm_num)
theorem B6567493 : Blo 1346992 6567493 := bbase (se 4 (by rfl) ⟨615702, by rfl⟩ : syracuseStep 6567493 = 1231405) (by norm_num)
theorem B3413573 : Blo 1346992 3413573 := bbase (se 4 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 3413573 = 640045) (by norm_num)
theorem B2020949 : Blo 1346992 2020949 := bbase (se 8 (by rfl) ⟨11841, by rfl⟩ : syracuseStep 2020949 = 23683) (by norm_num)
theorem B2020973 : Blo 1346992 2020973 := bbase (se 3 (by rfl) ⟨378932, by rfl⟩ : syracuseStep 2020973 = 757865) (by norm_num)
theorem B2274925 : Blo 1346992 2274925 := bbase (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) (by norm_num)
theorem B1619581 : Blo 1346992 1619581 := bbase (se 3 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 1619581 = 607343) (by norm_num)
theorem B2020997 : Blo 1346992 2020997 := bbase (se 4 (by rfl) ⟨189468, by rfl⟩ : syracuseStep 2020997 = 378937) (by norm_num)
theorem B10237589 : Blo 1346992 10237589 := bbase (se 6 (by rfl) ⟨239943, by rfl⟩ : syracuseStep 10237589 = 479887) (by norm_num)
theorem B2021021 : Blo 1346992 2021021 := bbase (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) (by norm_num)
theorem B2021045 : Blo 1346992 2021045 := bbase (se 5 (by rfl) ⟨94736, by rfl⟩ : syracuseStep 2021045 = 189473) (by norm_num)
theorem B2275013 : Blo 1346992 2275013 := bbase (se 4 (by rfl) ⟨213282, by rfl⟩ : syracuseStep 2275013 = 426565) (by norm_num)
theorem B2021069 : Blo 1346992 2021069 := bbase (se 3 (by rfl) ⟨378950, by rfl⟩ : syracuseStep 2021069 = 757901) (by norm_num)
theorem B8632021 : Blo 1346992 8632021 := bbase (se 7 (by rfl) ⟨101156, by rfl⟩ : syracuseStep 8632021 = 202313) (by norm_num)
theorem B5756629 : Blo 1346992 5756629 := bbase (se 7 (by rfl) ⟨67460, by rfl⟩ : syracuseStep 5756629 = 134921) (by norm_num)
theorem B1619677 : Blo 1346992 1619677 := bbase (se 3 (by rfl) ⟨303689, by rfl⟩ : syracuseStep 1619677 = 607379) (by norm_num)
theorem B2021093 : Blo 1346992 2021093 := bbase (se 4 (by rfl) ⟨189477, by rfl⟩ : syracuseStep 2021093 = 378955) (by norm_num)
theorem B2023421 : Blo 1346992 2023421 := bbase (se 3 (by rfl) ⟨379391, by rfl⟩ : syracuseStep 2023421 = 758783) (by norm_num)
theorem B2021117 : Blo 1346992 2021117 := bbase (se 3 (by rfl) ⟨378959, by rfl⟩ : syracuseStep 2021117 = 757919) (by norm_num)
theorem B5117701 : Blo 1346992 5117701 := bbase (se 4 (by rfl) ⟨479784, by rfl⟩ : syracuseStep 5117701 = 959569) (by norm_num)
theorem B3413765 : Blo 1346992 3413765 := bbase (se 4 (by rfl) ⟨320040, by rfl⟩ : syracuseStep 3413765 = 640081) (by norm_num)
theorem B2160389 : Blo 1346992 2160389 := bbase (se 4 (by rfl) ⟨202536, by rfl⟩ : syracuseStep 2160389 = 405073) (by norm_num)
theorem B2021141 : Blo 1346992 2021141 := bbase (se 6 (by rfl) ⟨47370, by rfl⟩ : syracuseStep 2021141 = 94741) (by norm_num)
theorem B4552469 : Blo 1346992 4552469 := bbase (se 6 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 4552469 = 213397) (by norm_num)
theorem B2021165 : Blo 1346992 2021165 := bbase (se 3 (by rfl) ⟨378968, by rfl⟩ : syracuseStep 2021165 = 757937) (by norm_num)
theorem B2021189 : Blo 1346992 2021189 := bbase (se 4 (by rfl) ⟨189486, by rfl⟩ : syracuseStep 2021189 = 378973) (by norm_num)
theorem B2275141 : Blo 1346992 2275141 := bbase (se 4 (by rfl) ⟨213294, by rfl⟩ : syracuseStep 2275141 = 426589) (by norm_num)
theorem B2021213 : Blo 1346992 2021213 := bbase (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) (by norm_num)
theorem B1619821 : Blo 1346992 1619821 := bbase (se 3 (by rfl) ⟨303716, by rfl⟩ : syracuseStep 1619821 = 607433) (by norm_num)
theorem B2021237 : Blo 1346992 2021237 := bbase (se 5 (by rfl) ⟨94745, by rfl⟩ : syracuseStep 2021237 = 189491) (by norm_num)
theorem B2160517 : Blo 1346992 2160517 := bbase (se 4 (by rfl) ⟨202548, by rfl⟩ : syracuseStep 2160517 = 405097) (by norm_num)
theorem B2021261 : Blo 1346992 2021261 := bbase (se 3 (by rfl) ⟨378986, by rfl⟩ : syracuseStep 2021261 = 757973) (by norm_num)
theorem B2275229 : Blo 1346992 2275229 := bbase (se 3 (by rfl) ⟨426605, by rfl⟩ : syracuseStep 2275229 = 853211) (by norm_num)
theorem B2021285 : Blo 1346992 2021285 := bbase (se 4 (by rfl) ⟨189495, by rfl⟩ : syracuseStep 2021285 = 378991) (by norm_num)
theorem B2021309 : Blo 1346992 2021309 := bbase (se 3 (by rfl) ⟨378995, by rfl⟩ : syracuseStep 2021309 = 757991) (by norm_num)
theorem B2021333 : Blo 1346992 2021333 := bbase (se 7 (by rfl) ⟨23687, by rfl⟩ : syracuseStep 2021333 = 47375) (by norm_num)
theorem B6920149 : Blo 1346992 6920149 := bbase (se 7 (by rfl) ⟨81095, by rfl⟩ : syracuseStep 6920149 = 162191) (by norm_num)
theorem B2021357 : Blo 1346992 2021357 := bbase (se 3 (by rfl) ⟨379004, by rfl⟩ : syracuseStep 2021357 = 758009) (by norm_num)
theorem B2021381 : Blo 1346992 2021381 := bbase (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) (by norm_num)
theorem B2021405 : Blo 1346992 2021405 := bbase (se 3 (by rfl) ⟨379013, by rfl⟩ : syracuseStep 2021405 = 758027) (by norm_num)
theorem B2275357 : Blo 1346992 2275357 := bbase (se 3 (by rfl) ⟨426629, by rfl⟩ : syracuseStep 2275357 = 853259) (by norm_num)
theorem B10229813 : Blo 1346992 10229813 := bbase (se 5 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 10229813 = 959045) (by norm_num)
theorem B2021429 : Blo 1346992 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B5118005 : Blo 1346992 5118005 := bbase (se 5 (by rfl) ⟨239906, by rfl⟩ : syracuseStep 5118005 = 479813) (by norm_num)
theorem B8755253 : Blo 1346992 8755253 := bbase (se 5 (by rfl) ⟨410402, by rfl⟩ : syracuseStep 8755253 = 820805) (by norm_num)
theorem B2021453 : Blo 1346992 2021453 := bbase (se 3 (by rfl) ⟨379022, by rfl⟩ : syracuseStep 2021453 = 758045) (by norm_num)
theorem B3414109 : Blo 1346992 3414109 := bbase (se 3 (by rfl) ⟨640145, by rfl⟩ : syracuseStep 3414109 = 1280291) (by norm_num)
theorem B2021477 : Blo 1346992 2021477 := bbase (se 4 (by rfl) ⟨189513, by rfl⟩ : syracuseStep 2021477 = 379027) (by norm_num)
theorem B2275445 : Blo 1346992 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B2021501 : Blo 1346992 2021501 := bbase (se 3 (by rfl) ⟨379031, by rfl⟩ : syracuseStep 2021501 = 758063) (by norm_num)
theorem B2021525 : Blo 1346992 2021525 := bbase (se 6 (by rfl) ⟨47379, by rfl⟩ : syracuseStep 2021525 = 94759) (by norm_num)
theorem B2021549 : Blo 1346992 2021549 := bbase (se 3 (by rfl) ⟨379040, by rfl⟩ : syracuseStep 2021549 = 758081) (by norm_num)
theorem B2021573 : Blo 1346992 2021573 := bbase (se 4 (by rfl) ⟨189522, by rfl⟩ : syracuseStep 2021573 = 379045) (by norm_num)
theorem B3414221 : Blo 1346992 3414221 := bbase (se 3 (by rfl) ⟨640166, by rfl⟩ : syracuseStep 3414221 = 1280333) (by norm_num)
theorem B2021597 : Blo 1346992 2021597 := bbase (se 3 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 2021597 = 758099) (by norm_num)
theorem B1439965 : Blo 1346992 1439965 := bbase (se 3 (by rfl) ⟨269993, by rfl⟩ : syracuseStep 1439965 = 539987) (by norm_num)
theorem B5462261 : Blo 1346992 5462261 := bbase (se 5 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 5462261 = 512087) (by norm_num)
theorem B2021621 : Blo 1346992 2021621 := bbase (se 5 (by rfl) ⟨94763, by rfl⟩ : syracuseStep 2021621 = 189527) (by norm_num)
theorem B2275573 : Blo 1346992 2275573 := bbase (se 5 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 2275573 = 213335) (by norm_num)
theorem B2021645 : Blo 1346992 2021645 := bbase (se 3 (by rfl) ⟨379058, by rfl⟩ : syracuseStep 2021645 = 758117) (by norm_num)
theorem B2021669 : Blo 1346992 2021669 := bbase (se 4 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 2021669 = 379063) (by norm_num)
theorem B1440037 : Blo 1346992 1440037 := bbase (se 4 (by rfl) ⟨135003, by rfl⟩ : syracuseStep 1440037 = 270007) (by norm_num)
theorem B2021693 : Blo 1346992 2021693 := bbase (se 3 (by rfl) ⟨379067, by rfl⟩ : syracuseStep 2021693 = 758135) (by norm_num)
theorem B2275661 : Blo 1346992 2275661 := bbase (se 3 (by rfl) ⟨426686, by rfl⟩ : syracuseStep 2275661 = 853373) (by norm_num)
theorem B2021717 : Blo 1346992 2021717 := bbase (se 10 (by rfl) ⟨2961, by rfl⟩ : syracuseStep 2021717 = 5923) (by norm_num)
theorem B2021741 : Blo 1346992 2021741 := bbase (se 3 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 2021741 = 758153) (by norm_num)
theorem B2021765 : Blo 1346992 2021765 := bbase (se 4 (by rfl) ⟨189540, by rfl⟩ : syracuseStep 2021765 = 379081) (by norm_num)
theorem B3414413 : Blo 1346992 3414413 := bbase (se 3 (by rfl) ⟨640202, by rfl⟩ : syracuseStep 3414413 = 1280405) (by norm_num)
theorem B7289237 : Blo 1346992 7289237 := bbase (se 6 (by rfl) ⟨170841, by rfl⟩ : syracuseStep 7289237 = 341683) (by norm_num)
theorem B2021789 : Blo 1346992 2021789 := bbase (se 3 (by rfl) ⟨379085, by rfl⟩ : syracuseStep 2021789 = 758171) (by norm_num)
theorem B2021813 : Blo 1346992 2021813 := bbase (se 5 (by rfl) ⟨94772, by rfl⟩ : syracuseStep 2021813 = 189545) (by norm_num)
theorem B4315589 : Blo 1346992 4315589 := bbase (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) (by norm_num)
theorem B2021837 : Blo 1346992 2021837 := bbase (se 3 (by rfl) ⟨379094, by rfl⟩ : syracuseStep 2021837 = 758189) (by norm_num)
theorem B2275789 : Blo 1346992 2275789 := bbase (se 3 (by rfl) ⟨426710, by rfl⟩ : syracuseStep 2275789 = 853421) (by norm_num)
theorem B1440217 : Blo 1346992 1440217 := bbase (se 2 (by rfl) ⟨540081, by rfl⟩ : syracuseStep 1440217 = 1080163) (by norm_num)
theorem B4610533 : Blo 1346992 4610533 := bbase (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) (by norm_num)
theorem B2021861 : Blo 1346992 2021861 := bbase (se 4 (by rfl) ⟨189549, by rfl⟩ : syracuseStep 2021861 = 379099) (by norm_num)
theorem B2021885 : Blo 1346992 2021885 := bbase (se 3 (by rfl) ⟨379103, by rfl⟩ : syracuseStep 2021885 = 758207) (by norm_num)
theorem B2021909 : Blo 1346992 2021909 := bbase (se 6 (by rfl) ⟨47388, by rfl⟩ : syracuseStep 2021909 = 94777) (by norm_num)
theorem B2275877 : Blo 1346992 2275877 := bbase (se 4 (by rfl) ⟨213363, by rfl⟩ : syracuseStep 2275877 = 426727) (by norm_num)
theorem B2021933 : Blo 1346992 2021933 := bbase (se 3 (by rfl) ⟨379112, by rfl⟩ : syracuseStep 2021933 = 758225) (by norm_num)
theorem B2021957 : Blo 1346992 2021957 := bbase (se 4 (by rfl) ⟨189558, by rfl⟩ : syracuseStep 2021957 = 379117) (by norm_num)
theorem B2808389 : Blo 1346992 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B2021981 : Blo 1346992 2021981 := bbase (se 3 (by rfl) ⟨379121, by rfl⟩ : syracuseStep 2021981 = 758243) (by norm_num)
theorem B2022005 : Blo 1346992 2022005 := bbase (se 5 (by rfl) ⟨94781, by rfl⟩ : syracuseStep 2022005 = 189563) (by norm_num)
theorem B2022029 : Blo 1346992 2022029 := bbase (se 3 (by rfl) ⟨379130, by rfl⟩ : syracuseStep 2022029 = 758261) (by norm_num)
theorem B2022053 : Blo 1346992 2022053 := bbase (se 4 (by rfl) ⟨189567, by rfl⟩ : syracuseStep 2022053 = 379135) (by norm_num)
theorem B2276005 : Blo 1346992 2276005 := bbase (se 4 (by rfl) ⟨213375, by rfl⟩ : syracuseStep 2276005 = 426751) (by norm_num)
theorem B2022077 : Blo 1346992 2022077 := bbase (se 3 (by rfl) ⟨379139, by rfl⟩ : syracuseStep 2022077 = 758279) (by norm_num)
theorem B2022101 : Blo 1346992 2022101 := bbase (se 7 (by rfl) ⟨23696, by rfl⟩ : syracuseStep 2022101 = 47393) (by norm_num)
theorem B6822629 : Blo 1346992 6822629 := bbase (se 4 (by rfl) ⟨639621, by rfl⟩ : syracuseStep 6822629 = 1279243) (by norm_num)
theorem B2022125 : Blo 1346992 2022125 := bbase (se 3 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 2022125 = 758297) (by norm_num)
theorem B1366777 : Blo 1346992 1366777 := bbase (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) (by norm_num)
theorem B2276093 : Blo 1346992 2276093 := bbase (se 3 (by rfl) ⟨426767, by rfl⟩ : syracuseStep 2276093 = 853535) (by norm_num)
theorem B2022149 : Blo 1346992 2022149 := bbase (se 4 (by rfl) ⟨189576, by rfl⟩ : syracuseStep 2022149 = 379153) (by norm_num)
theorem B6478613 : Blo 1346992 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B2022173 : Blo 1346992 2022173 := bbase (se 3 (by rfl) ⟨379157, by rfl⟩ : syracuseStep 2022173 = 758315) (by norm_num)
theorem B2022197 : Blo 1346992 2022197 := bbase (se 5 (by rfl) ⟨94790, by rfl⟩ : syracuseStep 2022197 = 189581) (by norm_num)
theorem B2022221 : Blo 1346992 2022221 := bbase (se 3 (by rfl) ⟨379166, by rfl⟩ : syracuseStep 2022221 = 758333) (by norm_num)
theorem B13130581 : Blo 1346992 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B2022245 : Blo 1346992 2022245 := bbase (se 4 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 2022245 = 379171) (by norm_num)
theorem B2022269 : Blo 1346992 2022269 := bbase (se 3 (by rfl) ⟨379175, by rfl⟩ : syracuseStep 2022269 = 758351) (by norm_num)
theorem B2276221 : Blo 1346992 2276221 := bbase (se 3 (by rfl) ⟨426791, by rfl⟩ : syracuseStep 2276221 = 853583) (by norm_num)
theorem B2022293 : Blo 1346992 2022293 := bbase (se 6 (by rfl) ⟨47397, by rfl⟩ : syracuseStep 2022293 = 94795) (by norm_num)
theorem B2022317 : Blo 1346992 2022317 := bbase (se 3 (by rfl) ⟨379184, by rfl⟩ : syracuseStep 2022317 = 758369) (by norm_num)
theorem B2022341 : Blo 1346992 2022341 := bbase (se 4 (by rfl) ⟨189594, by rfl⟩ : syracuseStep 2022341 = 379189) (by norm_num)
theorem B3840965 : Blo 1346992 3840965 := bbase (se 4 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 3840965 = 720181) (by norm_num)
theorem B2276309 : Blo 1346992 2276309 := bbase (se 7 (by rfl) ⟨26675, by rfl⟩ : syracuseStep 2276309 = 53351) (by norm_num)
theorem B2022365 : Blo 1346992 2022365 := bbase (se 3 (by rfl) ⟨379193, by rfl⟩ : syracuseStep 2022365 = 758387) (by norm_num)
theorem B2022389 : Blo 1346992 2022389 := bbase (se 5 (by rfl) ⟨94799, by rfl⟩ : syracuseStep 2022389 = 189599) (by norm_num)
theorem B4676597 : Blo 1346992 4676597 := bbase (se 5 (by rfl) ⟨219215, by rfl⟩ : syracuseStep 4676597 = 438431) (by norm_num)
theorem B2022413 : Blo 1346992 2022413 := bbase (se 3 (by rfl) ⟨379202, by rfl⟩ : syracuseStep 2022413 = 758405) (by norm_num)
theorem B2022437 : Blo 1346992 2022437 := bbase (se 4 (by rfl) ⟨189603, by rfl⟩ : syracuseStep 2022437 = 379207) (by norm_num)
theorem B2022461 : Blo 1346992 2022461 := bbase (se 3 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 2022461 = 758423) (by norm_num)
theorem B2022485 : Blo 1346992 2022485 := bbase (se 8 (by rfl) ⟨11850, by rfl⟩ : syracuseStep 2022485 = 23701) (by norm_num)
theorem B2022509 : Blo 1346992 2022509 := bbase (se 3 (by rfl) ⟨379220, by rfl⟩ : syracuseStep 2022509 = 758441) (by norm_num)
theorem B2022533 : Blo 1346992 2022533 := bbase (se 4 (by rfl) ⟨189612, by rfl⟩ : syracuseStep 2022533 = 379225) (by norm_num)
theorem B2022557 : Blo 1346992 2022557 := bbase (se 3 (by rfl) ⟨379229, by rfl⟩ : syracuseStep 2022557 = 758459) (by norm_num)
theorem B2022581 : Blo 1346992 2022581 := bbase (se 5 (by rfl) ⟨94808, by rfl⟩ : syracuseStep 2022581 = 189617) (by norm_num)
theorem B2022605 : Blo 1346992 2022605 := bbase (se 3 (by rfl) ⟨379238, by rfl⟩ : syracuseStep 2022605 = 758477) (by norm_num)
theorem B2022629 : Blo 1346992 2022629 := bbase (se 4 (by rfl) ⟨189621, by rfl⟩ : syracuseStep 2022629 = 379243) (by norm_num)
theorem B2022653 : Blo 1346992 2022653 := bbase (se 3 (by rfl) ⟨379247, by rfl⟩ : syracuseStep 2022653 = 758495) (by norm_num)
theorem B2022677 : Blo 1346992 2022677 := bbase (se 6 (by rfl) ⟨47406, by rfl⟩ : syracuseStep 2022677 = 94813) (by norm_num)
theorem B1367317 : Blo 1346992 1367317 := bbase (se 6 (by rfl) ⟨32046, by rfl⟩ : syracuseStep 1367317 = 64093) (by norm_num)
theorem B2022701 : Blo 1346992 2022701 := bbase (se 3 (by rfl) ⟨379256, by rfl⟩ : syracuseStep 2022701 = 758513) (by norm_num)
theorem B2022725 : Blo 1346992 2022725 := bbase (se 4 (by rfl) ⟨189630, by rfl⟩ : syracuseStep 2022725 = 379261) (by norm_num)
theorem B2022749 : Blo 1346992 2022749 := bbase (se 3 (by rfl) ⟨379265, by rfl⟩ : syracuseStep 2022749 = 758531) (by norm_num)
theorem B2022773 : Blo 1346992 2022773 := bbase (se 5 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 2022773 = 189635) (by norm_num)
theorem B2022797 : Blo 1346992 2022797 := bbase (se 3 (by rfl) ⟨379274, by rfl⟩ : syracuseStep 2022797 = 758549) (by norm_num)
theorem B2022821 : Blo 1346992 2022821 := bbase (se 4 (by rfl) ⟨189639, by rfl⟩ : syracuseStep 2022821 = 379279) (by norm_num)
theorem B2022845 : Blo 1346992 2022845 := bbase (se 3 (by rfl) ⟨379283, by rfl⟩ : syracuseStep 2022845 = 758567) (by norm_num)
theorem B2022869 : Blo 1346992 2022869 := bbase (se 7 (by rfl) ⟨23705, by rfl⟩ : syracuseStep 2022869 = 47411) (by norm_num)
theorem B2022893 : Blo 1346992 2022893 := bbase (se 3 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 2022893 = 758585) (by norm_num)
theorem B2022917 : Blo 1346992 2022917 := bbase (se 4 (by rfl) ⟨189648, by rfl⟩ : syracuseStep 2022917 = 379297) (by norm_num)
theorem B2022941 : Blo 1346992 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B2022965 : Blo 1346992 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B2022989 : Blo 1346992 2022989 := bbase (se 3 (by rfl) ⟨379310, by rfl⟩ : syracuseStep 2022989 = 758621) (by norm_num)
theorem B2023013 : Blo 1346992 2023013 := bbase (se 4 (by rfl) ⟨189657, by rfl⟩ : syracuseStep 2023013 = 379315) (by norm_num)
theorem B2023037 : Blo 1346992 2023037 := bbase (se 3 (by rfl) ⟨379319, by rfl⟩ : syracuseStep 2023037 = 758639) (by norm_num)
theorem B2023061 : Blo 1346992 2023061 := bbase (se 6 (by rfl) ⟨47415, by rfl⟩ : syracuseStep 2023061 = 94831) (by norm_num)
theorem B12304021 : Blo 1346992 12304021 := bbase (se 6 (by rfl) ⟨288375, by rfl⟩ : syracuseStep 12304021 = 576751) (by norm_num)
theorem B2023085 : Blo 1346992 2023085 := bbase (se 3 (by rfl) ⟨379328, by rfl⟩ : syracuseStep 2023085 = 758657) (by norm_num)
theorem B2023109 : Blo 1346992 2023109 := bbase (se 4 (by rfl) ⟨189666, by rfl⟩ : syracuseStep 2023109 = 379333) (by norm_num)
theorem B3030749 : Blo 1346992 3030749 := bbase (se 3 (by rfl) ⟨568265, by rfl⟩ : syracuseStep 3030749 = 1136531) (by norm_num)
theorem B2023133 : Blo 1346992 2023133 := bbase (se 3 (by rfl) ⟨379337, by rfl⟩ : syracuseStep 2023133 = 758675) (by norm_num)
theorem B2023157 : Blo 1346992 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B4316933 : Blo 1346992 4316933 := bbase (se 4 (by rfl) ⟨404712, by rfl⟩ : syracuseStep 4316933 = 809425) (by norm_num)
theorem B2023181 : Blo 1346992 2023181 := bbase (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) (by norm_num)
theorem B3030821 : Blo 1346992 3030821 := bbase (se 4 (by rfl) ⟨284139, by rfl⟩ : syracuseStep 3030821 = 568279) (by norm_num)
theorem B6913829 : Blo 1346992 6913829 := bbase (se 4 (by rfl) ⟨648171, by rfl⟩ : syracuseStep 6913829 = 1296343) (by norm_num)
theorem B2023205 : Blo 1346992 2023205 := bbase (se 4 (by rfl) ⟨189675, by rfl⟩ : syracuseStep 2023205 = 379351) (by norm_num)
theorem B2023229 : Blo 1346992 2023229 := bbase (se 3 (by rfl) ⟨379355, by rfl⟩ : syracuseStep 2023229 = 758711) (by norm_num)
theorem B3645269 : Blo 1346992 3645269 := bbase (se 9 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 3645269 = 21359) (by norm_num)
theorem B2023253 : Blo 1346992 2023253 := bbase (se 9 (by rfl) ⟨5927, by rfl⟩ : syracuseStep 2023253 = 11855) (by norm_num)
theorem B3284837 : Blo 1346992 3284837 := bbase (se 4 (by rfl) ⟨307953, by rfl⟩ : syracuseStep 3284837 = 615907) (by norm_num)
theorem B3030893 : Blo 1346992 3030893 := bbase (se 3 (by rfl) ⟨568292, by rfl⟩ : syracuseStep 3030893 = 1136585) (by norm_num)
theorem B2023277 : Blo 1346992 2023277 := bbase (se 3 (by rfl) ⟨379364, by rfl⟩ : syracuseStep 2023277 = 758729) (by norm_num)
theorem B4546421 : Blo 1346992 4546421 := bbase (se 5 (by rfl) ⟨213113, by rfl⟩ : syracuseStep 4546421 = 426227) (by norm_num)
theorem B1515397 : Blo 1346992 1515397 := bbase (se 4 (by rfl) ⟨142068, by rfl⟩ : syracuseStep 1515397 = 284137) (by norm_num)
theorem B2023301 : Blo 1346992 2023301 := bbase (se 4 (by rfl) ⟨189684, by rfl⟩ : syracuseStep 2023301 = 379369) (by norm_num)
theorem B2023325 : Blo 1346992 2023325 := bbase (se 3 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 2023325 = 758747) (by norm_num)
theorem B1515433 : Blo 1346992 1515433 := bbase (se 2 (by rfl) ⟨568287, by rfl⟩ : syracuseStep 1515433 = 1136575) (by norm_num)
theorem B3030965 : Blo 1346992 3030965 := bbase (se 5 (by rfl) ⟨142076, by rfl⟩ : syracuseStep 3030965 = 284153) (by norm_num)
theorem B2023349 : Blo 1346992 2023349 := bbase (se 5 (by rfl) ⟨94844, by rfl⟩ : syracuseStep 2023349 = 189689) (by norm_num)
theorem B1458109 : Blo 1346992 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1515469 : Blo 1346992 1515469 := bbase (se 3 (by rfl) ⟨284150, by rfl⟩ : syracuseStep 1515469 = 568301) (by norm_num)
theorem B2023373 : Blo 1346992 2023373 := bbase (se 3 (by rfl) ⟨379382, by rfl⟩ : syracuseStep 2023373 = 758765) (by norm_num)
theorem B2023397 : Blo 1346992 2023397 := bbase (se 4 (by rfl) ⟨189693, by rfl⟩ : syracuseStep 2023397 = 379387) (by norm_num)
theorem B1515505 : Blo 1346992 1515505 := bbase (se 2 (by rfl) ⟨568314, by rfl⟩ : syracuseStep 1515505 = 1136629) (by norm_num)
theorem B6823925 : Blo 1346992 6823925 := bbase (se 5 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 6823925 = 639743) (by norm_num)
theorem B3031037 : Blo 1346992 3031037 := bbase (se 3 (by rfl) ⟨568319, by rfl⟩ : syracuseStep 3031037 = 1136639) (by norm_num)
theorem B1515523 : Blo 1346992 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B2023427 : Blo 1346992 2023427 := bstep (se 1 (by rfl) ⟨1517570, by rfl⟩ : syracuseStep 2023427 = 3035141) B3035141
theorem B2023457 : Blo 1346992 2023457 := bstep (se 2 (by rfl) ⟨758796, by rfl⟩ : syracuseStep 2023457 = 1517593) B1517593
theorem B4317229 : Blo 1346992 4317229 := bstep (se 3 (by rfl) ⟨809480, by rfl⟩ : syracuseStep 4317229 = 1618961) B1618961
theorem B2023475 : Blo 1346992 2023475 := bstep (se 1 (by rfl) ⟨1517606, by rfl⟩ : syracuseStep 2023475 = 3035213) B3035213
theorem B4546637 : Blo 1346992 4546637 := bstep (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) B1704989
theorem B8642659 : Blo 1346992 8642659 := bstep (se 1 (by rfl) ⟨6481994, by rfl⟩ : syracuseStep 8642659 = 12963989) B12963989
theorem B4317293 : Blo 1346992 4317293 := bstep (se 3 (by rfl) ⟨809492, by rfl⟩ : syracuseStep 4317293 = 1618985) B1618985
theorem B4546691 : Blo 1346992 4546691 := bstep (se 1 (by rfl) ⟨3410018, by rfl⟩ : syracuseStep 4546691 = 6820037) B6820037
theorem B6480013 : Blo 1346992 6480013 := bstep (se 3 (by rfl) ⟨1215002, by rfl⟩ : syracuseStep 6480013 = 2430005) B2430005
theorem B1515667 : Blo 1346992 1515667 := bstep (se 1 (by rfl) ⟨1136750, by rfl⟩ : syracuseStep 1515667 = 2273501) B2273501
theorem B3031217 : Blo 1346992 3031217 := bstep (se 2 (by rfl) ⟨1136706, by rfl⟩ : syracuseStep 3031217 = 2273413) B2273413
theorem B3031235 : Blo 1346992 3031235 := bstep (se 1 (by rfl) ⟨2273426, by rfl⟩ : syracuseStep 3031235 = 4546853) B4546853
theorem B1515811 : Blo 1346992 1515811 := bstep (se 1 (by rfl) ⟨1136858, by rfl⟩ : syracuseStep 1515811 = 2273717) B2273717
theorem B9216355 : Blo 1346992 9216355 := bstep (se 1 (by rfl) ⟨6912266, by rfl⟩ : syracuseStep 9216355 = 13824533) B13824533
theorem B38846861 : Blo 1346992 38846861 := bstep (se 3 (by rfl) ⟨7283786, by rfl⟩ : syracuseStep 38846861 = 14567573) B14567573
theorem B4546961 : Blo 1346992 4546961 := bstep (se 2 (by rfl) ⟨1705110, by rfl⟩ : syracuseStep 4546961 = 3410221) B3410221
theorem B1515955 : Blo 1346992 1515955 := bstep (se 1 (by rfl) ⟨1136966, by rfl⟩ : syracuseStep 1515955 = 2273933) B2273933
theorem B3031505 : Blo 1346992 3031505 := bstep (se 2 (by rfl) ⟨1136814, by rfl⟩ : syracuseStep 3031505 = 2273629) B2273629
theorem B3031523 : Blo 1346992 3031523 := bstep (se 1 (by rfl) ⟨2273642, by rfl⟩ : syracuseStep 3031523 = 4547285) B4547285
theorem B9224675 : Blo 1346992 9224675 := bstep (se 1 (by rfl) ⟨6918506, by rfl⟩ : syracuseStep 9224675 = 13837013) B13837013
theorem B1516099 : Blo 1346992 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B11993741 : Blo 1346992 11993741 := bstep (se 3 (by rfl) ⟨2248826, by rfl⟩ : syracuseStep 11993741 = 4497653) B4497653
theorem B1729171 : Blo 1346992 1729171 := bstep (se 1 (by rfl) ⟨1296878, by rfl⟩ : syracuseStep 1729171 = 2593757) B2593757
theorem B1516243 : Blo 1346992 1516243 := bstep (se 1 (by rfl) ⟨1137182, by rfl⟩ : syracuseStep 1516243 = 2274365) B2274365
theorem B7291619 : Blo 1346992 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B3031793 : Blo 1346992 3031793 := bstep (se 2 (by rfl) ⟨1136922, by rfl⟩ : syracuseStep 3031793 = 2273845) B2273845
theorem B3031811 : Blo 1346992 3031811 := bstep (se 1 (by rfl) ⟨2273858, by rfl⟩ : syracuseStep 3031811 = 4547717) B4547717
theorem B1516387 : Blo 1346992 1516387 := bstep (se 1 (by rfl) ⟨1137290, by rfl⟩ : syracuseStep 1516387 = 2274581) B2274581
theorem B4547501 : Blo 1346992 4547501 := bstep (se 3 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 4547501 = 1705313) B1705313
theorem B1704883 : Blo 1346992 1704883 := bstep (se 1 (by rfl) ⟨1278662, by rfl⟩ : syracuseStep 1704883 = 2557325) B2557325
theorem B4547555 : Blo 1346992 4547555 := bstep (se 1 (by rfl) ⟨3410666, by rfl⟩ : syracuseStep 4547555 = 6821333) B6821333
theorem B1516531 : Blo 1346992 1516531 := bstep (se 1 (by rfl) ⟨1137398, by rfl⟩ : syracuseStep 1516531 = 2274797) B2274797
theorem B3032081 : Blo 1346992 3032081 := bstep (se 2 (by rfl) ⟨1137030, by rfl⟩ : syracuseStep 3032081 = 2274061) B2274061
theorem B1704979 : Blo 1346992 1704979 := bstep (se 1 (by rfl) ⟨1278734, by rfl⟩ : syracuseStep 1704979 = 2557469) B2557469
theorem B3032099 : Blo 1346992 3032099 := bstep (se 1 (by rfl) ⟨2274074, by rfl⟩ : syracuseStep 3032099 = 4548149) B4548149
theorem B7676963 : Blo 1346992 7676963 := bstep (se 1 (by rfl) ⟨5757722, by rfl⟩ : syracuseStep 7676963 = 11515445) B11515445
theorem B14566499 : Blo 1346992 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B6825059 : Blo 1346992 6825059 := bstep (se 1 (by rfl) ⟨5118794, by rfl⟩ : syracuseStep 6825059 = 10237589) B10237589
theorem B17507441 : Blo 1346992 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B1516675 : Blo 1346992 1516675 := bstep (se 1 (by rfl) ⟨1137506, by rfl⟩ : syracuseStep 1516675 = 2275013) B2275013
theorem B6481073 : Blo 1346992 6481073 := bstep (se 2 (by rfl) ⟨2430402, by rfl⟩ : syracuseStep 6481073 = 4860805) B4860805
theorem B4547825 : Blo 1346992 4547825 := bstep (se 2 (by rfl) ⟨1705434, by rfl⟩ : syracuseStep 4547825 = 3410869) B3410869
theorem B1516819 : Blo 1346992 1516819 := bstep (se 1 (by rfl) ⟨1137614, by rfl⟩ : syracuseStep 1516819 = 2275229) B2275229
theorem B3032369 : Blo 1346992 3032369 := bstep (se 2 (by rfl) ⟨1137138, by rfl⟩ : syracuseStep 3032369 = 2274277) B2274277
theorem B3032387 : Blo 1346992 3032387 := bstep (se 1 (by rfl) ⟨2274290, by rfl⟩ : syracuseStep 3032387 = 4548581) B4548581
theorem B1516963 : Blo 1346992 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B10241477 : Blo 1346992 10241477 := bstep (se 4 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 10241477 = 1920277) B1920277
theorem B1705475 : Blo 1346992 1705475 := bstep (se 1 (by rfl) ⟨1279106, by rfl⟩ : syracuseStep 1705475 = 2558213) B2558213
theorem B7489037 : Blo 1346992 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B1517107 : Blo 1346992 1517107 := bstep (se 1 (by rfl) ⟨1137830, by rfl⟩ : syracuseStep 1517107 = 2275661) B2275661
theorem B2557507 : Blo 1346992 2557507 := bstep (se 1 (by rfl) ⟨1918130, by rfl⟩ : syracuseStep 2557507 = 3836261) B3836261
theorem B3032657 : Blo 1346992 3032657 := bstep (se 2 (by rfl) ⟨1137246, by rfl⟩ : syracuseStep 3032657 = 2274493) B2274493
theorem B3032675 : Blo 1346992 3032675 := bstep (se 1 (by rfl) ⟨2274506, by rfl⟩ : syracuseStep 3032675 = 4549013) B4549013
theorem B3327601 : Blo 1346992 3327601 := bstep (se 2 (by rfl) ⟨1247850, by rfl⟩ : syracuseStep 3327601 = 2495701) B2495701
theorem B2877059 : Blo 1346992 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B1517251 : Blo 1346992 1517251 := bstep (se 1 (by rfl) ⟨1137938, by rfl⟩ : syracuseStep 1517251 = 2275877) B2275877
theorem B1918723 : Blo 1346992 1918723 := bstep (se 1 (by rfl) ⟨1439042, by rfl⟩ : syracuseStep 1918723 = 2878085) B2878085
theorem B4548365 : Blo 1346992 4548365 := bstep (se 3 (by rfl) ⟨852818, by rfl⟩ : syracuseStep 4548365 = 1705637) B1705637
theorem B4548419 : Blo 1346992 4548419 := bstep (se 1 (by rfl) ⟨3411314, by rfl⟩ : syracuseStep 4548419 = 6822629) B6822629
theorem B1517395 : Blo 1346992 1517395 := bstep (se 1 (by rfl) ⟨1138046, by rfl⟩ : syracuseStep 1517395 = 2276093) B2276093
theorem B1918819 : Blo 1346992 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B4319075 : Blo 1346992 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B3032945 : Blo 1346992 3032945 := bstep (se 2 (by rfl) ⟨1137354, by rfl⟩ : syracuseStep 3032945 = 2274709) B2274709
theorem B3032963 : Blo 1346992 3032963 := bstep (se 1 (by rfl) ⟨2274722, by rfl⟩ : syracuseStep 3032963 = 4549445) B4549445
theorem B6825869 : Blo 1346992 6825869 := bstep (se 3 (by rfl) ⟨1279850, by rfl⟩ : syracuseStep 6825869 = 2559701) B2559701
theorem B21858245 : Blo 1346992 21858245 := bstep (se 4 (by rfl) ⟨2049210, by rfl⟩ : syracuseStep 21858245 = 4098421) B4098421
theorem B1517539 : Blo 1346992 1517539 := bstep (se 1 (by rfl) ⟨1138154, by rfl⟩ : syracuseStep 1517539 = 2276309) B2276309
theorem B3835907 : Blo 1346992 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B2557955 : Blo 1346992 2557955 := bstep (se 1 (by rfl) ⟨1918466, by rfl⟩ : syracuseStep 2557955 = 3836933) B3836933
theorem B2050051 : Blo 1346992 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B11511821 : Blo 1346992 11511821 := bstep (se 3 (by rfl) ⟨2158466, by rfl⟩ : syracuseStep 11511821 = 4316933) B4316933
theorem B5761037 : Blo 1346992 5761037 := bstep (se 3 (by rfl) ⟨1080194, by rfl⟩ : syracuseStep 5761037 = 2160389) B2160389
theorem B4548689 : Blo 1346992 4548689 := bstep (se 2 (by rfl) ⟨1705758, by rfl⟩ : syracuseStep 4548689 = 3411517) B3411517
theorem B3033233 : Blo 1346992 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B3033251 : Blo 1346992 3033251 := bstep (se 1 (by rfl) ⟨2274938, by rfl⟩ : syracuseStep 3033251 = 4549877) B4549877
theorem B1706179 : Blo 1346992 1706179 := bstep (se 1 (by rfl) ⟨1279634, by rfl⟩ : syracuseStep 1706179 = 2559269) B2559269
theorem B2558243 : Blo 1346992 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B1706275 : Blo 1346992 1706275 := bstep (se 1 (by rfl) ⟨1279706, by rfl⟩ : syracuseStep 1706275 = 2559413) B2559413
theorem B1919315 : Blo 1346992 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B3033521 : Blo 1346992 3033521 := bstep (se 2 (by rfl) ⟨1137570, by rfl⟩ : syracuseStep 3033521 = 2275141) B2275141
theorem B3033539 : Blo 1346992 3033539 := bstep (se 1 (by rfl) ⟨2275154, by rfl⟩ : syracuseStep 3033539 = 4550309) B4550309
theorem B2877905 : Blo 1346992 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B4098545 : Blo 1346992 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B2189891 : Blo 1346992 2189891 := bstep (se 1 (by rfl) ⟨1642418, by rfl⟩ : syracuseStep 2189891 = 3284837) B3284837
theorem B1944145 : Blo 1346992 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B4549229 : Blo 1346992 4549229 := bstep (se 3 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 4549229 = 1705961) B1705961
theorem B3410545 : Blo 1346992 3410545 := bstep (se 2 (by rfl) ⟨1278954, by rfl⟩ : syracuseStep 3410545 = 2557909) B2557909
theorem B9226865 : Blo 1346992 9226865 := bstep (se 2 (by rfl) ⟨3460074, by rfl⟩ : syracuseStep 9226865 = 6920149) B6920149
theorem B4549283 : Blo 1346992 4549283 := bstep (se 1 (by rfl) ⟨3411962, by rfl⟩ : syracuseStep 4549283 = 6823925) B6823925
theorem B5114573 : Blo 1346992 5114573 := bstep (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) B1917965
theorem B3033809 : Blo 1346992 3033809 := bstep (se 2 (by rfl) ⟨1137678, by rfl⟩ : syracuseStep 3033809 = 2275357) B2275357
theorem B3033827 : Blo 1346992 3033827 := bstep (se 1 (by rfl) ⟨2275370, by rfl⟩ : syracuseStep 3033827 = 4550741) B4550741
theorem B17279729 : Blo 1346992 17279729 := bstep (se 2 (by rfl) ⟨6479898, by rfl⟩ : syracuseStep 17279729 = 12959797) B12959797
theorem B1706771 : Blo 1346992 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B3836717 : Blo 1346992 3836717 := bstep (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) B1438769
theorem B6916913 : Blo 1346992 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B3410819 : Blo 1346992 3410819 := bstep (se 1 (by rfl) ⟨2558114, by rfl⟩ : syracuseStep 3410819 = 5116229) B5116229
theorem B4549553 : Blo 1346992 4549553 := bstep (se 2 (by rfl) ⟨1706082, by rfl⟩ : syracuseStep 4549553 = 3412165) B3412165
theorem B1919953 : Blo 1346992 1919953 := bstep (se 2 (by rfl) ⟨719982, by rfl⟩ : syracuseStep 1919953 = 1439965) B1439965
theorem B1846243 : Blo 1346992 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B3836909 : Blo 1346992 3836909 := bstep (se 3 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 3836909 = 1438841) B1438841
theorem B3034097 : Blo 1346992 3034097 := bstep (se 2 (by rfl) ⟨1137786, by rfl⟩ : syracuseStep 3034097 = 2275573) B2275573
theorem B3034115 : Blo 1346992 3034115 := bstep (se 1 (by rfl) ⟨2275586, by rfl⟩ : syracuseStep 3034115 = 4551173) B4551173
theorem B3411011 : Blo 1346992 3411011 := bstep (se 1 (by rfl) ⟨2558258, by rfl⟩ : syracuseStep 3411011 = 5116517) B5116517
theorem B7892045 : Blo 1346992 7892045 := bstep (se 3 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 7892045 = 2959517) B2959517
theorem B2559185 : Blo 1346992 2559185 := bstep (se 2 (by rfl) ⟨959694, by rfl⟩ : syracuseStep 2559185 = 1919389) B1919389
theorem B3239153 : Blo 1346992 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B3034385 : Blo 1346992 3034385 := bstep (se 2 (by rfl) ⟨1137894, by rfl⟩ : syracuseStep 3034385 = 2275789) B2275789
theorem B1920289 : Blo 1346992 1920289 := bstep (se 2 (by rfl) ⟨720108, by rfl⟩ : syracuseStep 1920289 = 1440217) B1440217
theorem B3034403 : Blo 1346992 3034403 := bstep (se 1 (by rfl) ⟨2275802, by rfl⟩ : syracuseStep 3034403 = 4551605) B4551605
theorem B6147377 : Blo 1346992 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B1346995 : Blo 1346992 1346995 := bstep (se 1 (by rfl) ⟨1010246, by rfl⟩ : syracuseStep 1346995 = 2020493) B2020493
theorem B2305459 : Blo 1346992 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B1347011 : Blo 1346992 1347011 := bstep (se 1 (by rfl) ⟨1010258, by rfl⟩ : syracuseStep 1347011 = 2020517) B2020517
theorem B2158019 : Blo 1346992 2158019 := bstep (se 1 (by rfl) ⟨1618514, by rfl⟩ : syracuseStep 2158019 = 3237029) B3237029
theorem B4550093 : Blo 1346992 4550093 := bstep (se 3 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 4550093 = 1706285) B1706285
theorem B1347027 : Blo 1346992 1347027 := bstep (se 1 (by rfl) ⟨1010270, by rfl⟩ : syracuseStep 1347027 = 2020541) B2020541
theorem B1347043 : Blo 1346992 1347043 := bstep (se 1 (by rfl) ⟨1010282, by rfl⟩ : syracuseStep 1347043 = 2020565) B2020565
theorem B1347059 : Blo 1346992 1347059 := bstep (se 1 (by rfl) ⟨1010294, by rfl⟩ : syracuseStep 1347059 = 2020589) B2020589
theorem B1347075 : Blo 1346992 1347075 := bstep (se 1 (by rfl) ⟨1010306, by rfl⟩ : syracuseStep 1347075 = 2020613) B2020613
theorem B4550147 : Blo 1346992 4550147 := bstep (se 1 (by rfl) ⟨3412610, by rfl⟩ : syracuseStep 4550147 = 6825221) B6825221
theorem B1347091 : Blo 1346992 1347091 := bstep (se 1 (by rfl) ⟨1010318, by rfl⟩ : syracuseStep 1347091 = 2020637) B2020637
theorem B1347107 : Blo 1346992 1347107 := bstep (se 1 (by rfl) ⟨1010330, by rfl⟩ : syracuseStep 1347107 = 2020661) B2020661
theorem B3034673 : Blo 1346992 3034673 := bstep (se 2 (by rfl) ⟨1138002, by rfl⟩ : syracuseStep 3034673 = 2276005) B2276005
theorem B1347123 : Blo 1346992 1347123 := bstep (se 1 (by rfl) ⟨1010342, by rfl⟩ : syracuseStep 1347123 = 2020685) B2020685
theorem B1347139 : Blo 1346992 1347139 := bstep (se 1 (by rfl) ⟨1010354, by rfl⟩ : syracuseStep 1347139 = 2020709) B2020709
theorem B3034691 : Blo 1346992 3034691 := bstep (se 1 (by rfl) ⟨2276018, by rfl⟩ : syracuseStep 3034691 = 4552037) B4552037
theorem B1347155 : Blo 1346992 1347155 := bstep (se 1 (by rfl) ⟨1010366, by rfl⟩ : syracuseStep 1347155 = 2020733) B2020733
theorem B1347171 : Blo 1346992 1347171 := bstep (se 1 (by rfl) ⟨1010378, by rfl⟩ : syracuseStep 1347171 = 2020757) B2020757
theorem B1347187 : Blo 1346992 1347187 := bstep (se 1 (by rfl) ⟨1010390, by rfl⟩ : syracuseStep 1347187 = 2020781) B2020781
theorem B1347203 : Blo 1346992 1347203 := bstep (se 1 (by rfl) ⟨1010402, by rfl⟩ : syracuseStep 1347203 = 2020805) B2020805
theorem B2158211 : Blo 1346992 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B1347219 : Blo 1346992 1347219 := bstep (se 1 (by rfl) ⟨1010414, by rfl⟩ : syracuseStep 1347219 = 2020829) B2020829
theorem B1347235 : Blo 1346992 1347235 := bstep (se 1 (by rfl) ⟨1010426, by rfl⟩ : syracuseStep 1347235 = 2020853) B2020853
theorem B1347251 : Blo 1346992 1347251 := bstep (se 1 (by rfl) ⟨1010438, by rfl⟩ : syracuseStep 1347251 = 2020877) B2020877
theorem B1347267 : Blo 1346992 1347267 := bstep (se 1 (by rfl) ⟨1010450, by rfl⟩ : syracuseStep 1347267 = 2020901) B2020901
theorem B1347283 : Blo 1346992 1347283 := bstep (se 1 (by rfl) ⟨1010462, by rfl⟩ : syracuseStep 1347283 = 2020925) B2020925
theorem B1347299 : Blo 1346992 1347299 := bstep (se 1 (by rfl) ⟨1010474, by rfl⟩ : syracuseStep 1347299 = 2020949) B2020949
theorem B1347315 : Blo 1346992 1347315 := bstep (se 1 (by rfl) ⟨1010486, by rfl⟩ : syracuseStep 1347315 = 2020973) B2020973
theorem B1347331 : Blo 1346992 1347331 := bstep (se 1 (by rfl) ⟨1010498, by rfl⟩ : syracuseStep 1347331 = 2020997) B2020997
theorem B2158339 : Blo 1346992 2158339 := bstep (se 1 (by rfl) ⟨1618754, by rfl⟩ : syracuseStep 2158339 = 3237509) B3237509
theorem B9711373 : Blo 1346992 9711373 := bstep (se 3 (by rfl) ⟨1820882, by rfl⟩ : syracuseStep 9711373 = 3641765) B3641765
theorem B4550417 : Blo 1346992 4550417 := bstep (se 2 (by rfl) ⟨1706406, by rfl⟩ : syracuseStep 4550417 = 3412813) B3412813
theorem B1347347 : Blo 1346992 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B1347363 : Blo 1346992 1347363 := bstep (se 1 (by rfl) ⟨1010522, by rfl⟩ : syracuseStep 1347363 = 2021045) B2021045
theorem B1347379 : Blo 1346992 1347379 := bstep (se 1 (by rfl) ⟨1010534, by rfl⟩ : syracuseStep 1347379 = 2021069) B2021069
theorem B2273089 : Blo 1346992 2273089 := bstep (se 2 (by rfl) ⟨852408, by rfl⟩ : syracuseStep 2273089 = 1704817) B1704817
theorem B1347395 : Blo 1346992 1347395 := bstep (se 1 (by rfl) ⟨1010546, by rfl⟩ : syracuseStep 1347395 = 2021093) B2021093
theorem B9719621 : Blo 1346992 9719621 := bstep (se 4 (by rfl) ⟨911214, by rfl⟩ : syracuseStep 9719621 = 1822429) B1822429
theorem B1347411 : Blo 1346992 1347411 := bstep (se 1 (by rfl) ⟨1010558, by rfl⟩ : syracuseStep 1347411 = 2021117) B2021117
theorem B3034961 : Blo 1346992 3034961 := bstep (se 2 (by rfl) ⟨1138110, by rfl⟩ : syracuseStep 3034961 = 2276221) B2276221
theorem B2273123 : Blo 1346992 2273123 := bstep (se 1 (by rfl) ⟨1704842, by rfl⟩ : syracuseStep 2273123 = 3409685) B3409685
theorem B1347427 : Blo 1346992 1347427 := bstep (se 1 (by rfl) ⟨1010570, by rfl⟩ : syracuseStep 1347427 = 2021141) B2021141
theorem B3034979 : Blo 1346992 3034979 := bstep (se 1 (by rfl) ⟨2276234, by rfl⟩ : syracuseStep 3034979 = 4552469) B4552469
theorem B1347443 : Blo 1346992 1347443 := bstep (se 1 (by rfl) ⟨1010582, by rfl⟩ : syracuseStep 1347443 = 2021165) B2021165
theorem B1347459 : Blo 1346992 1347459 := bstep (se 1 (by rfl) ⟨1010594, by rfl⟩ : syracuseStep 1347459 = 2021189) B2021189
theorem B10383245 : Blo 1346992 10383245 := bstep (se 3 (by rfl) ⟨1946858, by rfl⟩ : syracuseStep 10383245 = 3893717) B3893717
theorem B1347475 : Blo 1346992 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B1347491 : Blo 1346992 1347491 := bstep (se 1 (by rfl) ⟨1010618, by rfl⟩ : syracuseStep 1347491 = 2021237) B2021237
theorem B1347507 : Blo 1346992 1347507 := bstep (se 1 (by rfl) ⟨1010630, by rfl⟩ : syracuseStep 1347507 = 2021261) B2021261
theorem B1347523 : Blo 1346992 1347523 := bstep (se 1 (by rfl) ⟨1010642, by rfl⟩ : syracuseStep 1347523 = 2021285) B2021285
theorem B3837901 : Blo 1346992 3837901 := bstep (se 3 (by rfl) ⟨719606, by rfl⟩ : syracuseStep 3837901 = 1439213) B1439213
theorem B8204237 : Blo 1346992 8204237 := bstep (se 3 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 8204237 = 3076589) B3076589
theorem B1347539 : Blo 1346992 1347539 := bstep (se 1 (by rfl) ⟨1010654, by rfl⟩ : syracuseStep 1347539 = 2021309) B2021309
theorem B2273251 : Blo 1346992 2273251 := bstep (se 1 (by rfl) ⟨1704938, by rfl⟩ : syracuseStep 2273251 = 3409877) B3409877
theorem B1347555 : Blo 1346992 1347555 := bstep (se 1 (by rfl) ⟨1010666, by rfl⟩ : syracuseStep 1347555 = 2021333) B2021333
theorem B3411953 : Blo 1346992 3411953 := bstep (se 2 (by rfl) ⟨1279482, by rfl⟩ : syracuseStep 3411953 = 2558965) B2558965
theorem B1347571 : Blo 1346992 1347571 := bstep (se 1 (by rfl) ⟨1010678, by rfl⟩ : syracuseStep 1347571 = 2021357) B2021357
theorem B1347587 : Blo 1346992 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B6230029 : Blo 1346992 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B1347603 : Blo 1346992 1347603 := bstep (se 1 (by rfl) ⟨1010702, by rfl⟩ : syracuseStep 1347603 = 2021405) B2021405
theorem B6819875 : Blo 1346992 6819875 := bstep (se 1 (by rfl) ⟨5114906, by rfl⟩ : syracuseStep 6819875 = 10229813) B10229813
theorem B1347619 : Blo 1346992 1347619 := bstep (se 1 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 1347619 = 2021429) B2021429
theorem B3412003 : Blo 1346992 3412003 := bstep (se 1 (by rfl) ⟨2559002, by rfl⟩ : syracuseStep 3412003 = 5118005) B5118005
theorem B5836835 : Blo 1346992 5836835 := bstep (se 1 (by rfl) ⟨4377626, by rfl⟩ : syracuseStep 5836835 = 8755253) B8755253
theorem B1347635 : Blo 1346992 1347635 := bstep (se 1 (by rfl) ⟨1010726, by rfl⟩ : syracuseStep 1347635 = 2021453) B2021453
theorem B1347651 : Blo 1346992 1347651 := bstep (se 1 (by rfl) ⟨1010738, by rfl⟩ : syracuseStep 1347651 = 2021477) B2021477
theorem B2560081 : Blo 1346992 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B1347667 : Blo 1346992 1347667 := bstep (se 1 (by rfl) ⟨1010750, by rfl⟩ : syracuseStep 1347667 = 2021501) B2021501
theorem B1347683 : Blo 1346992 1347683 := bstep (se 1 (by rfl) ⟨1010762, by rfl⟩ : syracuseStep 1347683 = 2021525) B2021525
theorem B2273393 : Blo 1346992 2273393 := bstep (se 2 (by rfl) ⟨852522, by rfl⟩ : syracuseStep 2273393 = 1705045) B1705045
theorem B1347699 : Blo 1346992 1347699 := bstep (se 1 (by rfl) ⟨1010774, by rfl⟩ : syracuseStep 1347699 = 2021549) B2021549
theorem B1347715 : Blo 1346992 1347715 := bstep (se 1 (by rfl) ⟨1010786, by rfl⟩ : syracuseStep 1347715 = 2021573) B2021573
theorem B1347731 : Blo 1346992 1347731 := bstep (se 1 (by rfl) ⟨1010798, by rfl⟩ : syracuseStep 1347731 = 2021597) B2021597
theorem B3641507 : Blo 1346992 3641507 := bstep (se 1 (by rfl) ⟨2731130, by rfl⟩ : syracuseStep 3641507 = 5462261) B5462261
theorem B1347747 : Blo 1346992 1347747 := bstep (se 1 (by rfl) ⟨1010810, by rfl⟩ : syracuseStep 1347747 = 2021621) B2021621
theorem B3412145 : Blo 1346992 3412145 := bstep (se 2 (by rfl) ⟨1279554, by rfl⟩ : syracuseStep 3412145 = 2559109) B2559109
theorem B2306225 : Blo 1346992 2306225 := bstep (se 2 (by rfl) ⟨864834, by rfl⟩ : syracuseStep 2306225 = 1729669) B1729669
theorem B1347763 : Blo 1346992 1347763 := bstep (se 1 (by rfl) ⟨1010822, by rfl⟩ : syracuseStep 1347763 = 2021645) B2021645
theorem B1347779 : Blo 1346992 1347779 := bstep (se 1 (by rfl) ⟨1010834, by rfl⟩ : syracuseStep 1347779 = 2021669) B2021669
theorem B7680197 : Blo 1346992 7680197 := bstep (se 4 (by rfl) ⟨720018, by rfl⟩ : syracuseStep 7680197 = 1440037) B1440037
theorem B1347795 : Blo 1346992 1347795 := bstep (se 1 (by rfl) ⟨1010846, by rfl⟩ : syracuseStep 1347795 = 2021693) B2021693
theorem B1347811 : Blo 1346992 1347811 := bstep (se 1 (by rfl) ⟨1010858, by rfl⟩ : syracuseStep 1347811 = 2021717) B2021717
theorem B10236131 : Blo 1346992 10236131 := bstep (se 1 (by rfl) ⟨7677098, by rfl⟩ : syracuseStep 10236131 = 15354197) B15354197
theorem B2273521 : Blo 1346992 2273521 := bstep (se 2 (by rfl) ⟨852570, by rfl⟩ : syracuseStep 2273521 = 1705141) B1705141
theorem B2560241 : Blo 1346992 2560241 := bstep (se 2 (by rfl) ⟨960090, by rfl⟩ : syracuseStep 2560241 = 1920181) B1920181
theorem B1347827 : Blo 1346992 1347827 := bstep (se 1 (by rfl) ⟨1010870, by rfl⟩ : syracuseStep 1347827 = 2021741) B2021741
theorem B1347843 : Blo 1346992 1347843 := bstep (se 1 (by rfl) ⟨1010882, by rfl⟩ : syracuseStep 1347843 = 2021765) B2021765
theorem B2273555 : Blo 1346992 2273555 := bstep (se 1 (by rfl) ⟨1705166, by rfl⟩ : syracuseStep 2273555 = 3410333) B3410333
theorem B1347859 : Blo 1346992 1347859 := bstep (se 1 (by rfl) ⟨1010894, by rfl⟩ : syracuseStep 1347859 = 2021789) B2021789
theorem B1347875 : Blo 1346992 1347875 := bstep (se 1 (by rfl) ⟨1010906, by rfl⟩ : syracuseStep 1347875 = 2021813) B2021813
theorem B4550957 : Blo 1346992 4550957 := bstep (se 3 (by rfl) ⟨853304, by rfl⟩ : syracuseStep 4550957 = 1706609) B1706609
theorem B1347891 : Blo 1346992 1347891 := bstep (se 1 (by rfl) ⟨1010918, by rfl⟩ : syracuseStep 1347891 = 2021837) B2021837
theorem B1347907 : Blo 1346992 1347907 := bstep (se 1 (by rfl) ⟨1010930, by rfl⟩ : syracuseStep 1347907 = 2021861) B2021861
theorem B1347923 : Blo 1346992 1347923 := bstep (se 1 (by rfl) ⟨1010942, by rfl⟩ : syracuseStep 1347923 = 2021885) B2021885
theorem B1347939 : Blo 1346992 1347939 := bstep (se 1 (by rfl) ⟨1010954, by rfl⟩ : syracuseStep 1347939 = 2021909) B2021909
theorem B4551011 : Blo 1346992 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B1823089 : Blo 1346992 1823089 := bstep (se 2 (by rfl) ⟨683658, by rfl⟩ : syracuseStep 1823089 = 1367317) B1367317
theorem B4321649 : Blo 1346992 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B1347955 : Blo 1346992 1347955 := bstep (se 1 (by rfl) ⟨1010966, by rfl⟩ : syracuseStep 1347955 = 2021933) B2021933
theorem B2158979 : Blo 1346992 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1347971 : Blo 1346992 1347971 := bstep (se 1 (by rfl) ⟨1010978, by rfl⟩ : syracuseStep 1347971 = 2021957) B2021957
theorem B2273683 : Blo 1346992 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B1347987 : Blo 1346992 1347987 := bstep (se 1 (by rfl) ⟨1010990, by rfl⟩ : syracuseStep 1347987 = 2021981) B2021981
theorem B1348003 : Blo 1346992 1348003 := bstep (se 1 (by rfl) ⟨1011002, by rfl⟩ : syracuseStep 1348003 = 2022005) B2022005
theorem B1348019 : Blo 1346992 1348019 := bstep (se 1 (by rfl) ⟨1011014, by rfl⟩ : syracuseStep 1348019 = 2022029) B2022029
theorem B1348035 : Blo 1346992 1348035 := bstep (se 1 (by rfl) ⟨1011026, by rfl⟩ : syracuseStep 1348035 = 2022053) B2022053
theorem B2159057 : Blo 1346992 2159057 := bstep (se 2 (by rfl) ⟨809646, by rfl⟩ : syracuseStep 2159057 = 1619293) B1619293
theorem B1348051 : Blo 1346992 1348051 := bstep (se 1 (by rfl) ⟨1011038, by rfl⟩ : syracuseStep 1348051 = 2022077) B2022077
theorem B1348067 : Blo 1346992 1348067 := bstep (se 1 (by rfl) ⟨1011050, by rfl⟩ : syracuseStep 1348067 = 2022101) B2022101
theorem B1348083 : Blo 1346992 1348083 := bstep (se 1 (by rfl) ⟨1011062, by rfl⟩ : syracuseStep 1348083 = 2022125) B2022125
theorem B1348099 : Blo 1346992 1348099 := bstep (se 1 (by rfl) ⟨1011074, by rfl⟩ : syracuseStep 1348099 = 2022149) B2022149
theorem B1348115 : Blo 1346992 1348115 := bstep (se 1 (by rfl) ⟨1011086, by rfl⟩ : syracuseStep 1348115 = 2022173) B2022173
theorem B2273825 : Blo 1346992 2273825 := bstep (se 2 (by rfl) ⟨852684, by rfl⟩ : syracuseStep 2273825 = 1705369) B1705369
theorem B1348131 : Blo 1346992 1348131 := bstep (se 1 (by rfl) ⟨1011098, by rfl⟩ : syracuseStep 1348131 = 2022197) B2022197
theorem B1348147 : Blo 1346992 1348147 := bstep (se 1 (by rfl) ⟨1011110, by rfl⟩ : syracuseStep 1348147 = 2022221) B2022221
theorem B1348163 : Blo 1346992 1348163 := bstep (se 1 (by rfl) ⟨1011122, by rfl⟩ : syracuseStep 1348163 = 2022245) B2022245
theorem B8639045 : Blo 1346992 8639045 := bstep (se 4 (by rfl) ⟨809910, by rfl⟩ : syracuseStep 8639045 = 1619821) B1619821
theorem B1348179 : Blo 1346992 1348179 := bstep (se 1 (by rfl) ⟨1011134, by rfl⟩ : syracuseStep 1348179 = 2022269) B2022269
theorem B1348195 : Blo 1346992 1348195 := bstep (se 1 (by rfl) ⟨1011146, by rfl⟩ : syracuseStep 1348195 = 2022293) B2022293
theorem B4551281 : Blo 1346992 4551281 := bstep (se 2 (by rfl) ⟨1706730, by rfl⟩ : syracuseStep 4551281 = 3413461) B3413461
theorem B1348211 : Blo 1346992 1348211 := bstep (se 1 (by rfl) ⟨1011158, by rfl⟩ : syracuseStep 1348211 = 2022317) B2022317
theorem B1348227 : Blo 1346992 1348227 := bstep (se 1 (by rfl) ⟨1011170, by rfl⟩ : syracuseStep 1348227 = 2022341) B2022341
theorem B2560643 : Blo 1346992 2560643 := bstep (se 1 (by rfl) ⟨1920482, by rfl⟩ : syracuseStep 2560643 = 3840965) B3840965
theorem B15348365 : Blo 1346992 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B7680653 : Blo 1346992 7680653 := bstep (se 3 (by rfl) ⟨1440122, by rfl⟩ : syracuseStep 7680653 = 2880245) B2880245
theorem B1348243 : Blo 1346992 1348243 := bstep (se 1 (by rfl) ⟨1011182, by rfl⟩ : syracuseStep 1348243 = 2022365) B2022365
theorem B2273953 : Blo 1346992 2273953 := bstep (se 2 (by rfl) ⟨852732, by rfl⟩ : syracuseStep 2273953 = 1705465) B1705465
theorem B1348259 : Blo 1346992 1348259 := bstep (se 1 (by rfl) ⟨1011194, by rfl⟩ : syracuseStep 1348259 = 2022389) B2022389
theorem B3117731 : Blo 1346992 3117731 := bstep (se 1 (by rfl) ⟨2338298, by rfl⟩ : syracuseStep 3117731 = 4676597) B4676597
theorem B2429617 : Blo 1346992 2429617 := bstep (se 2 (by rfl) ⟨911106, by rfl⟩ : syracuseStep 2429617 = 1822213) B1822213
theorem B1348275 : Blo 1346992 1348275 := bstep (se 1 (by rfl) ⟨1011206, by rfl⟩ : syracuseStep 1348275 = 2022413) B2022413
theorem B2273987 : Blo 1346992 2273987 := bstep (se 1 (by rfl) ⟨1705490, by rfl⟩ : syracuseStep 2273987 = 3410981) B3410981
theorem B1348291 : Blo 1346992 1348291 := bstep (se 1 (by rfl) ⟨1011218, by rfl⟩ : syracuseStep 1348291 = 2022437) B2022437
theorem B1348307 : Blo 1346992 1348307 := bstep (se 1 (by rfl) ⟨1011230, by rfl⟩ : syracuseStep 1348307 = 2022461) B2022461
theorem B1348323 : Blo 1346992 1348323 := bstep (se 1 (by rfl) ⟨1011242, by rfl⟩ : syracuseStep 1348323 = 2022485) B2022485
theorem B6828785 : Blo 1346992 6828785 := bstep (se 2 (by rfl) ⟨2560794, by rfl⟩ : syracuseStep 6828785 = 5121589) B5121589
theorem B1348339 : Blo 1346992 1348339 := bstep (se 1 (by rfl) ⟨1011254, by rfl⟩ : syracuseStep 1348339 = 2022509) B2022509
theorem B1348355 : Blo 1346992 1348355 := bstep (se 1 (by rfl) ⟨1011266, by rfl⟩ : syracuseStep 1348355 = 2022533) B2022533
theorem B7672589 : Blo 1346992 7672589 := bstep (se 3 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 7672589 = 2877221) B2877221
theorem B1348371 : Blo 1346992 1348371 := bstep (se 1 (by rfl) ⟨1011278, by rfl⟩ : syracuseStep 1348371 = 2022557) B2022557
theorem B42054421 : Blo 1346992 42054421 := bstep (se 6 (by rfl) ⟨985650, by rfl⟩ : syracuseStep 42054421 = 1971301) B1971301
theorem B1348387 : Blo 1346992 1348387 := bstep (se 1 (by rfl) ⟨1011290, by rfl⟩ : syracuseStep 1348387 = 2022581) B2022581
theorem B1348403 : Blo 1346992 1348403 := bstep (se 1 (by rfl) ⟨1011302, by rfl⟩ : syracuseStep 1348403 = 2022605) B2022605
theorem B2306881 : Blo 1346992 2306881 := bstep (se 2 (by rfl) ⟨865080, by rfl⟩ : syracuseStep 2306881 = 1730161) B1730161
theorem B2274115 : Blo 1346992 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B1348419 : Blo 1346992 1348419 := bstep (se 1 (by rfl) ⟨1011314, by rfl⟩ : syracuseStep 1348419 = 2022629) B2022629
theorem B6820685 : Blo 1346992 6820685 := bstep (se 3 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 6820685 = 2557757) B2557757
theorem B2159441 : Blo 1346992 2159441 := bstep (se 2 (by rfl) ⟨809790, by rfl⟩ : syracuseStep 2159441 = 1619581) B1619581
theorem B1348435 : Blo 1346992 1348435 := bstep (se 1 (by rfl) ⟨1011326, by rfl⟩ : syracuseStep 1348435 = 2022653) B2022653
theorem B1348451 : Blo 1346992 1348451 := bstep (se 1 (by rfl) ⟨1011338, by rfl⟩ : syracuseStep 1348451 = 2022677) B2022677
theorem B16405361 : Blo 1346992 16405361 := bstep (se 2 (by rfl) ⟨6152010, by rfl⟩ : syracuseStep 16405361 = 12304021) B12304021
theorem B1348467 : Blo 1346992 1348467 := bstep (se 1 (by rfl) ⟨1011350, by rfl⟩ : syracuseStep 1348467 = 2022701) B2022701
theorem B1348483 : Blo 1346992 1348483 := bstep (se 1 (by rfl) ⟨1011362, by rfl⟩ : syracuseStep 1348483 = 2022725) B2022725
theorem B2732945 : Blo 1346992 2732945 := bstep (se 2 (by rfl) ⟨1024854, by rfl⟩ : syracuseStep 2732945 = 2049709) B2049709
theorem B1348499 : Blo 1346992 1348499 := bstep (se 1 (by rfl) ⟨1011374, by rfl⟩ : syracuseStep 1348499 = 2022749) B2022749
theorem B1348515 : Blo 1346992 1348515 := bstep (se 1 (by rfl) ⟨1011386, by rfl⟩ : syracuseStep 1348515 = 2022773) B2022773
theorem B2732977 : Blo 1346992 2732977 := bstep (se 2 (by rfl) ⟨1024866, by rfl⟩ : syracuseStep 2732977 = 2049733) B2049733
theorem B1348531 : Blo 1346992 1348531 := bstep (se 1 (by rfl) ⟨1011398, by rfl⟩ : syracuseStep 1348531 = 2022797) B2022797
theorem B1348547 : Blo 1346992 1348547 := bstep (se 1 (by rfl) ⟨1011410, by rfl⟩ : syracuseStep 1348547 = 2022821) B2022821
theorem B2274257 : Blo 1346992 2274257 := bstep (se 2 (by rfl) ⟨852846, by rfl⟩ : syracuseStep 2274257 = 1705693) B1705693
theorem B2159569 : Blo 1346992 2159569 := bstep (se 2 (by rfl) ⟨809838, by rfl⟩ : syracuseStep 2159569 = 1619677) B1619677
theorem B1348563 : Blo 1346992 1348563 := bstep (se 1 (by rfl) ⟨1011422, by rfl⟩ : syracuseStep 1348563 = 2022845) B2022845
theorem B17265635 : Blo 1346992 17265635 := bstep (se 1 (by rfl) ⟨12949226, by rfl⟩ : syracuseStep 17265635 = 25898453) B25898453
theorem B1348579 : Blo 1346992 1348579 := bstep (se 1 (by rfl) ⟨1011434, by rfl⟩ : syracuseStep 1348579 = 2022869) B2022869
theorem B1348595 : Blo 1346992 1348595 := bstep (se 1 (by rfl) ⟨1011446, by rfl⟩ : syracuseStep 1348595 = 2022893) B2022893
theorem B1348611 : Blo 1346992 1348611 := bstep (se 1 (by rfl) ⟨1011458, by rfl⟩ : syracuseStep 1348611 = 2022917) B2022917
theorem B1348627 : Blo 1346992 1348627 := bstep (se 1 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 1348627 = 2022941) B2022941
theorem B1348643 : Blo 1346992 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B1348659 : Blo 1346992 1348659 := bstep (se 1 (by rfl) ⟨1011494, by rfl⟩ : syracuseStep 1348659 = 2022989) B2022989
theorem B1348675 : Blo 1346992 1348675 := bstep (se 1 (by rfl) ⟨1011506, by rfl⟩ : syracuseStep 1348675 = 2023013) B2023013
theorem B2274385 : Blo 1346992 2274385 := bstep (se 2 (by rfl) ⟨852894, by rfl⟩ : syracuseStep 2274385 = 1705789) B1705789
theorem B1348691 : Blo 1346992 1348691 := bstep (se 1 (by rfl) ⟨1011518, by rfl⟩ : syracuseStep 1348691 = 2023037) B2023037
theorem B1348707 : Blo 1346992 1348707 := bstep (se 1 (by rfl) ⟨1011530, by rfl⟩ : syracuseStep 1348707 = 2023061) B2023061
theorem B2274419 : Blo 1346992 2274419 := bstep (se 1 (by rfl) ⟨1705814, by rfl⟩ : syracuseStep 2274419 = 3411629) B3411629
theorem B1348723 : Blo 1346992 1348723 := bstep (se 1 (by rfl) ⟨1011542, by rfl⟩ : syracuseStep 1348723 = 2023085) B2023085
theorem B1348739 : Blo 1346992 1348739 := bstep (se 1 (by rfl) ⟨1011554, by rfl⟩ : syracuseStep 1348739 = 2023109) B2023109
theorem B1946755 : Blo 1346992 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B4551821 : Blo 1346992 4551821 := bstep (se 3 (by rfl) ⟨853466, by rfl⟩ : syracuseStep 4551821 = 1706933) B1706933
theorem B3413137 : Blo 1346992 3413137 := bstep (se 2 (by rfl) ⟨1279926, by rfl⟩ : syracuseStep 3413137 = 2559853) B2559853
theorem B2020499 : Blo 1346992 2020499 := bstep (se 1 (by rfl) ⟨1515374, by rfl⟩ : syracuseStep 2020499 = 3030749) B3030749
theorem B1348755 : Blo 1346992 1348755 := bstep (se 1 (by rfl) ⟨1011566, by rfl⟩ : syracuseStep 1348755 = 2023133) B2023133
theorem B1348771 : Blo 1346992 1348771 := bstep (se 1 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 1348771 = 2023157) B2023157
theorem B2020529 : Blo 1346992 2020529 := bstep (se 2 (by rfl) ⟨757698, by rfl⟩ : syracuseStep 2020529 = 1515397) B1515397
theorem B2880689 : Blo 1346992 2880689 := bstep (se 2 (by rfl) ⟨1080258, by rfl⟩ : syracuseStep 2880689 = 2160517) B2160517
theorem B1348787 : Blo 1346992 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B2020547 : Blo 1346992 2020547 := bstep (se 1 (by rfl) ⟨1515410, by rfl⟩ : syracuseStep 2020547 = 3030821) B3030821
theorem B4609219 : Blo 1346992 4609219 := bstep (se 1 (by rfl) ⟨3456914, by rfl⟩ : syracuseStep 4609219 = 6913829) B6913829
theorem B4551875 : Blo 1346992 4551875 := bstep (se 1 (by rfl) ⟨3413906, by rfl⟩ : syracuseStep 4551875 = 6827813) B6827813
theorem B1348803 : Blo 1346992 1348803 := bstep (se 1 (by rfl) ⟨1011602, by rfl⟩ : syracuseStep 1348803 = 2023205) B2023205
theorem B1348819 : Blo 1346992 1348819 := bstep (se 1 (by rfl) ⟨1011614, by rfl⟩ : syracuseStep 1348819 = 2023229) B2023229
theorem B2020577 : Blo 1346992 2020577 := bstep (se 2 (by rfl) ⟨757716, by rfl⟩ : syracuseStep 2020577 = 1515433) B1515433
theorem B2430179 : Blo 1346992 2430179 := bstep (se 1 (by rfl) ⟨1822634, by rfl⟩ : syracuseStep 2430179 = 3645269) B3645269
theorem B1348835 : Blo 1346992 1348835 := bstep (se 1 (by rfl) ⟨1011626, by rfl⟩ : syracuseStep 1348835 = 2023253) B2023253
theorem B2020595 : Blo 1346992 2020595 := bstep (se 1 (by rfl) ⟨1515446, by rfl⟩ : syracuseStep 2020595 = 3030893) B3030893
theorem B2274547 : Blo 1346992 2274547 := bstep (se 1 (by rfl) ⟨1705910, by rfl⟩ : syracuseStep 2274547 = 3411821) B3411821
theorem B1348851 : Blo 1346992 1348851 := bstep (se 1 (by rfl) ⟨1011638, by rfl⟩ : syracuseStep 1348851 = 2023277) B2023277
theorem B1348867 : Blo 1346992 1348867 := bstep (se 1 (by rfl) ⟨1011650, by rfl⟩ : syracuseStep 1348867 = 2023301) B2023301
theorem B2020625 : Blo 1346992 2020625 := bstep (se 2 (by rfl) ⟨757734, by rfl⟩ : syracuseStep 2020625 = 1515469) B1515469
theorem B1348883 : Blo 1346992 1348883 := bstep (se 1 (by rfl) ⟨1011662, by rfl⟩ : syracuseStep 1348883 = 2023325) B2023325
theorem B2020643 : Blo 1346992 2020643 := bstep (se 1 (by rfl) ⟨1515482, by rfl⟩ : syracuseStep 2020643 = 3030965) B3030965
theorem B1348899 : Blo 1346992 1348899 := bstep (se 1 (by rfl) ⟨1011674, by rfl⟩ : syracuseStep 1348899 = 2023349) B2023349
theorem B3642673 : Blo 1346992 3642673 := bstep (se 2 (by rfl) ⟨1366002, by rfl⟩ : syracuseStep 3642673 = 2732005) B2732005
theorem B1348915 : Blo 1346992 1348915 := bstep (se 1 (by rfl) ⟨1011686, by rfl⟩ : syracuseStep 1348915 = 2023373) B2023373
theorem B2020673 : Blo 1346992 2020673 := bstep (se 2 (by rfl) ⟨757752, by rfl⟩ : syracuseStep 2020673 = 1515505) B1515505
theorem B1348931 : Blo 1346992 1348931 := bstep (se 1 (by rfl) ⟨1011698, by rfl⟩ : syracuseStep 1348931 = 2023397) B2023397
theorem B4437325 : Blo 1346992 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B2020691 : Blo 1346992 2020691 := bstep (se 1 (by rfl) ⟨1515518, by rfl⟩ : syracuseStep 2020691 = 3031037) B3031037
theorem B1348947 : Blo 1346992 1348947 := bstep (se 1 (by rfl) ⟨1011710, by rfl⟩ : syracuseStep 1348947 = 2023421) B2023421
theorem B1348963 : Blo 1346992 1348963 := bstep (se 1 (by rfl) ⟨1011722, by rfl⟩ : syracuseStep 1348963 = 2023445) B2023445
theorem B2020721 : Blo 1346992 2020721 := bstep (se 2 (by rfl) ⟨757770, by rfl⟩ : syracuseStep 2020721 = 1515541) B1515541
theorem B1348979 : Blo 1346992 1348979 := bstep (se 1 (by rfl) ⟨1011734, by rfl⟩ : syracuseStep 1348979 = 2023469) B2023469
theorem B2274689 : Blo 1346992 2274689 := bstep (se 2 (by rfl) ⟨853008, by rfl⟩ : syracuseStep 2274689 = 1706017) B1706017
theorem B2020739 : Blo 1346992 2020739 := bstep (se 1 (by rfl) ⟨1515554, by rfl⟩ : syracuseStep 2020739 = 3031109) B3031109
theorem B2020769 : Blo 1346992 2020769 := bstep (se 2 (by rfl) ⟨757788, by rfl⟩ : syracuseStep 2020769 = 1515577) B1515577
theorem B3413411 : Blo 1346992 3413411 := bstep (se 1 (by rfl) ⟨2560058, by rfl⟩ : syracuseStep 3413411 = 5120117) B5120117
theorem B2020787 : Blo 1346992 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B17274293 : Blo 1346992 17274293 := bstep (se 5 (by rfl) ⟨809732, by rfl⟩ : syracuseStep 17274293 = 1619465) B1619465
theorem B2020817 : Blo 1346992 2020817 := bstep (se 2 (by rfl) ⟨757806, by rfl⟩ : syracuseStep 2020817 = 1515613) B1515613
theorem B4552145 : Blo 1346992 4552145 := bstep (se 2 (by rfl) ⟨1707054, by rfl⟩ : syracuseStep 4552145 = 3414109) B3414109
theorem B2020835 : Blo 1346992 2020835 := bstep (se 1 (by rfl) ⟨1515626, by rfl⟩ : syracuseStep 2020835 = 3031253) B3031253
theorem B2020865 : Blo 1346992 2020865 := bstep (se 2 (by rfl) ⟨757824, by rfl⟩ : syracuseStep 2020865 = 1515649) B1515649
theorem B2274817 : Blo 1346992 2274817 := bstep (se 2 (by rfl) ⟨853056, by rfl⟩ : syracuseStep 2274817 = 1706113) B1706113
theorem B2020883 : Blo 1346992 2020883 := bstep (se 1 (by rfl) ⟨1515662, by rfl⟩ : syracuseStep 2020883 = 3031325) B3031325
theorem B1439251 : Blo 1346992 1439251 := bstep (se 1 (by rfl) ⟨1079438, by rfl⟩ : syracuseStep 1439251 = 2158877) B2158877
theorem B2274851 : Blo 1346992 2274851 := bstep (se 1 (by rfl) ⟨1706138, by rfl⟩ : syracuseStep 2274851 = 3412277) B3412277
theorem B2020913 : Blo 1346992 2020913 := bstep (se 2 (by rfl) ⟨757842, by rfl⟩ : syracuseStep 2020913 = 1515685) B1515685
theorem B5117489 : Blo 1346992 5117489 := bstep (se 2 (by rfl) ⟨1919058, by rfl⟩ : syracuseStep 5117489 = 3838117) B3838117
theorem B2020931 : Blo 1346992 2020931 := bstep (se 1 (by rfl) ⟨1515698, by rfl⟩ : syracuseStep 2020931 = 3031397) B3031397
theorem B2020961 : Blo 1346992 2020961 := bstep (se 2 (by rfl) ⟨757860, by rfl⟩ : syracuseStep 2020961 = 1515721) B1515721
theorem B3413603 : Blo 1346992 3413603 := bstep (se 1 (by rfl) ⟨2560202, by rfl⟩ : syracuseStep 3413603 = 5120405) B5120405
theorem B4101731 : Blo 1346992 4101731 := bstep (se 1 (by rfl) ⟨3076298, by rfl⟩ : syracuseStep 4101731 = 6152597) B6152597
theorem B2020979 : Blo 1346992 2020979 := bstep (se 1 (by rfl) ⟨1515734, by rfl⟩ : syracuseStep 2020979 = 3031469) B3031469
theorem B2021009 : Blo 1346992 2021009 := bstep (se 2 (by rfl) ⟨757878, by rfl⟩ : syracuseStep 2021009 = 1515757) B1515757
theorem B3839633 : Blo 1346992 3839633 := bstep (se 2 (by rfl) ⟨1439862, by rfl⟩ : syracuseStep 3839633 = 2879725) B2879725
theorem B2021027 : Blo 1346992 2021027 := bstep (se 1 (by rfl) ⟨1515770, by rfl⟩ : syracuseStep 2021027 = 3031541) B3031541
theorem B5756579 : Blo 1346992 5756579 := bstep (se 1 (by rfl) ⟨4317434, by rfl⟩ : syracuseStep 5756579 = 8634869) B8634869
theorem B2274979 : Blo 1346992 2274979 := bstep (se 1 (by rfl) ⟨1706234, by rfl⟩ : syracuseStep 2274979 = 3412469) B3412469
theorem B2430641 : Blo 1346992 2430641 := bstep (se 2 (by rfl) ⟨911490, by rfl⟩ : syracuseStep 2430641 = 1822981) B1822981
theorem B2021057 : Blo 1346992 2021057 := bstep (se 2 (by rfl) ⟨757896, by rfl⟩ : syracuseStep 2021057 = 1515793) B1515793
theorem B2021075 : Blo 1346992 2021075 := bstep (se 1 (by rfl) ⟨1515806, by rfl⟩ : syracuseStep 2021075 = 3031613) B3031613
theorem B2021105 : Blo 1346992 2021105 := bstep (se 2 (by rfl) ⟨757914, by rfl⟩ : syracuseStep 2021105 = 1515829) B1515829
theorem B2021123 : Blo 1346992 2021123 := bstep (se 1 (by rfl) ⟨1515842, by rfl⟩ : syracuseStep 2021123 = 3031685) B3031685
theorem B2021153 : Blo 1346992 2021153 := bstep (se 2 (by rfl) ⟨757932, by rfl⟩ : syracuseStep 2021153 = 1515865) B1515865
theorem B2275121 : Blo 1346992 2275121 := bstep (se 2 (by rfl) ⟨853170, by rfl⟩ : syracuseStep 2275121 = 1706341) B1706341
theorem B2021171 : Blo 1346992 2021171 := bstep (se 1 (by rfl) ⟨1515878, by rfl⟩ : syracuseStep 2021171 = 3031757) B3031757
theorem B2021201 : Blo 1346992 2021201 := bstep (se 2 (by rfl) ⟨757950, by rfl⟩ : syracuseStep 2021201 = 1515901) B1515901
theorem B3839825 : Blo 1346992 3839825 := bstep (se 2 (by rfl) ⟨1439934, by rfl⟩ : syracuseStep 3839825 = 2879869) B2879869
theorem B2021219 : Blo 1346992 2021219 := bstep (se 1 (by rfl) ⟨1515914, by rfl⟩ : syracuseStep 2021219 = 3031829) B3031829
theorem B3643235 : Blo 1346992 3643235 := bstep (se 1 (by rfl) ⟨2732426, by rfl⟩ : syracuseStep 3643235 = 5464853) B5464853
theorem B2021249 : Blo 1346992 2021249 := bstep (se 2 (by rfl) ⟨757968, by rfl⟩ : syracuseStep 2021249 = 1515937) B1515937
theorem B119740301 : Blo 1346992 119740301 := bstep (se 3 (by rfl) ⟨22451306, by rfl⟩ : syracuseStep 119740301 = 44902613) B44902613
theorem B2021267 : Blo 1346992 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B2021297 : Blo 1346992 2021297 := bstep (se 2 (by rfl) ⟨757986, by rfl⟩ : syracuseStep 2021297 = 1515973) B1515973
theorem B2275249 : Blo 1346992 2275249 := bstep (se 2 (by rfl) ⟨853218, by rfl⟩ : syracuseStep 2275249 = 1706437) B1706437
theorem B2021315 : Blo 1346992 2021315 := bstep (se 1 (by rfl) ⟨1515986, by rfl⟩ : syracuseStep 2021315 = 3031973) B3031973
theorem B2275283 : Blo 1346992 2275283 := bstep (se 1 (by rfl) ⟨1706462, by rfl⟩ : syracuseStep 2275283 = 3412925) B3412925
theorem B2021345 : Blo 1346992 2021345 := bstep (se 2 (by rfl) ⟨758004, by rfl⟩ : syracuseStep 2021345 = 1516009) B1516009
theorem B4552685 : Blo 1346992 4552685 := bstep (se 3 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 4552685 = 1707257) B1707257
theorem B2021363 : Blo 1346992 2021363 := bstep (se 1 (by rfl) ⟨1516022, by rfl⟩ : syracuseStep 2021363 = 3032045) B3032045
theorem B2021393 : Blo 1346992 2021393 := bstep (se 2 (by rfl) ⟨758022, by rfl⟩ : syracuseStep 2021393 = 1516045) B1516045
theorem B2021411 : Blo 1346992 2021411 := bstep (se 1 (by rfl) ⟨1516058, by rfl⟩ : syracuseStep 2021411 = 3032117) B3032117
theorem B4552739 : Blo 1346992 4552739 := bstep (se 1 (by rfl) ⟨3414554, by rfl⟩ : syracuseStep 4552739 = 6829109) B6829109
theorem B19429429 : Blo 1346992 19429429 := bstep (se 5 (by rfl) ⟨910754, by rfl⟩ : syracuseStep 19429429 = 1821509) B1821509
theorem B2021441 : Blo 1346992 2021441 := bstep (se 2 (by rfl) ⟨758040, by rfl⟩ : syracuseStep 2021441 = 1516081) B1516081
theorem B2021459 : Blo 1346992 2021459 := bstep (se 1 (by rfl) ⟨1516094, by rfl⟩ : syracuseStep 2021459 = 3032189) B3032189
theorem B2275411 : Blo 1346992 2275411 := bstep (se 1 (by rfl) ⟨1706558, by rfl⟩ : syracuseStep 2275411 = 3413117) B3413117
theorem B4610147 : Blo 1346992 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B2021489 : Blo 1346992 2021489 := bstep (se 2 (by rfl) ⟨758058, by rfl⟩ : syracuseStep 2021489 = 1516117) B1516117
theorem B2021507 : Blo 1346992 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B2021537 : Blo 1346992 2021537 := bstep (se 2 (by rfl) ⟨758076, by rfl⟩ : syracuseStep 2021537 = 1516153) B1516153
theorem B2021555 : Blo 1346992 2021555 := bstep (se 1 (by rfl) ⟨1516166, by rfl⟩ : syracuseStep 2021555 = 3032333) B3032333
theorem B2021585 : Blo 1346992 2021585 := bstep (se 2 (by rfl) ⟨758094, by rfl⟩ : syracuseStep 2021585 = 1516189) B1516189
theorem B2275553 : Blo 1346992 2275553 := bstep (se 2 (by rfl) ⟨853332, by rfl⟩ : syracuseStep 2275553 = 1706665) B1706665
theorem B2021603 : Blo 1346992 2021603 := bstep (se 1 (by rfl) ⟨1516202, by rfl⟩ : syracuseStep 2021603 = 3032405) B3032405
theorem B2021633 : Blo 1346992 2021633 := bstep (se 2 (by rfl) ⟨758112, by rfl⟩ : syracuseStep 2021633 = 1516225) B1516225
theorem B2021651 : Blo 1346992 2021651 := bstep (se 1 (by rfl) ⟨1516238, by rfl⟩ : syracuseStep 2021651 = 3032477) B3032477
theorem B5462321 : Blo 1346992 5462321 := bstep (se 2 (by rfl) ⟨2048370, by rfl⟩ : syracuseStep 5462321 = 4096741) B4096741
theorem B2021681 : Blo 1346992 2021681 := bstep (se 2 (by rfl) ⟨758130, by rfl⟩ : syracuseStep 2021681 = 1516261) B1516261
theorem B2021699 : Blo 1346992 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B2021729 : Blo 1346992 2021729 := bstep (se 2 (by rfl) ⟨758148, by rfl⟩ : syracuseStep 2021729 = 1516297) B1516297
theorem B2275681 : Blo 1346992 2275681 := bstep (se 2 (by rfl) ⟨853380, by rfl⟩ : syracuseStep 2275681 = 1706761) B1706761
theorem B2021747 : Blo 1346992 2021747 := bstep (se 1 (by rfl) ⟨1516310, by rfl⟩ : syracuseStep 2021747 = 3032621) B3032621
theorem B2275715 : Blo 1346992 2275715 := bstep (se 1 (by rfl) ⟨1706786, by rfl⟩ : syracuseStep 2275715 = 3413573) B3413573
theorem B19437965 : Blo 1346992 19437965 := bstep (se 3 (by rfl) ⟨3644618, by rfl⟩ : syracuseStep 19437965 = 7289237) B7289237
theorem B2021777 : Blo 1346992 2021777 := bstep (se 2 (by rfl) ⟨758166, by rfl⟩ : syracuseStep 2021777 = 1516333) B1516333
theorem B2021795 : Blo 1346992 2021795 := bstep (se 1 (by rfl) ⟨1516346, by rfl⟩ : syracuseStep 2021795 = 3032693) B3032693
theorem B2021825 : Blo 1346992 2021825 := bstep (se 2 (by rfl) ⟨758184, by rfl⟩ : syracuseStep 2021825 = 1516369) B1516369
theorem B4315601 : Blo 1346992 4315601 := bstep (se 2 (by rfl) ⟨1618350, by rfl⟩ : syracuseStep 4315601 = 3236701) B3236701
theorem B2021843 : Blo 1346992 2021843 := bstep (se 1 (by rfl) ⟨1516382, by rfl⟩ : syracuseStep 2021843 = 3032765) B3032765
theorem B16407011 : Blo 1346992 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B2021873 : Blo 1346992 2021873 := bstep (se 2 (by rfl) ⟨758202, by rfl⟩ : syracuseStep 2021873 = 1516405) B1516405
theorem B2021891 : Blo 1346992 2021891 := bstep (se 1 (by rfl) ⟨1516418, by rfl⟩ : syracuseStep 2021891 = 3032837) B3032837
theorem B2275843 : Blo 1346992 2275843 := bstep (se 1 (by rfl) ⟨1706882, by rfl⟩ : syracuseStep 2275843 = 3413765) B3413765
theorem B3414545 : Blo 1346992 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B2021921 : Blo 1346992 2021921 := bstep (se 2 (by rfl) ⟨758220, by rfl⟩ : syracuseStep 2021921 = 1516441) B1516441
theorem B2021939 : Blo 1346992 2021939 := bstep (se 1 (by rfl) ⟨1516454, by rfl⟩ : syracuseStep 2021939 = 3032909) B3032909
theorem B3414595 : Blo 1346992 3414595 := bstep (se 1 (by rfl) ⟨2560946, by rfl⟩ : syracuseStep 3414595 = 5121893) B5121893
theorem B2021969 : Blo 1346992 2021969 := bstep (se 2 (by rfl) ⟨758238, by rfl⟩ : syracuseStep 2021969 = 1516477) B1516477
theorem B2021987 : Blo 1346992 2021987 := bstep (se 1 (by rfl) ⟨1516490, by rfl⟩ : syracuseStep 2021987 = 3032981) B3032981
theorem B19438193 : Blo 1346992 19438193 := bstep (se 2 (by rfl) ⟨7289322, by rfl⟩ : syracuseStep 19438193 = 14578645) B14578645
theorem B2022017 : Blo 1346992 2022017 := bstep (se 2 (by rfl) ⟨758256, by rfl⟩ : syracuseStep 2022017 = 1516513) B1516513
theorem B7289477 : Blo 1346992 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B17283725 : Blo 1346992 17283725 := bstep (se 3 (by rfl) ⟨3240698, by rfl⟩ : syracuseStep 17283725 = 6481397) B6481397
theorem B2275985 : Blo 1346992 2275985 := bstep (se 2 (by rfl) ⟨853494, by rfl⟩ : syracuseStep 2275985 = 1706989) B1706989
theorem B2022035 : Blo 1346992 2022035 := bstep (se 1 (by rfl) ⟨1516526, by rfl⟩ : syracuseStep 2022035 = 3033053) B3033053
theorem B2022065 : Blo 1346992 2022065 := bstep (se 2 (by rfl) ⟨758274, by rfl⟩ : syracuseStep 2022065 = 1516549) B1516549
theorem B2022083 : Blo 1346992 2022083 := bstep (se 1 (by rfl) ⟨1516562, by rfl⟩ : syracuseStep 2022083 = 3033125) B3033125
theorem B2022113 : Blo 1346992 2022113 := bstep (se 2 (by rfl) ⟨758292, by rfl⟩ : syracuseStep 2022113 = 1516585) B1516585
theorem B2022131 : Blo 1346992 2022131 := bstep (se 1 (by rfl) ⟨1516598, by rfl⟩ : syracuseStep 2022131 = 3033197) B3033197
theorem B5184269 : Blo 1346992 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B2022161 : Blo 1346992 2022161 := bstep (se 2 (by rfl) ⟨758310, by rfl⟩ : syracuseStep 2022161 = 1516621) B1516621
theorem B2276113 : Blo 1346992 2276113 := bstep (se 2 (by rfl) ⟨853542, by rfl⟩ : syracuseStep 2276113 = 1707085) B1707085
theorem B2022179 : Blo 1346992 2022179 := bstep (se 1 (by rfl) ⟨1516634, by rfl⟩ : syracuseStep 2022179 = 3033269) B3033269
theorem B3840817 : Blo 1346992 3840817 := bstep (se 2 (by rfl) ⟨1440306, by rfl⟩ : syracuseStep 3840817 = 2880613) B2880613
theorem B2276147 : Blo 1346992 2276147 := bstep (se 1 (by rfl) ⟨1707110, by rfl⟩ : syracuseStep 2276147 = 3414221) B3414221
theorem B2022209 : Blo 1346992 2022209 := bstep (se 2 (by rfl) ⟨758328, by rfl⟩ : syracuseStep 2022209 = 1516657) B1516657
theorem B2022227 : Blo 1346992 2022227 := bstep (se 1 (by rfl) ⟨1516670, by rfl⟩ : syracuseStep 2022227 = 3033341) B3033341
theorem B2022257 : Blo 1346992 2022257 := bstep (se 2 (by rfl) ⟨758346, by rfl⟩ : syracuseStep 2022257 = 1516693) B1516693
theorem B2022275 : Blo 1346992 2022275 := bstep (se 1 (by rfl) ⟨1516706, by rfl⟩ : syracuseStep 2022275 = 3033413) B3033413
theorem B2022305 : Blo 1346992 2022305 := bstep (se 2 (by rfl) ⟨758364, by rfl⟩ : syracuseStep 2022305 = 1516729) B1516729
theorem B2022323 : Blo 1346992 2022323 := bstep (se 1 (by rfl) ⟨1516742, by rfl⟩ : syracuseStep 2022323 = 3033485) B3033485
theorem B2276275 : Blo 1346992 2276275 := bstep (se 1 (by rfl) ⟨1707206, by rfl⟩ : syracuseStep 2276275 = 3414413) B3414413
theorem B7674821 : Blo 1346992 7674821 := bstep (se 4 (by rfl) ⟨719514, by rfl⟩ : syracuseStep 7674821 = 1439029) B1439029
theorem B4316113 : Blo 1346992 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B2022353 : Blo 1346992 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B5118947 : Blo 1346992 5118947 := bstep (se 1 (by rfl) ⟨3839210, by rfl⟩ : syracuseStep 5118947 = 7678421) B7678421
theorem B2022371 : Blo 1346992 2022371 := bstep (se 1 (by rfl) ⟨1516778, by rfl⟩ : syracuseStep 2022371 = 3033557) B3033557
theorem B2022401 : Blo 1346992 2022401 := bstep (se 2 (by rfl) ⟨758400, by rfl⟩ : syracuseStep 2022401 = 1516801) B1516801
theorem B2022419 : Blo 1346992 2022419 := bstep (se 1 (by rfl) ⟨1516814, by rfl⟩ : syracuseStep 2022419 = 3033629) B3033629
theorem B2022449 : Blo 1346992 2022449 := bstep (se 2 (by rfl) ⟨758418, by rfl⟩ : syracuseStep 2022449 = 1516837) B1516837
theorem B2276417 : Blo 1346992 2276417 := bstep (se 2 (by rfl) ⟨853656, by rfl⟩ : syracuseStep 2276417 = 1707313) B1707313
theorem B2022467 : Blo 1346992 2022467 := bstep (se 1 (by rfl) ⟨1516850, by rfl⟩ : syracuseStep 2022467 = 3033701) B3033701
theorem B3841091 : Blo 1346992 3841091 := bstep (se 1 (by rfl) ⟨2880818, by rfl⟩ : syracuseStep 3841091 = 5761637) B5761637
theorem B2022497 : Blo 1346992 2022497 := bstep (se 2 (by rfl) ⟨758436, by rfl⟩ : syracuseStep 2022497 = 1516873) B1516873
theorem B2022515 : Blo 1346992 2022515 := bstep (se 1 (by rfl) ⟨1516886, by rfl⟩ : syracuseStep 2022515 = 3033773) B3033773
theorem B2022545 : Blo 1346992 2022545 := bstep (se 2 (by rfl) ⟨758454, by rfl⟩ : syracuseStep 2022545 = 1516909) B1516909
theorem B2022563 : Blo 1346992 2022563 := bstep (se 1 (by rfl) ⟨1516922, by rfl⟩ : syracuseStep 2022563 = 3033845) B3033845
theorem B5463217 : Blo 1346992 5463217 := bstep (se 2 (by rfl) ⟨2048706, by rfl⟩ : syracuseStep 5463217 = 4097413) B4097413
theorem B2022593 : Blo 1346992 2022593 := bstep (se 2 (by rfl) ⟨758472, by rfl⟩ : syracuseStep 2022593 = 1516945) B1516945
theorem B2022611 : Blo 1346992 2022611 := bstep (se 1 (by rfl) ⟨1516958, by rfl⟩ : syracuseStep 2022611 = 3033917) B3033917
theorem B2022641 : Blo 1346992 2022641 := bstep (se 2 (by rfl) ⟨758490, by rfl⟩ : syracuseStep 2022641 = 1516981) B1516981
theorem B2022659 : Blo 1346992 2022659 := bstep (se 1 (by rfl) ⟨1516994, by rfl⟩ : syracuseStep 2022659 = 3033989) B3033989
theorem B3841283 : Blo 1346992 3841283 := bstep (se 1 (by rfl) ⟨2880962, by rfl⟩ : syracuseStep 3841283 = 5761925) B5761925
theorem B2022689 : Blo 1346992 2022689 := bstep (se 2 (by rfl) ⟨758508, by rfl⟩ : syracuseStep 2022689 = 1517017) B1517017
theorem B2022707 : Blo 1346992 2022707 := bstep (se 1 (by rfl) ⟨1517030, by rfl⟩ : syracuseStep 2022707 = 3034061) B3034061
theorem B2022737 : Blo 1346992 2022737 := bstep (se 2 (by rfl) ⟨758526, by rfl⟩ : syracuseStep 2022737 = 1517053) B1517053
theorem B2022755 : Blo 1346992 2022755 := bstep (se 1 (by rfl) ⟨1517066, by rfl⟩ : syracuseStep 2022755 = 3034133) B3034133
theorem B2022785 : Blo 1346992 2022785 := bstep (se 2 (by rfl) ⟨758544, by rfl⟩ : syracuseStep 2022785 = 1517089) B1517089
theorem B2022803 : Blo 1346992 2022803 := bstep (se 1 (by rfl) ⟨1517102, by rfl⟩ : syracuseStep 2022803 = 3034205) B3034205
theorem B8756657 : Blo 1346992 8756657 := bstep (se 2 (by rfl) ⟨3283746, by rfl⟩ : syracuseStep 8756657 = 6567493) B6567493
theorem B2022833 : Blo 1346992 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B2022851 : Blo 1346992 2022851 := bstep (se 1 (by rfl) ⟨1517138, by rfl⟩ : syracuseStep 2022851 = 3034277) B3034277
theorem B2022881 : Blo 1346992 2022881 := bstep (se 2 (by rfl) ⟨758580, by rfl⟩ : syracuseStep 2022881 = 1517161) B1517161
theorem B15351281 : Blo 1346992 15351281 := bstep (se 2 (by rfl) ⟨5756730, by rfl⟩ : syracuseStep 15351281 = 11513461) B11513461
theorem B2022899 : Blo 1346992 2022899 := bstep (se 1 (by rfl) ⟨1517174, by rfl⟩ : syracuseStep 2022899 = 3034349) B3034349
theorem B2022929 : Blo 1346992 2022929 := bstep (se 2 (by rfl) ⟨758598, by rfl⟩ : syracuseStep 2022929 = 1517197) B1517197
theorem B2022947 : Blo 1346992 2022947 := bstep (se 1 (by rfl) ⟨1517210, by rfl⟩ : syracuseStep 2022947 = 3034421) B3034421
theorem B2022977 : Blo 1346992 2022977 := bstep (se 2 (by rfl) ⟨758616, by rfl⟩ : syracuseStep 2022977 = 1517233) B1517233
theorem B2022995 : Blo 1346992 2022995 := bstep (se 1 (by rfl) ⟨1517246, by rfl⟩ : syracuseStep 2022995 = 3034493) B3034493
theorem B11509361 : Blo 1346992 11509361 := bstep (se 2 (by rfl) ⟨4316010, by rfl⟩ : syracuseStep 11509361 = 8632021) B8632021
theorem B7675505 : Blo 1346992 7675505 := bstep (se 2 (by rfl) ⟨2878314, by rfl⟩ : syracuseStep 7675505 = 5756629) B5756629
theorem B5758577 : Blo 1346992 5758577 := bstep (se 2 (by rfl) ⟨2159466, by rfl⟩ : syracuseStep 5758577 = 4318933) B4318933
theorem B2023025 : Blo 1346992 2023025 := bstep (se 2 (by rfl) ⟨758634, by rfl⟩ : syracuseStep 2023025 = 1517269) B1517269
theorem B2023043 : Blo 1346992 2023043 := bstep (se 1 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 2023043 = 3034565) B3034565
theorem B2023073 : Blo 1346992 2023073 := bstep (se 2 (by rfl) ⟨758652, by rfl⟩ : syracuseStep 2023073 = 1517305) B1517305
theorem B6823601 : Blo 1346992 6823601 := bstep (se 2 (by rfl) ⟨2558850, by rfl⟩ : syracuseStep 6823601 = 5117701) B5117701
theorem B2023091 : Blo 1346992 2023091 := bstep (se 1 (by rfl) ⟨1517318, by rfl⟩ : syracuseStep 2023091 = 3034637) B3034637
theorem B2023121 : Blo 1346992 2023121 := bstep (se 2 (by rfl) ⟨758670, by rfl⟩ : syracuseStep 2023121 = 1517341) B1517341
theorem B1728211 : Blo 1346992 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B7282403 : Blo 1346992 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B2023139 : Blo 1346992 2023139 := bstep (se 1 (by rfl) ⟨1517354, by rfl⟩ : syracuseStep 2023139 = 3034709) B3034709
theorem B2023169 : Blo 1346992 2023169 := bstep (se 2 (by rfl) ⟨758688, by rfl⟩ : syracuseStep 2023169 = 1517377) B1517377
theorem B2023187 : Blo 1346992 2023187 := bstep (se 1 (by rfl) ⟨1517390, by rfl⟩ : syracuseStep 2023187 = 3034781) B3034781
theorem B2023217 : Blo 1346992 2023217 := bstep (se 2 (by rfl) ⟨758706, by rfl⟩ : syracuseStep 2023217 = 1517413) B1517413
theorem B2023235 : Blo 1346992 2023235 := bstep (se 1 (by rfl) ⟨1517426, by rfl⟩ : syracuseStep 2023235 = 3034853) B3034853
theorem B2023265 : Blo 1346992 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B1515379 : Blo 1346992 1515379 := bstep (se 1 (by rfl) ⟨1136534, by rfl⟩ : syracuseStep 1515379 = 2273069) B2273069
theorem B2023283 : Blo 1346992 2023283 := bstep (se 1 (by rfl) ⟨1517462, by rfl⟩ : syracuseStep 2023283 = 3034925) B3034925
theorem B3030929 : Blo 1346992 3030929 := bstep (se 2 (by rfl) ⟨1136598, by rfl⟩ : syracuseStep 3030929 = 2273197) B2273197
theorem B3694481 : Blo 1346992 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B2023313 : Blo 1346992 2023313 := bstep (se 2 (by rfl) ⟨758742, by rfl⟩ : syracuseStep 2023313 = 1517485) B1517485
theorem B3030947 : Blo 1346992 3030947 := bstep (se 1 (by rfl) ⟨2273210, by rfl⟩ : syracuseStep 3030947 = 4546421) B4546421
theorem B2023331 : Blo 1346992 2023331 := bstep (se 1 (by rfl) ⟨1517498, by rfl⟩ : syracuseStep 2023331 = 3034997) B3034997
theorem B2023361 : Blo 1346992 2023361 := bstep (se 2 (by rfl) ⟨758760, by rfl⟩ : syracuseStep 2023361 = 1517521) B1517521
theorem B5119949 : Blo 1346992 5119949 := bstep (se 3 (by rfl) ⟨959990, by rfl⟩ : syracuseStep 5119949 = 1919981) B1919981
theorem B2023379 : Blo 1346992 2023379 := bstep (se 1 (by rfl) ⟨1517534, by rfl⟩ : syracuseStep 2023379 = 3035069) B3035069
theorem B10936291 : Blo 1346992 10936291 := bstep (se 1 (by rfl) ⟨8202218, by rfl⟩ : syracuseStep 10936291 = 16404437) B16404437
theorem B2023409 : Blo 1346992 2023409 := bstep (se 2 (by rfl) ⟨758778, by rfl⟩ : syracuseStep 2023409 = 1517557) B1517557
theorem B8306705 : Blo 1346992 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B4546583 : Blo 1346992 4546583 := bstep (se 1 (by rfl) ⟨3409937, by rfl⟩ : syracuseStep 4546583 = 6819875) B6819875
theorem B3891223 : Blo 1346992 3891223 := bstep (se 1 (by rfl) ⟨2918417, by rfl⟩ : syracuseStep 3891223 = 5836835) B5836835
theorem B3031091 : Blo 1346992 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B1515595 : Blo 1346992 1515595 := bstep (se 1 (by rfl) ⟨1136696, by rfl⟩ : syracuseStep 1515595 = 2273393) B2273393
theorem B3031127 : Blo 1346992 3031127 := bstep (se 1 (by rfl) ⟨2273345, by rfl⟩ : syracuseStep 3031127 = 4546691) B4546691
theorem B7676005 : Blo 1346992 7676005 := bstep (se 4 (by rfl) ⟨719625, by rfl⟩ : syracuseStep 7676005 = 1439251) B1439251
theorem B5120131 : Blo 1346992 5120131 := bstep (se 1 (by rfl) ⟨3840098, by rfl⟩ : syracuseStep 5120131 = 7680197) B7680197
theorem B6824087 : Blo 1346992 6824087 := bstep (se 1 (by rfl) ⟨5118065, by rfl⟩ : syracuseStep 6824087 = 10236131) B10236131
theorem B1515703 : Blo 1346992 1515703 := bstep (se 1 (by rfl) ⟨1136777, by rfl⟩ : syracuseStep 1515703 = 2273555) B2273555
theorem B3031307 : Blo 1346992 3031307 := bstep (se 1 (by rfl) ⟨2273480, by rfl⟩ : syracuseStep 3031307 = 4546961) B4546961
theorem B3031361 : Blo 1346992 3031361 := bstep (se 2 (by rfl) ⟨1136760, by rfl⟩ : syracuseStep 3031361 = 2273521) B2273521
theorem B1515883 : Blo 1346992 1515883 := bstep (se 1 (by rfl) ⟨1136912, by rfl⟩ : syracuseStep 1515883 = 2273825) B2273825
theorem B5759363 : Blo 1346992 5759363 := bstep (se 1 (by rfl) ⟨4319522, by rfl⟩ : syracuseStep 5759363 = 8639045) B8639045
theorem B10232243 : Blo 1346992 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B7995827 : Blo 1346992 7995827 := bstep (se 1 (by rfl) ⟨5996870, by rfl⟩ : syracuseStep 7995827 = 11993741) B11993741
theorem B5120435 : Blo 1346992 5120435 := bstep (se 1 (by rfl) ⟨3840326, by rfl⟩ : syracuseStep 5120435 = 7680653) B7680653
theorem B1515991 : Blo 1346992 1515991 := bstep (se 1 (by rfl) ⟨1136993, by rfl⟩ : syracuseStep 1515991 = 2273987) B2273987
theorem B12288473 : Blo 1346992 12288473 := bstep (se 2 (by rfl) ⟨4608177, by rfl⟩ : syracuseStep 12288473 = 9216355) B9216355
theorem B3031577 : Blo 1346992 3031577 := bstep (se 2 (by rfl) ⟨1136841, by rfl⟩ : syracuseStep 3031577 = 2273683) B2273683
theorem B4547123 : Blo 1346992 4547123 := bstep (se 1 (by rfl) ⟨3410342, by rfl⟩ : syracuseStep 4547123 = 6820685) B6820685
theorem B10936907 : Blo 1346992 10936907 := bstep (se 1 (by rfl) ⟨8202680, by rfl⟩ : syracuseStep 10936907 = 16405361) B16405361
theorem B3031667 : Blo 1346992 3031667 := bstep (se 1 (by rfl) ⟨2273750, by rfl⟩ : syracuseStep 3031667 = 4547501) B4547501
theorem B1516171 : Blo 1346992 1516171 := bstep (se 1 (by rfl) ⟨1137128, by rfl⟩ : syracuseStep 1516171 = 2274257) B2274257
theorem B11510423 : Blo 1346992 11510423 := bstep (se 1 (by rfl) ⟨8632817, by rfl⟩ : syracuseStep 11510423 = 17265635) B17265635
theorem B3031703 : Blo 1346992 3031703 := bstep (se 1 (by rfl) ⟨2273777, by rfl⟩ : syracuseStep 3031703 = 4547555) B4547555
theorem B1516279 : Blo 1346992 1516279 := bstep (se 1 (by rfl) ⟨1137209, by rfl⟩ : syracuseStep 1516279 = 2274419) B2274419
theorem B4547393 : Blo 1346992 4547393 := bstep (se 2 (by rfl) ⟨1705272, by rfl⟩ : syracuseStep 4547393 = 3410545) B3410545
theorem B3031883 : Blo 1346992 3031883 := bstep (se 1 (by rfl) ⟨2273912, by rfl⟩ : syracuseStep 3031883 = 4547825) B4547825
theorem B3031937 : Blo 1346992 3031937 := bstep (se 2 (by rfl) ⟨1136976, by rfl⟩ : syracuseStep 3031937 = 2273953) B2273953
theorem B1516459 : Blo 1346992 1516459 := bstep (se 1 (by rfl) ⟨1137344, by rfl⟩ : syracuseStep 1516459 = 2274689) B2274689
theorem B1516567 : Blo 1346992 1516567 := bstep (se 1 (by rfl) ⟨1137425, by rfl⟩ : syracuseStep 1516567 = 2274851) B2274851
theorem B5121089 : Blo 1346992 5121089 := bstep (se 2 (by rfl) ⟨1920408, by rfl⟩ : syracuseStep 5121089 = 3840817) B3840817
theorem B3032153 : Blo 1346992 3032153 := bstep (se 2 (by rfl) ⟨1137057, by rfl⟩ : syracuseStep 3032153 = 2274115) B2274115
theorem B3032243 : Blo 1346992 3032243 := bstep (se 1 (by rfl) ⟨2274182, by rfl⟩ : syracuseStep 3032243 = 4548365) B4548365
theorem B1516747 : Blo 1346992 1516747 := bstep (se 1 (by rfl) ⟨1137560, by rfl⟩ : syracuseStep 1516747 = 2275121) B2275121
theorem B3032279 : Blo 1346992 3032279 := bstep (se 1 (by rfl) ⟨2274209, by rfl⟩ : syracuseStep 3032279 = 4548419) B4548419
theorem B1516855 : Blo 1346992 1516855 := bstep (se 1 (by rfl) ⟨1137641, by rfl⟩ : syracuseStep 1516855 = 2275283) B2275283
theorem B2557271 : Blo 1346992 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1705303 : Blo 1346992 1705303 := bstep (se 1 (by rfl) ⟨1278977, by rfl⟩ : syracuseStep 1705303 = 2557955) B2557955
theorem B4547933 : Blo 1346992 4547933 := bstep (se 3 (by rfl) ⟨852737, by rfl⟩ : syracuseStep 4547933 = 1705475) B1705475
theorem B23029109 : Blo 1346992 23029109 := bstep (se 5 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 23029109 = 2158979) B2158979
theorem B3032459 : Blo 1346992 3032459 := bstep (se 1 (by rfl) ⟨2274344, by rfl⟩ : syracuseStep 3032459 = 4548689) B4548689
theorem B5469491 : Blo 1346992 5469491 := bstep (se 1 (by rfl) ⟨4102118, by rfl⟩ : syracuseStep 5469491 = 8204237) B8204237
theorem B3032513 : Blo 1346992 3032513 := bstep (se 2 (by rfl) ⟨1137192, by rfl⟩ : syracuseStep 3032513 = 2274385) B2274385
theorem B1517035 : Blo 1346992 1517035 := bstep (se 1 (by rfl) ⟨1137776, by rfl⟩ : syracuseStep 1517035 = 2275553) B2275553
theorem B7284289 : Blo 1346992 7284289 := bstep (se 2 (by rfl) ⟨2731608, by rfl⟩ : syracuseStep 7284289 = 5463217) B5463217
theorem B1517143 : Blo 1346992 1517143 := bstep (se 1 (by rfl) ⟨1137857, by rfl⟩ : syracuseStep 1517143 = 2275715) B2275715
theorem B6145625 : Blo 1346992 6145625 := bstep (se 2 (by rfl) ⟨2304609, by rfl⟩ : syracuseStep 6145625 = 4609219) B4609219
theorem B2877067 : Blo 1346992 2877067 := bstep (se 1 (by rfl) ⟨2157800, by rfl⟩ : syracuseStep 2877067 = 4315601) B4315601
theorem B1918603 : Blo 1346992 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B10938007 : Blo 1346992 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B3032729 : Blo 1346992 3032729 := bstep (se 2 (by rfl) ⟨1137273, by rfl⟩ : syracuseStep 3032729 = 2274547) B2274547
theorem B1459927 : Blo 1346992 1459927 := bstep (se 1 (by rfl) ⟨1094945, by rfl⟩ : syracuseStep 1459927 = 2189891) B2189891
theorem B3032819 : Blo 1346992 3032819 := bstep (se 1 (by rfl) ⟨2274614, by rfl⟩ : syracuseStep 3032819 = 4549229) B4549229
theorem B4859651 : Blo 1346992 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B1517323 : Blo 1346992 1517323 := bstep (se 1 (by rfl) ⟨1137992, by rfl⟩ : syracuseStep 1517323 = 2275985) B2275985
theorem B5916433 : Blo 1346992 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B3032855 : Blo 1346992 3032855 := bstep (se 1 (by rfl) ⟨2274641, by rfl⟩ : syracuseStep 3032855 = 4549283) B4549283
theorem B3409715 : Blo 1346992 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B11519819 : Blo 1346992 11519819 := bstep (se 1 (by rfl) ⟨8639864, by rfl⟩ : syracuseStep 11519819 = 17279729) B17279729
theorem B10233701 : Blo 1346992 10233701 := bstep (se 4 (by rfl) ⟨959409, by rfl⟩ : syracuseStep 10233701 = 1918819) B1918819
theorem B2557811 : Blo 1346992 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B1517431 : Blo 1346992 1517431 := bstep (se 1 (by rfl) ⟨1138073, by rfl⟩ : syracuseStep 1517431 = 2276147) B2276147
theorem B3073945 : Blo 1346992 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B3033035 : Blo 1346992 3033035 := bstep (se 1 (by rfl) ⟨2274776, by rfl⟩ : syracuseStep 3033035 = 4549553) B4549553
theorem B3033089 : Blo 1346992 3033089 := bstep (se 2 (by rfl) ⟨1137408, by rfl⟩ : syracuseStep 3033089 = 2274817) B2274817
theorem B1517611 : Blo 1346992 1517611 := bstep (se 1 (by rfl) ⟨1138208, by rfl⟩ : syracuseStep 1517611 = 2276417) B2276417
theorem B5261363 : Blo 1346992 5261363 := bstep (se 1 (by rfl) ⟨3946022, by rfl⟩ : syracuseStep 5261363 = 7892045) B7892045
theorem B3410009 : Blo 1346992 3410009 := bstep (se 2 (by rfl) ⟨1278753, by rfl⟩ : syracuseStep 3410009 = 2557507) B2557507
theorem B1706123 : Blo 1346992 1706123 := bstep (se 1 (by rfl) ⟨1279592, by rfl⟩ : syracuseStep 1706123 = 2559185) B2559185
theorem B4098251 : Blo 1346992 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B3033305 : Blo 1346992 3033305 := bstep (se 2 (by rfl) ⟨1137489, by rfl⟩ : syracuseStep 3033305 = 2274979) B2274979
theorem B14575877 : Blo 1346992 14575877 := bstep (se 4 (by rfl) ⟨1366488, by rfl⟩ : syracuseStep 14575877 = 2732977) B2732977
theorem B2304281 : Blo 1346992 2304281 := bstep (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) B1728211
theorem B3033395 : Blo 1346992 3033395 := bstep (se 1 (by rfl) ⟨2275046, by rfl⟩ : syracuseStep 3033395 = 4550093) B4550093
theorem B10234187 : Blo 1346992 10234187 := bstep (se 1 (by rfl) ⟨7675640, by rfl⟩ : syracuseStep 10234187 = 15351281) B15351281
theorem B3033431 : Blo 1346992 3033431 := bstep (se 1 (by rfl) ⟨2275073, by rfl⟩ : syracuseStep 3033431 = 4550147) B4550147
theorem B2877785 : Blo 1346992 2877785 := bstep (se 2 (by rfl) ⟨1079169, by rfl⟩ : syracuseStep 2877785 = 2158339) B2158339
theorem B2558297 : Blo 1346992 2558297 := bstep (se 2 (by rfl) ⟨959361, by rfl⟩ : syracuseStep 2558297 = 1918723) B1918723
theorem B4549067 : Blo 1346992 4549067 := bstep (se 1 (by rfl) ⟨3411800, by rfl⟩ : syracuseStep 4549067 = 6823601) B6823601
theorem B3033611 : Blo 1346992 3033611 := bstep (se 1 (by rfl) ⟨2275208, by rfl⟩ : syracuseStep 3033611 = 4550417) B4550417
theorem B3033665 : Blo 1346992 3033665 := bstep (se 2 (by rfl) ⟨1137624, by rfl⟩ : syracuseStep 3033665 = 2275249) B2275249
theorem B4549337 : Blo 1346992 4549337 := bstep (se 2 (by rfl) ⟨1706001, by rfl⟩ : syracuseStep 4549337 = 3412003) B3412003
theorem B25905905 : Blo 1346992 25905905 := bstep (se 2 (by rfl) ⟨9714714, by rfl⟩ : syracuseStep 25905905 = 19429429) B19429429
theorem B2878195 : Blo 1346992 2878195 := bstep (se 1 (by rfl) ⟨2158646, by rfl⟩ : syracuseStep 2878195 = 4317293) B4317293
theorem B2427671 : Blo 1346992 2427671 := bstep (se 1 (by rfl) ⟨1820753, by rfl⟩ : syracuseStep 2427671 = 3641507) B3641507
theorem B3033881 : Blo 1346992 3033881 := bstep (se 2 (by rfl) ⟨1137705, by rfl⟩ : syracuseStep 3033881 = 2275411) B2275411
theorem B1706827 : Blo 1346992 1706827 := bstep (se 1 (by rfl) ⟨1280120, by rfl⟩ : syracuseStep 1706827 = 2560241) B2560241
theorem B3033971 : Blo 1346992 3033971 := bstep (se 1 (by rfl) ⟨2275478, by rfl⟩ : syracuseStep 3033971 = 4550957) B4550957
theorem B3034007 : Blo 1346992 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B25897907 : Blo 1346992 25897907 := bstep (se 1 (by rfl) ⟨19423430, by rfl⟩ : syracuseStep 25897907 = 38846861) B38846861
theorem B3034187 : Blo 1346992 3034187 := bstep (se 1 (by rfl) ⟨2275640, by rfl⟩ : syracuseStep 3034187 = 4551281) B4551281
theorem B1707095 : Blo 1346992 1707095 := bstep (se 1 (by rfl) ⟨1280321, by rfl⟩ : syracuseStep 1707095 = 2560643) B2560643
theorem B3034241 : Blo 1346992 3034241 := bstep (se 2 (by rfl) ⟨1137840, by rfl⟩ : syracuseStep 3034241 = 2275681) B2275681
theorem B4861079 : Blo 1346992 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B5115059 : Blo 1346992 5115059 := bstep (se 1 (by rfl) ⟨3836294, by rfl⟩ : syracuseStep 5115059 = 7672589) B7672589
theorem B58264757 : Blo 1346992 58264757 := bstep (se 5 (by rfl) ⟨2731160, by rfl⟩ : syracuseStep 58264757 = 5462321) B5462321
theorem B3034457 : Blo 1346992 3034457 := bstep (se 2 (by rfl) ⟨1137921, by rfl⟩ : syracuseStep 3034457 = 2275843) B2275843
theorem B10243421 : Blo 1346992 10243421 := bstep (se 3 (by rfl) ⟨1920641, by rfl⟩ : syracuseStep 10243421 = 3841283) B3841283
theorem B9710999 : Blo 1346992 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B4550039 : Blo 1346992 4550039 := bstep (se 1 (by rfl) ⟨3412529, by rfl⟩ : syracuseStep 4550039 = 6825059) B6825059
theorem B1346999 : Blo 1346992 1346999 := bstep (se 1 (by rfl) ⟨1010249, by rfl⟩ : syracuseStep 1346999 = 2020499) B2020499
theorem B3034547 : Blo 1346992 3034547 := bstep (se 1 (by rfl) ⟨2275910, by rfl⟩ : syracuseStep 3034547 = 4551821) B4551821
theorem B1347019 : Blo 1346992 1347019 := bstep (se 1 (by rfl) ⟨1010264, by rfl⟩ : syracuseStep 1347019 = 2020529) B2020529
theorem B4320715 : Blo 1346992 4320715 := bstep (se 1 (by rfl) ⟨3240536, by rfl⟩ : syracuseStep 4320715 = 6481073) B6481073
theorem B1347031 : Blo 1346992 1347031 := bstep (se 1 (by rfl) ⟨1010273, by rfl⟩ : syracuseStep 1347031 = 2020547) B2020547
theorem B3034583 : Blo 1346992 3034583 := bstep (se 1 (by rfl) ⟨2275937, by rfl⟩ : syracuseStep 3034583 = 4551875) B4551875
theorem B1347051 : Blo 1346992 1347051 := bstep (se 1 (by rfl) ⟨1010288, by rfl⟩ : syracuseStep 1347051 = 2020577) B2020577
theorem B1347063 : Blo 1346992 1347063 := bstep (se 1 (by rfl) ⟨1010297, by rfl⟩ : syracuseStep 1347063 = 2020595) B2020595
theorem B1347083 : Blo 1346992 1347083 := bstep (se 1 (by rfl) ⟨1010312, by rfl⟩ : syracuseStep 1347083 = 2020625) B2020625
theorem B1347095 : Blo 1346992 1347095 := bstep (se 1 (by rfl) ⟨1010321, by rfl⟩ : syracuseStep 1347095 = 2020643) B2020643
theorem B1347115 : Blo 1346992 1347115 := bstep (se 1 (by rfl) ⟨1010336, by rfl⟩ : syracuseStep 1347115 = 2020673) B2020673
theorem B1347127 : Blo 1346992 1347127 := bstep (se 1 (by rfl) ⟨1010345, by rfl⟩ : syracuseStep 1347127 = 2020691) B2020691
theorem B3239489 : Blo 1346992 3239489 := bstep (se 2 (by rfl) ⟨1214808, by rfl⟩ : syracuseStep 3239489 = 2429617) B2429617
theorem B1347147 : Blo 1346992 1347147 := bstep (se 1 (by rfl) ⟨1010360, by rfl⟩ : syracuseStep 1347147 = 2020721) B2020721
theorem B1347159 : Blo 1346992 1347159 := bstep (se 1 (by rfl) ⟨1010369, by rfl⟩ : syracuseStep 1347159 = 2020739) B2020739
theorem B1347179 : Blo 1346992 1347179 := bstep (se 1 (by rfl) ⟨1010384, by rfl⟩ : syracuseStep 1347179 = 2020769) B2020769
theorem B1347191 : Blo 1346992 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B6827651 : Blo 1346992 6827651 := bstep (se 1 (by rfl) ⟨5120738, by rfl⟩ : syracuseStep 6827651 = 10241477) B10241477
theorem B1347211 : Blo 1346992 1347211 := bstep (se 1 (by rfl) ⟨1010408, by rfl⟩ : syracuseStep 1347211 = 2020817) B2020817
theorem B3034763 : Blo 1346992 3034763 := bstep (se 1 (by rfl) ⟨2276072, by rfl⟩ : syracuseStep 3034763 = 4552145) B4552145
theorem B1347223 : Blo 1346992 1347223 := bstep (se 1 (by rfl) ⟨1010417, by rfl⟩ : syracuseStep 1347223 = 2020835) B2020835
theorem B1347243 : Blo 1346992 1347243 := bstep (se 1 (by rfl) ⟨1010432, by rfl⟩ : syracuseStep 1347243 = 2020865) B2020865
theorem B4992691 : Blo 1346992 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B1347255 : Blo 1346992 1347255 := bstep (se 1 (by rfl) ⟨1010441, by rfl⟩ : syracuseStep 1347255 = 2020883) B2020883
theorem B3034817 : Blo 1346992 3034817 := bstep (se 2 (by rfl) ⟨1138056, by rfl⟩ : syracuseStep 3034817 = 2276113) B2276113
theorem B1347275 : Blo 1346992 1347275 := bstep (se 1 (by rfl) ⟨1010456, by rfl⟩ : syracuseStep 1347275 = 2020913) B2020913
theorem B3411659 : Blo 1346992 3411659 := bstep (se 1 (by rfl) ⟨2558744, by rfl⟩ : syracuseStep 3411659 = 5117489) B5117489
theorem B1347287 : Blo 1346992 1347287 := bstep (se 1 (by rfl) ⟨1010465, by rfl⟩ : syracuseStep 1347287 = 2020931) B2020931
theorem B1347307 : Blo 1346992 1347307 := bstep (se 1 (by rfl) ⟨1010480, by rfl⟩ : syracuseStep 1347307 = 2020961) B2020961
theorem B1347319 : Blo 1346992 1347319 := bstep (se 1 (by rfl) ⟨1010489, by rfl⟩ : syracuseStep 1347319 = 2020979) B2020979
theorem B3075841 : Blo 1346992 3075841 := bstep (se 2 (by rfl) ⟨1153440, by rfl⟩ : syracuseStep 3075841 = 2306881) B2306881
theorem B1347339 : Blo 1346992 1347339 := bstep (se 1 (by rfl) ⟨1010504, by rfl⟩ : syracuseStep 1347339 = 2021009) B2021009
theorem B2559755 : Blo 1346992 2559755 := bstep (se 1 (by rfl) ⟨1919816, by rfl⟩ : syracuseStep 2559755 = 3839633) B3839633
theorem B1347351 : Blo 1346992 1347351 := bstep (se 1 (by rfl) ⟨1010513, by rfl⟩ : syracuseStep 1347351 = 2021027) B2021027
theorem B3837719 : Blo 1346992 3837719 := bstep (se 1 (by rfl) ⟨2878289, by rfl⟩ : syracuseStep 3837719 = 5756579) B5756579
theorem B1347371 : Blo 1346992 1347371 := bstep (se 1 (by rfl) ⟨1010528, by rfl⟩ : syracuseStep 1347371 = 2021057) B2021057
theorem B1347383 : Blo 1346992 1347383 := bstep (se 1 (by rfl) ⟨1010537, by rfl⟩ : syracuseStep 1347383 = 2021075) B2021075
theorem B1347403 : Blo 1346992 1347403 := bstep (se 1 (by rfl) ⟨1010552, by rfl⟩ : syracuseStep 1347403 = 2021105) B2021105
theorem B1347415 : Blo 1346992 1347415 := bstep (se 1 (by rfl) ⟨1010561, by rfl⟩ : syracuseStep 1347415 = 2021123) B2021123
theorem B1347435 : Blo 1346992 1347435 := bstep (se 1 (by rfl) ⟨1010576, by rfl⟩ : syracuseStep 1347435 = 2021153) B2021153
theorem B1347447 : Blo 1346992 1347447 := bstep (se 1 (by rfl) ⟨1010585, by rfl⟩ : syracuseStep 1347447 = 2021171) B2021171
theorem B1347467 : Blo 1346992 1347467 := bstep (se 1 (by rfl) ⟨1010600, by rfl⟩ : syracuseStep 1347467 = 2021201) B2021201
theorem B1347479 : Blo 1346992 1347479 := bstep (se 1 (by rfl) ⟨1010609, by rfl⟩ : syracuseStep 1347479 = 2021219) B2021219
theorem B2428823 : Blo 1346992 2428823 := bstep (se 1 (by rfl) ⟨1821617, by rfl⟩ : syracuseStep 2428823 = 3643235) B3643235
theorem B2273177 : Blo 1346992 2273177 := bstep (se 2 (by rfl) ⟨852441, by rfl⟩ : syracuseStep 2273177 = 1704883) B1704883
theorem B2879383 : Blo 1346992 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B3035033 : Blo 1346992 3035033 := bstep (se 2 (by rfl) ⟨1138137, by rfl⟩ : syracuseStep 3035033 = 2276275) B2276275
theorem B1347499 : Blo 1346992 1347499 := bstep (se 1 (by rfl) ⟨1010624, by rfl⟩ : syracuseStep 1347499 = 2021249) B2021249
theorem B79826867 : Blo 1346992 79826867 := bstep (se 1 (by rfl) ⟨59870150, by rfl⟩ : syracuseStep 79826867 = 119740301) B119740301
theorem B4550579 : Blo 1346992 4550579 := bstep (se 1 (by rfl) ⟨3412934, by rfl⟩ : syracuseStep 4550579 = 6825869) B6825869
theorem B1347511 : Blo 1346992 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B5754817 : Blo 1346992 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B2879425 : Blo 1346992 2879425 := bstep (se 2 (by rfl) ⟨1079784, by rfl⟩ : syracuseStep 2879425 = 2159569) B2159569
theorem B2559937 : Blo 1346992 2559937 := bstep (se 2 (by rfl) ⟨959976, by rfl⟩ : syracuseStep 2559937 = 1919953) B1919953
theorem B1347531 : Blo 1346992 1347531 := bstep (se 1 (by rfl) ⟨1010648, by rfl⟩ : syracuseStep 1347531 = 2021297) B2021297
theorem B1347543 : Blo 1346992 1347543 := bstep (se 1 (by rfl) ⟨1010657, by rfl⟩ : syracuseStep 1347543 = 2021315) B2021315
theorem B2461657 : Blo 1346992 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B1347563 : Blo 1346992 1347563 := bstep (se 1 (by rfl) ⟨1010672, by rfl⟩ : syracuseStep 1347563 = 2021345) B2021345
theorem B3035123 : Blo 1346992 3035123 := bstep (se 1 (by rfl) ⟨2276342, by rfl⟩ : syracuseStep 3035123 = 4552685) B4552685
theorem B1347575 : Blo 1346992 1347575 := bstep (se 1 (by rfl) ⟨1010681, by rfl⟩ : syracuseStep 1347575 = 2021363) B2021363
theorem B1347595 : Blo 1346992 1347595 := bstep (se 1 (by rfl) ⟨1010696, by rfl⟩ : syracuseStep 1347595 = 2021393) B2021393
theorem B1347607 : Blo 1346992 1347607 := bstep (se 1 (by rfl) ⟨1010705, by rfl⟩ : syracuseStep 1347607 = 2021411) B2021411
theorem B3035159 : Blo 1346992 3035159 := bstep (se 1 (by rfl) ⟨2276369, by rfl⟩ : syracuseStep 3035159 = 4552739) B4552739
theorem B2273305 : Blo 1346992 2273305 := bstep (se 2 (by rfl) ⟨852489, by rfl⟩ : syracuseStep 2273305 = 1704979) B1704979
theorem B1347627 : Blo 1346992 1347627 := bstep (se 1 (by rfl) ⟨1010720, by rfl⟩ : syracuseStep 1347627 = 2021441) B2021441
theorem B1347639 : Blo 1346992 1347639 := bstep (se 1 (by rfl) ⟨1010729, by rfl⟩ : syracuseStep 1347639 = 2021459) B2021459
theorem B1347659 : Blo 1346992 1347659 := bstep (se 1 (by rfl) ⟨1010744, by rfl⟩ : syracuseStep 1347659 = 2021489) B2021489
theorem B1347671 : Blo 1346992 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B1347691 : Blo 1346992 1347691 := bstep (se 1 (by rfl) ⟨1010768, by rfl⟩ : syracuseStep 1347691 = 2021537) B2021537
theorem B1347703 : Blo 1346992 1347703 := bstep (se 1 (by rfl) ⟨1010777, by rfl⟩ : syracuseStep 1347703 = 2021555) B2021555
theorem B1347723 : Blo 1346992 1347723 := bstep (se 1 (by rfl) ⟨1010792, by rfl⟩ : syracuseStep 1347723 = 2021585) B2021585
theorem B1347735 : Blo 1346992 1347735 := bstep (se 1 (by rfl) ⟨1010801, by rfl⟩ : syracuseStep 1347735 = 2021603) B2021603
theorem B1347755 : Blo 1346992 1347755 := bstep (se 1 (by rfl) ⟨1010816, by rfl⟩ : syracuseStep 1347755 = 2021633) B2021633
theorem B29151413 : Blo 1346992 29151413 := bstep (se 5 (by rfl) ⟨1366472, by rfl⟩ : syracuseStep 29151413 = 2732945) B2732945
theorem B1347767 : Blo 1346992 1347767 := bstep (se 1 (by rfl) ⟨1010825, by rfl⟩ : syracuseStep 1347767 = 2021651) B2021651
theorem B4550849 : Blo 1346992 4550849 := bstep (se 2 (by rfl) ⟨1706568, by rfl⟩ : syracuseStep 4550849 = 3413137) B3413137
theorem B1347787 : Blo 1346992 1347787 := bstep (se 1 (by rfl) ⟨1010840, by rfl⟩ : syracuseStep 1347787 = 2021681) B2021681
theorem B1347799 : Blo 1346992 1347799 := bstep (se 1 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 1347799 = 2021699) B2021699
theorem B1347819 : Blo 1346992 1347819 := bstep (se 1 (by rfl) ⟨1010864, by rfl⟩ : syracuseStep 1347819 = 2021729) B2021729
theorem B1347831 : Blo 1346992 1347831 := bstep (se 1 (by rfl) ⟨1010873, by rfl⟩ : syracuseStep 1347831 = 2021747) B2021747
theorem B1347851 : Blo 1346992 1347851 := bstep (se 1 (by rfl) ⟨1010888, by rfl⟩ : syracuseStep 1347851 = 2021777) B2021777
theorem B1347863 : Blo 1346992 1347863 := bstep (se 1 (by rfl) ⟨1010897, by rfl⟩ : syracuseStep 1347863 = 2021795) B2021795
theorem B1347883 : Blo 1346992 1347883 := bstep (se 1 (by rfl) ⟨1010912, by rfl⟩ : syracuseStep 1347883 = 2021825) B2021825
theorem B1347895 : Blo 1346992 1347895 := bstep (se 1 (by rfl) ⟨1010921, by rfl⟩ : syracuseStep 1347895 = 2021843) B2021843
theorem B2732363 : Blo 1346992 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B1347915 : Blo 1346992 1347915 := bstep (se 1 (by rfl) ⟨1010936, by rfl⟩ : syracuseStep 1347915 = 2021873) B2021873
theorem B1347927 : Blo 1346992 1347927 := bstep (se 1 (by rfl) ⟨1010945, by rfl⟩ : syracuseStep 1347927 = 2021891) B2021891
theorem B7672157 : Blo 1346992 7672157 := bstep (se 3 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 7672157 = 2877059) B2877059
theorem B1347947 : Blo 1346992 1347947 := bstep (se 1 (by rfl) ⟨1010960, by rfl⟩ : syracuseStep 1347947 = 2021921) B2021921
theorem B1347959 : Blo 1346992 1347959 := bstep (se 1 (by rfl) ⟨1010969, by rfl⟩ : syracuseStep 1347959 = 2021939) B2021939
theorem B2560385 : Blo 1346992 2560385 := bstep (se 2 (by rfl) ⟨960144, by rfl⟩ : syracuseStep 2560385 = 1920289) B1920289
theorem B1347979 : Blo 1346992 1347979 := bstep (se 1 (by rfl) ⟨1010984, by rfl⟩ : syracuseStep 1347979 = 2021969) B2021969
theorem B1347991 : Blo 1346992 1347991 := bstep (se 1 (by rfl) ⟨1010993, by rfl⟩ : syracuseStep 1347991 = 2021987) B2021987
theorem B1348011 : Blo 1346992 1348011 := bstep (se 1 (by rfl) ⟨1011008, by rfl⟩ : syracuseStep 1348011 = 2022017) B2022017
theorem B11522483 : Blo 1346992 11522483 := bstep (se 1 (by rfl) ⟨8641862, by rfl⟩ : syracuseStep 11522483 = 17283725) B17283725
theorem B1348023 : Blo 1346992 1348023 := bstep (se 1 (by rfl) ⟨1011017, by rfl⟩ : syracuseStep 1348023 = 2022035) B2022035
theorem B1348043 : Blo 1346992 1348043 := bstep (se 1 (by rfl) ⟨1011032, by rfl⟩ : syracuseStep 1348043 = 2022065) B2022065
theorem B1348055 : Blo 1346992 1348055 := bstep (se 1 (by rfl) ⟨1011041, by rfl⟩ : syracuseStep 1348055 = 2022083) B2022083
theorem B1348075 : Blo 1346992 1348075 := bstep (se 1 (by rfl) ⟨1011056, by rfl⟩ : syracuseStep 1348075 = 2022113) B2022113
theorem B1348087 : Blo 1346992 1348087 := bstep (se 1 (by rfl) ⟨1011065, by rfl⟩ : syracuseStep 1348087 = 2022131) B2022131
theorem B1348107 : Blo 1346992 1348107 := bstep (se 1 (by rfl) ⟨1011080, by rfl⟩ : syracuseStep 1348107 = 2022161) B2022161
theorem B1348119 : Blo 1346992 1348119 := bstep (se 1 (by rfl) ⟨1011089, by rfl⟩ : syracuseStep 1348119 = 2022179) B2022179
theorem B1348139 : Blo 1346992 1348139 := bstep (se 1 (by rfl) ⟨1011104, by rfl⟩ : syracuseStep 1348139 = 2022209) B2022209
theorem B1348151 : Blo 1346992 1348151 := bstep (se 1 (by rfl) ⟨1011113, by rfl⟩ : syracuseStep 1348151 = 2022227) B2022227
theorem B1348171 : Blo 1346992 1348171 := bstep (se 1 (by rfl) ⟨1011128, by rfl⟩ : syracuseStep 1348171 = 2022257) B2022257
theorem B2273879 : Blo 1346992 2273879 := bstep (se 1 (by rfl) ⟨1705409, by rfl⟩ : syracuseStep 2273879 = 3410819) B3410819
theorem B1348183 : Blo 1346992 1348183 := bstep (se 1 (by rfl) ⟨1011137, by rfl⟩ : syracuseStep 1348183 = 2022275) B2022275
theorem B1348203 : Blo 1346992 1348203 := bstep (se 1 (by rfl) ⟨1011152, by rfl⟩ : syracuseStep 1348203 = 2022305) B2022305
theorem B1348215 : Blo 1346992 1348215 := bstep (se 1 (by rfl) ⟨1011161, by rfl⟩ : syracuseStep 1348215 = 2022323) B2022323
theorem B5116547 : Blo 1346992 5116547 := bstep (se 1 (by rfl) ⟨3837410, by rfl⟩ : syracuseStep 5116547 = 7674821) B7674821
theorem B1348235 : Blo 1346992 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B3412631 : Blo 1346992 3412631 := bstep (se 1 (by rfl) ⟨2559473, by rfl⟩ : syracuseStep 3412631 = 5118947) B5118947
theorem B1348247 : Blo 1346992 1348247 := bstep (se 1 (by rfl) ⟨1011185, by rfl⟩ : syracuseStep 1348247 = 2022371) B2022371
theorem B1348267 : Blo 1346992 1348267 := bstep (se 1 (by rfl) ⟨1011200, by rfl⟩ : syracuseStep 1348267 = 2022401) B2022401
theorem B1348279 : Blo 1346992 1348279 := bstep (se 1 (by rfl) ⟨1011209, by rfl⟩ : syracuseStep 1348279 = 2022419) B2022419
theorem B1348299 : Blo 1346992 1348299 := bstep (se 1 (by rfl) ⟨1011224, by rfl⟩ : syracuseStep 1348299 = 2022449) B2022449
theorem B2274007 : Blo 1346992 2274007 := bstep (se 1 (by rfl) ⟨1705505, by rfl⟩ : syracuseStep 2274007 = 3411011) B3411011
theorem B1348311 : Blo 1346992 1348311 := bstep (se 1 (by rfl) ⟨1011233, by rfl⟩ : syracuseStep 1348311 = 2022467) B2022467
theorem B2560727 : Blo 1346992 2560727 := bstep (se 1 (by rfl) ⟨1920545, by rfl⟩ : syracuseStep 2560727 = 3841091) B3841091
theorem B4551389 : Blo 1346992 4551389 := bstep (se 3 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 4551389 = 1706771) B1706771
theorem B1348331 : Blo 1346992 1348331 := bstep (se 1 (by rfl) ⟨1011248, by rfl⟩ : syracuseStep 1348331 = 2022497) B2022497
theorem B1348343 : Blo 1346992 1348343 := bstep (se 1 (by rfl) ⟨1011257, by rfl⟩ : syracuseStep 1348343 = 2022515) B2022515
theorem B1348363 : Blo 1346992 1348363 := bstep (se 1 (by rfl) ⟨1011272, by rfl⟩ : syracuseStep 1348363 = 2022545) B2022545
theorem B1348375 : Blo 1346992 1348375 := bstep (se 1 (by rfl) ⟨1011281, by rfl⟩ : syracuseStep 1348375 = 2022563) B2022563
theorem B1348395 : Blo 1346992 1348395 := bstep (se 1 (by rfl) ⟨1011296, by rfl⟩ : syracuseStep 1348395 = 2022593) B2022593
theorem B1348407 : Blo 1346992 1348407 := bstep (se 1 (by rfl) ⟨1011305, by rfl⟩ : syracuseStep 1348407 = 2022611) B2022611
theorem B4436801 : Blo 1346992 4436801 := bstep (se 2 (by rfl) ⟨1663800, by rfl⟩ : syracuseStep 4436801 = 3327601) B3327601
theorem B2159435 : Blo 1346992 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B1348427 : Blo 1346992 1348427 := bstep (se 1 (by rfl) ⟨1011320, by rfl⟩ : syracuseStep 1348427 = 2022641) B2022641
theorem B1348439 : Blo 1346992 1348439 := bstep (se 1 (by rfl) ⟨1011329, by rfl⟩ : syracuseStep 1348439 = 2022659) B2022659
theorem B1348459 : Blo 1346992 1348459 := bstep (se 1 (by rfl) ⟨1011344, by rfl⟩ : syracuseStep 1348459 = 2022689) B2022689
theorem B1348471 : Blo 1346992 1348471 := bstep (se 1 (by rfl) ⟨1011353, by rfl⟩ : syracuseStep 1348471 = 2022707) B2022707
theorem B1348491 : Blo 1346992 1348491 := bstep (se 1 (by rfl) ⟨1011368, by rfl⟩ : syracuseStep 1348491 = 2022737) B2022737
theorem B1348503 : Blo 1346992 1348503 := bstep (se 1 (by rfl) ⟨1011377, by rfl⟩ : syracuseStep 1348503 = 2022755) B2022755
theorem B1348523 : Blo 1346992 1348523 := bstep (se 1 (by rfl) ⟨1011392, by rfl⟩ : syracuseStep 1348523 = 2022785) B2022785
theorem B1348535 : Blo 1346992 1348535 := bstep (se 1 (by rfl) ⟨1011401, by rfl⟩ : syracuseStep 1348535 = 2022803) B2022803
theorem B5837771 : Blo 1346992 5837771 := bstep (se 1 (by rfl) ⟨4378328, by rfl⟩ : syracuseStep 5837771 = 8756657) B8756657
theorem B1348555 : Blo 1346992 1348555 := bstep (se 1 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 1348555 = 2022833) B2022833
theorem B1438679 : Blo 1346992 1438679 := bstep (se 1 (by rfl) ⟨1079009, by rfl⟩ : syracuseStep 1438679 = 2158019) B2158019
theorem B1348567 : Blo 1346992 1348567 := bstep (se 1 (by rfl) ⟨1011425, by rfl⟩ : syracuseStep 1348567 = 2022851) B2022851
theorem B1348587 : Blo 1346992 1348587 := bstep (se 1 (by rfl) ⟨1011440, by rfl⟩ : syracuseStep 1348587 = 2022881) B2022881
theorem B1348599 : Blo 1346992 1348599 := bstep (se 1 (by rfl) ⟨1011449, by rfl⟩ : syracuseStep 1348599 = 2022899) B2022899
theorem B1348619 : Blo 1346992 1348619 := bstep (se 1 (by rfl) ⟨1011464, by rfl⟩ : syracuseStep 1348619 = 2022929) B2022929
theorem B12948497 : Blo 1346992 12948497 := bstep (se 2 (by rfl) ⟨4855686, by rfl⟩ : syracuseStep 12948497 = 9711373) B9711373
theorem B1348631 : Blo 1346992 1348631 := bstep (se 1 (by rfl) ⟨1011473, by rfl⟩ : syracuseStep 1348631 = 2022947) B2022947
theorem B1348651 : Blo 1346992 1348651 := bstep (se 1 (by rfl) ⟨1011488, by rfl⟩ : syracuseStep 1348651 = 2022977) B2022977
theorem B1348663 : Blo 1346992 1348663 := bstep (se 1 (by rfl) ⟨1011497, by rfl⟩ : syracuseStep 1348663 = 2022995) B2022995
theorem B7672907 : Blo 1346992 7672907 := bstep (se 1 (by rfl) ⟨5754680, by rfl⟩ : syracuseStep 7672907 = 11509361) B11509361
theorem B5117003 : Blo 1346992 5117003 := bstep (se 1 (by rfl) ⟨3837752, by rfl⟩ : syracuseStep 5117003 = 7675505) B7675505
theorem B3839051 : Blo 1346992 3839051 := bstep (se 1 (by rfl) ⟨2879288, by rfl⟩ : syracuseStep 3839051 = 5758577) B5758577
theorem B1348683 : Blo 1346992 1348683 := bstep (se 1 (by rfl) ⟨1011512, by rfl⟩ : syracuseStep 1348683 = 2023025) B2023025
theorem B1438807 : Blo 1346992 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B1348695 : Blo 1346992 1348695 := bstep (se 1 (by rfl) ⟨1011521, by rfl⟩ : syracuseStep 1348695 = 2023043) B2023043
theorem B1348715 : Blo 1346992 1348715 := bstep (se 1 (by rfl) ⟨1011536, by rfl⟩ : syracuseStep 1348715 = 2023073) B2023073
theorem B1348727 : Blo 1346992 1348727 := bstep (se 1 (by rfl) ⟨1011545, by rfl⟩ : syracuseStep 1348727 = 2023091) B2023091
theorem B1348747 : Blo 1346992 1348747 := bstep (se 1 (by rfl) ⟨1011560, by rfl⟩ : syracuseStep 1348747 = 2023121) B2023121
theorem B4854935 : Blo 1346992 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B1348759 : Blo 1346992 1348759 := bstep (se 1 (by rfl) ⟨1011569, by rfl⟩ : syracuseStep 1348759 = 2023139) B2023139
theorem B2020505 : Blo 1346992 2020505 := bstep (se 2 (by rfl) ⟨757689, by rfl⟩ : syracuseStep 2020505 = 1515379) B1515379
theorem B1348779 : Blo 1346992 1348779 := bstep (se 1 (by rfl) ⟨1011584, by rfl⟩ : syracuseStep 1348779 = 2023169) B2023169
theorem B1348791 : Blo 1346992 1348791 := bstep (se 1 (by rfl) ⟨1011593, by rfl⟩ : syracuseStep 1348791 = 2023187) B2023187
theorem B1348811 : Blo 1346992 1348811 := bstep (se 1 (by rfl) ⟨1011608, by rfl⟩ : syracuseStep 1348811 = 2023217) B2023217
theorem B1348823 : Blo 1346992 1348823 := bstep (se 1 (by rfl) ⟨1011617, by rfl⟩ : syracuseStep 1348823 = 2023235) B2023235
theorem B1348843 : Blo 1346992 1348843 := bstep (se 1 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 1348843 = 2023265) B2023265
theorem B1348855 : Blo 1346992 1348855 := bstep (se 1 (by rfl) ⟨1011641, by rfl⟩ : syracuseStep 1348855 = 2023283) B2023283
theorem B2020619 : Blo 1346992 2020619 := bstep (se 1 (by rfl) ⟨1515464, by rfl⟩ : syracuseStep 2020619 = 3030929) B3030929
theorem B2462987 : Blo 1346992 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B1348875 : Blo 1346992 1348875 := bstep (se 1 (by rfl) ⟨1011656, by rfl⟩ : syracuseStep 1348875 = 2023313) B2023313
theorem B5117201 : Blo 1346992 5117201 := bstep (se 2 (by rfl) ⟨1918950, by rfl⟩ : syracuseStep 5117201 = 3837901) B3837901
theorem B2020631 : Blo 1346992 2020631 := bstep (se 1 (by rfl) ⟨1515473, by rfl⟩ : syracuseStep 2020631 = 3030947) B3030947
theorem B1348887 : Blo 1346992 1348887 := bstep (se 1 (by rfl) ⟨1011665, by rfl⟩ : syracuseStep 1348887 = 2023331) B2023331
theorem B1348907 : Blo 1346992 1348907 := bstep (se 1 (by rfl) ⟨1011680, by rfl⟩ : syracuseStep 1348907 = 2023361) B2023361
theorem B3413299 : Blo 1346992 3413299 := bstep (se 1 (by rfl) ⟨2559974, by rfl⟩ : syracuseStep 3413299 = 5119949) B5119949
theorem B1348919 : Blo 1346992 1348919 := bstep (se 1 (by rfl) ⟨1011689, by rfl⟩ : syracuseStep 1348919 = 2023379) B2023379
theorem B2274635 : Blo 1346992 2274635 := bstep (se 1 (by rfl) ⟨1705976, by rfl⟩ : syracuseStep 2274635 = 3411953) B3411953
theorem B1348939 : Blo 1346992 1348939 := bstep (se 1 (by rfl) ⟨1011704, by rfl⟩ : syracuseStep 1348939 = 2023409) B2023409
theorem B1348951 : Blo 1346992 1348951 := bstep (se 1 (by rfl) ⟨1011713, by rfl⟩ : syracuseStep 1348951 = 2023427) B2023427
theorem B2020697 : Blo 1346992 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B2733401 : Blo 1346992 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B1348971 : Blo 1346992 1348971 := bstep (se 1 (by rfl) ⟨1011728, by rfl⟩ : syracuseStep 1348971 = 2023457) B2023457
theorem B1348983 : Blo 1346992 1348983 := bstep (se 1 (by rfl) ⟨1011737, by rfl⟩ : syracuseStep 1348983 = 2023475) B2023475
theorem B5756305 : Blo 1346992 5756305 := bstep (se 2 (by rfl) ⟨2158614, by rfl⟩ : syracuseStep 5756305 = 4317229) B4317229
theorem B3413441 : Blo 1346992 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2020811 : Blo 1346992 2020811 := bstep (se 1 (by rfl) ⟨1515608, by rfl⟩ : syracuseStep 2020811 = 3031217) B3031217
theorem B2274763 : Blo 1346992 2274763 := bstep (se 1 (by rfl) ⟨1706072, by rfl⟩ : syracuseStep 2274763 = 3412145) B3412145
theorem B1537483 : Blo 1346992 1537483 := bstep (se 1 (by rfl) ⟨1153112, by rfl⟩ : syracuseStep 1537483 = 2306225) B2306225
theorem B2020823 : Blo 1346992 2020823 := bstep (se 1 (by rfl) ⟨1515617, by rfl⟩ : syracuseStep 2020823 = 3031235) B3031235
theorem B11523545 : Blo 1346992 11523545 := bstep (se 2 (by rfl) ⟨4321329, by rfl⟩ : syracuseStep 11523545 = 8642659) B8642659
theorem B8640017 : Blo 1346992 8640017 := bstep (se 2 (by rfl) ⟨3240006, by rfl⟩ : syracuseStep 8640017 = 6480013) B6480013
theorem B2020889 : Blo 1346992 2020889 := bstep (se 2 (by rfl) ⟨757833, by rfl⟩ : syracuseStep 2020889 = 1515667) B1515667
theorem B2881099 : Blo 1346992 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B2274905 : Blo 1346992 2274905 := bstep (se 2 (by rfl) ⟨853089, by rfl⟩ : syracuseStep 2274905 = 1706179) B1706179
theorem B2021003 : Blo 1346992 2021003 := bstep (se 1 (by rfl) ⟨1515752, by rfl⟩ : syracuseStep 2021003 = 3031505) B3031505
theorem B1439371 : Blo 1346992 1439371 := bstep (se 1 (by rfl) ⟨1079528, by rfl⟩ : syracuseStep 1439371 = 2159057) B2159057
theorem B2021015 : Blo 1346992 2021015 := bstep (se 1 (by rfl) ⟨1515761, by rfl⟩ : syracuseStep 2021015 = 3031523) B3031523
theorem B6149783 : Blo 1346992 6149783 := bstep (se 1 (by rfl) ⟨4612337, by rfl⟩ : syracuseStep 6149783 = 9224675) B9224675
theorem B2021081 : Blo 1346992 2021081 := bstep (se 2 (by rfl) ⟨757905, by rfl⟩ : syracuseStep 2021081 = 1515811) B1515811
theorem B2275033 : Blo 1346992 2275033 := bstep (se 2 (by rfl) ⟨853137, by rfl⟩ : syracuseStep 2275033 = 1706275) B1706275
theorem B10368773 : Blo 1346992 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B897160981 : Blo 1346992 897160981 := bstep (se 6 (by rfl) ⟨21027210, by rfl⟩ : syracuseStep 897160981 = 42054421) B42054421
theorem B7681837 : Blo 1346992 7681837 := bstep (se 3 (by rfl) ⟨1440344, by rfl⟩ : syracuseStep 7681837 = 2880689) B2880689
theorem B2430785 : Blo 1346992 2430785 := bstep (se 2 (by rfl) ⟨911544, by rfl⟩ : syracuseStep 2430785 = 1823089) B1823089
theorem B2021195 : Blo 1346992 2021195 := bstep (se 1 (by rfl) ⟨1515896, by rfl⟩ : syracuseStep 2021195 = 3031793) B3031793
theorem B4552523 : Blo 1346992 4552523 := bstep (se 1 (by rfl) ⟨3414392, by rfl⟩ : syracuseStep 4552523 = 6828785) B6828785
theorem B2021207 : Blo 1346992 2021207 := bstep (se 1 (by rfl) ⟨1515905, by rfl⟩ : syracuseStep 2021207 = 3031811) B3031811
theorem B1439627 : Blo 1346992 1439627 := bstep (se 1 (by rfl) ⟨1079720, by rfl⟩ : syracuseStep 1439627 = 2159441) B2159441
theorem B2021273 : Blo 1346992 2021273 := bstep (se 2 (by rfl) ⟨757977, by rfl⟩ : syracuseStep 2021273 = 1515955) B1515955
theorem B2021387 : Blo 1346992 2021387 := bstep (se 1 (by rfl) ⟨1516040, by rfl⟩ : syracuseStep 2021387 = 3032081) B3032081
theorem B2021399 : Blo 1346992 2021399 := bstep (se 1 (by rfl) ⟨1516049, by rfl⟩ : syracuseStep 2021399 = 3032099) B3032099
theorem B5117975 : Blo 1346992 5117975 := bstep (se 1 (by rfl) ⟨3838481, by rfl⟩ : syracuseStep 5117975 = 7676963) B7676963
theorem B11671627 : Blo 1346992 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B2021465 : Blo 1346992 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B4552793 : Blo 1346992 4552793 := bstep (se 2 (by rfl) ⟨1707297, by rfl⟩ : syracuseStep 4552793 = 3414595) B3414595
theorem B6821981 : Blo 1346992 6821981 := bstep (se 3 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 6821981 = 2558243) B2558243
theorem B9222245 : Blo 1346992 9222245 := bstep (se 4 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 9222245 = 1729171) B1729171
theorem B1620119 : Blo 1346992 1620119 := bstep (se 1 (by rfl) ⟨1215089, by rfl⟩ : syracuseStep 1620119 = 2430179) B2430179
theorem B2021579 : Blo 1346992 2021579 := bstep (se 1 (by rfl) ⟨1516184, by rfl⟩ : syracuseStep 2021579 = 3032369) B3032369
theorem B2021591 : Blo 1346992 2021591 := bstep (se 1 (by rfl) ⟨1516193, by rfl⟩ : syracuseStep 2021591 = 3032387) B3032387
theorem B5118173 : Blo 1346992 5118173 := bstep (se 3 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 5118173 = 1919315) B1919315
theorem B2275607 : Blo 1346992 2275607 := bstep (se 1 (by rfl) ⟨1706705, by rfl⟩ : syracuseStep 2275607 = 3413411) B3413411
theorem B2021657 : Blo 1346992 2021657 := bstep (se 2 (by rfl) ⟨758121, by rfl⟩ : syracuseStep 2021657 = 1516243) B1516243
theorem B11516195 : Blo 1346992 11516195 := bstep (se 1 (by rfl) ⟨8637146, by rfl⟩ : syracuseStep 11516195 = 17274293) B17274293
theorem B49174901 : Blo 1346992 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B2021771 : Blo 1346992 2021771 := bstep (se 1 (by rfl) ⟨1516328, by rfl⟩ : syracuseStep 2021771 = 3032657) B3032657
theorem B2021783 : Blo 1346992 2021783 := bstep (se 1 (by rfl) ⟨1516337, by rfl⟩ : syracuseStep 2021783 = 3032675) B3032675
theorem B2275735 : Blo 1346992 2275735 := bstep (se 1 (by rfl) ⟨1706801, by rfl⟩ : syracuseStep 2275735 = 3413603) B3413603
theorem B2734487 : Blo 1346992 2734487 := bstep (se 1 (by rfl) ⟨2050865, by rfl⟩ : syracuseStep 2734487 = 4101731) B4101731
theorem B1620427 : Blo 1346992 1620427 := bstep (se 1 (by rfl) ⟨1215320, by rfl⟩ : syracuseStep 1620427 = 2430641) B2430641
theorem B2021849 : Blo 1346992 2021849 := bstep (se 2 (by rfl) ⟨758193, by rfl⟩ : syracuseStep 2021849 = 1516387) B1516387
theorem B2021963 : Blo 1346992 2021963 := bstep (se 1 (by rfl) ⟨1516472, by rfl⟩ : syracuseStep 2021963 = 3032945) B3032945
theorem B2021975 : Blo 1346992 2021975 := bstep (se 1 (by rfl) ⟨1516481, by rfl⟩ : syracuseStep 2021975 = 3032963) B3032963
theorem B14572163 : Blo 1346992 14572163 := bstep (se 1 (by rfl) ⟨10929122, by rfl⟩ : syracuseStep 14572163 = 21858245) B21858245
theorem B2022041 : Blo 1346992 2022041 := bstep (se 2 (by rfl) ⟨758265, by rfl⟩ : syracuseStep 2022041 = 1516531) B1516531
theorem B7674547 : Blo 1346992 7674547 := bstep (se 1 (by rfl) ⟨5755910, by rfl⟩ : syracuseStep 7674547 = 11511821) B11511821
theorem B3840691 : Blo 1346992 3840691 := bstep (se 1 (by rfl) ⟨2880518, by rfl⟩ : syracuseStep 3840691 = 5761037) B5761037
theorem B2022155 : Blo 1346992 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B2022167 : Blo 1346992 2022167 := bstep (se 1 (by rfl) ⟨1516625, by rfl⟩ : syracuseStep 2022167 = 3033251) B3033251
theorem B2022233 : Blo 1346992 2022233 := bstep (se 2 (by rfl) ⟨758337, by rfl⟩ : syracuseStep 2022233 = 1516675) B1516675
theorem B2595673 : Blo 1346992 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B12958643 : Blo 1346992 12958643 := bstep (se 1 (by rfl) ⟨9718982, by rfl⟩ : syracuseStep 12958643 = 19437965) B19437965
theorem B2022347 : Blo 1346992 2022347 := bstep (se 1 (by rfl) ⟨1516760, by rfl⟩ : syracuseStep 2022347 = 3033521) B3033521
theorem B2022359 : Blo 1346992 2022359 := bstep (se 1 (by rfl) ⟨1516769, by rfl⟩ : syracuseStep 2022359 = 3033539) B3033539
theorem B2276363 : Blo 1346992 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B2022425 : Blo 1346992 2022425 := bstep (se 2 (by rfl) ⟨758409, by rfl⟩ : syracuseStep 2022425 = 1516819) B1516819
theorem B4856897 : Blo 1346992 4856897 := bstep (se 2 (by rfl) ⟨1821336, by rfl⟩ : syracuseStep 4856897 = 3642673) B3642673
theorem B12958795 : Blo 1346992 12958795 := bstep (se 1 (by rfl) ⟨9719096, by rfl⟩ : syracuseStep 12958795 = 19438193) B19438193
theorem B6151243 : Blo 1346992 6151243 := bstep (se 1 (by rfl) ⟨4613432, by rfl⟩ : syracuseStep 6151243 = 9226865) B9226865
theorem B8313949 : Blo 1346992 8313949 := bstep (se 3 (by rfl) ⟨1558865, by rfl⟩ : syracuseStep 8313949 = 3117731) B3117731
theorem B2022539 : Blo 1346992 2022539 := bstep (se 1 (by rfl) ⟨1516904, by rfl⟩ : syracuseStep 2022539 = 3033809) B3033809
theorem B2022551 : Blo 1346992 2022551 := bstep (se 1 (by rfl) ⟨1516913, by rfl⟩ : syracuseStep 2022551 = 3033827) B3033827
theorem B3456179 : Blo 1346992 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B4611275 : Blo 1346992 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B2022617 : Blo 1346992 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B2022731 : Blo 1346992 2022731 := bstep (se 1 (by rfl) ⟨1517048, by rfl⟩ : syracuseStep 2022731 = 3034097) B3034097
theorem B2022743 : Blo 1346992 2022743 := bstep (se 1 (by rfl) ⟨1517057, by rfl⟩ : syracuseStep 2022743 = 3034115) B3034115
theorem B2022809 : Blo 1346992 2022809 := bstep (se 2 (by rfl) ⟨758553, by rfl⟩ : syracuseStep 2022809 = 1517107) B1517107
theorem B2022923 : Blo 1346992 2022923 := bstep (se 1 (by rfl) ⟨1517192, by rfl⟩ : syracuseStep 2022923 = 3034385) B3034385
theorem B2022935 : Blo 1346992 2022935 := bstep (se 1 (by rfl) ⟨1517201, by rfl⟩ : syracuseStep 2022935 = 3034403) B3034403
theorem B10239533 : Blo 1346992 10239533 := bstep (se 3 (by rfl) ⟨1919912, by rfl⟩ : syracuseStep 10239533 = 3839825) B3839825
theorem B2023001 : Blo 1346992 2023001 := bstep (se 2 (by rfl) ⟨758625, by rfl⟩ : syracuseStep 2023001 = 1517251) B1517251
theorem B2023115 : Blo 1346992 2023115 := bstep (se 1 (by rfl) ⟨1517336, by rfl⟩ : syracuseStep 2023115 = 3034673) B3034673
theorem B2023127 : Blo 1346992 2023127 := bstep (se 1 (by rfl) ⟨1517345, by rfl⟩ : syracuseStep 2023127 = 3034691) B3034691
theorem B3030785 : Blo 1346992 3030785 := bstep (se 2 (by rfl) ⟨1136544, by rfl⟩ : syracuseStep 3030785 = 2273089) B2273089
theorem B2023193 : Blo 1346992 2023193 := bstep (se 2 (by rfl) ⟨758697, by rfl⟩ : syracuseStep 2023193 = 1517395) B1517395
theorem B6479747 : Blo 1346992 6479747 := bstep (se 1 (by rfl) ⟨4859810, by rfl⟩ : syracuseStep 6479747 = 9719621) B9719621
theorem B2023307 : Blo 1346992 2023307 := bstep (se 1 (by rfl) ⟨1517480, by rfl⟩ : syracuseStep 2023307 = 3034961) B3034961
theorem B1515415 : Blo 1346992 1515415 := bstep (se 1 (by rfl) ⟨1136561, by rfl⟩ : syracuseStep 1515415 = 2273123) B2273123
theorem B2023319 : Blo 1346992 2023319 := bstep (se 1 (by rfl) ⟨1517489, by rfl⟩ : syracuseStep 2023319 = 3034979) B3034979
theorem B6922163 : Blo 1346992 6922163 := bstep (se 1 (by rfl) ⟨5191622, by rfl⟩ : syracuseStep 6922163 = 10383245) B10383245
theorem B10231757 : Blo 1346992 10231757 := bstep (se 3 (by rfl) ⟨1918454, by rfl⟩ : syracuseStep 10231757 = 3836909) B3836909
theorem B3031001 : Blo 1346992 3031001 := bstep (se 2 (by rfl) ⟨1136625, by rfl⟩ : syracuseStep 3031001 = 2273251) B2273251
theorem B14581721 : Blo 1346992 14581721 := bstep (se 2 (by rfl) ⟨5468145, by rfl⟩ : syracuseStep 14581721 = 10936291) B10936291
theorem B2023385 : Blo 1346992 2023385 := bstep (se 2 (by rfl) ⟨758769, by rfl⟩ : syracuseStep 2023385 = 1517539) B1517539
theorem B5537803 : Blo 1346992 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B3031055 : Blo 1346992 3031055 := bstep (se 1 (by rfl) ⟨2273291, by rfl⟩ : syracuseStep 3031055 = 4546583) B4546583
theorem B2023439 : Blo 1346992 2023439 := bstep (se 1 (by rfl) ⟨1517579, by rfl⟩ : syracuseStep 2023439 = 3035159) B3035159
theorem B3031073 : Blo 1346992 3031073 := bstep (se 2 (by rfl) ⟨1136652, by rfl⟩ : syracuseStep 3031073 = 2273305) B2273305
theorem B2023481 : Blo 1346992 2023481 := bstep (se 2 (by rfl) ⟨758805, by rfl⟩ : syracuseStep 2023481 = 1517611) B1517611
theorem B8192315 : Blo 1346992 8192315 := bstep (se 1 (by rfl) ⟨6144236, by rfl⟩ : syracuseStep 8192315 = 12288473) B12288473
theorem B3031415 : Blo 1346992 3031415 := bstep (se 1 (by rfl) ⟨2273561, by rfl⟩ : syracuseStep 3031415 = 4547123) B4547123
theorem B7291271 : Blo 1346992 7291271 := bstep (se 1 (by rfl) ⟨5468453, by rfl⟩ : syracuseStep 7291271 = 10936907) B10936907
theorem B1515919 : Blo 1346992 1515919 := bstep (se 1 (by rfl) ⟨1136939, by rfl⟩ : syracuseStep 1515919 = 2273879) B2273879
theorem B3031595 : Blo 1346992 3031595 := bstep (se 1 (by rfl) ⟨2273696, by rfl⟩ : syracuseStep 3031595 = 4547393) B4547393
theorem B2957867 : Blo 1346992 2957867 := bstep (se 1 (by rfl) ⟨2218400, by rfl⟩ : syracuseStep 2957867 = 4436801) B4436801
theorem B3891847 : Blo 1346992 3891847 := bstep (se 1 (by rfl) ⟨2918885, by rfl⟩ : syracuseStep 3891847 = 5837771) B5837771
theorem B6144749 : Blo 1346992 6144749 := bstep (se 3 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 6144749 = 2304281) B2304281
theorem B58336037 : Blo 1346992 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B1516423 : Blo 1346992 1516423 := bstep (se 1 (by rfl) ⟨1137317, by rfl⟩ : syracuseStep 1516423 = 2274635) B2274635
theorem B3031955 : Blo 1346992 3031955 := bstep (se 1 (by rfl) ⟨2273966, by rfl⟩ : syracuseStep 3031955 = 4547933) B4547933
theorem B10232729 : Blo 1346992 10232729 := bstep (se 2 (by rfl) ⟨3837273, by rfl⟩ : syracuseStep 10232729 = 7674547) B7674547
theorem B5120921 : Blo 1346992 5120921 := bstep (se 2 (by rfl) ⟨1920345, by rfl⟩ : syracuseStep 5120921 = 3840691) B3840691
theorem B15352739 : Blo 1346992 15352739 := bstep (se 1 (by rfl) ⟨11514554, by rfl⟩ : syracuseStep 15352739 = 23029109) B23029109
theorem B3032009 : Blo 1346992 3032009 := bstep (se 2 (by rfl) ⟨1137003, by rfl⟩ : syracuseStep 3032009 = 2274007) B2274007
theorem B5760011 : Blo 1346992 5760011 := bstep (se 1 (by rfl) ⟨4320008, by rfl⟩ : syracuseStep 5760011 = 8640017) B8640017
theorem B4097083 : Blo 1346992 4097083 := bstep (se 1 (by rfl) ⟨3072812, by rfl⟩ : syracuseStep 4097083 = 6145625) B6145625
theorem B1516603 : Blo 1346992 1516603 := bstep (se 1 (by rfl) ⟨1137452, by rfl⟩ : syracuseStep 1516603 = 2274905) B2274905
theorem B1705207 : Blo 1346992 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B3507575 : Blo 1346992 3507575 := bstep (se 1 (by rfl) ⟨2630681, by rfl⟩ : syracuseStep 3507575 = 5261363) B5261363
theorem B4547987 : Blo 1346992 4547987 := bstep (se 1 (by rfl) ⟨3410990, by rfl⟩ : syracuseStep 4547987 = 6821981) B6821981
theorem B17278393 : Blo 1346992 17278393 := bstep (se 2 (by rfl) ⟨6479397, by rfl⟩ : syracuseStep 17278393 = 12958795) B12958795
theorem B8201657 : Blo 1346992 8201657 := bstep (se 2 (by rfl) ⟨3075621, by rfl⟩ : syracuseStep 8201657 = 6151243) B6151243
theorem B1918409 : Blo 1346992 1918409 := bstep (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) B1438807
theorem B11085265 : Blo 1346992 11085265 := bstep (se 2 (by rfl) ⟨4156974, by rfl⟩ : syracuseStep 11085265 = 8313949) B8313949
theorem B9717251 : Blo 1346992 9717251 := bstep (se 1 (by rfl) ⟨7287938, by rfl⟩ : syracuseStep 9717251 = 14575877) B14575877
theorem B1517071 : Blo 1346992 1517071 := bstep (se 1 (by rfl) ⟨1137803, by rfl⟩ : syracuseStep 1517071 = 2275607) B2275607
theorem B7677463 : Blo 1346992 7677463 := bstep (se 1 (by rfl) ⟨5758097, by rfl⟩ : syracuseStep 7677463 = 11516195) B11516195
theorem B1918523 : Blo 1346992 1918523 := bstep (se 1 (by rfl) ⟨1438892, by rfl⟩ : syracuseStep 1918523 = 2877785) B2877785
theorem B1705531 : Blo 1346992 1705531 := bstep (se 1 (by rfl) ⟨1279148, by rfl⟩ : syracuseStep 1705531 = 2558297) B2558297
theorem B3032711 : Blo 1346992 3032711 := bstep (se 1 (by rfl) ⟨2274533, by rfl⟩ : syracuseStep 3032711 = 4549067) B4549067
theorem B3032891 : Blo 1346992 3032891 := bstep (se 1 (by rfl) ⟨2274668, by rfl⟩ : syracuseStep 3032891 = 4549337) B4549337
theorem B17270603 : Blo 1346992 17270603 := bstep (se 1 (by rfl) ⟨12952952, by rfl⟩ : syracuseStep 17270603 = 25905905) B25905905
theorem B3033017 : Blo 1346992 3033017 := bstep (se 2 (by rfl) ⟨1137381, by rfl⟩ : syracuseStep 3033017 = 2274763) B2274763
theorem B2049977 : Blo 1346992 2049977 := bstep (se 2 (by rfl) ⟨768741, by rfl⟩ : syracuseStep 2049977 = 1537483) B1537483
theorem B5760953 : Blo 1346992 5760953 := bstep (se 2 (by rfl) ⟨2160357, by rfl⟩ : syracuseStep 5760953 = 4320715) B4320715
theorem B1517575 : Blo 1346992 1517575 := bstep (se 1 (by rfl) ⟨1138181, by rfl⟩ : syracuseStep 1517575 = 2276363) B2276363
theorem B3237931 : Blo 1346992 3237931 := bstep (se 1 (by rfl) ⟨2428448, by rfl⟩ : syracuseStep 3237931 = 4856897) B4856897
theorem B2304119 : Blo 1346992 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B3410039 : Blo 1346992 3410039 := bstep (se 1 (by rfl) ⟨2557529, by rfl⟩ : syracuseStep 3410039 = 5115059) B5115059
theorem B3074183 : Blo 1346992 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B3836089 : Blo 1346992 3836089 := bstep (se 2 (by rfl) ⟨1438533, by rfl⟩ : syracuseStep 3836089 = 2877067) B2877067
theorem B2558137 : Blo 1346992 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B1919161 : Blo 1346992 1919161 := bstep (se 2 (by rfl) ⟨719685, by rfl⟩ : syracuseStep 1919161 = 1439371) B1439371
theorem B6473999 : Blo 1346992 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B3033359 : Blo 1346992 3033359 := bstep (se 1 (by rfl) ⟨2275019, by rfl⟩ : syracuseStep 3033359 = 4550039) B4550039
theorem B3033377 : Blo 1346992 3033377 := bstep (se 2 (by rfl) ⟨1137516, by rfl⟩ : syracuseStep 3033377 = 2275033) B2275033
theorem B1196214641 : Blo 1346992 1196214641 := bstep (se 2 (by rfl) ⟨448580490, by rfl⟩ : syracuseStep 1196214641 = 897160981) B897160981
theorem B6826355 : Blo 1346992 6826355 := bstep (se 1 (by rfl) ⟨5119766, by rfl⟩ : syracuseStep 6826355 = 10239533) B10239533
theorem B10242449 : Blo 1346992 10242449 := bstep (se 2 (by rfl) ⟨3840918, by rfl⟩ : syracuseStep 10242449 = 7681837) B7681837
theorem B1706503 : Blo 1346992 1706503 := bstep (se 1 (by rfl) ⟨1279877, by rfl⟩ : syracuseStep 1706503 = 2559755) B2559755
theorem B2558479 : Blo 1346992 2558479 := bstep (se 1 (by rfl) ⟨1918859, by rfl⟩ : syracuseStep 2558479 = 3837719) B3837719
theorem B4098593 : Blo 1346992 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B3836477 : Blo 1346992 3836477 := bstep (se 3 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 3836477 = 1438679) B1438679
theorem B4319831 : Blo 1346992 4319831 := bstep (se 1 (by rfl) ⟨3239873, by rfl⟩ : syracuseStep 4319831 = 6479747) B6479747
theorem B53217911 : Blo 1346992 53217911 := bstep (se 1 (by rfl) ⟨39913433, by rfl⟩ : syracuseStep 53217911 = 79826867) B79826867
theorem B3033719 : Blo 1346992 3033719 := bstep (se 1 (by rfl) ⟨2275289, by rfl⟩ : syracuseStep 3033719 = 4550579) B4550579
theorem B4614775 : Blo 1346992 4614775 := bstep (se 1 (by rfl) ⟨3461081, by rfl⟩ : syracuseStep 4614775 = 6922163) B6922163
theorem B5188297 : Blo 1346992 5188297 := bstep (se 2 (by rfl) ⟨1945611, by rfl⟩ : syracuseStep 5188297 = 3891223) B3891223
theorem B4549391 : Blo 1346992 4549391 := bstep (se 1 (by rfl) ⟨3412043, by rfl⟩ : syracuseStep 4549391 = 6824087) B6824087
theorem B19434275 : Blo 1346992 19434275 := bstep (se 1 (by rfl) ⟨14575706, by rfl⟩ : syracuseStep 19434275 = 29151413) B29151413
theorem B3033899 : Blo 1346992 3033899 := bstep (se 1 (by rfl) ⟨2275424, by rfl⟩ : syracuseStep 3033899 = 4550849) B4550849
theorem B10234673 : Blo 1346992 10234673 := bstep (se 2 (by rfl) ⟨3838002, by rfl⟩ : syracuseStep 10234673 = 7676005) B7676005
theorem B6826841 : Blo 1346992 6826841 := bstep (se 2 (by rfl) ⟨2560065, by rfl⟩ : syracuseStep 6826841 = 5120131) B5120131
theorem B1821575 : Blo 1346992 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B5114771 : Blo 1346992 5114771 := bstep (se 1 (by rfl) ⟨3836078, by rfl⟩ : syracuseStep 5114771 = 7672157) B7672157
theorem B1706923 : Blo 1346992 1706923 := bstep (se 1 (by rfl) ⟨1280192, by rfl⟩ : syracuseStep 1706923 = 2560385) B2560385
theorem B4549661 : Blo 1346992 4549661 := bstep (se 3 (by rfl) ⟨853061, by rfl⟩ : syracuseStep 4549661 = 1706123) B1706123
theorem B12946493 : Blo 1346992 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B4320317 : Blo 1346992 4320317 := bstep (se 3 (by rfl) ⟨810059, by rfl⟩ : syracuseStep 4320317 = 1620119) B1620119
theorem B3411031 : Blo 1346992 3411031 := bstep (se 1 (by rfl) ⟨2558273, by rfl⟩ : syracuseStep 3411031 = 5116547) B5116547
theorem B1707151 : Blo 1346992 1707151 := bstep (se 1 (by rfl) ⟨1280363, by rfl⟩ : syracuseStep 1707151 = 2560727) B2560727
theorem B3034259 : Blo 1346992 3034259 := bstep (se 1 (by rfl) ⟨2275694, by rfl⟩ : syracuseStep 3034259 = 4551389) B4551389
theorem B3034313 : Blo 1346992 3034313 := bstep (se 2 (by rfl) ⟨1137867, by rfl⟩ : syracuseStep 3034313 = 2275735) B2275735
theorem B5115271 : Blo 1346992 5115271 := bstep (se 1 (by rfl) ⟨3836453, by rfl⟩ : syracuseStep 5115271 = 7672907) B7672907
theorem B3411335 : Blo 1346992 3411335 := bstep (se 1 (by rfl) ⟨2558501, by rfl⟩ : syracuseStep 3411335 = 5117003) B5117003
theorem B2559367 : Blo 1346992 2559367 := bstep (se 1 (by rfl) ⟨1919525, by rfl⟩ : syracuseStep 2559367 = 3839051) B3839051
theorem B1347003 : Blo 1346992 1347003 := bstep (se 1 (by rfl) ⟨1010252, by rfl⟩ : syracuseStep 1347003 = 2020505) B2020505
theorem B14585309 : Blo 1346992 14585309 := bstep (se 3 (by rfl) ⟨2734745, by rfl⟩ : syracuseStep 14585309 = 5469491) B5469491
theorem B1347079 : Blo 1346992 1347079 := bstep (se 1 (by rfl) ⟨1010309, by rfl⟩ : syracuseStep 1347079 = 2020619) B2020619
theorem B3411467 : Blo 1346992 3411467 := bstep (se 1 (by rfl) ⟨2558600, by rfl⟩ : syracuseStep 3411467 = 5117201) B5117201
theorem B1347087 : Blo 1346992 1347087 := bstep (se 1 (by rfl) ⟨1010315, by rfl⟩ : syracuseStep 1347087 = 2020631) B2020631
theorem B1347131 : Blo 1346992 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B1822267 : Blo 1346992 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B6819389 : Blo 1346992 6819389 := bstep (se 3 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 6819389 = 2557271) B2557271
theorem B1347207 : Blo 1346992 1347207 := bstep (se 1 (by rfl) ⟨1010405, by rfl⟩ : syracuseStep 1347207 = 2020811) B2020811
theorem B1347215 : Blo 1346992 1347215 := bstep (se 1 (by rfl) ⟨1010411, by rfl⟩ : syracuseStep 1347215 = 2020823) B2020823
theorem B3837593 : Blo 1346992 3837593 := bstep (se 2 (by rfl) ⟨1439097, by rfl⟩ : syracuseStep 3837593 = 2878195) B2878195
theorem B1347259 : Blo 1346992 1347259 := bstep (se 1 (by rfl) ⟨1010444, by rfl⟩ : syracuseStep 1347259 = 2020889) B2020889
theorem B1347335 : Blo 1346992 1347335 := bstep (se 1 (by rfl) ⟨1010501, by rfl⟩ : syracuseStep 1347335 = 2021003) B2021003
theorem B1347343 : Blo 1346992 1347343 := bstep (se 1 (by rfl) ⟨1010507, by rfl⟩ : syracuseStep 1347343 = 2021015) B2021015
theorem B3460897 : Blo 1346992 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B7786277 : Blo 1346992 7786277 := bstep (se 4 (by rfl) ⟨729963, by rfl⟩ : syracuseStep 7786277 = 1459927) B1459927
theorem B1347387 : Blo 1346992 1347387 := bstep (se 1 (by rfl) ⟨1010540, by rfl⟩ : syracuseStep 1347387 = 2021081) B2021081
theorem B3239767 : Blo 1346992 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B2273143 : Blo 1346992 2273143 := bstep (se 1 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 2273143 = 3409715) B3409715
theorem B1347463 : Blo 1346992 1347463 := bstep (se 1 (by rfl) ⟨1010597, by rfl⟩ : syracuseStep 1347463 = 2021195) B2021195
theorem B7679879 : Blo 1346992 7679879 := bstep (se 1 (by rfl) ⟨5759909, by rfl⟩ : syracuseStep 7679879 = 11519819) B11519819
theorem B3035015 : Blo 1346992 3035015 := bstep (se 1 (by rfl) ⟨2276261, by rfl⟩ : syracuseStep 3035015 = 4552523) B4552523
theorem B1347471 : Blo 1346992 1347471 := bstep (se 1 (by rfl) ⟨1010603, by rfl⟩ : syracuseStep 1347471 = 2021207) B2021207
theorem B1347515 : Blo 1346992 1347515 := bstep (se 1 (by rfl) ⟨1010636, by rfl⟩ : syracuseStep 1347515 = 2021273) B2021273
theorem B1347591 : Blo 1346992 1347591 := bstep (se 1 (by rfl) ⟨1010693, by rfl⟩ : syracuseStep 1347591 = 2021387) B2021387
theorem B1347599 : Blo 1346992 1347599 := bstep (se 1 (by rfl) ⟨1010699, by rfl⟩ : syracuseStep 1347599 = 2021399) B2021399
theorem B3411983 : Blo 1346992 3411983 := bstep (se 1 (by rfl) ⟨2558987, by rfl⟩ : syracuseStep 3411983 = 5117975) B5117975
theorem B2273339 : Blo 1346992 2273339 := bstep (se 1 (by rfl) ⟨1705004, by rfl⟩ : syracuseStep 2273339 = 3410009) B3410009
theorem B1347643 : Blo 1346992 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B3035195 : Blo 1346992 3035195 := bstep (se 1 (by rfl) ⟨2276396, by rfl⟩ : syracuseStep 3035195 = 4552793) B4552793
theorem B6148163 : Blo 1346992 6148163 := bstep (se 1 (by rfl) ⟨4611122, by rfl⟩ : syracuseStep 6148163 = 9222245) B9222245
theorem B504868949 : Blo 1346992 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B2732167 : Blo 1346992 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B1347719 : Blo 1346992 1347719 := bstep (se 1 (by rfl) ⟨1010789, by rfl⟩ : syracuseStep 1347719 = 2021579) B2021579
theorem B1347727 : Blo 1346992 1347727 := bstep (se 1 (by rfl) ⟨1010795, by rfl⟩ : syracuseStep 1347727 = 2021591) B2021591
theorem B3412115 : Blo 1346992 3412115 := bstep (se 1 (by rfl) ⟨2559086, by rfl⟩ : syracuseStep 3412115 = 5118173) B5118173
theorem B1347771 : Blo 1346992 1347771 := bstep (se 1 (by rfl) ⟨1010828, by rfl⟩ : syracuseStep 1347771 = 2021657) B2021657
theorem B1347847 : Blo 1346992 1347847 := bstep (se 1 (by rfl) ⟨1010885, by rfl⟩ : syracuseStep 1347847 = 2021771) B2021771
theorem B1347855 : Blo 1346992 1347855 := bstep (se 1 (by rfl) ⟨1010891, by rfl⟩ : syracuseStep 1347855 = 2021783) B2021783
theorem B1822991 : Blo 1346992 1822991 := bstep (se 1 (by rfl) ⟨1367243, by rfl⟩ : syracuseStep 1822991 = 2734487) B2734487
theorem B1347899 : Blo 1346992 1347899 := bstep (se 1 (by rfl) ⟨1010924, by rfl⟩ : syracuseStep 1347899 = 2021849) B2021849
theorem B1347975 : Blo 1346992 1347975 := bstep (se 1 (by rfl) ⟨1010981, by rfl⟩ : syracuseStep 1347975 = 2021963) B2021963
theorem B1347983 : Blo 1346992 1347983 := bstep (se 1 (by rfl) ⟨1010987, by rfl⟩ : syracuseStep 1347983 = 2021975) B2021975
theorem B4551065 : Blo 1346992 4551065 := bstep (se 2 (by rfl) ⟨1706649, by rfl⟩ : syracuseStep 4551065 = 3413299) B3413299
theorem B1348027 : Blo 1346992 1348027 := bstep (se 1 (by rfl) ⟨1011020, by rfl⟩ : syracuseStep 1348027 = 2022041) B2022041
theorem B2273737 : Blo 1346992 2273737 := bstep (se 2 (by rfl) ⟨852651, by rfl⟩ : syracuseStep 2273737 = 1705303) B1705303
theorem B1348103 : Blo 1346992 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B1618447 : Blo 1346992 1618447 := bstep (se 1 (by rfl) ⟨1213835, by rfl⟩ : syracuseStep 1618447 = 2427671) B2427671
theorem B1348111 : Blo 1346992 1348111 := bstep (se 1 (by rfl) ⟨1011083, by rfl⟩ : syracuseStep 1348111 = 2022167) B2022167
theorem B1348155 : Blo 1346992 1348155 := bstep (se 1 (by rfl) ⟨1011116, by rfl⟩ : syracuseStep 1348155 = 2022233) B2022233
theorem B17265271 : Blo 1346992 17265271 := bstep (se 1 (by rfl) ⟨12948953, by rfl⟩ : syracuseStep 17265271 = 25897907) B25897907
theorem B8639095 : Blo 1346992 8639095 := bstep (se 1 (by rfl) ⟨6479321, by rfl⟩ : syracuseStep 8639095 = 12958643) B12958643
theorem B1348231 : Blo 1346992 1348231 := bstep (se 1 (by rfl) ⟨1011173, by rfl⟩ : syracuseStep 1348231 = 2022347) B2022347
theorem B1348239 : Blo 1346992 1348239 := bstep (se 1 (by rfl) ⟨1011179, by rfl⟩ : syracuseStep 1348239 = 2022359) B2022359
theorem B1348283 : Blo 1346992 1348283 := bstep (se 1 (by rfl) ⟨1011212, by rfl⟩ : syracuseStep 1348283 = 2022425) B2022425
theorem B9712385 : Blo 1346992 9712385 := bstep (se 2 (by rfl) ⟨3642144, by rfl⟩ : syracuseStep 9712385 = 7284289) B7284289
theorem B1348359 : Blo 1346992 1348359 := bstep (se 1 (by rfl) ⟨1011269, by rfl⟩ : syracuseStep 1348359 = 2022539) B2022539
theorem B1348367 : Blo 1346992 1348367 := bstep (se 1 (by rfl) ⟨1011275, by rfl⟩ : syracuseStep 1348367 = 2022551) B2022551
theorem B3240719 : Blo 1346992 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B38843171 : Blo 1346992 38843171 := bstep (se 1 (by rfl) ⟨29132378, by rfl⟩ : syracuseStep 38843171 = 58264757) B58264757
theorem B1348411 : Blo 1346992 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B1348487 : Blo 1346992 1348487 := bstep (se 1 (by rfl) ⟨1011365, by rfl⟩ : syracuseStep 1348487 = 2022731) B2022731
theorem B1348495 : Blo 1346992 1348495 := bstep (se 1 (by rfl) ⟨1011371, by rfl⟩ : syracuseStep 1348495 = 2022743) B2022743
theorem B6828947 : Blo 1346992 6828947 := bstep (se 1 (by rfl) ⟨5121710, by rfl⟩ : syracuseStep 6828947 = 10243421) B10243421
theorem B6656921 : Blo 1346992 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B1348539 : Blo 1346992 1348539 := bstep (se 1 (by rfl) ⟨1011404, by rfl⟩ : syracuseStep 1348539 = 2022809) B2022809
theorem B4101121 : Blo 1346992 4101121 := bstep (se 2 (by rfl) ⟨1537920, by rfl⟩ : syracuseStep 4101121 = 3075841) B3075841
theorem B1348615 : Blo 1346992 1348615 := bstep (se 1 (by rfl) ⟨1011461, by rfl⟩ : syracuseStep 1348615 = 2022923) B2022923
theorem B1348623 : Blo 1346992 1348623 := bstep (se 1 (by rfl) ⟨1011467, by rfl⟩ : syracuseStep 1348623 = 2022935) B2022935
theorem B3839005 : Blo 1346992 3839005 := bstep (se 3 (by rfl) ⟨719813, by rfl⟩ : syracuseStep 3839005 = 1439627) B1439627
theorem B2159659 : Blo 1346992 2159659 := bstep (se 1 (by rfl) ⟨1619744, by rfl⟩ : syracuseStep 2159659 = 3239489) B3239489
theorem B1348667 : Blo 1346992 1348667 := bstep (se 1 (by rfl) ⟨1011500, by rfl⟩ : syracuseStep 1348667 = 2023001) B2023001
theorem B6476861 : Blo 1346992 6476861 := bstep (se 3 (by rfl) ⟨1214411, by rfl⟩ : syracuseStep 6476861 = 2428823) B2428823
theorem B4551767 : Blo 1346992 4551767 := bstep (se 1 (by rfl) ⟨3413825, by rfl⟩ : syracuseStep 4551767 = 6827651) B6827651
theorem B2274439 : Blo 1346992 2274439 := bstep (se 1 (by rfl) ⟨1705829, by rfl⟩ : syracuseStep 2274439 = 3411659) B3411659
theorem B1348743 : Blo 1346992 1348743 := bstep (se 1 (by rfl) ⟨1011557, by rfl⟩ : syracuseStep 1348743 = 2023115) B2023115
theorem B1348751 : Blo 1346992 1348751 := bstep (se 1 (by rfl) ⟨1011563, by rfl⟩ : syracuseStep 1348751 = 2023127) B2023127
theorem B2020523 : Blo 1346992 2020523 := bstep (se 1 (by rfl) ⟨1515392, by rfl⟩ : syracuseStep 2020523 = 3030785) B3030785
theorem B1348795 : Blo 1346992 1348795 := bstep (se 1 (by rfl) ⟨1011596, by rfl⟩ : syracuseStep 1348795 = 2023193) B2023193
theorem B2020553 : Blo 1346992 2020553 := bstep (se 2 (by rfl) ⟨757707, by rfl⟩ : syracuseStep 2020553 = 1515415) B1515415
theorem B3839177 : Blo 1346992 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B7673089 : Blo 1346992 7673089 := bstep (se 2 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 7673089 = 5754817) B5754817
theorem B3839233 : Blo 1346992 3839233 := bstep (se 2 (by rfl) ⟨1439712, by rfl⟩ : syracuseStep 3839233 = 2879425) B2879425
theorem B3413249 : Blo 1346992 3413249 := bstep (se 2 (by rfl) ⟨1279968, by rfl⟩ : syracuseStep 3413249 = 2559937) B2559937
theorem B1348871 : Blo 1346992 1348871 := bstep (se 1 (by rfl) ⟨1011653, by rfl⟩ : syracuseStep 1348871 = 2023307) B2023307
theorem B1348879 : Blo 1346992 1348879 := bstep (se 1 (by rfl) ⟨1011659, by rfl⟩ : syracuseStep 1348879 = 2023319) B2023319
theorem B3282209 : Blo 1346992 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B6821171 : Blo 1346992 6821171 := bstep (se 1 (by rfl) ⟨5115878, by rfl⟩ : syracuseStep 6821171 = 10231757) B10231757
theorem B2020667 : Blo 1346992 2020667 := bstep (se 1 (by rfl) ⟨1515500, by rfl⟩ : syracuseStep 2020667 = 3031001) B3031001
theorem B9721147 : Blo 1346992 9721147 := bstep (se 1 (by rfl) ⟨7290860, by rfl⟩ : syracuseStep 9721147 = 14581721) B14581721
theorem B1348923 : Blo 1346992 1348923 := bstep (se 1 (by rfl) ⟨1011692, by rfl⟩ : syracuseStep 1348923 = 2023385) B2023385
theorem B2020727 : Blo 1346992 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B2020751 : Blo 1346992 2020751 := bstep (se 1 (by rfl) ⟨1515563, by rfl⟩ : syracuseStep 2020751 = 3031127) B3031127
theorem B2020793 : Blo 1346992 2020793 := bstep (se 2 (by rfl) ⟨757797, by rfl⟩ : syracuseStep 2020793 = 1515595) B1515595
theorem B15562169 : Blo 1346992 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B2020871 : Blo 1346992 2020871 := bstep (se 1 (by rfl) ⟨1515653, by rfl⟩ : syracuseStep 2020871 = 3031307) B3031307
theorem B2020907 : Blo 1346992 2020907 := bstep (se 1 (by rfl) ⟨1515680, by rfl⟩ : syracuseStep 2020907 = 3031361) B3031361
theorem B4552253 : Blo 1346992 4552253 := bstep (se 3 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 4552253 = 1707095) B1707095
theorem B2020937 : Blo 1346992 2020937 := bstep (se 2 (by rfl) ⟨757851, by rfl⟩ : syracuseStep 2020937 = 1515703) B1515703
theorem B3839575 : Blo 1346992 3839575 := bstep (se 1 (by rfl) ⟨2879681, by rfl⟩ : syracuseStep 3839575 = 5759363) B5759363
theorem B6821495 : Blo 1346992 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B5330551 : Blo 1346992 5330551 := bstep (se 1 (by rfl) ⟨3997913, by rfl⟩ : syracuseStep 5330551 = 7995827) B7995827
theorem B3413623 : Blo 1346992 3413623 := bstep (se 1 (by rfl) ⟨2560217, by rfl⟩ : syracuseStep 3413623 = 5120435) B5120435
theorem B7681655 : Blo 1346992 7681655 := bstep (se 1 (by rfl) ⟨5761241, by rfl⟩ : syracuseStep 7681655 = 11522483) B11522483
theorem B2021051 : Blo 1346992 2021051 := bstep (se 1 (by rfl) ⟨1515788, by rfl⟩ : syracuseStep 2021051 = 3031577) B3031577
theorem B15365861 : Blo 1346992 15365861 := bstep (se 4 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 15365861 = 2881099) B2881099
theorem B2021111 : Blo 1346992 2021111 := bstep (se 1 (by rfl) ⟨1515833, by rfl⟩ : syracuseStep 2021111 = 3031667) B3031667
theorem B7673615 : Blo 1346992 7673615 := bstep (se 1 (by rfl) ⟨5755211, by rfl⟩ : syracuseStep 7673615 = 11510423) B11510423
theorem B2021135 : Blo 1346992 2021135 := bstep (se 1 (by rfl) ⟨1515851, by rfl⟩ : syracuseStep 2021135 = 3031703) B3031703
theorem B2275087 : Blo 1346992 2275087 := bstep (se 1 (by rfl) ⟨1706315, by rfl⟩ : syracuseStep 2275087 = 3412631) B3412631
theorem B2021177 : Blo 1346992 2021177 := bstep (se 2 (by rfl) ⟨757941, by rfl⟩ : syracuseStep 2021177 = 1515883) B1515883
theorem B2021255 : Blo 1346992 2021255 := bstep (se 1 (by rfl) ⟨1515941, by rfl⟩ : syracuseStep 2021255 = 3031883) B3031883
theorem B1439623 : Blo 1346992 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B2021291 : Blo 1346992 2021291 := bstep (se 1 (by rfl) ⟨1515968, by rfl⟩ : syracuseStep 2021291 = 3031937) B3031937
theorem B2160569 : Blo 1346992 2160569 := bstep (se 2 (by rfl) ⟨810213, by rfl⟩ : syracuseStep 2160569 = 1620427) B1620427
theorem B2021321 : Blo 1346992 2021321 := bstep (se 2 (by rfl) ⟨757995, by rfl⟩ : syracuseStep 2021321 = 1515991) B1515991
theorem B8632331 : Blo 1346992 8632331 := bstep (se 1 (by rfl) ⟨6474248, by rfl⟩ : syracuseStep 8632331 = 12948497) B12948497
theorem B6567965 : Blo 1346992 6567965 := bstep (se 3 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 6567965 = 2462987) B2462987
theorem B3414059 : Blo 1346992 3414059 := bstep (se 1 (by rfl) ⟨2560544, by rfl⟩ : syracuseStep 3414059 = 5121089) B5121089
theorem B2021435 : Blo 1346992 2021435 := bstep (se 1 (by rfl) ⟨1516076, by rfl⟩ : syracuseStep 2021435 = 3032153) B3032153
theorem B2021495 : Blo 1346992 2021495 := bstep (se 1 (by rfl) ⟨1516121, by rfl⟩ : syracuseStep 2021495 = 3032243) B3032243
theorem B2021519 : Blo 1346992 2021519 := bstep (se 1 (by rfl) ⟨1516139, by rfl⟩ : syracuseStep 2021519 = 3032279) B3032279
theorem B2021561 : Blo 1346992 2021561 := bstep (se 2 (by rfl) ⟨758085, by rfl⟩ : syracuseStep 2021561 = 1516171) B1516171
theorem B2021639 : Blo 1346992 2021639 := bstep (se 1 (by rfl) ⟨1516229, by rfl⟩ : syracuseStep 2021639 = 3032459) B3032459
theorem B2021675 : Blo 1346992 2021675 := bstep (se 1 (by rfl) ⟨1516256, by rfl⟩ : syracuseStep 2021675 = 3032513) B3032513
theorem B2275627 : Blo 1346992 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B7682363 : Blo 1346992 7682363 := bstep (se 1 (by rfl) ⟨5761772, by rfl⟩ : syracuseStep 7682363 = 11523545) B11523545
theorem B2021705 : Blo 1346992 2021705 := bstep (se 2 (by rfl) ⟨758139, by rfl⟩ : syracuseStep 2021705 = 1516279) B1516279
theorem B2275769 : Blo 1346992 2275769 := bstep (se 2 (by rfl) ⟨853413, by rfl⟩ : syracuseStep 2275769 = 1706827) B1706827
theorem B2021819 : Blo 1346992 2021819 := bstep (se 1 (by rfl) ⟨1516364, by rfl⟩ : syracuseStep 2021819 = 3032729) B3032729
theorem B2021879 : Blo 1346992 2021879 := bstep (se 1 (by rfl) ⟨1516409, by rfl⟩ : syracuseStep 2021879 = 3032819) B3032819
theorem B6912515 : Blo 1346992 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B2021903 : Blo 1346992 2021903 := bstep (se 1 (by rfl) ⟨1516427, by rfl⟩ : syracuseStep 2021903 = 3032855) B3032855
theorem B1620523 : Blo 1346992 1620523 := bstep (se 1 (by rfl) ⟨1215392, by rfl⟩ : syracuseStep 1620523 = 2430785) B2430785
theorem B2021945 : Blo 1346992 2021945 := bstep (se 2 (by rfl) ⟨758229, by rfl⟩ : syracuseStep 2021945 = 1516459) B1516459
theorem B6822467 : Blo 1346992 6822467 := bstep (se 1 (by rfl) ⟨5116850, by rfl⟩ : syracuseStep 6822467 = 10233701) B10233701
theorem B2022023 : Blo 1346992 2022023 := bstep (se 1 (by rfl) ⟨1516517, by rfl⟩ : syracuseStep 2022023 = 3033035) B3033035
theorem B2022059 : Blo 1346992 2022059 := bstep (se 1 (by rfl) ⟨1516544, by rfl⟩ : syracuseStep 2022059 = 3033089) B3033089
theorem B2022089 : Blo 1346992 2022089 := bstep (se 2 (by rfl) ⟨758283, by rfl⟩ : syracuseStep 2022089 = 1516567) B1516567
theorem B2022203 : Blo 1346992 2022203 := bstep (se 1 (by rfl) ⟨1516652, by rfl⟩ : syracuseStep 2022203 = 3033305) B3033305
theorem B2022263 : Blo 1346992 2022263 := bstep (se 1 (by rfl) ⟨1516697, by rfl⟩ : syracuseStep 2022263 = 3033395) B3033395
theorem B6822791 : Blo 1346992 6822791 := bstep (se 1 (by rfl) ⟨5117093, by rfl⟩ : syracuseStep 6822791 = 10234187) B10234187
theorem B2022287 : Blo 1346992 2022287 := bstep (se 1 (by rfl) ⟨1516715, by rfl⟩ : syracuseStep 2022287 = 3033431) B3033431
theorem B32783267 : Blo 1346992 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B2022329 : Blo 1346992 2022329 := bstep (se 2 (by rfl) ⟨758373, by rfl⟩ : syracuseStep 2022329 = 1516747) B1516747
theorem B2022407 : Blo 1346992 2022407 := bstep (se 1 (by rfl) ⟨1516805, by rfl⟩ : syracuseStep 2022407 = 3033611) B3033611
theorem B2022443 : Blo 1346992 2022443 := bstep (se 1 (by rfl) ⟨1516832, by rfl⟩ : syracuseStep 2022443 = 3033665) B3033665
theorem B16399421 : Blo 1346992 16399421 := bstep (se 3 (by rfl) ⟨3074891, by rfl⟩ : syracuseStep 16399421 = 6149783) B6149783
theorem B2022473 : Blo 1346992 2022473 := bstep (se 2 (by rfl) ⟨758427, by rfl⟩ : syracuseStep 2022473 = 1516855) B1516855
theorem B9714775 : Blo 1346992 9714775 := bstep (se 1 (by rfl) ⟨7286081, by rfl⟩ : syracuseStep 9714775 = 14572163) B14572163
theorem B2022587 : Blo 1346992 2022587 := bstep (se 1 (by rfl) ⟨1516940, by rfl⟩ : syracuseStep 2022587 = 3033881) B3033881
theorem B7675073 : Blo 1346992 7675073 := bstep (se 2 (by rfl) ⟨2878152, by rfl⟩ : syracuseStep 7675073 = 5756305) B5756305
theorem B2022647 : Blo 1346992 2022647 := bstep (se 1 (by rfl) ⟨1516985, by rfl⟩ : syracuseStep 2022647 = 3033971) B3033971
theorem B2022671 : Blo 1346992 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B2022713 : Blo 1346992 2022713 := bstep (se 2 (by rfl) ⟨758517, by rfl⟩ : syracuseStep 2022713 = 1517035) B1517035
theorem B2022791 : Blo 1346992 2022791 := bstep (se 1 (by rfl) ⟨1517093, by rfl⟩ : syracuseStep 2022791 = 3034187) B3034187
theorem B2022827 : Blo 1346992 2022827 := bstep (se 1 (by rfl) ⟨1517120, by rfl⟩ : syracuseStep 2022827 = 3034241) B3034241
theorem B2022857 : Blo 1346992 2022857 := bstep (se 2 (by rfl) ⟨758571, by rfl⟩ : syracuseStep 2022857 = 1517143) B1517143
theorem B2022971 : Blo 1346992 2022971 := bstep (se 1 (by rfl) ⟨1517228, by rfl⟩ : syracuseStep 2022971 = 3034457) B3034457
theorem B2023031 : Blo 1346992 2023031 := bstep (se 1 (by rfl) ⟨1517273, by rfl⟩ : syracuseStep 2023031 = 3034547) B3034547
theorem B2023055 : Blo 1346992 2023055 := bstep (se 1 (by rfl) ⟨1517291, by rfl⟩ : syracuseStep 2023055 = 3034583) B3034583
theorem B2023097 : Blo 1346992 2023097 := bstep (se 2 (by rfl) ⟨758661, by rfl⟩ : syracuseStep 2023097 = 1517323) B1517323
theorem B2023175 : Blo 1346992 2023175 := bstep (se 1 (by rfl) ⟨1517381, by rfl⟩ : syracuseStep 2023175 = 3034763) B3034763
theorem B2023211 : Blo 1346992 2023211 := bstep (se 1 (by rfl) ⟨1517408, by rfl⟩ : syracuseStep 2023211 = 3034817) B3034817
theorem B2023241 : Blo 1346992 2023241 := bstep (se 2 (by rfl) ⟨758715, by rfl⟩ : syracuseStep 2023241 = 1517431) B1517431
theorem B1515451 : Blo 1346992 1515451 := bstep (se 1 (by rfl) ⟨1136588, by rfl⟩ : syracuseStep 1515451 = 2273177) B2273177
theorem B2023355 : Blo 1346992 2023355 := bstep (se 1 (by rfl) ⟨1517516, by rfl⟩ : syracuseStep 2023355 = 3035033) B3035033
theorem B2023415 : Blo 1346992 2023415 := bstep (se 1 (by rfl) ⟨1517561, by rfl⟩ : syracuseStep 2023415 = 3035123) B3035123
theorem B2023433 : Blo 1346992 2023433 := bstep (se 2 (by rfl) ⟨758787, by rfl⟩ : syracuseStep 2023433 = 1517575) B1517575
theorem B15360029 : Blo 1346992 15360029 := bstep (se 3 (by rfl) ⟨2880005, by rfl⟩ : syracuseStep 15360029 = 5760011) B5760011
theorem B1515559 : Blo 1346992 1515559 := bstep (se 1 (by rfl) ⟨1136669, by rfl⟩ : syracuseStep 1515559 = 2273339) B2273339
theorem B2023463 : Blo 1346992 2023463 := bstep (se 1 (by rfl) ⟨1517597, by rfl⟩ : syracuseStep 2023463 = 3035195) B3035195
theorem B4317241 : Blo 1346992 4317241 := bstep (se 2 (by rfl) ⟨1618965, by rfl⟩ : syracuseStep 4317241 = 3237931) B3237931
theorem B4096499 : Blo 1346992 4096499 := bstep (se 1 (by rfl) ⟨3072374, by rfl⟩ : syracuseStep 4096499 = 6144749) B6144749
theorem B25895447 : Blo 1346992 25895447 := bstep (se 1 (by rfl) ⟨19421585, by rfl⟩ : syracuseStep 25895447 = 38843171) B38843171
theorem B3031649 : Blo 1346992 3031649 := bstep (se 2 (by rfl) ⟨1136868, by rfl⟩ : syracuseStep 3031649 = 2273737) B2273737
theorem B23020361 : Blo 1346992 23020361 := bstep (se 2 (by rfl) ⟨8632635, by rfl⟩ : syracuseStep 23020361 = 17265271) B17265271
theorem B11518793 : Blo 1346992 11518793 := bstep (se 2 (by rfl) ⟨4319547, by rfl⟩ : syracuseStep 11518793 = 8639095) B8639095
theorem B2188139 : Blo 1346992 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B4547447 : Blo 1346992 4547447 := bstep (se 1 (by rfl) ⟨3410585, by rfl⟩ : syracuseStep 4547447 = 6821171) B6821171
theorem B3031991 : Blo 1346992 3031991 := bstep (se 1 (by rfl) ⟨2273993, by rfl⟩ : syracuseStep 3031991 = 4547987) B4547987
theorem B4547663 : Blo 1346992 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B5121103 : Blo 1346992 5121103 := bstep (se 1 (by rfl) ⟨3840827, by rfl⟩ : syracuseStep 5121103 = 7681655) B7681655
theorem B37414133 : Blo 1346992 37414133 := bstep (se 5 (by rfl) ⟨1753787, by rfl⟩ : syracuseStep 37414133 = 3507575) B3507575
theorem B25912669 : Blo 1346992 25912669 := bstep (se 3 (by rfl) ⟨4858625, by rfl⟩ : syracuseStep 25912669 = 9717251) B9717251
theorem B2049455 : Blo 1346992 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B4548041 : Blo 1346992 4548041 := bstep (se 2 (by rfl) ⟨1705515, by rfl⟩ : syracuseStep 4548041 = 3411031) B3411031
theorem B12953033 : Blo 1346992 12953033 := bstep (se 2 (by rfl) ⟨4857387, by rfl⟩ : syracuseStep 12953033 = 9714775) B9714775
theorem B3032585 : Blo 1346992 3032585 := bstep (se 2 (by rfl) ⟨1137219, by rfl⟩ : syracuseStep 3032585 = 2274439) B2274439
theorem B5121575 : Blo 1346992 5121575 := bstep (se 1 (by rfl) ⟨3841181, by rfl⟩ : syracuseStep 5121575 = 7682363) B7682363
theorem B797476427 : Blo 1346992 797476427 := bstep (se 1 (by rfl) ⟨598107320, by rfl⟩ : syracuseStep 797476427 = 1196214641) B1196214641
theorem B1517179 : Blo 1346992 1517179 := bstep (se 1 (by rfl) ⟨1137884, by rfl⟩ : syracuseStep 1517179 = 2275769) B2275769
theorem B2557651 : Blo 1346992 2557651 := bstep (se 1 (by rfl) ⟨1918238, by rfl⟩ : syracuseStep 2557651 = 3836477) B3836477
theorem B4548311 : Blo 1346992 4548311 := bstep (se 1 (by rfl) ⟨3411233, by rfl⟩ : syracuseStep 4548311 = 6822467) B6822467
theorem B12961529 : Blo 1346992 12961529 := bstep (se 2 (by rfl) ⟨4860573, by rfl⟩ : syracuseStep 12961529 = 9721147) B9721147
theorem B17278757 : Blo 1346992 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B3032927 : Blo 1346992 3032927 := bstep (se 1 (by rfl) ⟨2274695, by rfl⟩ : syracuseStep 3032927 = 4549391) B4549391
theorem B23037857 : Blo 1346992 23037857 := bstep (se 2 (by rfl) ⟨8639196, by rfl⟩ : syracuseStep 23037857 = 17278393) B17278393
theorem B4548527 : Blo 1346992 4548527 := bstep (se 1 (by rfl) ⟨3411395, by rfl⟩ : syracuseStep 4548527 = 6822791) B6822791
theorem B3409847 : Blo 1346992 3409847 := bstep (se 1 (by rfl) ⟨2557385, by rfl⟩ : syracuseStep 3409847 = 5114771) B5114771
theorem B3033107 : Blo 1346992 3033107 := bstep (se 1 (by rfl) ⟨2274830, by rfl⟩ : syracuseStep 3033107 = 4549661) B4549661
theorem B7677989 : Blo 1346992 7677989 := bstep (se 4 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 7677989 = 1439623) B1439623
theorem B3033449 : Blo 1346992 3033449 := bstep (se 2 (by rfl) ⟨1137543, by rfl⟩ : syracuseStep 3033449 = 2275087) B2275087
theorem B4614529 : Blo 1346992 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B2558395 : Blo 1346992 2558395 := bstep (se 1 (by rfl) ⟨1918796, by rfl⟩ : syracuseStep 2558395 = 3837593) B3837593
theorem B7383737 : Blo 1346992 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B4098775 : Blo 1346992 4098775 := bstep (se 1 (by rfl) ⟨3074081, by rfl⟩ : syracuseStep 4098775 = 6148163) B6148163
theorem B336579299 : Blo 1346992 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B34523981 : Blo 1346992 34523981 := bstep (se 3 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 34523981 = 12946493) B12946493
theorem B17271629 : Blo 1346992 17271629 := bstep (se 3 (by rfl) ⟨3238430, by rfl⟩ : syracuseStep 17271629 = 6476861) B6476861
theorem B5114785 : Blo 1346992 5114785 := bstep (se 2 (by rfl) ⟨1918044, by rfl⟩ : syracuseStep 5114785 = 3836089) B3836089
theorem B3410849 : Blo 1346992 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B2558881 : Blo 1346992 2558881 := bstep (se 2 (by rfl) ⟨959580, by rfl⟩ : syracuseStep 2558881 = 1919161) B1919161
theorem B4860847 : Blo 1346992 4860847 := bstep (se 1 (by rfl) ⟨3645635, by rfl⟩ : syracuseStep 4860847 = 7291271) B7291271
theorem B3034043 : Blo 1346992 3034043 := bstep (se 1 (by rfl) ⟨2275532, by rfl⟩ : syracuseStep 3034043 = 4551065) B4551065
theorem B3034169 : Blo 1346992 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B6474923 : Blo 1346992 6474923 := bstep (se 1 (by rfl) ⟨4856192, by rfl⟩ : syracuseStep 6474923 = 9712385) B9712385
theorem B38890691 : Blo 1346992 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B10235159 : Blo 1346992 10235159 := bstep (se 1 (by rfl) ⟨7676369, by rfl⟩ : syracuseStep 10235159 = 15352739) B15352739
theorem B24612133 : Blo 1346992 24612133 := bstep (se 4 (by rfl) ⟨2307387, by rfl⟩ : syracuseStep 24612133 = 4614775) B4614775
theorem B2157929 : Blo 1346992 2157929 := bstep (se 2 (by rfl) ⟨809223, by rfl⟩ : syracuseStep 2157929 = 1618447) B1618447
theorem B3411305 : Blo 1346992 3411305 := bstep (se 2 (by rfl) ⟨1279239, by rfl⟩ : syracuseStep 3411305 = 2558479) B2558479
theorem B4861309 : Blo 1346992 4861309 := bstep (se 3 (by rfl) ⟨911495, by rfl⟩ : syracuseStep 4861309 = 1822991) B1822991
theorem B3034511 : Blo 1346992 3034511 := bstep (se 1 (by rfl) ⟨2275883, by rfl⟩ : syracuseStep 3034511 = 4551767) B4551767
theorem B1347015 : Blo 1346992 1347015 := bstep (se 1 (by rfl) ⟨1010261, by rfl⟩ : syracuseStep 1347015 = 2020523) B2020523
theorem B1347035 : Blo 1346992 1347035 := bstep (se 1 (by rfl) ⟨1010276, by rfl⟩ : syracuseStep 1347035 = 2020553) B2020553
theorem B2559451 : Blo 1346992 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B5189129 : Blo 1346992 5189129 := bstep (se 2 (by rfl) ⟨1945923, by rfl⟩ : syracuseStep 5189129 = 3891847) B3891847
theorem B1347111 : Blo 1346992 1347111 := bstep (se 1 (by rfl) ⟨1010333, by rfl⟩ : syracuseStep 1347111 = 2020667) B2020667
theorem B1347151 : Blo 1346992 1347151 := bstep (se 1 (by rfl) ⟨1010363, by rfl⟩ : syracuseStep 1347151 = 2020727) B2020727
theorem B1347167 : Blo 1346992 1347167 := bstep (se 1 (by rfl) ⟨1010375, by rfl⟩ : syracuseStep 1347167 = 2020751) B2020751
theorem B6917729 : Blo 1346992 6917729 := bstep (se 2 (by rfl) ⟨2594148, by rfl⟩ : syracuseStep 6917729 = 5188297) B5188297
theorem B1347195 : Blo 1346992 1347195 := bstep (se 1 (by rfl) ⟨1010396, by rfl⟩ : syracuseStep 1347195 = 2020793) B2020793
theorem B10374779 : Blo 1346992 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B5467771 : Blo 1346992 5467771 := bstep (se 1 (by rfl) ⟨4100828, by rfl⟩ : syracuseStep 5467771 = 8201657) B8201657
theorem B1347247 : Blo 1346992 1347247 := bstep (se 1 (by rfl) ⟨1010435, by rfl⟩ : syracuseStep 1347247 = 2020871) B2020871
theorem B1347271 : Blo 1346992 1347271 := bstep (se 1 (by rfl) ⟨1010453, by rfl⟩ : syracuseStep 1347271 = 2020907) B2020907
theorem B3034835 : Blo 1346992 3034835 := bstep (se 1 (by rfl) ⟨2276126, by rfl⟩ : syracuseStep 3034835 = 4552253) B4552253
theorem B1347291 : Blo 1346992 1347291 := bstep (se 1 (by rfl) ⟨1010468, by rfl⟩ : syracuseStep 1347291 = 2020937) B2020937
theorem B1347367 : Blo 1346992 1347367 := bstep (se 1 (by rfl) ⟨1010525, by rfl⟩ : syracuseStep 1347367 = 2021051) B2021051
theorem B10243907 : Blo 1346992 10243907 := bstep (se 1 (by rfl) ⟨7682930, by rfl⟩ : syracuseStep 10243907 = 15365861) B15365861
theorem B1347407 : Blo 1346992 1347407 := bstep (se 1 (by rfl) ⟨1010555, by rfl⟩ : syracuseStep 1347407 = 2021111) B2021111
theorem B5115743 : Blo 1346992 5115743 := bstep (se 1 (by rfl) ⟨3836807, by rfl⟩ : syracuseStep 5115743 = 7673615) B7673615
theorem B1347423 : Blo 1346992 1347423 := bstep (se 1 (by rfl) ⟨1010567, by rfl⟩ : syracuseStep 1347423 = 2021135) B2021135
theorem B5115757 : Blo 1346992 5115757 := bstep (se 3 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 5115757 = 1918409) B1918409
theorem B1347451 : Blo 1346992 1347451 := bstep (se 1 (by rfl) ⟨1010588, by rfl⟩ : syracuseStep 1347451 = 2021177) B2021177
theorem B11513735 : Blo 1346992 11513735 := bstep (se 1 (by rfl) ⟨8635301, by rfl⟩ : syracuseStep 11513735 = 17270603) B17270603
theorem B1347503 : Blo 1346992 1347503 := bstep (se 1 (by rfl) ⟨1010627, by rfl⟩ : syracuseStep 1347503 = 2021255) B2021255
theorem B1347527 : Blo 1346992 1347527 := bstep (se 1 (by rfl) ⟨1010645, by rfl⟩ : syracuseStep 1347527 = 2021291) B2021291
theorem B1347547 : Blo 1346992 1347547 := bstep (se 1 (by rfl) ⟨1010660, by rfl⟩ : syracuseStep 1347547 = 2021321) B2021321
theorem B5468161 : Blo 1346992 5468161 := bstep (se 2 (by rfl) ⟨2050560, by rfl⟩ : syracuseStep 5468161 = 4101121) B4101121
theorem B5754887 : Blo 1346992 5754887 := bstep (se 1 (by rfl) ⟨4316165, by rfl⟩ : syracuseStep 5754887 = 8632331) B8632331
theorem B4378643 : Blo 1346992 4378643 := bstep (se 1 (by rfl) ⟨3283982, by rfl⟩ : syracuseStep 4378643 = 6567965) B6567965
theorem B1347623 : Blo 1346992 1347623 := bstep (se 1 (by rfl) ⟨1010717, by rfl⟩ : syracuseStep 1347623 = 2021435) B2021435
theorem B2879545 : Blo 1346992 2879545 := bstep (se 2 (by rfl) ⟨1079829, by rfl⟩ : syracuseStep 2879545 = 2159659) B2159659
theorem B1536079 : Blo 1346992 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B2273359 : Blo 1346992 2273359 := bstep (se 1 (by rfl) ⟨1705019, by rfl⟩ : syracuseStep 2273359 = 3410039) B3410039
theorem B1347663 : Blo 1346992 1347663 := bstep (se 1 (by rfl) ⟨1010747, by rfl⟩ : syracuseStep 1347663 = 2021495) B2021495
theorem B1347679 : Blo 1346992 1347679 := bstep (se 1 (by rfl) ⟨1010759, by rfl⟩ : syracuseStep 1347679 = 2021519) B2021519
theorem B1347707 : Blo 1346992 1347707 := bstep (se 1 (by rfl) ⟨1010780, by rfl⟩ : syracuseStep 1347707 = 2021561) B2021561
theorem B5116061 : Blo 1346992 5116061 := bstep (se 3 (by rfl) ⟨959261, by rfl⟩ : syracuseStep 5116061 = 1918523) B1918523
theorem B1347759 : Blo 1346992 1347759 := bstep (se 1 (by rfl) ⟨1010819, by rfl⟩ : syracuseStep 1347759 = 2021639) B2021639
theorem B1347783 : Blo 1346992 1347783 := bstep (se 1 (by rfl) ⟨1010837, by rfl⟩ : syracuseStep 1347783 = 2021675) B2021675
theorem B1347803 : Blo 1346992 1347803 := bstep (se 1 (by rfl) ⟨1010852, by rfl⟩ : syracuseStep 1347803 = 2021705) B2021705
theorem B4550903 : Blo 1346992 4550903 := bstep (se 1 (by rfl) ⟨3413177, by rfl⟩ : syracuseStep 4550903 = 6826355) B6826355
theorem B6828299 : Blo 1346992 6828299 := bstep (se 1 (by rfl) ⟨5121224, by rfl⟩ : syracuseStep 6828299 = 10242449) B10242449
theorem B1347879 : Blo 1346992 1347879 := bstep (se 1 (by rfl) ⟨1010909, by rfl⟩ : syracuseStep 1347879 = 2021819) B2021819
theorem B141914429 : Blo 1346992 141914429 := bstep (se 3 (by rfl) ⟨26608955, by rfl⟩ : syracuseStep 141914429 = 53217911) B53217911
theorem B2273609 : Blo 1346992 2273609 := bstep (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) B1705207
theorem B1347919 : Blo 1346992 1347919 := bstep (se 1 (by rfl) ⟨1010939, by rfl⟩ : syracuseStep 1347919 = 2021879) B2021879
theorem B4608343 : Blo 1346992 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B1347935 : Blo 1346992 1347935 := bstep (se 1 (by rfl) ⟨1010951, by rfl⟩ : syracuseStep 1347935 = 2021903) B2021903
theorem B2732395 : Blo 1346992 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B1347963 : Blo 1346992 1347963 := bstep (se 1 (by rfl) ⟨1010972, by rfl⟩ : syracuseStep 1347963 = 2021945) B2021945
theorem B2879887 : Blo 1346992 2879887 := bstep (se 1 (by rfl) ⟨2159915, by rfl⟩ : syracuseStep 2879887 = 4319831) B4319831
theorem B1348015 : Blo 1346992 1348015 := bstep (se 1 (by rfl) ⟨1011011, by rfl⟩ : syracuseStep 1348015 = 2022023) B2022023
theorem B1348039 : Blo 1346992 1348039 := bstep (se 1 (by rfl) ⟨1011029, by rfl⟩ : syracuseStep 1348039 = 2022059) B2022059
theorem B1348059 : Blo 1346992 1348059 := bstep (se 1 (by rfl) ⟨1011044, by rfl⟩ : syracuseStep 1348059 = 2022089) B2022089
theorem B6820361 : Blo 1346992 6820361 := bstep (se 2 (by rfl) ⟨2557635, by rfl⟩ : syracuseStep 6820361 = 5115271) B5115271
theorem B3412489 : Blo 1346992 3412489 := bstep (se 2 (by rfl) ⟨1279683, by rfl⟩ : syracuseStep 3412489 = 2559367) B2559367
theorem B12956183 : Blo 1346992 12956183 := bstep (se 1 (by rfl) ⟨9717137, by rfl⟩ : syracuseStep 12956183 = 19434275) B19434275
theorem B1348135 : Blo 1346992 1348135 := bstep (se 1 (by rfl) ⟨1011101, by rfl⟩ : syracuseStep 1348135 = 2022203) B2022203
theorem B4551227 : Blo 1346992 4551227 := bstep (se 1 (by rfl) ⟨3413420, by rfl⟩ : syracuseStep 4551227 = 6826841) B6826841
theorem B1348175 : Blo 1346992 1348175 := bstep (se 1 (by rfl) ⟨1011131, by rfl⟩ : syracuseStep 1348175 = 2022263) B2022263
theorem B1348191 : Blo 1346992 1348191 := bstep (se 1 (by rfl) ⟨1011143, by rfl⟩ : syracuseStep 1348191 = 2022287) B2022287
theorem B1348219 : Blo 1346992 1348219 := bstep (se 1 (by rfl) ⟨1011164, by rfl⟩ : syracuseStep 1348219 = 2022329) B2022329
theorem B1348271 : Blo 1346992 1348271 := bstep (se 1 (by rfl) ⟨1011203, by rfl⟩ : syracuseStep 1348271 = 2022407) B2022407
theorem B1348295 : Blo 1346992 1348295 := bstep (se 1 (by rfl) ⟨1011221, by rfl⟩ : syracuseStep 1348295 = 2022443) B2022443
theorem B10236617 : Blo 1346992 10236617 := bstep (se 2 (by rfl) ⟨3838731, by rfl⟩ : syracuseStep 10236617 = 7677463) B7677463
theorem B10932947 : Blo 1346992 10932947 := bstep (se 1 (by rfl) ⟨8199710, by rfl⟩ : syracuseStep 10932947 = 16399421) B16399421
theorem B2880211 : Blo 1346992 2880211 := bstep (se 1 (by rfl) ⟨2160158, by rfl⟩ : syracuseStep 2880211 = 4320317) B4320317
theorem B1348315 : Blo 1346992 1348315 := bstep (se 1 (by rfl) ⟨1011236, by rfl⟩ : syracuseStep 1348315 = 2022473) B2022473
theorem B2274041 : Blo 1346992 2274041 := bstep (se 2 (by rfl) ⟨852765, by rfl⟩ : syracuseStep 2274041 = 1705531) B1705531
theorem B2429689 : Blo 1346992 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B1348391 : Blo 1346992 1348391 := bstep (se 1 (by rfl) ⟨1011293, by rfl⟩ : syracuseStep 1348391 = 2022587) B2022587
theorem B5116715 : Blo 1346992 5116715 := bstep (se 1 (by rfl) ⟨3837536, by rfl⟩ : syracuseStep 5116715 = 7675073) B7675073
theorem B7107401 : Blo 1346992 7107401 := bstep (se 2 (by rfl) ⟨2665275, by rfl⟩ : syracuseStep 7107401 = 5330551) B5330551
theorem B4551497 : Blo 1346992 4551497 := bstep (se 2 (by rfl) ⟨1706811, by rfl⟩ : syracuseStep 4551497 = 3413623) B3413623
theorem B1348431 : Blo 1346992 1348431 := bstep (se 1 (by rfl) ⟨1011323, by rfl⟩ : syracuseStep 1348431 = 2022647) B2022647
theorem B1348447 : Blo 1346992 1348447 := bstep (se 1 (by rfl) ⟨1011335, by rfl⟩ : syracuseStep 1348447 = 2022671) B2022671
theorem B1348475 : Blo 1346992 1348475 := bstep (se 1 (by rfl) ⟨1011356, by rfl⟩ : syracuseStep 1348475 = 2022713) B2022713
theorem B2274223 : Blo 1346992 2274223 := bstep (se 1 (by rfl) ⟨1705667, by rfl⟩ : syracuseStep 2274223 = 3411335) B3411335
theorem B1348527 : Blo 1346992 1348527 := bstep (se 1 (by rfl) ⟨1011395, by rfl⟩ : syracuseStep 1348527 = 2022791) B2022791
theorem B1348551 : Blo 1346992 1348551 := bstep (se 1 (by rfl) ⟨1011413, by rfl⟩ : syracuseStep 1348551 = 2022827) B2022827
theorem B1348571 : Blo 1346992 1348571 := bstep (se 1 (by rfl) ⟨1011428, by rfl⟩ : syracuseStep 1348571 = 2022857) B2022857
theorem B2274311 : Blo 1346992 2274311 := bstep (se 1 (by rfl) ⟨1705733, by rfl⟩ : syracuseStep 2274311 = 3411467) B3411467
theorem B1348647 : Blo 1346992 1348647 := bstep (se 1 (by rfl) ⟨1011485, by rfl⟩ : syracuseStep 1348647 = 2022971) B2022971
theorem B1348687 : Blo 1346992 1348687 := bstep (se 1 (by rfl) ⟨1011515, by rfl⟩ : syracuseStep 1348687 = 2023031) B2023031
theorem B1348703 : Blo 1346992 1348703 := bstep (se 1 (by rfl) ⟨1011527, by rfl⟩ : syracuseStep 1348703 = 2023055) B2023055
theorem B1348731 : Blo 1346992 1348731 := bstep (se 1 (by rfl) ⟨1011548, by rfl⟩ : syracuseStep 1348731 = 2023097) B2023097
theorem B1348783 : Blo 1346992 1348783 := bstep (se 1 (by rfl) ⟨1011587, by rfl⟩ : syracuseStep 1348783 = 2023175) B2023175
theorem B5190851 : Blo 1346992 5190851 := bstep (se 1 (by rfl) ⟨3893138, by rfl⟩ : syracuseStep 5190851 = 7786277) B7786277
theorem B1348807 : Blo 1346992 1348807 := bstep (se 1 (by rfl) ⟨1011605, by rfl⟩ : syracuseStep 1348807 = 2023211) B2023211
theorem B1348827 : Blo 1346992 1348827 := bstep (se 1 (by rfl) ⟨1011620, by rfl⟩ : syracuseStep 1348827 = 2023241) B2023241
theorem B2020601 : Blo 1346992 2020601 := bstep (se 2 (by rfl) ⟨757725, by rfl⟩ : syracuseStep 2020601 = 1515451) B1515451
theorem B1348903 : Blo 1346992 1348903 := bstep (se 1 (by rfl) ⟨1011677, by rfl⟩ : syracuseStep 1348903 = 2023355) B2023355
theorem B1348943 : Blo 1346992 1348943 := bstep (se 1 (by rfl) ⟨1011707, by rfl⟩ : syracuseStep 1348943 = 2023415) B2023415
theorem B2020703 : Blo 1346992 2020703 := bstep (se 1 (by rfl) ⟨1515527, by rfl⟩ : syracuseStep 2020703 = 3031055) B3031055
theorem B2274655 : Blo 1346992 2274655 := bstep (se 1 (by rfl) ⟨1705991, by rfl⟩ : syracuseStep 2274655 = 3411983) B3411983
theorem B1348959 : Blo 1346992 1348959 := bstep (se 1 (by rfl) ⟨1011719, by rfl⟩ : syracuseStep 1348959 = 2023439) B2023439
theorem B2020715 : Blo 1346992 2020715 := bstep (se 1 (by rfl) ⟨1515536, by rfl⟩ : syracuseStep 2020715 = 3031073) B3031073
theorem B1348987 : Blo 1346992 1348987 := bstep (se 1 (by rfl) ⟨1011740, by rfl⟩ : syracuseStep 1348987 = 2023481) B2023481
theorem B2274743 : Blo 1346992 2274743 := bstep (se 1 (by rfl) ⟨1706057, by rfl⟩ : syracuseStep 2274743 = 3412115) B3412115
theorem B3642889 : Blo 1346992 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B5461543 : Blo 1346992 5461543 := bstep (se 1 (by rfl) ⟨4096157, by rfl⟩ : syracuseStep 5461543 = 8192315) B8192315
theorem B2020943 : Blo 1346992 2020943 := bstep (se 1 (by rfl) ⟨1515707, by rfl⟩ : syracuseStep 2020943 = 3031415) B3031415
theorem B2021063 : Blo 1346992 2021063 := bstep (se 1 (by rfl) ⟨1515797, by rfl⟩ : syracuseStep 2021063 = 3031595) B3031595
theorem B1971911 : Blo 1346992 1971911 := bstep (se 1 (by rfl) ⟨1478933, by rfl⟩ : syracuseStep 1971911 = 2957867) B2957867
theorem B2160479 : Blo 1346992 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B2021225 : Blo 1346992 2021225 := bstep (se 2 (by rfl) ⟨757959, by rfl⟩ : syracuseStep 2021225 = 1515919) B1515919
theorem B2021303 : Blo 1346992 2021303 := bstep (se 1 (by rfl) ⟨1515977, by rfl⟩ : syracuseStep 2021303 = 3031955) B3031955
theorem B4552631 : Blo 1346992 4552631 := bstep (se 1 (by rfl) ⟨3414473, by rfl⟩ : syracuseStep 4552631 = 6828947) B6828947
theorem B6821819 : Blo 1346992 6821819 := bstep (se 1 (by rfl) ⟨5116364, by rfl⟩ : syracuseStep 6821819 = 10232729) B10232729
theorem B4437947 : Blo 1346992 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B3413947 : Blo 1346992 3413947 := bstep (se 1 (by rfl) ⟨2560460, by rfl⟩ : syracuseStep 3413947 = 5120921) B5120921
theorem B2021339 : Blo 1346992 2021339 := bstep (se 1 (by rfl) ⟨1516004, by rfl⟩ : syracuseStep 2021339 = 3032009) B3032009
theorem B2275337 : Blo 1346992 2275337 := bstep (se 2 (by rfl) ⟨853251, by rfl⟩ : syracuseStep 2275337 = 1706503) B1706503
theorem B2160697 : Blo 1346992 2160697 := bstep (se 2 (by rfl) ⟨810261, by rfl⟩ : syracuseStep 2160697 = 1620523) B1620523
theorem B2275499 : Blo 1346992 2275499 := bstep (se 1 (by rfl) ⟨1706624, by rfl⟩ : syracuseStep 2275499 = 3413249) B3413249
theorem B2021807 : Blo 1346992 2021807 := bstep (se 1 (by rfl) ⟨1516355, by rfl⟩ : syracuseStep 2021807 = 3032711) B3032711
theorem B2021897 : Blo 1346992 2021897 := bstep (se 2 (by rfl) ⟨758211, by rfl⟩ : syracuseStep 2021897 = 1516423) B1516423
theorem B2021927 : Blo 1346992 2021927 := bstep (se 1 (by rfl) ⟨1516445, by rfl⟩ : syracuseStep 2021927 = 3032891) B3032891
theorem B2275897 : Blo 1346992 2275897 := bstep (se 2 (by rfl) ⟨853461, by rfl⟩ : syracuseStep 2275897 = 1706923) B1706923
theorem B2022011 : Blo 1346992 2022011 := bstep (se 1 (by rfl) ⟨1516508, by rfl⟩ : syracuseStep 2022011 = 3033017) B3033017
theorem B1366651 : Blo 1346992 1366651 := bstep (se 1 (by rfl) ⟨1024988, by rfl⟩ : syracuseStep 1366651 = 2049977) B2049977
theorem B3840635 : Blo 1346992 3840635 := bstep (se 1 (by rfl) ⟨2880476, by rfl⟩ : syracuseStep 3840635 = 5760953) B5760953
theorem B1440379 : Blo 1346992 1440379 := bstep (se 1 (by rfl) ⟨1080284, by rfl⟩ : syracuseStep 1440379 = 2160569) B2160569
theorem B2276039 : Blo 1346992 2276039 := bstep (se 1 (by rfl) ⟨1707029, by rfl⟩ : syracuseStep 2276039 = 3414059) B3414059
theorem B5118673 : Blo 1346992 5118673 := bstep (se 2 (by rfl) ⟨1919502, by rfl⟩ : syracuseStep 5118673 = 3839005) B3839005
theorem B5462777 : Blo 1346992 5462777 := bstep (se 2 (by rfl) ⟨2048541, by rfl⟩ : syracuseStep 5462777 = 4097083) B4097083
theorem B2022137 : Blo 1346992 2022137 := bstep (se 2 (by rfl) ⟨758301, by rfl⟩ : syracuseStep 2022137 = 1516603) B1516603
theorem B4315999 : Blo 1346992 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B2022239 : Blo 1346992 2022239 := bstep (se 1 (by rfl) ⟨1516679, by rfl⟩ : syracuseStep 2022239 = 3033359) B3033359
theorem B2276201 : Blo 1346992 2276201 := bstep (se 2 (by rfl) ⟨853575, by rfl⟩ : syracuseStep 2276201 = 1707151) B1707151
theorem B2022251 : Blo 1346992 2022251 := bstep (se 1 (by rfl) ⟨1516688, by rfl⟩ : syracuseStep 2022251 = 3033377) B3033377
theorem B10230785 : Blo 1346992 10230785 := bstep (se 2 (by rfl) ⟨3836544, by rfl⟩ : syracuseStep 10230785 = 7673089) B7673089
theorem B5118977 : Blo 1346992 5118977 := bstep (se 2 (by rfl) ⟨1919616, by rfl⟩ : syracuseStep 5118977 = 3839233) B3839233
theorem B2022479 : Blo 1346992 2022479 := bstep (se 1 (by rfl) ⟨1516859, by rfl⟩ : syracuseStep 2022479 = 3033719) B3033719
theorem B2022599 : Blo 1346992 2022599 := bstep (se 1 (by rfl) ⟨1516949, by rfl⟩ : syracuseStep 2022599 = 3033899) B3033899
theorem B6823115 : Blo 1346992 6823115 := bstep (se 1 (by rfl) ⟨5117336, by rfl⟩ : syracuseStep 6823115 = 10234673) B10234673
theorem B21855511 : Blo 1346992 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B2022761 : Blo 1346992 2022761 := bstep (se 2 (by rfl) ⟨758535, by rfl⟩ : syracuseStep 2022761 = 1517071) B1517071
theorem B2022839 : Blo 1346992 2022839 := bstep (se 1 (by rfl) ⟨1517129, by rfl⟩ : syracuseStep 2022839 = 3034259) B3034259
theorem B5119433 : Blo 1346992 5119433 := bstep (se 2 (by rfl) ⟨1919787, by rfl⟩ : syracuseStep 5119433 = 3839575) B3839575
theorem B2022875 : Blo 1346992 2022875 := bstep (se 1 (by rfl) ⟨1517156, by rfl⟩ : syracuseStep 2022875 = 3034313) B3034313
theorem B9723539 : Blo 1346992 9723539 := bstep (se 1 (by rfl) ⟨7292654, by rfl⟩ : syracuseStep 9723539 = 14585309) B14585309
theorem B4857533 : Blo 1346992 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B4546259 : Blo 1346992 4546259 := bstep (se 1 (by rfl) ⟨3409694, by rfl⟩ : syracuseStep 4546259 = 6819389) B6819389
theorem B59121413 : Blo 1346992 59121413 := bstep (se 4 (by rfl) ⟨5542632, by rfl⟩ : syracuseStep 59121413 = 11085265) B11085265
theorem B3030857 : Blo 1346992 3030857 := bstep (se 2 (by rfl) ⟨1136571, by rfl⟩ : syracuseStep 3030857 = 2273143) B2273143
theorem B5119919 : Blo 1346992 5119919 := bstep (se 1 (by rfl) ⟨3839939, by rfl⟩ : syracuseStep 5119919 = 7679879) B7679879
theorem B2023343 : Blo 1346992 2023343 := bstep (se 1 (by rfl) ⟨1517507, by rfl⟩ : syracuseStep 2023343 = 3035015) B3035015
theorem B7290881 : Blo 1346992 7290881 := bstep (se 2 (by rfl) ⟨2734080, by rfl⟩ : syracuseStep 7290881 = 5468161) B5468161
theorem B10240019 : Blo 1346992 10240019 := bstep (se 1 (by rfl) ⟨7680014, by rfl⟩ : syracuseStep 10240019 = 15360029) B15360029
theorem B2048105 : Blo 1346992 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B3031145 : Blo 1346992 3031145 := bstep (se 2 (by rfl) ⟨1136679, by rfl⟩ : syracuseStep 3031145 = 2273359) B2273359
theorem B94609619 : Blo 1346992 94609619 := bstep (se 1 (by rfl) ⟨70957214, by rfl⟩ : syracuseStep 94609619 = 141914429) B141914429
theorem B1515739 : Blo 1346992 1515739 := bstep (se 1 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 1515739 = 2273609) B2273609
theorem B4546907 : Blo 1346992 4546907 := bstep (se 1 (by rfl) ⟨3410180, by rfl⟩ : syracuseStep 4546907 = 6820361) B6820361
theorem B6144457 : Blo 1346992 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B6824411 : Blo 1346992 6824411 := bstep (se 1 (by rfl) ⟨5118308, by rfl⟩ : syracuseStep 6824411 = 10236617) B10236617
theorem B1516027 : Blo 1346992 1516027 := bstep (se 1 (by rfl) ⟨1137020, by rfl⟩ : syracuseStep 1516027 = 2274041) B2274041
theorem B6152705 : Blo 1346992 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B3031631 : Blo 1346992 3031631 := bstep (se 1 (by rfl) ⟨2273723, by rfl⟩ : syracuseStep 3031631 = 4547447) B4547447
theorem B1516207 : Blo 1346992 1516207 := bstep (se 1 (by rfl) ⟨1137155, by rfl⟩ : syracuseStep 1516207 = 2274311) B2274311
theorem B3031775 : Blo 1346992 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B6824897 : Blo 1346992 6824897 := bstep (se 2 (by rfl) ⟨2559336, by rfl⟩ : syracuseStep 6824897 = 5118673) B5118673
theorem B5465033 : Blo 1346992 5465033 := bstep (se 2 (by rfl) ⟨2049387, by rfl⟩ : syracuseStep 5465033 = 4098775) B4098775
theorem B1516495 : Blo 1346992 1516495 := bstep (se 1 (by rfl) ⟨1137371, by rfl⟩ : syracuseStep 1516495 = 2274743) B2274743
theorem B3032027 : Blo 1346992 3032027 := bstep (se 1 (by rfl) ⟨2274020, by rfl⟩ : syracuseStep 3032027 = 4548041) B4548041
theorem B8635355 : Blo 1346992 8635355 := bstep (se 1 (by rfl) ⟨6476516, by rfl⟩ : syracuseStep 8635355 = 12953033) B12953033
theorem B3032207 : Blo 1346992 3032207 := bstep (se 1 (by rfl) ⟨2274155, by rfl⟩ : syracuseStep 3032207 = 4548311) B4548311
theorem B11519171 : Blo 1346992 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B3032297 : Blo 1346992 3032297 := bstep (se 2 (by rfl) ⟨1137111, by rfl⟩ : syracuseStep 3032297 = 2274223) B2274223
theorem B6481129 : Blo 1346992 6481129 := bstep (se 2 (by rfl) ⟨2430423, by rfl⟩ : syracuseStep 6481129 = 4860847) B4860847
theorem B3032351 : Blo 1346992 3032351 := bstep (se 1 (by rfl) ⟨2274263, by rfl⟩ : syracuseStep 3032351 = 4548527) B4548527
theorem B4547879 : Blo 1346992 4547879 := bstep (se 1 (by rfl) ⟨3410909, by rfl⟩ : syracuseStep 4547879 = 6821819) B6821819
theorem B1516891 : Blo 1346992 1516891 := bstep (se 1 (by rfl) ⟨1137668, by rfl⟩ : syracuseStep 1516891 = 2275337) B2275337
theorem B1516999 : Blo 1346992 1516999 := bstep (se 1 (by rfl) ⟨1137749, by rfl⟩ : syracuseStep 1516999 = 2275499) B2275499
theorem B3032873 : Blo 1346992 3032873 := bstep (se 2 (by rfl) ⟨1137327, by rfl⟩ : syracuseStep 3032873 = 2274655) B2274655
theorem B1517359 : Blo 1346992 1517359 := bstep (se 1 (by rfl) ⟨1138019, by rfl⟩ : syracuseStep 1517359 = 2276039) B2276039
theorem B6481745 : Blo 1346992 6481745 := bstep (se 2 (by rfl) ⟨2430654, by rfl⟩ : syracuseStep 6481745 = 4861309) B4861309
theorem B1517467 : Blo 1346992 1517467 := bstep (se 1 (by rfl) ⟨1138100, by rfl⟩ : syracuseStep 1517467 = 2276201) B2276201
theorem B4548743 : Blo 1346992 4548743 := bstep (se 1 (by rfl) ⟨3411557, by rfl⟩ : syracuseStep 4548743 = 6823115) B6823115
theorem B5761277 : Blo 1346992 5761277 := bstep (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) B2160479
theorem B3410201 : Blo 1346992 3410201 := bstep (se 2 (by rfl) ⟨1278825, by rfl⟩ : syracuseStep 3410201 = 2557651) B2557651
theorem B5835037 : Blo 1346992 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B3459419 : Blo 1346992 3459419 := bstep (se 1 (by rfl) ⟨2594564, by rfl⟩ : syracuseStep 3459419 = 5189129) B5189129
theorem B6916519 : Blo 1346992 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B6482359 : Blo 1346992 6482359 := bstep (se 1 (by rfl) ⟨4861769, by rfl⟩ : syracuseStep 6482359 = 9723539) B9723539
theorem B3238355 : Blo 1346992 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B39414275 : Blo 1346992 39414275 := bstep (se 1 (by rfl) ⟨29560706, by rfl⟩ : syracuseStep 39414275 = 59121413) B59121413
theorem B3410495 : Blo 1346992 3410495 := bstep (se 1 (by rfl) ⟨2557871, by rfl⟩ : syracuseStep 3410495 = 5115743) B5115743
theorem B3836591 : Blo 1346992 3836591 := bstep (se 1 (by rfl) ⟨2877443, by rfl⟩ : syracuseStep 3836591 = 5754887) B5754887
theorem B2919095 : Blo 1346992 2919095 := bstep (se 1 (by rfl) ⟨2189321, by rfl⟩ : syracuseStep 2919095 = 4378643) B4378643
theorem B3410707 : Blo 1346992 3410707 := bstep (se 1 (by rfl) ⟨2558030, by rfl⟩ : syracuseStep 3410707 = 5116061) B5116061
theorem B3033935 : Blo 1346992 3033935 := bstep (se 1 (by rfl) ⟨2275451, by rfl⟩ : syracuseStep 3033935 = 4550903) B4550903
theorem B17263631 : Blo 1346992 17263631 := bstep (se 1 (by rfl) ⟨12947723, by rfl⟩ : syracuseStep 17263631 = 25895447) B25895447
theorem B8637455 : Blo 1346992 8637455 := bstep (se 1 (by rfl) ⟨6478091, by rfl⟩ : syracuseStep 8637455 = 12956183) B12956183
theorem B3034151 : Blo 1346992 3034151 := bstep (se 1 (by rfl) ⟨2275613, by rfl⟩ : syracuseStep 3034151 = 4551227) B4551227
theorem B3411143 : Blo 1346992 3411143 := bstep (se 1 (by rfl) ⟨2558357, by rfl⟩ : syracuseStep 3411143 = 5116715) B5116715
theorem B15346907 : Blo 1346992 15346907 := bstep (se 1 (by rfl) ⟨11510180, by rfl⟩ : syracuseStep 15346907 = 23020361) B23020361
theorem B4738267 : Blo 1346992 4738267 := bstep (se 1 (by rfl) ⟨3553700, by rfl⟩ : syracuseStep 4738267 = 7107401) B7107401
theorem B7679195 : Blo 1346992 7679195 := bstep (se 1 (by rfl) ⟨5759396, by rfl⟩ : syracuseStep 7679195 = 11518793) B11518793
theorem B3034331 : Blo 1346992 3034331 := bstep (se 1 (by rfl) ⟨2275748, by rfl⟩ : syracuseStep 3034331 = 4551497) B4551497
theorem B3411193 : Blo 1346992 3411193 := bstep (se 2 (by rfl) ⟨1279197, by rfl⟩ : syracuseStep 3411193 = 2558395) B2558395
theorem B4549985 : Blo 1346992 4549985 := bstep (se 2 (by rfl) ⟨1706244, by rfl⟩ : syracuseStep 4549985 = 3412489) B3412489
theorem B3034529 : Blo 1346992 3034529 := bstep (se 2 (by rfl) ⟨1137948, by rfl⟩ : syracuseStep 3034529 = 2275897) B2275897
theorem B3460567 : Blo 1346992 3460567 := bstep (se 1 (by rfl) ⟨2595425, by rfl⟩ : syracuseStep 3460567 = 5190851) B5190851
theorem B1920505 : Blo 1346992 1920505 := bstep (se 2 (by rfl) ⟨720189, by rfl⟩ : syracuseStep 1920505 = 1440379) B1440379
theorem B1347067 : Blo 1346992 1347067 := bstep (se 1 (by rfl) ⟨1010300, by rfl⟩ : syracuseStep 1347067 = 2020601) B2020601
theorem B1347135 : Blo 1346992 1347135 := bstep (se 1 (by rfl) ⟨1010351, by rfl⟩ : syracuseStep 1347135 = 2020703) B2020703
theorem B1347143 : Blo 1346992 1347143 := bstep (se 1 (by rfl) ⟨1010357, by rfl⟩ : syracuseStep 1347143 = 2020715) B2020715
theorem B3239585 : Blo 1346992 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B1347295 : Blo 1346992 1347295 := bstep (se 1 (by rfl) ⟨1010471, by rfl⟩ : syracuseStep 1347295 = 2020943) B2020943
theorem B5754665 : Blo 1346992 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B1347375 : Blo 1346992 1347375 := bstep (se 1 (by rfl) ⟨1010531, by rfl⟩ : syracuseStep 1347375 = 2021063) B2021063
theorem B6819713 : Blo 1346992 6819713 := bstep (se 2 (by rfl) ⟨2557392, by rfl⟩ : syracuseStep 6819713 = 5114785) B5114785
theorem B3411841 : Blo 1346992 3411841 := bstep (se 2 (by rfl) ⟨1279440, by rfl⟩ : syracuseStep 3411841 = 2558881) B2558881
theorem B1347483 : Blo 1346992 1347483 := bstep (se 1 (by rfl) ⟨1010612, by rfl⟩ : syracuseStep 1347483 = 2021225) B2021225
theorem B2273231 : Blo 1346992 2273231 := bstep (se 1 (by rfl) ⟨1704923, by rfl⟩ : syracuseStep 2273231 = 3409847) B3409847
theorem B1347535 : Blo 1346992 1347535 := bstep (se 1 (by rfl) ⟨1010651, by rfl⟩ : syracuseStep 1347535 = 2021303) B2021303
theorem B3035087 : Blo 1346992 3035087 := bstep (se 1 (by rfl) ⟨2276315, by rfl⟩ : syracuseStep 3035087 = 4552631) B4552631
theorem B10923997 : Blo 1346992 10923997 := bstep (se 3 (by rfl) ⟨2048249, by rfl⟩ : syracuseStep 10923997 = 4096499) B4096499
theorem B1347559 : Blo 1346992 1347559 := bstep (se 1 (by rfl) ⟨1010669, by rfl⟩ : syracuseStep 1347559 = 2021339) B2021339
theorem B6828137 : Blo 1346992 6828137 := bstep (se 2 (by rfl) ⟨2560551, by rfl⟩ : syracuseStep 6828137 = 5121103) B5121103
theorem B1347871 : Blo 1346992 1347871 := bstep (se 1 (by rfl) ⟨1010903, by rfl⟩ : syracuseStep 1347871 = 2021807) B2021807
theorem B1347931 : Blo 1346992 1347931 := bstep (se 1 (by rfl) ⟨1010948, by rfl⟩ : syracuseStep 1347931 = 2021897) B2021897
theorem B1347951 : Blo 1346992 1347951 := bstep (se 1 (by rfl) ⟨1010963, by rfl⟩ : syracuseStep 1347951 = 2021927) B2021927
theorem B1348007 : Blo 1346992 1348007 := bstep (se 1 (by rfl) ⟨1011005, by rfl⟩ : syracuseStep 1348007 = 2022011) B2022011
theorem B2560423 : Blo 1346992 2560423 := bstep (se 1 (by rfl) ⟨1920317, by rfl⟩ : syracuseStep 2560423 = 3840635) B3840635
theorem B34550225 : Blo 1346992 34550225 := bstep (se 2 (by rfl) ⟨12956334, by rfl⟩ : syracuseStep 34550225 = 25912669) B25912669
theorem B3641851 : Blo 1346992 3641851 := bstep (se 1 (by rfl) ⟨2731388, by rfl⟩ : syracuseStep 3641851 = 5462777) B5462777
theorem B1348091 : Blo 1346992 1348091 := bstep (se 1 (by rfl) ⟨1011068, by rfl⟩ : syracuseStep 1348091 = 2022137) B2022137
theorem B23015987 : Blo 1346992 23015987 := bstep (se 1 (by rfl) ⟨17261990, by rfl⟩ : syracuseStep 23015987 = 34523981) B34523981
theorem B11514419 : Blo 1346992 11514419 := bstep (se 1 (by rfl) ⟨8635814, by rfl⟩ : syracuseStep 11514419 = 17271629) B17271629
theorem B1348159 : Blo 1346992 1348159 := bstep (se 1 (by rfl) ⟨1011119, by rfl⟩ : syracuseStep 1348159 = 2022239) B2022239
theorem B1348167 : Blo 1346992 1348167 := bstep (se 1 (by rfl) ⟨1011125, by rfl⟩ : syracuseStep 1348167 = 2022251) B2022251
theorem B2273899 : Blo 1346992 2273899 := bstep (se 1 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 2273899 = 3410849) B3410849
theorem B3412601 : Blo 1346992 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B6820523 : Blo 1346992 6820523 := bstep (se 1 (by rfl) ⟨5115392, by rfl⟩ : syracuseStep 6820523 = 10230785) B10230785
theorem B3412651 : Blo 1346992 3412651 := bstep (se 1 (by rfl) ⟨2559488, by rfl⟩ : syracuseStep 3412651 = 5118977) B5118977
theorem B1348319 : Blo 1346992 1348319 := bstep (se 1 (by rfl) ⟨1011239, by rfl⟩ : syracuseStep 1348319 = 2022479) B2022479
theorem B1348399 : Blo 1346992 1348399 := bstep (se 1 (by rfl) ⟨1011299, by rfl⟩ : syracuseStep 1348399 = 2022599) B2022599
theorem B1438619 : Blo 1346992 1438619 := bstep (se 1 (by rfl) ⟨1078964, by rfl⟩ : syracuseStep 1438619 = 2157929) B2157929
theorem B2274203 : Blo 1346992 2274203 := bstep (se 1 (by rfl) ⟨1705652, by rfl⟩ : syracuseStep 2274203 = 3411305) B3411305
theorem B1348507 : Blo 1346992 1348507 := bstep (se 1 (by rfl) ⟨1011380, by rfl⟩ : syracuseStep 1348507 = 2022761) B2022761
theorem B1348559 : Blo 1346992 1348559 := bstep (se 1 (by rfl) ⟨1011419, by rfl⟩ : syracuseStep 1348559 = 2022839) B2022839
theorem B3412955 : Blo 1346992 3412955 := bstep (se 1 (by rfl) ⟨2559716, by rfl⟩ : syracuseStep 3412955 = 5119433) B5119433
theorem B1348583 : Blo 1346992 1348583 := bstep (se 1 (by rfl) ⟨1011437, by rfl⟩ : syracuseStep 1348583 = 2022875) B2022875
theorem B6821009 : Blo 1346992 6821009 := bstep (se 2 (by rfl) ⟨2557878, by rfl⟩ : syracuseStep 6821009 = 5115757) B5115757
theorem B11834525 : Blo 1346992 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B6829271 : Blo 1346992 6829271 := bstep (se 1 (by rfl) ⟨5121953, by rfl⟩ : syracuseStep 6829271 = 10243907) B10243907
theorem B2020571 : Blo 1346992 2020571 := bstep (se 1 (by rfl) ⟨1515428, by rfl⟩ : syracuseStep 2020571 = 3030857) B3030857
theorem B4551929 : Blo 1346992 4551929 := bstep (se 2 (by rfl) ⟨1706973, by rfl⟩ : syracuseStep 4551929 = 3413947) B3413947
theorem B3413279 : Blo 1346992 3413279 := bstep (se 1 (by rfl) ⟨2559959, by rfl⟩ : syracuseStep 3413279 = 5119919) B5119919
theorem B1348895 : Blo 1346992 1348895 := bstep (se 1 (by rfl) ⟨1011671, by rfl⟩ : syracuseStep 1348895 = 2023343) B2023343
theorem B1348955 : Blo 1346992 1348955 := bstep (se 1 (by rfl) ⟨1011716, by rfl⟩ : syracuseStep 1348955 = 2023433) B2023433
theorem B1348975 : Blo 1346992 1348975 := bstep (se 1 (by rfl) ⟨1011731, by rfl⟩ : syracuseStep 1348975 = 2023463) B2023463
theorem B2020745 : Blo 1346992 2020745 := bstep (se 2 (by rfl) ⟨757779, by rfl⟩ : syracuseStep 2020745 = 1515559) B1515559
theorem B5756321 : Blo 1346992 5756321 := bstep (se 2 (by rfl) ⟨2158620, by rfl⟩ : syracuseStep 5756321 = 4317241) B4317241
theorem B3839393 : Blo 1346992 3839393 := bstep (se 2 (by rfl) ⟨1439772, by rfl⟩ : syracuseStep 3839393 = 2879545) B2879545
theorem B2880929 : Blo 1346992 2880929 := bstep (se 2 (by rfl) ⟨1080348, by rfl⟩ : syracuseStep 2880929 = 2160697) B2160697
theorem B4552199 : Blo 1346992 4552199 := bstep (se 1 (by rfl) ⟨3414149, by rfl⟩ : syracuseStep 4552199 = 6828299) B6828299
theorem B2021099 : Blo 1346992 2021099 := bstep (se 1 (by rfl) ⟨1515824, by rfl⟩ : syracuseStep 2021099 = 3031649) B3031649
theorem B7288631 : Blo 1346992 7288631 := bstep (se 1 (by rfl) ⟨5466473, by rfl⟩ : syracuseStep 7288631 = 10932947) B10932947
theorem B3643193 : Blo 1346992 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B3839849 : Blo 1346992 3839849 := bstep (se 2 (by rfl) ⟨1439943, by rfl⟩ : syracuseStep 3839849 = 2879887) B2879887
theorem B2021327 : Blo 1346992 2021327 := bstep (se 1 (by rfl) ⟨1515995, by rfl⟩ : syracuseStep 2021327 = 3031991) B3031991
theorem B7288805 : Blo 1346992 7288805 := bstep (se 4 (by rfl) ⟨683325, by rfl⟩ : syracuseStep 7288805 = 1366651) B1366651
theorem B24942755 : Blo 1346992 24942755 := bstep (se 1 (by rfl) ⟨18707066, by rfl⟩ : syracuseStep 24942755 = 37414133) B37414133
theorem B3840281 : Blo 1346992 3840281 := bstep (se 2 (by rfl) ⟨1440105, by rfl⟩ : syracuseStep 3840281 = 2880211) B2880211
theorem B1366303 : Blo 1346992 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B2021723 : Blo 1346992 2021723 := bstep (se 1 (by rfl) ⟨1516292, by rfl⟩ : syracuseStep 2021723 = 3032585) B3032585
theorem B3414383 : Blo 1346992 3414383 := bstep (se 1 (by rfl) ⟨2560787, by rfl⟩ : syracuseStep 3414383 = 5121575) B5121575
theorem B531650951 : Blo 1346992 531650951 := bstep (se 1 (by rfl) ⟨398738213, by rfl⟩ : syracuseStep 531650951 = 797476427) B797476427
theorem B8641019 : Blo 1346992 8641019 := bstep (se 1 (by rfl) ⟨6480764, by rfl⟩ : syracuseStep 8641019 = 12961529) B12961529
theorem B2021951 : Blo 1346992 2021951 := bstep (se 1 (by rfl) ⟨1516463, by rfl⟩ : syracuseStep 2021951 = 3032927) B3032927
theorem B15358571 : Blo 1346992 15358571 := bstep (se 1 (by rfl) ⟨11518928, by rfl⟩ : syracuseStep 15358571 = 23037857) B23037857
theorem B2022071 : Blo 1346992 2022071 := bstep (se 1 (by rfl) ⟨1516553, by rfl⟩ : syracuseStep 2022071 = 3033107) B3033107
theorem B5118659 : Blo 1346992 5118659 := bstep (se 1 (by rfl) ⟨3838994, by rfl⟩ : syracuseStep 5118659 = 7677989) B7677989
theorem B116562725 : Blo 1346992 116562725 := bstep (se 4 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 116562725 = 21855511) B21855511
theorem B2022299 : Blo 1346992 2022299 := bstep (se 1 (by rfl) ⟨1516724, by rfl⟩ : syracuseStep 2022299 = 3033449) B3033449
theorem B18447277 : Blo 1346992 18447277 := bstep (se 3 (by rfl) ⟨3458864, by rfl⟩ : syracuseStep 18447277 = 6917729) B6917729
theorem B32816177 : Blo 1346992 32816177 := bstep (se 2 (by rfl) ⟨12306066, by rfl⟩ : syracuseStep 32816177 = 24612133) B24612133
theorem B4922491 : Blo 1346992 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B224386199 : Blo 1346992 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B5258429 : Blo 1346992 5258429 := bstep (se 3 (by rfl) ⟨985955, by rfl⟩ : syracuseStep 5258429 = 1971911) B1971911
theorem B2022695 : Blo 1346992 2022695 := bstep (se 1 (by rfl) ⟨1517021, by rfl⟩ : syracuseStep 2022695 = 3034043) B3034043
theorem B4857185 : Blo 1346992 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B2022779 : Blo 1346992 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B7282057 : Blo 1346992 7282057 := bstep (se 2 (by rfl) ⟨2730771, by rfl⟩ : syracuseStep 7282057 = 5461543) B5461543
theorem B4316615 : Blo 1346992 4316615 := bstep (se 1 (by rfl) ⟨3237461, by rfl⟩ : syracuseStep 4316615 = 6474923) B6474923
theorem B25927127 : Blo 1346992 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B7290361 : Blo 1346992 7290361 := bstep (se 2 (by rfl) ⟨2733885, by rfl⟩ : syracuseStep 7290361 = 5467771) B5467771
theorem B2022905 : Blo 1346992 2022905 := bstep (se 2 (by rfl) ⟨758589, by rfl⟩ : syracuseStep 2022905 = 1517179) B1517179
theorem B6823439 : Blo 1346992 6823439 := bstep (se 1 (by rfl) ⟨5117579, by rfl⟩ : syracuseStep 6823439 = 10235159) B10235159
theorem B2023007 : Blo 1346992 2023007 := bstep (se 1 (by rfl) ⟨1517255, by rfl⟩ : syracuseStep 2023007 = 3034511) B3034511
theorem B3030839 : Blo 1346992 3030839 := bstep (se 1 (by rfl) ⟨2273129, by rfl⟩ : syracuseStep 3030839 = 4546259) B4546259
theorem B2023223 : Blo 1346992 2023223 := bstep (se 1 (by rfl) ⟨1517417, by rfl⟩ : syracuseStep 2023223 = 3034835) B3034835
theorem B7675823 : Blo 1346992 7675823 := bstep (se 1 (by rfl) ⟨5756867, by rfl⟩ : syracuseStep 7675823 = 11513735) B11513735
theorem B3031271 : Blo 1346992 3031271 := bstep (se 1 (by rfl) ⟨2273453, by rfl⟩ : syracuseStep 3031271 = 4546907) B4546907
theorem B15343991 : Blo 1346992 15343991 := bstep (se 1 (by rfl) ⟨11507993, by rfl⟩ : syracuseStep 15343991 = 23015987) B23015987
theorem B7676279 : Blo 1346992 7676279 := bstep (se 1 (by rfl) ⟨5757209, by rfl⟩ : syracuseStep 7676279 = 11514419) B11514419
theorem B4547015 : Blo 1346992 4547015 := bstep (se 1 (by rfl) ⟨3410261, by rfl⟩ : syracuseStep 4547015 = 6820523) B6820523
theorem B8643145 : Blo 1346992 8643145 := bstep (se 2 (by rfl) ⟨3241179, by rfl⟩ : syracuseStep 8643145 = 6482359) B6482359
theorem B8192609 : Blo 1346992 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B1516135 : Blo 1346992 1516135 := bstep (se 1 (by rfl) ⟨1137101, by rfl⟩ : syracuseStep 1516135 = 2274203) B2274203
theorem B4547339 : Blo 1346992 4547339 := bstep (se 1 (by rfl) ⟨3410504, by rfl⟩ : syracuseStep 4547339 = 6821009) B6821009
theorem B7889683 : Blo 1346992 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B3031865 : Blo 1346992 3031865 := bstep (se 2 (by rfl) ⟨1136949, by rfl⟩ : syracuseStep 3031865 = 2273899) B2273899
theorem B3031919 : Blo 1346992 3031919 := bstep (se 1 (by rfl) ⟨2273939, by rfl⟩ : syracuseStep 3031919 = 4547879) B4547879
theorem B12952493 : Blo 1346992 12952493 := bstep (se 3 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 12952493 = 4857185) B4857185
theorem B4547609 : Blo 1346992 4547609 := bstep (se 2 (by rfl) ⟨1705353, by rfl⟩ : syracuseStep 4547609 = 3410707) B3410707
theorem B4859087 : Blo 1346992 4859087 := bstep (se 1 (by rfl) ⟨3644315, by rfl⟩ : syracuseStep 4859087 = 7288631) B7288631
theorem B4859203 : Blo 1346992 4859203 := bstep (se 1 (by rfl) ⟨3644402, by rfl⟩ : syracuseStep 4859203 = 7288805) B7288805
theorem B3032495 : Blo 1346992 3032495 := bstep (se 1 (by rfl) ⟨2274371, by rfl⟩ : syracuseStep 3032495 = 4548743) B4548743
theorem B6563321 : Blo 1346992 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B6317689 : Blo 1346992 6317689 := bstep (se 2 (by rfl) ⟨2369133, by rfl⟩ : syracuseStep 6317689 = 4738267) B4738267
theorem B4548257 : Blo 1346992 4548257 := bstep (se 2 (by rfl) ⟨1705596, by rfl⟩ : syracuseStep 4548257 = 3411193) B3411193
theorem B5760679 : Blo 1346992 5760679 := bstep (se 1 (by rfl) ⟨4320509, by rfl⟩ : syracuseStep 5760679 = 8641019) B8641019
theorem B2557727 : Blo 1346992 2557727 := bstep (se 1 (by rfl) ⟨1918295, by rfl⟩ : syracuseStep 2557727 = 3836591) B3836591
theorem B9709409 : Blo 1346992 9709409 := bstep (se 2 (by rfl) ⟨3641028, by rfl⟩ : syracuseStep 9709409 = 7282057) B7282057
theorem B4614089 : Blo 1346992 4614089 := bstep (se 2 (by rfl) ⟨1730283, by rfl⟩ : syracuseStep 4614089 = 3460567) B3460567
theorem B3033323 : Blo 1346992 3033323 := bstep (se 1 (by rfl) ⟨2274992, by rfl⟩ : syracuseStep 3033323 = 4549985) B4549985
theorem B2877743 : Blo 1346992 2877743 := bstep (se 1 (by rfl) ⟨2158307, by rfl⟩ : syracuseStep 2877743 = 4316615) B4316615
theorem B4548959 : Blo 1346992 4548959 := bstep (se 1 (by rfl) ⟨3411719, by rfl⟩ : syracuseStep 4548959 = 6823439) B6823439
theorem B3836317 : Blo 1346992 3836317 := bstep (se 3 (by rfl) ⟨719309, by rfl⟩ : syracuseStep 3836317 = 1438619) B1438619
theorem B4549121 : Blo 1346992 4549121 := bstep (se 2 (by rfl) ⟨1705920, by rfl⟩ : syracuseStep 4549121 = 3411841) B3411841
theorem B3836443 : Blo 1346992 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B4860587 : Blo 1346992 4860587 := bstep (se 1 (by rfl) ⟨3645440, by rfl⟩ : syracuseStep 4860587 = 7290881) B7290881
theorem B6826679 : Blo 1346992 6826679 := bstep (se 1 (by rfl) ⟨5120009, by rfl⟩ : syracuseStep 6826679 = 10240019) B10240019
theorem B63073079 : Blo 1346992 63073079 := bstep (se 1 (by rfl) ⟨47304809, by rfl⟩ : syracuseStep 63073079 = 94609619) B94609619
theorem B4549607 : Blo 1346992 4549607 := bstep (se 1 (by rfl) ⟨3412205, by rfl⟩ : syracuseStep 4549607 = 6824411) B6824411
theorem B1821737 : Blo 1346992 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B4549931 : Blo 1346992 4549931 := bstep (se 1 (by rfl) ⟨3412448, by rfl⟩ : syracuseStep 4549931 = 6824897) B6824897
theorem B7679447 : Blo 1346992 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B1347047 : Blo 1346992 1347047 := bstep (se 1 (by rfl) ⟨1010285, by rfl⟩ : syracuseStep 1347047 = 2020571) B2020571
theorem B3034619 : Blo 1346992 3034619 := bstep (se 1 (by rfl) ⟨2275964, by rfl⟩ : syracuseStep 3034619 = 4551929) B4551929
theorem B4550201 : Blo 1346992 4550201 := bstep (se 2 (by rfl) ⟨1706325, by rfl⟩ : syracuseStep 4550201 = 3412651) B3412651
theorem B1347163 : Blo 1346992 1347163 := bstep (se 1 (by rfl) ⟨1010372, by rfl⟩ : syracuseStep 1347163 = 2020745) B2020745
theorem B3837547 : Blo 1346992 3837547 := bstep (se 1 (by rfl) ⟨2878160, by rfl⟩ : syracuseStep 3837547 = 5756321) B5756321
theorem B2559595 : Blo 1346992 2559595 := bstep (se 1 (by rfl) ⟨1919696, by rfl⟩ : syracuseStep 2559595 = 3839393) B3839393
theorem B1920619 : Blo 1346992 1920619 := bstep (se 1 (by rfl) ⟨1440464, by rfl⟩ : syracuseStep 1920619 = 2880929) B2880929
theorem B3034799 : Blo 1346992 3034799 := bstep (se 1 (by rfl) ⟨2276099, by rfl⟩ : syracuseStep 3034799 = 4552199) B4552199
theorem B1347399 : Blo 1346992 1347399 := bstep (se 1 (by rfl) ⟨1010549, by rfl⟩ : syracuseStep 1347399 = 2021099) B2021099
theorem B2428795 : Blo 1346992 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B4321163 : Blo 1346992 4321163 := bstep (se 1 (by rfl) ⟨3240872, by rfl⟩ : syracuseStep 4321163 = 6481745) B6481745
theorem B24596369 : Blo 1346992 24596369 := bstep (se 2 (by rfl) ⟨9223638, by rfl⟩ : syracuseStep 24596369 = 18447277) B18447277
theorem B2559899 : Blo 1346992 2559899 := bstep (se 1 (by rfl) ⟨1919924, by rfl⟩ : syracuseStep 2559899 = 3839849) B3839849
theorem B1347551 : Blo 1346992 1347551 := bstep (se 1 (by rfl) ⟨1010663, by rfl⟩ : syracuseStep 1347551 = 2021327) B2021327
theorem B2273467 : Blo 1346992 2273467 := bstep (se 1 (by rfl) ⟨1705100, by rfl⟩ : syracuseStep 2273467 = 3410201) B3410201
theorem B2560187 : Blo 1346992 2560187 := bstep (se 1 (by rfl) ⟨1920140, by rfl⟩ : syracuseStep 2560187 = 3840281) B3840281
theorem B1347815 : Blo 1346992 1347815 := bstep (se 1 (by rfl) ⟨1010861, by rfl⟩ : syracuseStep 1347815 = 2021723) B2021723
theorem B2306279 : Blo 1346992 2306279 := bstep (se 1 (by rfl) ⟨1729709, by rfl⟩ : syracuseStep 2306279 = 3459419) B3459419
theorem B2158903 : Blo 1346992 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B26276183 : Blo 1346992 26276183 := bstep (se 1 (by rfl) ⟨19707137, by rfl⟩ : syracuseStep 26276183 = 39414275) B39414275
theorem B2273663 : Blo 1346992 2273663 := bstep (se 1 (by rfl) ⟨1705247, by rfl⟩ : syracuseStep 2273663 = 3410495) B3410495
theorem B1347967 : Blo 1346992 1347967 := bstep (se 1 (by rfl) ⟨1010975, by rfl⟩ : syracuseStep 1347967 = 2021951) B2021951
theorem B1348047 : Blo 1346992 1348047 := bstep (se 1 (by rfl) ⟨1011035, by rfl⟩ : syracuseStep 1348047 = 2022071) B2022071
theorem B1946063 : Blo 1346992 1946063 := bstep (se 1 (by rfl) ⟨1459547, by rfl⟩ : syracuseStep 1946063 = 2919095) B2919095
theorem B3412439 : Blo 1346992 3412439 := bstep (se 1 (by rfl) ⟨2559329, by rfl⟩ : syracuseStep 3412439 = 5118659) B5118659
theorem B1348199 : Blo 1346992 1348199 := bstep (se 1 (by rfl) ⟨1011149, by rfl⟩ : syracuseStep 1348199 = 2022299) B2022299
theorem B9720481 : Blo 1346992 9720481 := bstep (se 2 (by rfl) ⟨3645180, by rfl⟩ : syracuseStep 9720481 = 7290361) B7290361
theorem B2560673 : Blo 1346992 2560673 := bstep (se 2 (by rfl) ⟨960252, by rfl⟩ : syracuseStep 2560673 = 1920505) B1920505
theorem B21877451 : Blo 1346992 21877451 := bstep (se 1 (by rfl) ⟨16408088, by rfl⟩ : syracuseStep 21877451 = 32816177) B32816177
theorem B149590799 : Blo 1346992 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B2274095 : Blo 1346992 2274095 := bstep (se 1 (by rfl) ⟨1705571, by rfl⟩ : syracuseStep 2274095 = 3411143) B3411143
theorem B1348463 : Blo 1346992 1348463 := bstep (se 1 (by rfl) ⟨1011347, by rfl⟩ : syracuseStep 1348463 = 2022695) B2022695
theorem B1348519 : Blo 1346992 1348519 := bstep (se 1 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 1348519 = 2022779) B2022779
theorem B1348603 : Blo 1346992 1348603 := bstep (se 1 (by rfl) ⟨1011452, by rfl⟩ : syracuseStep 1348603 = 2022905) B2022905
theorem B1348671 : Blo 1346992 1348671 := bstep (se 1 (by rfl) ⟨1011503, by rfl⟩ : syracuseStep 1348671 = 2023007) B2023007
theorem B2159723 : Blo 1346992 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B2020559 : Blo 1346992 2020559 := bstep (se 1 (by rfl) ⟨1515419, by rfl⟩ : syracuseStep 2020559 = 3030839) B3030839
theorem B1348815 : Blo 1346992 1348815 := bstep (se 1 (by rfl) ⟨1011611, by rfl⟩ : syracuseStep 1348815 = 2023223) B2023223
theorem B5117215 : Blo 1346992 5117215 := bstep (se 1 (by rfl) ⟨3837911, by rfl⟩ : syracuseStep 5117215 = 7675823) B7675823
theorem B2020763 : Blo 1346992 2020763 := bstep (se 1 (by rfl) ⟨1515572, by rfl⟩ : syracuseStep 2020763 = 3031145) B3031145
theorem B4552091 : Blo 1346992 4552091 := bstep (se 1 (by rfl) ⟨3414068, by rfl⟩ : syracuseStep 4552091 = 6828137) B6828137
theorem B5461613 : Blo 1346992 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B2020985 : Blo 1346992 2020985 := bstep (se 2 (by rfl) ⟨757869, by rfl⟩ : syracuseStep 2020985 = 1515739) B1515739
theorem B23033483 : Blo 1346992 23033483 := bstep (se 1 (by rfl) ⟨17275112, by rfl⟩ : syracuseStep 23033483 = 34550225) B34550225
theorem B4101803 : Blo 1346992 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B7780049 : Blo 1346992 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B2021087 : Blo 1346992 2021087 := bstep (se 1 (by rfl) ⟨1515815, by rfl⟩ : syracuseStep 2021087 = 3031631) B3031631
theorem B2275067 : Blo 1346992 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B2021183 : Blo 1346992 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B9222025 : Blo 1346992 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B3413897 : Blo 1346992 3413897 := bstep (se 2 (by rfl) ⟨1280211, by rfl⟩ : syracuseStep 3413897 = 2560423) B2560423
theorem B3643355 : Blo 1346992 3643355 := bstep (se 1 (by rfl) ⟨2732516, by rfl⟩ : syracuseStep 3643355 = 5465033) B5465033
theorem B2021351 : Blo 1346992 2021351 := bstep (se 1 (by rfl) ⟨1516013, by rfl⟩ : syracuseStep 2021351 = 3032027) B3032027
theorem B5756903 : Blo 1346992 5756903 := bstep (se 1 (by rfl) ⟨4317677, by rfl⟩ : syracuseStep 5756903 = 8635355) B8635355
theorem B2275303 : Blo 1346992 2275303 := bstep (se 1 (by rfl) ⟨1706477, by rfl⟩ : syracuseStep 2275303 = 3412955) B3412955
theorem B2021369 : Blo 1346992 2021369 := bstep (se 2 (by rfl) ⟨758013, by rfl⟩ : syracuseStep 2021369 = 1516027) B1516027
theorem B4855801 : Blo 1346992 4855801 := bstep (se 2 (by rfl) ⟨1820925, by rfl⟩ : syracuseStep 4855801 = 3641851) B3641851
theorem B2021471 : Blo 1346992 2021471 := bstep (se 1 (by rfl) ⟨1516103, by rfl⟩ : syracuseStep 2021471 = 3032207) B3032207
theorem B4552847 : Blo 1346992 4552847 := bstep (se 1 (by rfl) ⟨3414635, by rfl⟩ : syracuseStep 4552847 = 6829271) B6829271
theorem B2021531 : Blo 1346992 2021531 := bstep (se 1 (by rfl) ⟨1516148, by rfl⟩ : syracuseStep 2021531 = 3032297) B3032297
theorem B2021567 : Blo 1346992 2021567 := bstep (se 1 (by rfl) ⟨1516175, by rfl⟩ : syracuseStep 2021567 = 3032351) B3032351
theorem B2275519 : Blo 1346992 2275519 := bstep (se 1 (by rfl) ⟨1706639, by rfl⟩ : syracuseStep 2275519 = 3413279) B3413279
theorem B2021609 : Blo 1346992 2021609 := bstep (se 2 (by rfl) ⟨758103, by rfl⟩ : syracuseStep 2021609 = 1516207) B1516207
theorem B2021915 : Blo 1346992 2021915 := bstep (se 1 (by rfl) ⟨1516436, by rfl⟩ : syracuseStep 2021915 = 3032873) B3032873
theorem B2021993 : Blo 1346992 2021993 := bstep (se 2 (by rfl) ⟨758247, by rfl⟩ : syracuseStep 2021993 = 1516495) B1516495
theorem B16628503 : Blo 1346992 16628503 := bstep (se 1 (by rfl) ⟨12471377, by rfl⟩ : syracuseStep 16628503 = 24942755) B24942755
theorem B3840851 : Blo 1346992 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B2276255 : Blo 1346992 2276255 := bstep (se 1 (by rfl) ⟨1707191, by rfl⟩ : syracuseStep 2276255 = 3414383) B3414383
theorem B354433967 : Blo 1346992 354433967 := bstep (se 1 (by rfl) ⟨265825475, by rfl⟩ : syracuseStep 354433967 = 531650951) B531650951
theorem B8641505 : Blo 1346992 8641505 := bstep (se 2 (by rfl) ⟨3240564, by rfl⟩ : syracuseStep 8641505 = 6481129) B6481129
theorem B10239047 : Blo 1346992 10239047 := bstep (se 1 (by rfl) ⟨7679285, by rfl⟩ : syracuseStep 10239047 = 15358571) B15358571
theorem B2022521 : Blo 1346992 2022521 := bstep (se 2 (by rfl) ⟨758445, by rfl⟩ : syracuseStep 2022521 = 1516891) B1516891
theorem B77708483 : Blo 1346992 77708483 := bstep (se 1 (by rfl) ⟨58281362, by rfl⟩ : syracuseStep 77708483 = 116562725) B116562725
theorem B2022623 : Blo 1346992 2022623 := bstep (se 1 (by rfl) ⟨1516967, by rfl⟩ : syracuseStep 2022623 = 3033935) B3033935
theorem B2022665 : Blo 1346992 2022665 := bstep (se 2 (by rfl) ⟨758499, by rfl⟩ : syracuseStep 2022665 = 1516999) B1516999
theorem B11509087 : Blo 1346992 11509087 := bstep (se 1 (by rfl) ⟨8631815, by rfl⟩ : syracuseStep 11509087 = 17263631) B17263631
theorem B5758303 : Blo 1346992 5758303 := bstep (se 1 (by rfl) ⟨4318727, by rfl⟩ : syracuseStep 5758303 = 8637455) B8637455
theorem B2022767 : Blo 1346992 2022767 := bstep (se 1 (by rfl) ⟨1517075, by rfl⟩ : syracuseStep 2022767 = 3034151) B3034151
theorem B3505619 : Blo 1346992 3505619 := bstep (se 1 (by rfl) ⟨2629214, by rfl⟩ : syracuseStep 3505619 = 5258429) B5258429
theorem B10231271 : Blo 1346992 10231271 := bstep (se 1 (by rfl) ⟨7673453, by rfl⟩ : syracuseStep 10231271 = 15346907) B15346907
theorem B5119463 : Blo 1346992 5119463 := bstep (se 1 (by rfl) ⟨3839597, by rfl⟩ : syracuseStep 5119463 = 7679195) B7679195
theorem B2022887 : Blo 1346992 2022887 := bstep (se 1 (by rfl) ⟨1517165, by rfl⟩ : syracuseStep 2022887 = 3034331) B3034331
theorem B2023019 : Blo 1346992 2023019 := bstep (se 1 (by rfl) ⟨1517264, by rfl⟩ : syracuseStep 2023019 = 3034529) B3034529
theorem B17284751 : Blo 1346992 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B2023145 : Blo 1346992 2023145 := bstep (se 2 (by rfl) ⟨758679, by rfl⟩ : syracuseStep 2023145 = 1517359) B1517359
theorem B2023289 : Blo 1346992 2023289 := bstep (se 2 (by rfl) ⟨758733, by rfl⟩ : syracuseStep 2023289 = 1517467) B1517467
theorem B4546475 : Blo 1346992 4546475 := bstep (se 1 (by rfl) ⟨3409856, by rfl⟩ : syracuseStep 4546475 = 6819713) B6819713
theorem B14565329 : Blo 1346992 14565329 := bstep (se 2 (by rfl) ⟨5461998, by rfl⟩ : syracuseStep 14565329 = 10923997) B10923997
theorem B1515487 : Blo 1346992 1515487 := bstep (se 1 (by rfl) ⟨1136615, by rfl⟩ : syracuseStep 1515487 = 2273231) B2273231
theorem B2023391 : Blo 1346992 2023391 := bstep (se 1 (by rfl) ⟨1517543, by rfl⟩ : syracuseStep 2023391 = 3035087) B3035087
theorem B4857965 : Blo 1346992 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B3031289 : Blo 1346992 3031289 := bstep (se 2 (by rfl) ⟨1136733, by rfl⟩ : syracuseStep 3031289 = 2273467) B2273467
theorem B1515775 : Blo 1346992 1515775 := bstep (se 1 (by rfl) ⟨1136831, by rfl⟩ : syracuseStep 1515775 = 2273663) B2273663
theorem B5759261 : Blo 1346992 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B3031343 : Blo 1346992 3031343 := bstep (se 1 (by rfl) ⟨2273507, by rfl⟩ : syracuseStep 3031343 = 4547015) B4547015
theorem B3031559 : Blo 1346992 3031559 := bstep (se 1 (by rfl) ⟨2273669, by rfl⟩ : syracuseStep 3031559 = 4547339) B4547339
theorem B1516063 : Blo 1346992 1516063 := bstep (se 1 (by rfl) ⟨1137047, by rfl⟩ : syracuseStep 1516063 = 2274095) B2274095
theorem B8634995 : Blo 1346992 8634995 := bstep (se 1 (by rfl) ⟨6476246, by rfl⟩ : syracuseStep 8634995 = 12952493) B12952493
theorem B3031739 : Blo 1346992 3031739 := bstep (se 1 (by rfl) ⟨2273804, by rfl⟩ : syracuseStep 3031739 = 4547609) B4547609
theorem B12960641 : Blo 1346992 12960641 := bstep (se 2 (by rfl) ⟨4860240, by rfl⟩ : syracuseStep 12960641 = 9720481) B9720481
theorem B4375547 : Blo 1346992 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B10519577 : Blo 1346992 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B3032171 : Blo 1346992 3032171 := bstep (se 1 (by rfl) ⟨2274128, by rfl⟩ : syracuseStep 3032171 = 4548257) B4548257
theorem B5186699 : Blo 1346992 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B1516711 : Blo 1346992 1516711 := bstep (se 1 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 1516711 = 2275067) B2275067
theorem B1705151 : Blo 1346992 1705151 := bstep (se 1 (by rfl) ⟨1278863, by rfl⟩ : syracuseStep 1705151 = 2557727) B2557727
theorem B9348317 : Blo 1346992 9348317 := bstep (se 3 (by rfl) ⟨1752809, by rfl⟩ : syracuseStep 9348317 = 3505619) B3505619
theorem B1918495 : Blo 1346992 1918495 := bstep (se 1 (by rfl) ⟨1438871, by rfl⟩ : syracuseStep 1918495 = 2877743) B2877743
theorem B3032639 : Blo 1346992 3032639 := bstep (se 1 (by rfl) ⟨2274479, by rfl⟩ : syracuseStep 3032639 = 4548959) B4548959
theorem B3032747 : Blo 1346992 3032747 := bstep (se 1 (by rfl) ⟨2274560, by rfl⟩ : syracuseStep 3032747 = 4549121) B4549121
theorem B12961565 : Blo 1346992 12961565 := bstep (se 3 (by rfl) ⟨2430293, by rfl⟩ : syracuseStep 12961565 = 4860587) B4860587
theorem B15345449 : Blo 1346992 15345449 := bstep (se 2 (by rfl) ⟨5754543, by rfl⟩ : syracuseStep 15345449 = 11509087) B11509087
theorem B7677737 : Blo 1346992 7677737 := bstep (se 2 (by rfl) ⟨2879151, by rfl⟩ : syracuseStep 7677737 = 5758303) B5758303
theorem B1517503 : Blo 1346992 1517503 := bstep (se 1 (by rfl) ⟨1138127, by rfl⟩ : syracuseStep 1517503 = 2276255) B2276255
theorem B5761003 : Blo 1346992 5761003 := bstep (se 1 (by rfl) ⟨4320752, by rfl⟩ : syracuseStep 5761003 = 8641505) B8641505
theorem B3033071 : Blo 1346992 3033071 := bstep (se 1 (by rfl) ⟨2274803, by rfl⟩ : syracuseStep 3033071 = 4549607) B4549607
theorem B6826031 : Blo 1346992 6826031 := bstep (se 1 (by rfl) ⟨5119523, by rfl⟩ : syracuseStep 6826031 = 10239047) B10239047
theorem B8423585 : Blo 1346992 8423585 := bstep (se 2 (by rfl) ⟨3158844, by rfl⟩ : syracuseStep 8423585 = 6317689) B6317689
theorem B3033287 : Blo 1346992 3033287 := bstep (se 1 (by rfl) ⟨2274965, by rfl⟩ : syracuseStep 3033287 = 4549931) B4549931
theorem B3033467 : Blo 1346992 3033467 := bstep (se 1 (by rfl) ⟨2275100, by rfl⟩ : syracuseStep 3033467 = 4550201) B4550201
theorem B3238393 : Blo 1346992 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B1706599 : Blo 1346992 1706599 := bstep (se 1 (by rfl) ⟨1279949, by rfl⟩ : syracuseStep 1706599 = 2559899) B2559899
theorem B3033737 : Blo 1346992 3033737 := bstep (se 2 (by rfl) ⟨1137651, by rfl⟩ : syracuseStep 3033737 = 2275303) B2275303
theorem B9710219 : Blo 1346992 9710219 := bstep (se 1 (by rfl) ⟨7282664, by rfl⟩ : syracuseStep 9710219 = 14565329) B14565329
theorem B6474401 : Blo 1346992 6474401 := bstep (se 2 (by rfl) ⟨2427900, by rfl⟩ : syracuseStep 6474401 = 4855801) B4855801
theorem B17517455 : Blo 1346992 17517455 := bstep (se 1 (by rfl) ⟨13138091, by rfl⟩ : syracuseStep 17517455 = 26276183) B26276183
theorem B3034025 : Blo 1346992 3034025 := bstep (se 2 (by rfl) ⟨1137759, by rfl⟩ : syracuseStep 3034025 = 2275519) B2275519
theorem B2878537 : Blo 1346992 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B14584967 : Blo 1346992 14584967 := bstep (se 1 (by rfl) ⟨10938725, by rfl⟩ : syracuseStep 14584967 = 21877451) B21877451
theorem B6827165 : Blo 1346992 6827165 := bstep (se 3 (by rfl) ⟨1280093, by rfl⟩ : syracuseStep 6827165 = 2560187) B2560187
theorem B5115089 : Blo 1346992 5115089 := bstep (se 2 (by rfl) ⟨1918158, by rfl⟩ : syracuseStep 5115089 = 3836317) B3836317
theorem B5115257 : Blo 1346992 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B1347039 : Blo 1346992 1347039 := bstep (se 1 (by rfl) ⟨1010279, by rfl⟩ : syracuseStep 1347039 = 2020559) B2020559
theorem B1347175 : Blo 1346992 1347175 := bstep (se 1 (by rfl) ⟨1010381, by rfl⟩ : syracuseStep 1347175 = 2020763) B2020763
theorem B3034727 : Blo 1346992 3034727 := bstep (se 1 (by rfl) ⟨2276045, by rfl⟩ : syracuseStep 3034727 = 4552091) B4552091
theorem B22171337 : Blo 1346992 22171337 := bstep (se 2 (by rfl) ⟨8314251, by rfl⟩ : syracuseStep 22171337 = 16628503) B16628503
theorem B3641075 : Blo 1346992 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B1347323 : Blo 1346992 1347323 := bstep (se 1 (by rfl) ⟨1010492, by rfl⟩ : syracuseStep 1347323 = 2020985) B2020985
theorem B15355655 : Blo 1346992 15355655 := bstep (se 1 (by rfl) ⟨11516741, by rfl⟩ : syracuseStep 15355655 = 23033483) B23033483
theorem B1347391 : Blo 1346992 1347391 := bstep (se 1 (by rfl) ⟨1010543, by rfl⟩ : syracuseStep 1347391 = 2021087) B2021087
theorem B5189501 : Blo 1346992 5189501 := bstep (se 3 (by rfl) ⟨973031, by rfl⟩ : syracuseStep 5189501 = 1946063) B1946063
theorem B1347455 : Blo 1346992 1347455 := bstep (se 1 (by rfl) ⟨1010591, by rfl⟩ : syracuseStep 1347455 = 2021183) B2021183
theorem B2428903 : Blo 1346992 2428903 := bstep (se 1 (by rfl) ⟨1821677, by rfl⟩ : syracuseStep 2428903 = 3643355) B3643355
theorem B1347567 : Blo 1346992 1347567 := bstep (se 1 (by rfl) ⟨1010675, by rfl⟩ : syracuseStep 1347567 = 2021351) B2021351
theorem B3837935 : Blo 1346992 3837935 := bstep (se 1 (by rfl) ⟨2878451, by rfl⟩ : syracuseStep 3837935 = 5756903) B5756903
theorem B1347579 : Blo 1346992 1347579 := bstep (se 1 (by rfl) ⟨1010684, by rfl⟩ : syracuseStep 1347579 = 2021369) B2021369
theorem B1347647 : Blo 1346992 1347647 := bstep (se 1 (by rfl) ⟨1010735, by rfl⟩ : syracuseStep 1347647 = 2021471) B2021471
theorem B3035231 : Blo 1346992 3035231 := bstep (se 1 (by rfl) ⟨2276423, by rfl⟩ : syracuseStep 3035231 = 4552847) B4552847
theorem B1347687 : Blo 1346992 1347687 := bstep (se 1 (by rfl) ⟨1010765, by rfl⟩ : syracuseStep 1347687 = 2021531) B2021531
theorem B1347711 : Blo 1346992 1347711 := bstep (se 1 (by rfl) ⟨1010783, by rfl⟩ : syracuseStep 1347711 = 2021567) B2021567
theorem B1347739 : Blo 1346992 1347739 := bstep (se 1 (by rfl) ⟨1010804, by rfl⟩ : syracuseStep 1347739 = 2021609) B2021609
theorem B1347943 : Blo 1346992 1347943 := bstep (se 1 (by rfl) ⟨1010957, by rfl⟩ : syracuseStep 1347943 = 2021915) B2021915
theorem B1347995 : Blo 1346992 1347995 := bstep (se 1 (by rfl) ⟨1010996, by rfl⟩ : syracuseStep 1347995 = 2021993) B2021993
theorem B6828461 : Blo 1346992 6828461 := bstep (se 3 (by rfl) ⟨1280336, by rfl⟩ : syracuseStep 6828461 = 2560673) B2560673
theorem B4551119 : Blo 1346992 4551119 := bstep (se 1 (by rfl) ⟨3413339, by rfl⟩ : syracuseStep 4551119 = 6826679) B6826679
theorem B2560567 : Blo 1346992 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B1348347 : Blo 1346992 1348347 := bstep (se 1 (by rfl) ⟨1011260, by rfl⟩ : syracuseStep 1348347 = 2022521) B2022521
theorem B5116729 : Blo 1346992 5116729 := bstep (se 2 (by rfl) ⟨1918773, by rfl⟩ : syracuseStep 5116729 = 3837547) B3837547
theorem B3412793 : Blo 1346992 3412793 := bstep (se 2 (by rfl) ⟨1279797, by rfl⟩ : syracuseStep 3412793 = 2559595) B2559595
theorem B2560825 : Blo 1346992 2560825 := bstep (se 2 (by rfl) ⟨960309, by rfl⟩ : syracuseStep 2560825 = 1920619) B1920619
theorem B1348415 : Blo 1346992 1348415 := bstep (se 1 (by rfl) ⟨1011311, by rfl⟩ : syracuseStep 1348415 = 2022623) B2022623
theorem B1348443 : Blo 1346992 1348443 := bstep (se 1 (by rfl) ⟨1011332, by rfl⟩ : syracuseStep 1348443 = 2022665) B2022665
theorem B7680905 : Blo 1346992 7680905 := bstep (se 2 (by rfl) ⟨2880339, by rfl⟩ : syracuseStep 7680905 = 5760679) B5760679
theorem B1348511 : Blo 1346992 1348511 := bstep (se 1 (by rfl) ⟨1011383, by rfl⟩ : syracuseStep 1348511 = 2022767) B2022767
theorem B25891757 : Blo 1346992 25891757 := bstep (se 3 (by rfl) ⟨4854704, by rfl⟩ : syracuseStep 25891757 = 9709409) B9709409
theorem B6820847 : Blo 1346992 6820847 := bstep (se 1 (by rfl) ⟨5115635, by rfl⟩ : syracuseStep 6820847 = 10231271) B10231271
theorem B3412975 : Blo 1346992 3412975 := bstep (se 1 (by rfl) ⟨2559731, by rfl⟩ : syracuseStep 3412975 = 5119463) B5119463
theorem B1348591 : Blo 1346992 1348591 := bstep (se 1 (by rfl) ⟨1011443, by rfl⟩ : syracuseStep 1348591 = 2022887) B2022887
theorem B1348679 : Blo 1346992 1348679 := bstep (se 1 (by rfl) ⟨1011509, by rfl⟩ : syracuseStep 1348679 = 2023019) B2023019
theorem B11523167 : Blo 1346992 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B1348763 : Blo 1346992 1348763 := bstep (se 1 (by rfl) ⟨1011572, by rfl⟩ : syracuseStep 1348763 = 2023145) B2023145
theorem B1348859 : Blo 1346992 1348859 := bstep (se 1 (by rfl) ⟨1011644, by rfl⟩ : syracuseStep 1348859 = 2023289) B2023289
theorem B2880775 : Blo 1346992 2880775 := bstep (se 1 (by rfl) ⟨2160581, by rfl⟩ : syracuseStep 2880775 = 4321163) B4321163
theorem B16397579 : Blo 1346992 16397579 := bstep (se 1 (by rfl) ⟨12298184, by rfl⟩ : syracuseStep 16397579 = 24596369) B24596369
theorem B2020649 : Blo 1346992 2020649 := bstep (se 2 (by rfl) ⟨757743, by rfl⟩ : syracuseStep 2020649 = 1515487) B1515487
theorem B1348927 : Blo 1346992 1348927 := bstep (se 1 (by rfl) ⟨1011695, by rfl⟩ : syracuseStep 1348927 = 2023391) B2023391
theorem B2020847 : Blo 1346992 2020847 := bstep (se 1 (by rfl) ⟨1515635, by rfl⟩ : syracuseStep 2020847 = 3031271) B3031271
theorem B10229327 : Blo 1346992 10229327 := bstep (se 1 (by rfl) ⟨7671995, by rfl⟩ : syracuseStep 10229327 = 15343991) B15343991
theorem B5117519 : Blo 1346992 5117519 := bstep (se 1 (by rfl) ⟨3838139, by rfl⟩ : syracuseStep 5117519 = 7676279) B7676279
theorem B2274959 : Blo 1346992 2274959 := bstep (se 1 (by rfl) ⟨1706219, by rfl⟩ : syracuseStep 2274959 = 3412439) B3412439
theorem B5461739 : Blo 1346992 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B99727199 : Blo 1346992 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B2021243 : Blo 1346992 2021243 := bstep (se 1 (by rfl) ⟨1515932, by rfl⟩ : syracuseStep 2021243 = 3031865) B3031865
theorem B12957565 : Blo 1346992 12957565 := bstep (se 3 (by rfl) ⟨2429543, by rfl⟩ : syracuseStep 12957565 = 4859087) B4859087
theorem B2021279 : Blo 1346992 2021279 := bstep (se 1 (by rfl) ⟨1515959, by rfl⟩ : syracuseStep 2021279 = 3031919) B3031919
theorem B6150077 : Blo 1346992 6150077 := bstep (se 3 (by rfl) ⟨1153139, by rfl⟩ : syracuseStep 6150077 = 2306279) B2306279
theorem B11524193 : Blo 1346992 11524193 := bstep (se 2 (by rfl) ⟨4321572, by rfl⟩ : syracuseStep 11524193 = 8643145) B8643145
theorem B2021513 : Blo 1346992 2021513 := bstep (se 2 (by rfl) ⟨758067, by rfl⟩ : syracuseStep 2021513 = 1516135) B1516135
theorem B2021663 : Blo 1346992 2021663 := bstep (se 1 (by rfl) ⟨1516247, by rfl⟩ : syracuseStep 2021663 = 3032495) B3032495
theorem B2734535 : Blo 1346992 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B2275931 : Blo 1346992 2275931 := bstep (se 1 (by rfl) ⟨1706948, by rfl⟩ : syracuseStep 2275931 = 3413897) B3413897
theorem B2022215 : Blo 1346992 2022215 := bstep (se 1 (by rfl) ⟨1516661, by rfl⟩ : syracuseStep 2022215 = 3033323) B3033323
theorem B6822953 : Blo 1346992 6822953 := bstep (se 2 (by rfl) ⟨2558607, by rfl⟩ : syracuseStep 6822953 = 5117215) B5117215
theorem B6478937 : Blo 1346992 6478937 := bstep (se 2 (by rfl) ⟨2429601, by rfl⟩ : syracuseStep 6478937 = 4859203) B4859203
theorem B42048719 : Blo 1346992 42048719 := bstep (se 1 (by rfl) ⟨31536539, by rfl⟩ : syracuseStep 42048719 = 63073079) B63073079
theorem B236289311 : Blo 1346992 236289311 := bstep (se 1 (by rfl) ⟨177216983, by rfl⟩ : syracuseStep 236289311 = 354433967) B354433967
theorem B51805655 : Blo 1346992 51805655 := bstep (se 1 (by rfl) ⟨38854241, by rfl⟩ : syracuseStep 51805655 = 77708483) B77708483
theorem B5119631 : Blo 1346992 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B2023079 : Blo 1346992 2023079 := bstep (se 1 (by rfl) ⟨1517309, by rfl⟩ : syracuseStep 2023079 = 3034619) B3034619
theorem B2023199 : Blo 1346992 2023199 := bstep (se 1 (by rfl) ⟨1517399, by rfl⟩ : syracuseStep 2023199 = 3034799) B3034799
theorem B12296033 : Blo 1346992 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B12304237 : Blo 1346992 12304237 := bstep (se 3 (by rfl) ⟨2307044, by rfl⟩ : syracuseStep 12304237 = 4614089) B4614089
theorem B3030983 : Blo 1346992 3030983 := bstep (se 1 (by rfl) ⟨2273237, by rfl⟩ : syracuseStep 3030983 = 4546475) B4546475
theorem B2023487 : Blo 1346992 2023487 := bstep (se 1 (by rfl) ⟨1517615, by rfl⟩ : syracuseStep 2023487 = 3035231) B3035231
theorem B4547069 : Blo 1346992 4547069 := bstep (se 3 (by rfl) ⟨852575, by rfl⟩ : syracuseStep 4547069 = 1705151) B1705151
theorem B5120603 : Blo 1346992 5120603 := bstep (se 1 (by rfl) ⟨3840452, by rfl⟩ : syracuseStep 5120603 = 7680905) B7680905
theorem B17261171 : Blo 1346992 17261171 := bstep (se 1 (by rfl) ⟨12945878, by rfl⟩ : syracuseStep 17261171 = 25891757) B25891757
theorem B4547231 : Blo 1346992 4547231 := bstep (se 1 (by rfl) ⟨3410423, by rfl⟩ : syracuseStep 4547231 = 6820847) B6820847
theorem B4317857 : Blo 1346992 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B2917031 : Blo 1346992 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B7013051 : Blo 1346992 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B3457799 : Blo 1346992 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B1516639 : Blo 1346992 1516639 := bstep (se 1 (by rfl) ⟨1137479, by rfl⟩ : syracuseStep 1516639 = 2274959) B2274959
theorem B1517287 : Blo 1346992 1517287 := bstep (se 1 (by rfl) ⟨1137965, by rfl⟩ : syracuseStep 1517287 = 2275931) B2275931
theorem B6473479 : Blo 1346992 6473479 := bstep (se 1 (by rfl) ⟨4855109, by rfl⟩ : syracuseStep 6473479 = 9710219) B9710219
theorem B4548635 : Blo 1346992 4548635 := bstep (se 1 (by rfl) ⟨3411476, by rfl⟩ : syracuseStep 4548635 = 6822953) B6822953
theorem B2557993 : Blo 1346992 2557993 := bstep (se 2 (by rfl) ⟨959247, by rfl⟩ : syracuseStep 2557993 = 1918495) B1918495
theorem B4319291 : Blo 1346992 4319291 := bstep (se 1 (by rfl) ⟨3239468, by rfl⟩ : syracuseStep 4319291 = 6478937) B6478937
theorem B3410059 : Blo 1346992 3410059 := bstep (se 1 (by rfl) ⟨2557544, by rfl⟩ : syracuseStep 3410059 = 5115089) B5115089
theorem B157526207 : Blo 1346992 157526207 := bstep (se 1 (by rfl) ⟨118144655, by rfl⟩ : syracuseStep 157526207 = 236289311) B236289311
theorem B3410171 : Blo 1346992 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B14780891 : Blo 1346992 14780891 := bstep (se 1 (by rfl) ⟨11085668, by rfl⟩ : syracuseStep 14780891 = 22171337) B22171337
theorem B2427383 : Blo 1346992 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B3459667 : Blo 1346992 3459667 := bstep (se 1 (by rfl) ⟨2594750, by rfl⟩ : syracuseStep 3459667 = 5189501) B5189501
theorem B3238537 : Blo 1346992 3238537 := bstep (se 2 (by rfl) ⟨1214451, by rfl⟩ : syracuseStep 3238537 = 2428903) B2428903
theorem B2558623 : Blo 1346992 2558623 := bstep (se 1 (by rfl) ⟨1918967, by rfl⟩ : syracuseStep 2558623 = 3837935) B3837935
theorem B3238643 : Blo 1346992 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B3034079 : Blo 1346992 3034079 := bstep (se 1 (by rfl) ⟨2275559, by rfl⟩ : syracuseStep 3034079 = 4551119) B4551119
theorem B10931719 : Blo 1346992 10931719 := bstep (se 1 (by rfl) ⟨8198789, by rfl⟩ : syracuseStep 10931719 = 16397579) B16397579
theorem B1347099 : Blo 1346992 1347099 := bstep (se 1 (by rfl) ⟨1010324, by rfl⟩ : syracuseStep 1347099 = 2020649) B2020649
theorem B1347231 : Blo 1346992 1347231 := bstep (se 1 (by rfl) ⟨1010423, by rfl⟩ : syracuseStep 1347231 = 2020847) B2020847
theorem B6819551 : Blo 1346992 6819551 := bstep (se 1 (by rfl) ⟨5114663, by rfl⟩ : syracuseStep 6819551 = 10229327) B10229327
theorem B3411679 : Blo 1346992 3411679 := bstep (se 1 (by rfl) ⟨2558759, by rfl⟩ : syracuseStep 3411679 = 5117519) B5117519
theorem B3641159 : Blo 1346992 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B1347495 : Blo 1346992 1347495 := bstep (se 1 (by rfl) ⟨1010621, by rfl⟩ : syracuseStep 1347495 = 2021243) B2021243
theorem B1347519 : Blo 1346992 1347519 := bstep (se 1 (by rfl) ⟨1010639, by rfl⟩ : syracuseStep 1347519 = 2021279) B2021279
theorem B4100051 : Blo 1346992 4100051 := bstep (se 1 (by rfl) ⟨3075038, by rfl⟩ : syracuseStep 4100051 = 6150077) B6150077
theorem B4550633 : Blo 1346992 4550633 := bstep (se 2 (by rfl) ⟨1706487, by rfl⟩ : syracuseStep 4550633 = 3412975) B3412975
theorem B4550687 : Blo 1346992 4550687 := bstep (se 1 (by rfl) ⟨3413015, by rfl⟩ : syracuseStep 4550687 = 6826031) B6826031
theorem B1347675 : Blo 1346992 1347675 := bstep (se 1 (by rfl) ⟨1010756, by rfl⟩ : syracuseStep 1347675 = 2021513) B2021513
theorem B3838049 : Blo 1346992 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B5615723 : Blo 1346992 5615723 := bstep (se 1 (by rfl) ⟨4211792, by rfl⟩ : syracuseStep 5615723 = 8423585) B8423585
theorem B1347775 : Blo 1346992 1347775 := bstep (se 1 (by rfl) ⟨1010831, by rfl⟩ : syracuseStep 1347775 = 2021663) B2021663
theorem B1823023 : Blo 1346992 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B1348143 : Blo 1346992 1348143 := bstep (se 1 (by rfl) ⟨1011107, by rfl⟩ : syracuseStep 1348143 = 2022215) B2022215
theorem B11678303 : Blo 1346992 11678303 := bstep (se 1 (by rfl) ⟨8758727, by rfl⟩ : syracuseStep 11678303 = 17517455) B17517455
theorem B4551443 : Blo 1346992 4551443 := bstep (se 1 (by rfl) ⟨3413582, by rfl⟩ : syracuseStep 4551443 = 6827165) B6827165
theorem B3413087 : Blo 1346992 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B1348719 : Blo 1346992 1348719 := bstep (se 1 (by rfl) ⟨1011539, by rfl⟩ : syracuseStep 1348719 = 2023079) B2023079
theorem B16405649 : Blo 1346992 16405649 := bstep (se 2 (by rfl) ⟨6152118, by rfl⟩ : syracuseStep 16405649 = 12304237) B12304237
theorem B10237103 : Blo 1346992 10237103 := bstep (se 1 (by rfl) ⟨7677827, by rfl⟩ : syracuseStep 10237103 = 15355655) B15355655
theorem B1348799 : Blo 1346992 1348799 := bstep (se 1 (by rfl) ⟨1011599, by rfl⟩ : syracuseStep 1348799 = 2023199) B2023199
theorem B8197355 : Blo 1346992 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B2020655 : Blo 1346992 2020655 := bstep (se 1 (by rfl) ⟨1515491, by rfl⟩ : syracuseStep 2020655 = 3030983) B3030983
theorem B7681337 : Blo 1346992 7681337 := bstep (se 2 (by rfl) ⟨2880501, by rfl⟩ : syracuseStep 7681337 = 5761003) B5761003
theorem B2020859 : Blo 1346992 2020859 := bstep (se 1 (by rfl) ⟨1515644, by rfl⟩ : syracuseStep 2020859 = 3031289) B3031289
theorem B3839507 : Blo 1346992 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B2020895 : Blo 1346992 2020895 := bstep (se 1 (by rfl) ⟨1515671, by rfl⟩ : syracuseStep 2020895 = 3031343) B3031343
theorem B4552307 : Blo 1346992 4552307 := bstep (se 1 (by rfl) ⟨3414230, by rfl⟩ : syracuseStep 4552307 = 6828461) B6828461
theorem B2021033 : Blo 1346992 2021033 := bstep (se 2 (by rfl) ⟨757887, by rfl⟩ : syracuseStep 2021033 = 1515775) B1515775
theorem B2021039 : Blo 1346992 2021039 := bstep (se 1 (by rfl) ⟨1515779, by rfl⟩ : syracuseStep 2021039 = 3031559) B3031559
theorem B5756663 : Blo 1346992 5756663 := bstep (se 1 (by rfl) ⟨4317497, by rfl⟩ : syracuseStep 5756663 = 8634995) B8634995
theorem B2021159 : Blo 1346992 2021159 := bstep (se 1 (by rfl) ⟨1515869, by rfl⟩ : syracuseStep 2021159 = 3031739) B3031739
theorem B2275195 : Blo 1346992 2275195 := bstep (se 1 (by rfl) ⟨1706396, by rfl⟩ : syracuseStep 2275195 = 3412793) B3412793
theorem B8640427 : Blo 1346992 8640427 := bstep (se 1 (by rfl) ⟨6480320, by rfl⟩ : syracuseStep 8640427 = 12960641) B12960641
theorem B2021417 : Blo 1346992 2021417 := bstep (se 2 (by rfl) ⟨758031, by rfl⟩ : syracuseStep 2021417 = 1516063) B1516063
theorem B7682111 : Blo 1346992 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B2021447 : Blo 1346992 2021447 := bstep (se 1 (by rfl) ⟨1516085, by rfl⟩ : syracuseStep 2021447 = 3032171) B3032171
theorem B3414089 : Blo 1346992 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B2275465 : Blo 1346992 2275465 := bstep (se 2 (by rfl) ⟨853299, by rfl⟩ : syracuseStep 2275465 = 1706599) B1706599
theorem B6232211 : Blo 1346992 6232211 := bstep (se 1 (by rfl) ⟨4674158, by rfl⟩ : syracuseStep 6232211 = 9348317) B9348317
theorem B2021759 : Blo 1346992 2021759 := bstep (se 1 (by rfl) ⟨1516319, by rfl⟩ : syracuseStep 2021759 = 3032639) B3032639
theorem B6822305 : Blo 1346992 6822305 := bstep (se 2 (by rfl) ⟨2558364, by rfl⟩ : syracuseStep 6822305 = 5116729) B5116729
theorem B3414433 : Blo 1346992 3414433 := bstep (se 2 (by rfl) ⟨1280412, by rfl⟩ : syracuseStep 3414433 = 2560825) B2560825
theorem B2021831 : Blo 1346992 2021831 := bstep (se 1 (by rfl) ⟨1516373, by rfl⟩ : syracuseStep 2021831 = 3032747) B3032747
theorem B8641043 : Blo 1346992 8641043 := bstep (se 1 (by rfl) ⟨6480782, by rfl⟩ : syracuseStep 8641043 = 12961565) B12961565
theorem B10230299 : Blo 1346992 10230299 := bstep (se 1 (by rfl) ⟨7672724, by rfl⟩ : syracuseStep 10230299 = 15345449) B15345449
theorem B5118491 : Blo 1346992 5118491 := bstep (se 1 (by rfl) ⟨3838868, by rfl⟩ : syracuseStep 5118491 = 7677737) B7677737
theorem B66484799 : Blo 1346992 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B2022047 : Blo 1346992 2022047 := bstep (se 1 (by rfl) ⟨1516535, by rfl⟩ : syracuseStep 2022047 = 3033071) B3033071
theorem B7682795 : Blo 1346992 7682795 := bstep (se 1 (by rfl) ⟨5762096, by rfl⟩ : syracuseStep 7682795 = 11524193) B11524193
theorem B2022191 : Blo 1346992 2022191 := bstep (se 1 (by rfl) ⟨1516643, by rfl⟩ : syracuseStep 2022191 = 3033287) B3033287
theorem B2022281 : Blo 1346992 2022281 := bstep (se 2 (by rfl) ⟨758355, by rfl⟩ : syracuseStep 2022281 = 1516711) B1516711
theorem B2022311 : Blo 1346992 2022311 := bstep (se 1 (by rfl) ⟨1516733, by rfl⟩ : syracuseStep 2022311 = 3033467) B3033467
theorem B3841033 : Blo 1346992 3841033 := bstep (se 2 (by rfl) ⟨1440387, by rfl⟩ : syracuseStep 3841033 = 2880775) B2880775
theorem B2022491 : Blo 1346992 2022491 := bstep (se 1 (by rfl) ⟨1516868, by rfl⟩ : syracuseStep 2022491 = 3033737) B3033737
theorem B4316267 : Blo 1346992 4316267 := bstep (se 1 (by rfl) ⟨3237200, by rfl⟩ : syracuseStep 4316267 = 6474401) B6474401
theorem B2022683 : Blo 1346992 2022683 := bstep (se 1 (by rfl) ⟨1517012, by rfl⟩ : syracuseStep 2022683 = 3034025) B3034025
theorem B9723311 : Blo 1346992 9723311 := bstep (se 1 (by rfl) ⟨7292483, by rfl⟩ : syracuseStep 9723311 = 14584967) B14584967
theorem B28032479 : Blo 1346992 28032479 := bstep (se 1 (by rfl) ⟨21024359, by rfl⟩ : syracuseStep 28032479 = 42048719) B42048719
theorem B34537103 : Blo 1346992 34537103 := bstep (se 1 (by rfl) ⟨25902827, by rfl⟩ : syracuseStep 34537103 = 51805655) B51805655
theorem B2023151 : Blo 1346992 2023151 := bstep (se 1 (by rfl) ⟨1517363, by rfl⟩ : syracuseStep 2023151 = 3034727) B3034727
theorem B17276753 : Blo 1346992 17276753 := bstep (se 2 (by rfl) ⟨6478782, by rfl⟩ : syracuseStep 17276753 = 12957565) B12957565
theorem B2023337 : Blo 1346992 2023337 := bstep (se 2 (by rfl) ⟨758751, by rfl⟩ : syracuseStep 2023337 = 1517503) B1517503
theorem B11518109 : Blo 1346992 11518109 := bstep (se 3 (by rfl) ⟨2159645, by rfl⟩ : syracuseStep 11518109 = 4319291) B4319291
theorem B4546745 : Blo 1346992 4546745 := bstep (se 2 (by rfl) ⟨1705029, by rfl⟩ : syracuseStep 4546745 = 3410059) B3410059
theorem B11510045 : Blo 1346992 11510045 := bstep (se 3 (by rfl) ⟨2158133, by rfl⟩ : syracuseStep 11510045 = 4316267) B4316267
theorem B14975261 : Blo 1346992 14975261 := bstep (se 3 (by rfl) ⟨2807861, by rfl⟩ : syracuseStep 14975261 = 5615723) B5615723
theorem B3031379 : Blo 1346992 3031379 := bstep (se 1 (by rfl) ⟨2273534, by rfl⟩ : syracuseStep 3031379 = 4547069) B4547069
theorem B3031487 : Blo 1346992 3031487 := bstep (se 1 (by rfl) ⟨2273615, by rfl⟩ : syracuseStep 3031487 = 4547231) B4547231
theorem B10937099 : Blo 1346992 10937099 := bstep (se 1 (by rfl) ⟨8202824, by rfl⟩ : syracuseStep 10937099 = 16405649) B16405649
theorem B4612889 : Blo 1346992 4612889 := bstep (se 2 (by rfl) ⟨1729833, by rfl⟩ : syracuseStep 4612889 = 3459667) B3459667
theorem B6824735 : Blo 1346992 6824735 := bstep (se 1 (by rfl) ⟨5118551, by rfl⟩ : syracuseStep 6824735 = 10237103) B10237103
theorem B5464903 : Blo 1346992 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B4318049 : Blo 1346992 4318049 := bstep (se 2 (by rfl) ⟨1619268, by rfl⟩ : syracuseStep 4318049 = 3238537) B3238537
theorem B5120891 : Blo 1346992 5120891 := bstep (se 1 (by rfl) ⟨3840668, by rfl⟩ : syracuseStep 5120891 = 7681337) B7681337
theorem B5121377 : Blo 1346992 5121377 := bstep (se 2 (by rfl) ⟨1920516, by rfl⟩ : syracuseStep 5121377 = 3841033) B3841033
theorem B3032423 : Blo 1346992 3032423 := bstep (se 1 (by rfl) ⟨2274317, by rfl⟩ : syracuseStep 3032423 = 4548635) B4548635
theorem B5121407 : Blo 1346992 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B4154807 : Blo 1346992 4154807 := bstep (se 1 (by rfl) ⟨3116105, by rfl⟩ : syracuseStep 4154807 = 6232211) B6232211
theorem B4548203 : Blo 1346992 4548203 := bstep (se 1 (by rfl) ⟨3411152, by rfl⟩ : syracuseStep 4548203 = 6822305) B6822305
theorem B5760695 : Blo 1346992 5760695 := bstep (se 1 (by rfl) ⟨4320521, by rfl⟩ : syracuseStep 5760695 = 8641043) B8641043
theorem B5121863 : Blo 1346992 5121863 := bstep (se 1 (by rfl) ⟨3841397, by rfl⟩ : syracuseStep 5121863 = 7682795) B7682795
theorem B8636381 : Blo 1346992 8636381 := bstep (se 3 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 8636381 = 3238643) B3238643
theorem B14575625 : Blo 1346992 14575625 := bstep (se 2 (by rfl) ⟨5465859, by rfl⟩ : syracuseStep 14575625 = 10931719) B10931719
theorem B9709757 : Blo 1346992 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B6482207 : Blo 1346992 6482207 := bstep (se 1 (by rfl) ⟨4861655, by rfl⟩ : syracuseStep 6482207 = 9723311) B9723311
theorem B4548905 : Blo 1346992 4548905 := bstep (se 2 (by rfl) ⟨1705839, by rfl⟩ : syracuseStep 4548905 = 3411679) B3411679
theorem B18688319 : Blo 1346992 18688319 := bstep (se 1 (by rfl) ⟨14016239, by rfl⟩ : syracuseStep 18688319 = 28032479) B28032479
theorem B3033593 : Blo 1346992 3033593 := bstep (se 2 (by rfl) ⟨1137597, by rfl⟩ : syracuseStep 3033593 = 2275195) B2275195
theorem B11520569 : Blo 1346992 11520569 := bstep (se 2 (by rfl) ⟨4320213, by rfl⟩ : syracuseStep 11520569 = 8640427) B8640427
theorem B3033755 : Blo 1346992 3033755 := bstep (se 1 (by rfl) ⟨2275316, by rfl⟩ : syracuseStep 3033755 = 4550633) B4550633
theorem B3033791 : Blo 1346992 3033791 := bstep (se 1 (by rfl) ⟨2275343, by rfl⟩ : syracuseStep 3033791 = 4550687) B4550687
theorem B3410657 : Blo 1346992 3410657 := bstep (se 2 (by rfl) ⟨1278996, by rfl⟩ : syracuseStep 3410657 = 2557993) B2557993
theorem B2558699 : Blo 1346992 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B3033953 : Blo 1346992 3033953 := bstep (se 2 (by rfl) ⟨1137732, by rfl⟩ : syracuseStep 3033953 = 2275465) B2275465
theorem B2878571 : Blo 1346992 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B2305199 : Blo 1346992 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B3034295 : Blo 1346992 3034295 := bstep (se 1 (by rfl) ⟨2275721, by rfl⟩ : syracuseStep 3034295 = 4551443) B4551443
theorem B1347103 : Blo 1346992 1347103 := bstep (se 1 (by rfl) ⟨1010327, by rfl⟩ : syracuseStep 1347103 = 2020655) B2020655
theorem B3411497 : Blo 1346992 3411497 := bstep (se 2 (by rfl) ⟨1279311, by rfl⟩ : syracuseStep 3411497 = 2558623) B2558623
theorem B1347239 : Blo 1346992 1347239 := bstep (se 1 (by rfl) ⟨1010429, by rfl⟩ : syracuseStep 1347239 = 2020859) B2020859
theorem B2559671 : Blo 1346992 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B1347263 : Blo 1346992 1347263 := bstep (se 1 (by rfl) ⟨1010447, by rfl⟩ : syracuseStep 1347263 = 2020895) B2020895
theorem B3034871 : Blo 1346992 3034871 := bstep (se 1 (by rfl) ⟨2276153, by rfl⟩ : syracuseStep 3034871 = 4552307) B4552307
theorem B1347355 : Blo 1346992 1347355 := bstep (se 1 (by rfl) ⟨1010516, by rfl⟩ : syracuseStep 1347355 = 2021033) B2021033
theorem B1347359 : Blo 1346992 1347359 := bstep (se 1 (by rfl) ⟨1010519, by rfl⟩ : syracuseStep 1347359 = 2021039) B2021039
theorem B3837775 : Blo 1346992 3837775 := bstep (se 1 (by rfl) ⟨2878331, by rfl⟩ : syracuseStep 3837775 = 5756663) B5756663
theorem B1347439 : Blo 1346992 1347439 := bstep (se 1 (by rfl) ⟨1010579, by rfl⟩ : syracuseStep 1347439 = 2021159) B2021159
theorem B39415709 : Blo 1346992 39415709 := bstep (se 3 (by rfl) ⟨7390445, by rfl⟩ : syracuseStep 39415709 = 14780891) B14780891
theorem B1347611 : Blo 1346992 1347611 := bstep (se 1 (by rfl) ⟨1010708, by rfl⟩ : syracuseStep 1347611 = 2021417) B2021417
theorem B1347631 : Blo 1346992 1347631 := bstep (se 1 (by rfl) ⟨1010723, by rfl⟩ : syracuseStep 1347631 = 2021447) B2021447
theorem B105017471 : Blo 1346992 105017471 := bstep (se 1 (by rfl) ⟨78763103, by rfl⟩ : syracuseStep 105017471 = 157526207) B157526207
theorem B2273447 : Blo 1346992 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B31142141 : Blo 1346992 31142141 := bstep (se 3 (by rfl) ⟨5839151, by rfl⟩ : syracuseStep 31142141 = 11678303) B11678303
theorem B1347839 : Blo 1346992 1347839 := bstep (se 1 (by rfl) ⟨1010879, by rfl⟩ : syracuseStep 1347839 = 2021759) B2021759
theorem B1347887 : Blo 1346992 1347887 := bstep (se 1 (by rfl) ⟨1010915, by rfl⟩ : syracuseStep 1347887 = 2021831) B2021831
theorem B1618255 : Blo 1346992 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B6820199 : Blo 1346992 6820199 := bstep (se 1 (by rfl) ⟨5115149, by rfl⟩ : syracuseStep 6820199 = 10230299) B10230299
theorem B3412327 : Blo 1346992 3412327 := bstep (se 1 (by rfl) ⟨2559245, by rfl⟩ : syracuseStep 3412327 = 5118491) B5118491
theorem B44323199 : Blo 1346992 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B7778749 : Blo 1346992 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B1348031 : Blo 1346992 1348031 := bstep (se 1 (by rfl) ⟨1011023, by rfl⟩ : syracuseStep 1348031 = 2022047) B2022047
theorem B1348127 : Blo 1346992 1348127 := bstep (se 1 (by rfl) ⟨1011095, by rfl⟩ : syracuseStep 1348127 = 2022191) B2022191
theorem B1348187 : Blo 1346992 1348187 := bstep (se 1 (by rfl) ⟨1011140, by rfl⟩ : syracuseStep 1348187 = 2022281) B2022281
theorem B1348207 : Blo 1346992 1348207 := bstep (se 1 (by rfl) ⟨1011155, by rfl⟩ : syracuseStep 1348207 = 2022311) B2022311
theorem B1348327 : Blo 1346992 1348327 := bstep (se 1 (by rfl) ⟨1011245, by rfl⟩ : syracuseStep 1348327 = 2022491) B2022491
theorem B1348455 : Blo 1346992 1348455 := bstep (se 1 (by rfl) ⟨1011341, by rfl⟩ : syracuseStep 1348455 = 2022683) B2022683
theorem B8631305 : Blo 1346992 8631305 := bstep (se 2 (by rfl) ⟨3236739, by rfl⟩ : syracuseStep 8631305 = 6473479) B6473479
theorem B23024735 : Blo 1346992 23024735 := bstep (se 1 (by rfl) ⟨17268551, by rfl⟩ : syracuseStep 23024735 = 34537103) B34537103
theorem B1348767 : Blo 1346992 1348767 := bstep (se 1 (by rfl) ⟨1011575, by rfl⟩ : syracuseStep 1348767 = 2023151) B2023151
theorem B1348891 : Blo 1346992 1348891 := bstep (se 1 (by rfl) ⟨1011668, by rfl⟩ : syracuseStep 1348891 = 2023337) B2023337
theorem B2733367 : Blo 1346992 2733367 := bstep (se 1 (by rfl) ⟨2050025, by rfl⟩ : syracuseStep 2733367 = 4100051) B4100051
theorem B1348991 : Blo 1346992 1348991 := bstep (se 1 (by rfl) ⟨1011743, by rfl⟩ : syracuseStep 1348991 = 2023487) B2023487
theorem B3413735 : Blo 1346992 3413735 := bstep (se 1 (by rfl) ⟨2560301, by rfl⟩ : syracuseStep 3413735 = 5120603) B5120603
theorem B2430697 : Blo 1346992 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B11507447 : Blo 1346992 11507447 := bstep (se 1 (by rfl) ⟨8630585, by rfl⟩ : syracuseStep 11507447 = 17261171) B17261171
theorem B4675367 : Blo 1346992 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B4552577 : Blo 1346992 4552577 := bstep (se 2 (by rfl) ⟨1707216, by rfl⟩ : syracuseStep 4552577 = 3414433) B3414433
theorem B2275391 : Blo 1346992 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B2276059 : Blo 1346992 2276059 := bstep (se 1 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 2276059 = 3414089) B3414089
theorem B2022185 : Blo 1346992 2022185 := bstep (se 2 (by rfl) ⟨758319, by rfl⟩ : syracuseStep 2022185 = 1516639) B1516639
theorem B2022719 : Blo 1346992 2022719 := bstep (se 1 (by rfl) ⟨1517039, by rfl⟩ : syracuseStep 2022719 = 3034079) B3034079
theorem B2023049 : Blo 1346992 2023049 := bstep (se 2 (by rfl) ⟨758643, by rfl⟩ : syracuseStep 2023049 = 1517287) B1517287
theorem B4546367 : Blo 1346992 4546367 := bstep (se 1 (by rfl) ⟨3409775, by rfl⟩ : syracuseStep 4546367 = 6819551) B6819551
theorem B11517835 : Blo 1346992 11517835 := bstep (se 1 (by rfl) ⟨8638376, by rfl⟩ : syracuseStep 11517835 = 17276753) B17276753
theorem B1515631 : Blo 1346992 1515631 := bstep (se 1 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 1515631 = 2273447) B2273447
theorem B3031163 : Blo 1346992 3031163 := bstep (se 1 (by rfl) ⟨2273372, by rfl⟩ : syracuseStep 3031163 = 4546745) B4546745
theorem B4546799 : Blo 1346992 4546799 := bstep (se 1 (by rfl) ⟨3410099, by rfl⟩ : syracuseStep 4546799 = 6820199) B6820199
theorem B29548799 : Blo 1346992 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B7291399 : Blo 1346992 7291399 := bstep (se 1 (by rfl) ⟨5468549, by rfl⟩ : syracuseStep 7291399 = 10937099) B10937099
theorem B10371665 : Blo 1346992 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B2769871 : Blo 1346992 2769871 := bstep (se 1 (by rfl) ⟨2077403, by rfl⟩ : syracuseStep 2769871 = 4154807) B4154807
theorem B3032135 : Blo 1346992 3032135 := bstep (se 1 (by rfl) ⟨2274101, by rfl⟩ : syracuseStep 3032135 = 4548203) B4548203
theorem B9717083 : Blo 1346992 9717083 := bstep (se 1 (by rfl) ⟨7287812, by rfl⟩ : syracuseStep 9717083 = 14575625) B14575625
theorem B1516927 : Blo 1346992 1516927 := bstep (se 1 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 1516927 = 2275391) B2275391
theorem B6473171 : Blo 1346992 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B3032603 : Blo 1346992 3032603 := bstep (se 1 (by rfl) ⟨2274452, by rfl⟩ : syracuseStep 3032603 = 4548905) B4548905
theorem B1705799 : Blo 1346992 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B1919047 : Blo 1346992 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B1706447 : Blo 1346992 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B70011647 : Blo 1346992 70011647 := bstep (se 1 (by rfl) ⟨52508735, by rfl⟩ : syracuseStep 70011647 = 105017471) B105017471
theorem B7678739 : Blo 1346992 7678739 := bstep (se 1 (by rfl) ⟨5759054, by rfl⟩ : syracuseStep 7678739 = 11518109) B11518109
theorem B20761427 : Blo 1346992 20761427 := bstep (se 1 (by rfl) ⟨15571070, by rfl⟩ : syracuseStep 20761427 = 31142141) B31142141
theorem B2157673 : Blo 1346992 2157673 := bstep (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) B1618255
theorem B6147197 : Blo 1346992 6147197 := bstep (se 3 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 6147197 = 2305199) B2305199
theorem B4549769 : Blo 1346992 4549769 := bstep (se 2 (by rfl) ⟨1706163, by rfl⟩ : syracuseStep 4549769 = 3412327) B3412327
theorem B3075259 : Blo 1346992 3075259 := bstep (se 1 (by rfl) ⟨2306444, by rfl⟩ : syracuseStep 3075259 = 4612889) B4612889
theorem B4549823 : Blo 1346992 4549823 := bstep (se 1 (by rfl) ⟨3412367, by rfl⟩ : syracuseStep 4549823 = 6824735) B6824735
theorem B5754203 : Blo 1346992 5754203 := bstep (se 1 (by rfl) ⟨4315652, by rfl⟩ : syracuseStep 5754203 = 8631305) B8631305
theorem B3034745 : Blo 1346992 3034745 := bstep (se 2 (by rfl) ⟨1138029, by rfl⟩ : syracuseStep 3034745 = 2276059) B2276059
theorem B7286537 : Blo 1346992 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B7671631 : Blo 1346992 7671631 := bstep (se 1 (by rfl) ⟨5753723, by rfl⟩ : syracuseStep 7671631 = 11507447) B11507447
theorem B3116911 : Blo 1346992 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B3035051 : Blo 1346992 3035051 := bstep (se 1 (by rfl) ⟨2276288, by rfl⟩ : syracuseStep 3035051 = 4552577) B4552577
theorem B4321471 : Blo 1346992 4321471 := bstep (se 1 (by rfl) ⟨3241103, by rfl⟩ : syracuseStep 4321471 = 6482207) B6482207
theorem B7680379 : Blo 1346992 7680379 := bstep (se 1 (by rfl) ⟨5760284, by rfl⟩ : syracuseStep 7680379 = 11520569) B11520569
theorem B2273771 : Blo 1346992 2273771 := bstep (se 1 (by rfl) ⟨1705328, by rfl⟩ : syracuseStep 2273771 = 3410657) B3410657
theorem B1348123 : Blo 1346992 1348123 := bstep (se 1 (by rfl) ⟨1011092, by rfl⟩ : syracuseStep 1348123 = 2022185) B2022185
theorem B1348479 : Blo 1346992 1348479 := bstep (se 1 (by rfl) ⟨1011359, by rfl⟩ : syracuseStep 1348479 = 2022719) B2022719
theorem B11514797 : Blo 1346992 11514797 := bstep (se 3 (by rfl) ⟨2159024, by rfl⟩ : syracuseStep 11514797 = 4318049) B4318049
theorem B3240929 : Blo 1346992 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B2274331 : Blo 1346992 2274331 := bstep (se 1 (by rfl) ⟨1705748, by rfl⟩ : syracuseStep 2274331 = 3411497) B3411497
theorem B1348699 : Blo 1346992 1348699 := bstep (se 1 (by rfl) ⟨1011524, by rfl⟩ : syracuseStep 1348699 = 2023049) B2023049
theorem B5117033 : Blo 1346992 5117033 := bstep (se 2 (by rfl) ⟨1918887, by rfl⟩ : syracuseStep 5117033 = 3837775) B3837775
theorem B15357113 : Blo 1346992 15357113 := bstep (se 2 (by rfl) ⟨5758917, by rfl⟩ : syracuseStep 15357113 = 11517835) B11517835
theorem B26277139 : Blo 1346992 26277139 := bstep (se 1 (by rfl) ⟨19707854, by rfl⟩ : syracuseStep 26277139 = 39415709) B39415709
theorem B7673363 : Blo 1346992 7673363 := bstep (se 1 (by rfl) ⟨5755022, by rfl⟩ : syracuseStep 7673363 = 11510045) B11510045
theorem B9983507 : Blo 1346992 9983507 := bstep (se 1 (by rfl) ⟨7487630, by rfl⟩ : syracuseStep 9983507 = 14975261) B14975261
theorem B2020919 : Blo 1346992 2020919 := bstep (se 1 (by rfl) ⟨1515689, by rfl⟩ : syracuseStep 2020919 = 3031379) B3031379
theorem B2020991 : Blo 1346992 2020991 := bstep (se 1 (by rfl) ⟨1515743, by rfl⟩ : syracuseStep 2020991 = 3031487) B3031487
theorem B3413927 : Blo 1346992 3413927 := bstep (se 1 (by rfl) ⟨2560445, by rfl⟩ : syracuseStep 3413927 = 5120891) B5120891
theorem B15349823 : Blo 1346992 15349823 := bstep (se 1 (by rfl) ⟨11512367, by rfl⟩ : syracuseStep 15349823 = 23024735) B23024735
theorem B3414251 : Blo 1346992 3414251 := bstep (se 1 (by rfl) ⟨2560688, by rfl⟩ : syracuseStep 3414251 = 5121377) B5121377
theorem B2021615 : Blo 1346992 2021615 := bstep (se 1 (by rfl) ⟨1516211, by rfl⟩ : syracuseStep 2021615 = 3032423) B3032423
theorem B3414271 : Blo 1346992 3414271 := bstep (se 1 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 3414271 = 5121407) B5121407
theorem B3840463 : Blo 1346992 3840463 := bstep (se 1 (by rfl) ⟨2880347, by rfl⟩ : syracuseStep 3840463 = 5760695) B5760695
theorem B2275823 : Blo 1346992 2275823 := bstep (se 1 (by rfl) ⟨1706867, by rfl⟩ : syracuseStep 2275823 = 3413735) B3413735
theorem B3414575 : Blo 1346992 3414575 := bstep (se 1 (by rfl) ⟨2560931, by rfl⟩ : syracuseStep 3414575 = 5121863) B5121863
theorem B5757587 : Blo 1346992 5757587 := bstep (se 1 (by rfl) ⟨4318190, by rfl⟩ : syracuseStep 5757587 = 8636381) B8636381
theorem B12458879 : Blo 1346992 12458879 := bstep (se 1 (by rfl) ⟨9344159, by rfl⟩ : syracuseStep 12458879 = 18688319) B18688319
theorem B2022395 : Blo 1346992 2022395 := bstep (se 1 (by rfl) ⟨1516796, by rfl⟩ : syracuseStep 2022395 = 3033593) B3033593
theorem B3644489 : Blo 1346992 3644489 := bstep (se 2 (by rfl) ⟨1366683, by rfl⟩ : syracuseStep 3644489 = 2733367) B2733367
theorem B2022503 : Blo 1346992 2022503 := bstep (se 1 (by rfl) ⟨1516877, by rfl⟩ : syracuseStep 2022503 = 3033755) B3033755
theorem B2022527 : Blo 1346992 2022527 := bstep (se 1 (by rfl) ⟨1516895, by rfl⟩ : syracuseStep 2022527 = 3033791) B3033791
theorem B2022635 : Blo 1346992 2022635 := bstep (se 1 (by rfl) ⟨1516976, by rfl⟩ : syracuseStep 2022635 = 3033953) B3033953
theorem B2022863 : Blo 1346992 2022863 := bstep (se 1 (by rfl) ⟨1517147, by rfl⟩ : syracuseStep 2022863 = 3034295) B3034295
theorem B2023247 : Blo 1346992 2023247 := bstep (se 1 (by rfl) ⟨1517435, by rfl⟩ : syracuseStep 2023247 = 3034871) B3034871
theorem B3030911 : Blo 1346992 3030911 := bstep (se 1 (by rfl) ⟨2273183, by rfl⟩ : syracuseStep 3030911 = 4546367) B4546367
theorem B3031199 : Blo 1346992 3031199 := bstep (se 1 (by rfl) ⟨2273399, by rfl⟩ : syracuseStep 3031199 = 4546799) B4546799
theorem B1515847 : Blo 1346992 1515847 := bstep (se 1 (by rfl) ⟨1136885, by rfl⟩ : syracuseStep 1515847 = 2273771) B2273771
theorem B6914443 : Blo 1346992 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B10240505 : Blo 1346992 10240505 := bstep (se 2 (by rfl) ⟨3840189, by rfl⟩ : syracuseStep 10240505 = 7680379) B7680379
theorem B5120617 : Blo 1346992 5120617 := bstep (se 2 (by rfl) ⟨1920231, by rfl⟩ : syracuseStep 5120617 = 3840463) B3840463
theorem B7676531 : Blo 1346992 7676531 := bstep (se 1 (by rfl) ⟨5757398, by rfl⟩ : syracuseStep 7676531 = 11514797) B11514797
theorem B3032441 : Blo 1346992 3032441 := bstep (se 2 (by rfl) ⟨1137165, by rfl⟩ : syracuseStep 3032441 = 2274331) B2274331
theorem B10233215 : Blo 1346992 10233215 := bstep (se 1 (by rfl) ⟨7674911, by rfl⟩ : syracuseStep 10233215 = 15349823) B15349823
theorem B2876897 : Blo 1346992 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B1517215 : Blo 1346992 1517215 := bstep (se 1 (by rfl) ⟨1137911, by rfl⟩ : syracuseStep 1517215 = 2275823) B2275823
theorem B4098131 : Blo 1346992 4098131 := bstep (se 1 (by rfl) ⟨3073598, by rfl⟩ : syracuseStep 4098131 = 6147197) B6147197
theorem B3033179 : Blo 1346992 3033179 := bstep (se 1 (by rfl) ⟨2274884, by rfl⟩ : syracuseStep 3033179 = 4549769) B4549769
theorem B3033215 : Blo 1346992 3033215 := bstep (se 1 (by rfl) ⟨2274911, by rfl⟩ : syracuseStep 3033215 = 4549823) B4549823
theorem B4548797 : Blo 1346992 4548797 := bstep (se 3 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 4548797 = 1705799) B1705799
theorem B3836135 : Blo 1346992 3836135 := bstep (se 1 (by rfl) ⟨2877101, by rfl⟩ : syracuseStep 3836135 = 5754203) B5754203
theorem B4155881 : Blo 1346992 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B2558729 : Blo 1346992 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B5761961 : Blo 1346992 5761961 := bstep (se 2 (by rfl) ⟨2160735, by rfl⟩ : syracuseStep 5761961 = 4321471) B4321471
theorem B3411355 : Blo 1346992 3411355 := bstep (se 1 (by rfl) ⟨2558516, by rfl⟩ : syracuseStep 3411355 = 5117033) B5117033
theorem B5115575 : Blo 1346992 5115575 := bstep (se 1 (by rfl) ⟨3836681, by rfl⟩ : syracuseStep 5115575 = 7673363) B7673363
theorem B1347279 : Blo 1346992 1347279 := bstep (se 1 (by rfl) ⟨1010459, by rfl⟩ : syracuseStep 1347279 = 2020919) B2020919
theorem B1347327 : Blo 1346992 1347327 := bstep (se 1 (by rfl) ⟨1010495, by rfl⟩ : syracuseStep 1347327 = 2020991) B2020991
theorem B4550525 : Blo 1346992 4550525 := bstep (se 3 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 4550525 = 1706447) B1706447
theorem B1347743 : Blo 1346992 1347743 := bstep (se 1 (by rfl) ⟨1010807, by rfl⟩ : syracuseStep 1347743 = 2021615) B2021615
theorem B4100345 : Blo 1346992 4100345 := bstep (se 2 (by rfl) ⟨1537629, by rfl⟩ : syracuseStep 4100345 = 3075259) B3075259
theorem B3838391 : Blo 1346992 3838391 := bstep (se 1 (by rfl) ⟨2878793, by rfl⟩ : syracuseStep 3838391 = 5757587) B5757587
theorem B46674431 : Blo 1346992 46674431 := bstep (se 1 (by rfl) ⟨35005823, by rfl⟩ : syracuseStep 46674431 = 70011647) B70011647
theorem B13840951 : Blo 1346992 13840951 := bstep (se 1 (by rfl) ⟨10380713, by rfl⟩ : syracuseStep 13840951 = 20761427) B20761427
theorem B1348263 : Blo 1346992 1348263 := bstep (se 1 (by rfl) ⟨1011197, by rfl⟩ : syracuseStep 1348263 = 2022395) B2022395
theorem B2429659 : Blo 1346992 2429659 := bstep (se 1 (by rfl) ⟨1822244, by rfl⟩ : syracuseStep 2429659 = 3644489) B3644489
theorem B1348335 : Blo 1346992 1348335 := bstep (se 1 (by rfl) ⟨1011251, by rfl⟩ : syracuseStep 1348335 = 2022503) B2022503
theorem B1348351 : Blo 1346992 1348351 := bstep (se 1 (by rfl) ⟨1011263, by rfl⟩ : syracuseStep 1348351 = 2022527) B2022527
theorem B1348423 : Blo 1346992 1348423 := bstep (se 1 (by rfl) ⟨1011317, by rfl⟩ : syracuseStep 1348423 = 2022635) B2022635
theorem B1348575 : Blo 1346992 1348575 := bstep (se 1 (by rfl) ⟨1011431, by rfl⟩ : syracuseStep 1348575 = 2022863) B2022863
theorem B10228841 : Blo 1346992 10228841 := bstep (se 2 (by rfl) ⟨3835815, by rfl⟩ : syracuseStep 10228841 = 7671631) B7671631
theorem B1348831 : Blo 1346992 1348831 := bstep (se 1 (by rfl) ⟨1011623, by rfl⟩ : syracuseStep 1348831 = 2023247) B2023247
theorem B2020607 : Blo 1346992 2020607 := bstep (se 1 (by rfl) ⟨1515455, by rfl⟩ : syracuseStep 2020607 = 3030911) B3030911
theorem B2020775 : Blo 1346992 2020775 := bstep (se 1 (by rfl) ⟨1515581, by rfl⟩ : syracuseStep 2020775 = 3031163) B3031163
theorem B2020841 : Blo 1346992 2020841 := bstep (se 2 (by rfl) ⟨757815, by rfl⟩ : syracuseStep 2020841 = 1515631) B1515631
theorem B19699199 : Blo 1346992 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B4552361 : Blo 1346992 4552361 := bstep (se 2 (by rfl) ⟨1707135, by rfl⟩ : syracuseStep 4552361 = 3414271) B3414271
theorem B9721865 : Blo 1346992 9721865 := bstep (se 2 (by rfl) ⟨3645699, by rfl⟩ : syracuseStep 9721865 = 7291399) B7291399
theorem B2021423 : Blo 1346992 2021423 := bstep (se 1 (by rfl) ⟨1516067, by rfl⟩ : syracuseStep 2021423 = 3032135) B3032135
theorem B10238075 : Blo 1346992 10238075 := bstep (se 1 (by rfl) ⟨7678556, by rfl⟩ : syracuseStep 10238075 = 15357113) B15357113
theorem B6478055 : Blo 1346992 6478055 := bstep (se 1 (by rfl) ⟨4858541, by rfl⟩ : syracuseStep 6478055 = 9717083) B9717083
theorem B4315447 : Blo 1346992 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B2021735 : Blo 1346992 2021735 := bstep (se 1 (by rfl) ⟨1516301, by rfl⟩ : syracuseStep 2021735 = 3032603) B3032603
theorem B3693161 : Blo 1346992 3693161 := bstep (se 2 (by rfl) ⟨1384935, by rfl⟩ : syracuseStep 3693161 = 2769871) B2769871
theorem B2275951 : Blo 1346992 2275951 := bstep (se 1 (by rfl) ⟨1706963, by rfl⟩ : syracuseStep 2275951 = 3413927) B3413927
theorem B26622685 : Blo 1346992 26622685 := bstep (se 3 (by rfl) ⟨4991753, by rfl⟩ : syracuseStep 26622685 = 9983507) B9983507
theorem B2276167 : Blo 1346992 2276167 := bstep (se 1 (by rfl) ⟨1707125, by rfl⟩ : syracuseStep 2276167 = 3414251) B3414251
theorem B35036185 : Blo 1346992 35036185 := bstep (se 2 (by rfl) ⟨13138569, by rfl⟩ : syracuseStep 35036185 = 26277139) B26277139
theorem B2276383 : Blo 1346992 2276383 := bstep (se 1 (by rfl) ⟨1707287, by rfl⟩ : syracuseStep 2276383 = 3414575) B3414575
theorem B2022569 : Blo 1346992 2022569 := bstep (se 2 (by rfl) ⟨758463, by rfl⟩ : syracuseStep 2022569 = 1516927) B1516927
theorem B5119159 : Blo 1346992 5119159 := bstep (se 1 (by rfl) ⟨3839369, by rfl⟩ : syracuseStep 5119159 = 7678739) B7678739
theorem B8305919 : Blo 1346992 8305919 := bstep (se 1 (by rfl) ⟨6229439, by rfl⟩ : syracuseStep 8305919 = 12458879) B12458879
theorem B19430765 : Blo 1346992 19430765 := bstep (se 3 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 19430765 = 7286537) B7286537
theorem B2023163 : Blo 1346992 2023163 := bstep (se 1 (by rfl) ⟨1517372, by rfl⟩ : syracuseStep 2023163 = 3034745) B3034745
theorem B8642477 : Blo 1346992 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B2023367 : Blo 1346992 2023367 := bstep (se 1 (by rfl) ⟨1517525, by rfl⟩ : syracuseStep 2023367 = 3035051) B3035051
theorem B35496913 : Blo 1346992 35496913 := bstep (se 2 (by rfl) ⟨13311342, by rfl⟩ : syracuseStep 35496913 = 26622685) B26622685
theorem B1917931 : Blo 1346992 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B13132799 : Blo 1346992 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B6481243 : Blo 1346992 6481243 := bstep (se 1 (by rfl) ⟨4860932, by rfl⟩ : syracuseStep 6481243 = 9721865) B9721865
theorem B6825383 : Blo 1346992 6825383 := bstep (se 1 (by rfl) ⟨5119037, by rfl⟩ : syracuseStep 6825383 = 10238075) B10238075
theorem B3032531 : Blo 1346992 3032531 := bstep (se 1 (by rfl) ⟨2274398, by rfl⟩ : syracuseStep 3032531 = 4548797) B4548797
theorem B2557423 : Blo 1346992 2557423 := bstep (se 1 (by rfl) ⟨1918067, by rfl⟩ : syracuseStep 2557423 = 3836135) B3836135
theorem B4318703 : Blo 1346992 4318703 := bstep (se 1 (by rfl) ⟨3239027, by rfl⟩ : syracuseStep 4318703 = 6478055) B6478055
theorem B6825545 : Blo 1346992 6825545 := bstep (se 2 (by rfl) ⟨2559579, by rfl⟩ : syracuseStep 6825545 = 5119159) B5119159
theorem B4548473 : Blo 1346992 4548473 := bstep (se 2 (by rfl) ⟨1705677, by rfl⟩ : syracuseStep 4548473 = 3411355) B3411355
theorem B12953843 : Blo 1346992 12953843 := bstep (se 1 (by rfl) ⟨9715382, by rfl⟩ : syracuseStep 12953843 = 19430765) B19430765
theorem B23046605 : Blo 1346992 23046605 := bstep (se 3 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 23046605 = 8642477) B8642477
theorem B3410383 : Blo 1346992 3410383 := bstep (se 1 (by rfl) ⟨2557787, by rfl⟩ : syracuseStep 3410383 = 5115575) B5115575
theorem B3033683 : Blo 1346992 3033683 := bstep (se 1 (by rfl) ⟨2275262, by rfl⟩ : syracuseStep 3033683 = 4550525) B4550525
theorem B2558927 : Blo 1346992 2558927 := bstep (se 1 (by rfl) ⟨1919195, by rfl⟩ : syracuseStep 2558927 = 3838391) B3838391
theorem B6827003 : Blo 1346992 6827003 := bstep (se 1 (by rfl) ⟨5120252, by rfl⟩ : syracuseStep 6827003 = 10240505) B10240505
theorem B31116287 : Blo 1346992 31116287 := bstep (se 1 (by rfl) ⟨23337215, by rfl⟩ : syracuseStep 31116287 = 46674431) B46674431
theorem B5753929 : Blo 1346992 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B9219257 : Blo 1346992 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B6819227 : Blo 1346992 6819227 := bstep (se 1 (by rfl) ⟨5114420, by rfl⟩ : syracuseStep 6819227 = 10228841) B10228841
theorem B6827489 : Blo 1346992 6827489 := bstep (se 2 (by rfl) ⟨2560308, by rfl⟩ : syracuseStep 6827489 = 5120617) B5120617
theorem B3034601 : Blo 1346992 3034601 := bstep (se 2 (by rfl) ⟨1137975, by rfl⟩ : syracuseStep 3034601 = 2275951) B2275951
theorem B1347071 : Blo 1346992 1347071 := bstep (se 1 (by rfl) ⟨1010303, by rfl⟩ : syracuseStep 1347071 = 2020607) B2020607
theorem B1347183 : Blo 1346992 1347183 := bstep (se 1 (by rfl) ⟨1010387, by rfl⟩ : syracuseStep 1347183 = 2020775) B2020775
theorem B1347227 : Blo 1346992 1347227 := bstep (se 1 (by rfl) ⟨1010420, by rfl⟩ : syracuseStep 1347227 = 2020841) B2020841
theorem B3034889 : Blo 1346992 3034889 := bstep (se 2 (by rfl) ⟨1138083, by rfl⟩ : syracuseStep 3034889 = 2276167) B2276167
theorem B3034907 : Blo 1346992 3034907 := bstep (se 1 (by rfl) ⟨2276180, by rfl⟩ : syracuseStep 3034907 = 4552361) B4552361
theorem B1347615 : Blo 1346992 1347615 := bstep (se 1 (by rfl) ⟨1010711, by rfl⟩ : syracuseStep 1347615 = 2021423) B2021423
theorem B46714913 : Blo 1346992 46714913 := bstep (se 2 (by rfl) ⟨17518092, by rfl⟩ : syracuseStep 46714913 = 35036185) B35036185
theorem B3035177 : Blo 1346992 3035177 := bstep (se 2 (by rfl) ⟨1138191, by rfl⟩ : syracuseStep 3035177 = 2276383) B2276383
theorem B2732087 : Blo 1346992 2732087 := bstep (se 1 (by rfl) ⟨2049065, by rfl⟩ : syracuseStep 2732087 = 4098131) B4098131
theorem B1347823 : Blo 1346992 1347823 := bstep (se 1 (by rfl) ⟨1010867, by rfl⟩ : syracuseStep 1347823 = 2021735) B2021735
theorem B2462107 : Blo 1346992 2462107 := bstep (se 1 (by rfl) ⟨1846580, by rfl⟩ : syracuseStep 2462107 = 3693161) B3693161
theorem B1348379 : Blo 1346992 1348379 := bstep (se 1 (by rfl) ⟨1011284, by rfl⟩ : syracuseStep 1348379 = 2022569) B2022569
theorem B1348775 : Blo 1346992 1348775 := bstep (se 1 (by rfl) ⟨1011581, by rfl⟩ : syracuseStep 1348775 = 2023163) B2023163
theorem B1348911 : Blo 1346992 1348911 := bstep (se 1 (by rfl) ⟨1011683, by rfl⟩ : syracuseStep 1348911 = 2023367) B2023367
theorem B2020799 : Blo 1346992 2020799 := bstep (se 1 (by rfl) ⟨1515599, by rfl⟩ : syracuseStep 2020799 = 3031199) B3031199
theorem B2733563 : Blo 1346992 2733563 := bstep (se 1 (by rfl) ⟨2050172, by rfl⟩ : syracuseStep 2733563 = 4100345) B4100345
theorem B5117687 : Blo 1346992 5117687 := bstep (se 1 (by rfl) ⟨3838265, by rfl⟩ : syracuseStep 5117687 = 7676531) B7676531
theorem B2021129 : Blo 1346992 2021129 := bstep (se 2 (by rfl) ⟨757923, by rfl⟩ : syracuseStep 2021129 = 1515847) B1515847
theorem B18454601 : Blo 1346992 18454601 := bstep (se 2 (by rfl) ⟨6920475, by rfl⟩ : syracuseStep 18454601 = 13840951) B13840951
theorem B2021627 : Blo 1346992 2021627 := bstep (se 1 (by rfl) ⟨1516220, by rfl⟩ : syracuseStep 2021627 = 3032441) B3032441
theorem B6822143 : Blo 1346992 6822143 := bstep (se 1 (by rfl) ⟨5116607, by rfl⟩ : syracuseStep 6822143 = 10233215) B10233215
theorem B12958181 : Blo 1346992 12958181 := bstep (se 4 (by rfl) ⟨1214829, by rfl⟩ : syracuseStep 12958181 = 2429659) B2429659
theorem B11082349 : Blo 1346992 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B2022119 : Blo 1346992 2022119 := bstep (se 1 (by rfl) ⟨1516589, by rfl⟩ : syracuseStep 2022119 = 3033179) B3033179
theorem B2022143 : Blo 1346992 2022143 := bstep (se 1 (by rfl) ⟨1516607, by rfl⟩ : syracuseStep 2022143 = 3033215) B3033215
theorem B3841307 : Blo 1346992 3841307 := bstep (se 1 (by rfl) ⟨2880980, by rfl⟩ : syracuseStep 3841307 = 5761961) B5761961
theorem B6823277 : Blo 1346992 6823277 := bstep (se 3 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 6823277 = 2558729) B2558729
theorem B5537279 : Blo 1346992 5537279 := bstep (se 1 (by rfl) ⟨4152959, by rfl⟩ : syracuseStep 5537279 = 8305919) B8305919
theorem B2022953 : Blo 1346992 2022953 := bstep (se 2 (by rfl) ⟨758607, by rfl⟩ : syracuseStep 2022953 = 1517215) B1517215
theorem B2023451 : Blo 1346992 2023451 := bstep (se 1 (by rfl) ⟨1517588, by rfl⟩ : syracuseStep 2023451 = 3035177) B3035177
theorem B4547177 : Blo 1346992 4547177 := bstep (se 2 (by rfl) ⟨1705191, by rfl⟩ : syracuseStep 4547177 = 3410383) B3410383
theorem B3032315 : Blo 1346992 3032315 := bstep (se 1 (by rfl) ⟨2274236, by rfl⟩ : syracuseStep 3032315 = 4548473) B4548473
theorem B2557241 : Blo 1346992 2557241 := bstep (se 2 (by rfl) ⟨958965, by rfl⟩ : syracuseStep 2557241 = 1917931) B1917931
theorem B8635895 : Blo 1346992 8635895 := bstep (se 1 (by rfl) ⟨6476921, by rfl⟩ : syracuseStep 8635895 = 12953843) B12953843
theorem B4548095 : Blo 1346992 4548095 := bstep (se 1 (by rfl) ⟨3411071, by rfl⟩ : syracuseStep 4548095 = 6822143) B6822143
theorem B1705951 : Blo 1346992 1705951 := bstep (se 1 (by rfl) ⟨1279463, by rfl⟩ : syracuseStep 1705951 = 2558927) B2558927
theorem B3409897 : Blo 1346992 3409897 := bstep (se 2 (by rfl) ⟨1278711, by rfl⟩ : syracuseStep 3409897 = 2557423) B2557423
theorem B20744191 : Blo 1346992 20744191 := bstep (se 1 (by rfl) ⟨15558143, by rfl⟩ : syracuseStep 20744191 = 31116287) B31116287
theorem B6146171 : Blo 1346992 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B4548851 : Blo 1346992 4548851 := bstep (se 1 (by rfl) ⟨3411638, by rfl⟩ : syracuseStep 4548851 = 6823277) B6823277
theorem B7285565 : Blo 1346992 7285565 := bstep (se 3 (by rfl) ⟨1366043, by rfl⟩ : syracuseStep 7285565 = 2732087) B2732087
theorem B49212269 : Blo 1346992 49212269 := bstep (se 3 (by rfl) ⟨9227300, by rfl⟩ : syracuseStep 49212269 = 18454601) B18454601
theorem B4550255 : Blo 1346992 4550255 := bstep (se 1 (by rfl) ⟨3412691, by rfl⟩ : syracuseStep 4550255 = 6825383) B6825383
theorem B1347199 : Blo 1346992 1347199 := bstep (se 1 (by rfl) ⟨1010399, by rfl⟩ : syracuseStep 1347199 = 2020799) B2020799
theorem B2879135 : Blo 1346992 2879135 := bstep (se 1 (by rfl) ⟨2159351, by rfl⟩ : syracuseStep 2879135 = 4318703) B4318703
theorem B1822375 : Blo 1346992 1822375 := bstep (se 1 (by rfl) ⟨1366781, by rfl⟩ : syracuseStep 1822375 = 2733563) B2733563
theorem B4550363 : Blo 1346992 4550363 := bstep (se 1 (by rfl) ⟨3412772, by rfl⟩ : syracuseStep 4550363 = 6825545) B6825545
theorem B3411791 : Blo 1346992 3411791 := bstep (se 1 (by rfl) ⟨2558843, by rfl⟩ : syracuseStep 3411791 = 5117687) B5117687
theorem B1347419 : Blo 1346992 1347419 := bstep (se 1 (by rfl) ⟨1010564, by rfl⟩ : syracuseStep 1347419 = 2021129) B2021129
theorem B47329217 : Blo 1346992 47329217 := bstep (se 2 (by rfl) ⟨17748456, by rfl⟩ : syracuseStep 47329217 = 35496913) B35496913
theorem B14766077 : Blo 1346992 14766077 := bstep (se 3 (by rfl) ⟨2768639, by rfl⟩ : syracuseStep 14766077 = 5537279) B5537279
theorem B7671905 : Blo 1346992 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B1347751 : Blo 1346992 1347751 := bstep (se 1 (by rfl) ⟨1010813, by rfl⟩ : syracuseStep 1347751 = 2021627) B2021627
theorem B15364403 : Blo 1346992 15364403 := bstep (se 1 (by rfl) ⟨11523302, by rfl⟩ : syracuseStep 15364403 = 23046605) B23046605
theorem B8638787 : Blo 1346992 8638787 := bstep (se 1 (by rfl) ⟨6479090, by rfl⟩ : syracuseStep 8638787 = 12958181) B12958181
theorem B1348079 : Blo 1346992 1348079 := bstep (se 1 (by rfl) ⟨1011059, by rfl⟩ : syracuseStep 1348079 = 2022119) B2022119
theorem B1348095 : Blo 1346992 1348095 := bstep (se 1 (by rfl) ⟨1011071, by rfl⟩ : syracuseStep 1348095 = 2022143) B2022143
theorem B4551335 : Blo 1346992 4551335 := bstep (se 1 (by rfl) ⟨3413501, by rfl⟩ : syracuseStep 4551335 = 6827003) B6827003
theorem B2560871 : Blo 1346992 2560871 := bstep (se 1 (by rfl) ⟨1920653, by rfl⟩ : syracuseStep 2560871 = 3841307) B3841307
theorem B4551659 : Blo 1346992 4551659 := bstep (se 1 (by rfl) ⟨3413744, by rfl⟩ : syracuseStep 4551659 = 6827489) B6827489
theorem B1348635 : Blo 1346992 1348635 := bstep (se 1 (by rfl) ⟨1011476, by rfl⟩ : syracuseStep 1348635 = 2022953) B2022953
theorem B31143275 : Blo 1346992 31143275 := bstep (se 1 (by rfl) ⟨23357456, by rfl⟩ : syracuseStep 31143275 = 46714913) B46714913
theorem B3282809 : Blo 1346992 3282809 := bstep (se 2 (by rfl) ⟨1231053, by rfl⟩ : syracuseStep 3282809 = 2462107) B2462107
theorem B8755199 : Blo 1346992 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B14776465 : Blo 1346992 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B2021687 : Blo 1346992 2021687 := bstep (se 1 (by rfl) ⟨1516265, by rfl⟩ : syracuseStep 2021687 = 3032531) B3032531
theorem B2022455 : Blo 1346992 2022455 := bstep (se 1 (by rfl) ⟨1516841, by rfl⟩ : syracuseStep 2022455 = 3033683) B3033683
theorem B8641657 : Blo 1346992 8641657 := bstep (se 2 (by rfl) ⟨3240621, by rfl⟩ : syracuseStep 8641657 = 6481243) B6481243
theorem B4546151 : Blo 1346992 4546151 := bstep (se 1 (by rfl) ⟨3409613, by rfl⟩ : syracuseStep 4546151 = 6819227) B6819227
theorem B2023067 : Blo 1346992 2023067 := bstep (se 1 (by rfl) ⟨1517300, by rfl⟩ : syracuseStep 2023067 = 3034601) B3034601
theorem B2023259 : Blo 1346992 2023259 := bstep (se 1 (by rfl) ⟨1517444, by rfl⟩ : syracuseStep 2023259 = 3034889) B3034889
theorem B2023271 : Blo 1346992 2023271 := bstep (se 1 (by rfl) ⟨1517453, by rfl⟩ : syracuseStep 2023271 = 3034907) B3034907
theorem B19701953 : Blo 1346992 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B5759191 : Blo 1346992 5759191 := bstep (se 1 (by rfl) ⟨4319393, by rfl⟩ : syracuseStep 5759191 = 8638787) B8638787
theorem B3031451 : Blo 1346992 3031451 := bstep (se 1 (by rfl) ⟨2273588, by rfl⟩ : syracuseStep 3031451 = 4547177) B4547177
theorem B1704827 : Blo 1346992 1704827 := bstep (se 1 (by rfl) ⟨1278620, by rfl⟩ : syracuseStep 1704827 = 2557241) B2557241
theorem B3032063 : Blo 1346992 3032063 := bstep (se 1 (by rfl) ⟨2274047, by rfl⟩ : syracuseStep 3032063 = 4548095) B4548095
theorem B4097447 : Blo 1346992 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B3032567 : Blo 1346992 3032567 := bstep (se 1 (by rfl) ⟨2274425, by rfl⟩ : syracuseStep 3032567 = 4548851) B4548851
theorem B3033503 : Blo 1346992 3033503 := bstep (se 1 (by rfl) ⟨2275127, by rfl⟩ : syracuseStep 3033503 = 4550255) B4550255
theorem B1919423 : Blo 1346992 1919423 := bstep (se 1 (by rfl) ⟨1439567, by rfl⟩ : syracuseStep 1919423 = 2879135) B2879135
theorem B3033575 : Blo 1346992 3033575 := bstep (se 1 (by rfl) ⟨2275181, by rfl⟩ : syracuseStep 3033575 = 4550363) B4550363
theorem B27658921 : Blo 1346992 27658921 := bstep (se 2 (by rfl) ⟨10372095, by rfl⟩ : syracuseStep 27658921 = 20744191) B20744191
theorem B5114603 : Blo 1346992 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B10242935 : Blo 1346992 10242935 := bstep (se 1 (by rfl) ⟨7682201, by rfl⟩ : syracuseStep 10242935 = 15364403) B15364403
theorem B3034223 : Blo 1346992 3034223 := bstep (se 1 (by rfl) ⟨2275667, by rfl⟩ : syracuseStep 3034223 = 4551335) B4551335
theorem B1707247 : Blo 1346992 1707247 := bstep (se 1 (by rfl) ⟨1280435, by rfl⟩ : syracuseStep 1707247 = 2560871) B2560871
theorem B3034439 : Blo 1346992 3034439 := bstep (se 1 (by rfl) ⟨2275829, by rfl⟩ : syracuseStep 3034439 = 4551659) B4551659
theorem B20762183 : Blo 1346992 20762183 := bstep (se 1 (by rfl) ⟨15571637, by rfl⟩ : syracuseStep 20762183 = 31143275) B31143275
theorem B5836799 : Blo 1346992 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B11522209 : Blo 1346992 11522209 := bstep (se 2 (by rfl) ⟨4320828, by rfl⟩ : syracuseStep 11522209 = 8641657) B8641657
theorem B1347791 : Blo 1346992 1347791 := bstep (se 1 (by rfl) ⟨1010843, by rfl⟩ : syracuseStep 1347791 = 2021687) B2021687
theorem B1348303 : Blo 1346992 1348303 := bstep (se 1 (by rfl) ⟨1011227, by rfl⟩ : syracuseStep 1348303 = 2022455) B2022455
theorem B2429833 : Blo 1346992 2429833 := bstep (se 2 (by rfl) ⟨911187, by rfl⟩ : syracuseStep 2429833 = 1822375) B1822375
theorem B8754157 : Blo 1346992 8754157 := bstep (se 3 (by rfl) ⟨1641404, by rfl⟩ : syracuseStep 8754157 = 3282809) B3282809
theorem B1348711 : Blo 1346992 1348711 := bstep (se 1 (by rfl) ⟨1011533, by rfl⟩ : syracuseStep 1348711 = 2023067) B2023067
theorem B2274527 : Blo 1346992 2274527 := bstep (se 1 (by rfl) ⟨1705895, by rfl⟩ : syracuseStep 2274527 = 3411791) B3411791
theorem B1348839 : Blo 1346992 1348839 := bstep (se 1 (by rfl) ⟨1011629, by rfl⟩ : syracuseStep 1348839 = 2023259) B2023259
theorem B1348847 : Blo 1346992 1348847 := bstep (se 1 (by rfl) ⟨1011635, by rfl⟩ : syracuseStep 1348847 = 2023271) B2023271
theorem B2274601 : Blo 1346992 2274601 := bstep (se 2 (by rfl) ⟨852975, by rfl⟩ : syracuseStep 2274601 = 1705951) B1705951
theorem B31552811 : Blo 1346992 31552811 := bstep (se 1 (by rfl) ⟨23664608, by rfl⟩ : syracuseStep 31552811 = 47329217) B47329217
theorem B39376205 : Blo 1346992 39376205 := bstep (se 3 (by rfl) ⟨7383038, by rfl⟩ : syracuseStep 39376205 = 14766077) B14766077
theorem B1348967 : Blo 1346992 1348967 := bstep (se 1 (by rfl) ⟨1011725, by rfl⟩ : syracuseStep 1348967 = 2023451) B2023451
theorem B2021543 : Blo 1346992 2021543 := bstep (se 1 (by rfl) ⟨1516157, by rfl⟩ : syracuseStep 2021543 = 3032315) B3032315
theorem B5757263 : Blo 1346992 5757263 := bstep (se 1 (by rfl) ⟨4317947, by rfl⟩ : syracuseStep 5757263 = 8635895) B8635895
theorem B4857043 : Blo 1346992 4857043 := bstep (se 1 (by rfl) ⟨3642782, by rfl⟩ : syracuseStep 4857043 = 7285565) B7285565
theorem B32808179 : Blo 1346992 32808179 := bstep (se 1 (by rfl) ⟨24606134, by rfl⟩ : syracuseStep 32808179 = 49212269) B49212269
theorem B3030767 : Blo 1346992 3030767 := bstep (se 1 (by rfl) ⟨2273075, by rfl⟩ : syracuseStep 3030767 = 4546151) B4546151
theorem B4546529 : Blo 1346992 4546529 := bstep (se 2 (by rfl) ⟨1704948, by rfl⟩ : syracuseStep 4546529 = 3409897) B3409897
theorem B1516351 : Blo 1346992 1516351 := bstep (se 1 (by rfl) ⟨1137263, by rfl⟩ : syracuseStep 1516351 = 2274527) B2274527
theorem B3032801 : Blo 1346992 3032801 := bstep (se 2 (by rfl) ⟨1137300, by rfl⟩ : syracuseStep 3032801 = 2274601) B2274601
theorem B43706101 : Blo 1346992 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B3409735 : Blo 1346992 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B13134635 : Blo 1346992 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B15362945 : Blo 1346992 15362945 := bstep (se 2 (by rfl) ⟨5761104, by rfl⟩ : syracuseStep 15362945 = 11522209) B11522209
theorem B7678921 : Blo 1346992 7678921 := bstep (se 2 (by rfl) ⟨2879595, by rfl⟩ : syracuseStep 7678921 = 5759191) B5759191
theorem B26250803 : Blo 1346992 26250803 := bstep (se 1 (by rfl) ⟨19688102, by rfl⟩ : syracuseStep 26250803 = 39376205) B39376205
theorem B3239777 : Blo 1346992 3239777 := bstep (se 2 (by rfl) ⟨1214916, by rfl⟩ : syracuseStep 3239777 = 2429833) B2429833
theorem B1347695 : Blo 1346992 1347695 := bstep (se 1 (by rfl) ⟨1010771, by rfl⟩ : syracuseStep 1347695 = 2021543) B2021543
theorem B3838175 : Blo 1346992 3838175 := bstep (se 1 (by rfl) ⟨2878631, by rfl⟩ : syracuseStep 3838175 = 5757263) B5757263
theorem B6476057 : Blo 1346992 6476057 := bstep (se 2 (by rfl) ⟨2428521, by rfl⟩ : syracuseStep 6476057 = 4857043) B4857043
theorem B6828623 : Blo 1346992 6828623 := bstep (se 1 (by rfl) ⟨5121467, by rfl⟩ : syracuseStep 6828623 = 10242935) B10242935
theorem B13841455 : Blo 1346992 13841455 := bstep (se 1 (by rfl) ⟨10381091, by rfl⟩ : syracuseStep 13841455 = 20762183) B20762183
theorem B2020511 : Blo 1346992 2020511 := bstep (se 1 (by rfl) ⟨1515383, by rfl⟩ : syracuseStep 2020511 = 3030767) B3030767
theorem B2020967 : Blo 1346992 2020967 := bstep (se 1 (by rfl) ⟨1515725, by rfl⟩ : syracuseStep 2020967 = 3031451) B3031451
theorem B2021375 : Blo 1346992 2021375 := bstep (se 1 (by rfl) ⟨1516031, by rfl⟩ : syracuseStep 2021375 = 3032063) B3032063
theorem B21035207 : Blo 1346992 21035207 := bstep (se 1 (by rfl) ⟨15776405, by rfl⟩ : syracuseStep 21035207 = 31552811) B31552811
theorem B36878561 : Blo 1346992 36878561 := bstep (se 2 (by rfl) ⟨13829460, by rfl⟩ : syracuseStep 36878561 = 27658921) B27658921
theorem B2021711 : Blo 1346992 2021711 := bstep (se 1 (by rfl) ⟨1516283, by rfl⟩ : syracuseStep 2021711 = 3032567) B3032567
theorem B5118461 : Blo 1346992 5118461 := bstep (se 3 (by rfl) ⟨959711, by rfl⟩ : syracuseStep 5118461 = 1919423) B1919423
theorem B11672209 : Blo 1346992 11672209 := bstep (se 2 (by rfl) ⟨4377078, by rfl⟩ : syracuseStep 11672209 = 8754157) B8754157
theorem B2022335 : Blo 1346992 2022335 := bstep (se 1 (by rfl) ⟨1516751, by rfl⟩ : syracuseStep 2022335 = 3033503) B3033503
theorem B2276329 : Blo 1346992 2276329 := bstep (se 2 (by rfl) ⟨853623, by rfl⟩ : syracuseStep 2276329 = 1707247) B1707247
theorem B2022383 : Blo 1346992 2022383 := bstep (se 1 (by rfl) ⟨1516787, by rfl⟩ : syracuseStep 2022383 = 3033575) B3033575
theorem B2022815 : Blo 1346992 2022815 := bstep (se 1 (by rfl) ⟨1517111, by rfl⟩ : syracuseStep 2022815 = 3034223) B3034223
theorem B21872119 : Blo 1346992 21872119 := bstep (se 1 (by rfl) ⟨16404089, by rfl⟩ : syracuseStep 21872119 = 32808179) B32808179
theorem B2022959 : Blo 1346992 2022959 := bstep (se 1 (by rfl) ⟨1517219, by rfl⟩ : syracuseStep 2022959 = 3034439) B3034439
theorem B4546205 : Blo 1346992 4546205 := bstep (se 3 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 4546205 = 1704827) B1704827
theorem B3031019 : Blo 1346992 3031019 := bstep (se 1 (by rfl) ⟨2273264, by rfl⟩ : syracuseStep 3031019 = 4546529) B4546529
theorem B3891199 : Blo 1346992 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B4317371 : Blo 1346992 4317371 := bstep (se 1 (by rfl) ⟨3238028, by rfl⟩ : syracuseStep 4317371 = 6476057) B6476057
theorem B24585707 : Blo 1346992 24585707 := bstep (se 1 (by rfl) ⟨18439280, by rfl⟩ : syracuseStep 24585707 = 36878561) B36878561
theorem B10241963 : Blo 1346992 10241963 := bstep (se 1 (by rfl) ⟨7681472, by rfl⟩ : syracuseStep 10241963 = 15362945) B15362945
theorem B17500535 : Blo 1346992 17500535 := bstep (se 1 (by rfl) ⟨13125401, by rfl⟩ : syracuseStep 17500535 = 26250803) B26250803
theorem B5188265 : Blo 1346992 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B2558783 : Blo 1346992 2558783 := bstep (se 1 (by rfl) ⟨1919087, by rfl⟩ : syracuseStep 2558783 = 3838175) B3838175
theorem B56093885 : Blo 1346992 56093885 := bstep (se 3 (by rfl) ⟨10517603, by rfl⟩ : syracuseStep 56093885 = 21035207) B21035207
theorem B1347007 : Blo 1346992 1347007 := bstep (se 1 (by rfl) ⟨1010255, by rfl⟩ : syracuseStep 1347007 = 2020511) B2020511
theorem B1347311 : Blo 1346992 1347311 := bstep (se 1 (by rfl) ⟨1010483, by rfl⟩ : syracuseStep 1347311 = 2020967) B2020967
theorem B3035105 : Blo 1346992 3035105 := bstep (se 2 (by rfl) ⟨1138164, by rfl⟩ : syracuseStep 3035105 = 2276329) B2276329
theorem B1347583 : Blo 1346992 1347583 := bstep (se 1 (by rfl) ⟨1010687, by rfl⟩ : syracuseStep 1347583 = 2021375) B2021375
theorem B1347807 : Blo 1346992 1347807 := bstep (se 1 (by rfl) ⟨1010855, by rfl⟩ : syracuseStep 1347807 = 2021711) B2021711
theorem B3412307 : Blo 1346992 3412307 := bstep (se 1 (by rfl) ⟨2559230, by rfl⟩ : syracuseStep 3412307 = 5118461) B5118461
theorem B1348223 : Blo 1346992 1348223 := bstep (se 1 (by rfl) ⟨1011167, by rfl⟩ : syracuseStep 1348223 = 2022335) B2022335
theorem B1348255 : Blo 1346992 1348255 := bstep (se 1 (by rfl) ⟨1011191, by rfl⟩ : syracuseStep 1348255 = 2022383) B2022383
theorem B1348543 : Blo 1346992 1348543 := bstep (se 1 (by rfl) ⟨1011407, by rfl⟩ : syracuseStep 1348543 = 2022815) B2022815
theorem B58274801 : Blo 1346992 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B1348639 : Blo 1346992 1348639 := bstep (se 1 (by rfl) ⟨1011479, by rfl⟩ : syracuseStep 1348639 = 2022959) B2022959
theorem B2159851 : Blo 1346992 2159851 := bstep (se 1 (by rfl) ⟨1619888, by rfl⟩ : syracuseStep 2159851 = 3239777) B3239777
theorem B2020679 : Blo 1346992 2020679 := bstep (se 1 (by rfl) ⟨1515509, by rfl⟩ : syracuseStep 2020679 = 3031019) B3031019
theorem B4552415 : Blo 1346992 4552415 := bstep (se 1 (by rfl) ⟨3414311, by rfl⟩ : syracuseStep 4552415 = 6828623) B6828623
theorem B15562945 : Blo 1346992 15562945 := bstep (se 2 (by rfl) ⟨5836104, by rfl⟩ : syracuseStep 15562945 = 11672209) B11672209
theorem B2021801 : Blo 1346992 2021801 := bstep (se 2 (by rfl) ⟨758175, by rfl⟩ : syracuseStep 2021801 = 1516351) B1516351
theorem B2021867 : Blo 1346992 2021867 := bstep (se 1 (by rfl) ⟨1516400, by rfl⟩ : syracuseStep 2021867 = 3032801) B3032801
theorem B10238561 : Blo 1346992 10238561 := bstep (se 2 (by rfl) ⟨3839460, by rfl⟩ : syracuseStep 10238561 = 7678921) B7678921
theorem B18455273 : Blo 1346992 18455273 := bstep (se 2 (by rfl) ⟨6920727, by rfl⟩ : syracuseStep 18455273 = 13841455) B13841455
theorem B8756423 : Blo 1346992 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B29162825 : Blo 1346992 29162825 := bstep (se 2 (by rfl) ⟨10936059, by rfl⟩ : syracuseStep 29162825 = 21872119) B21872119
theorem B4546313 : Blo 1346992 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B3030803 : Blo 1346992 3030803 := bstep (se 1 (by rfl) ⟨2273102, by rfl⟩ : syracuseStep 3030803 = 4546205) B4546205
theorem B20750593 : Blo 1346992 20750593 := bstep (se 2 (by rfl) ⟨7781472, by rfl⟩ : syracuseStep 20750593 = 15562945) B15562945
theorem B11667023 : Blo 1346992 11667023 := bstep (se 1 (by rfl) ⟨8750267, by rfl⟩ : syracuseStep 11667023 = 17500535) B17500535
theorem B6825707 : Blo 1346992 6825707 := bstep (se 1 (by rfl) ⟨5119280, by rfl⟩ : syracuseStep 6825707 = 10238561) B10238561
theorem B3458843 : Blo 1346992 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B1705855 : Blo 1346992 1705855 := bstep (se 1 (by rfl) ⟨1279391, by rfl⟩ : syracuseStep 1705855 = 2558783) B2558783
theorem B19441883 : Blo 1346992 19441883 := bstep (se 1 (by rfl) ⟨14581412, by rfl⟩ : syracuseStep 19441883 = 29162825) B29162825
theorem B2878247 : Blo 1346992 2878247 := bstep (se 1 (by rfl) ⟨2158685, by rfl⟩ : syracuseStep 2878247 = 4317371) B4317371
theorem B38849867 : Blo 1346992 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B1347119 : Blo 1346992 1347119 := bstep (se 1 (by rfl) ⟨1010339, by rfl⟩ : syracuseStep 1347119 = 2020679) B2020679
theorem B3034943 : Blo 1346992 3034943 := bstep (se 1 (by rfl) ⟨2276207, by rfl⟩ : syracuseStep 3034943 = 4552415) B4552415
theorem B6827975 : Blo 1346992 6827975 := bstep (se 1 (by rfl) ⟨5120981, by rfl⟩ : syracuseStep 6827975 = 10241963) B10241963
theorem B1347867 : Blo 1346992 1347867 := bstep (se 1 (by rfl) ⟨1010900, by rfl⟩ : syracuseStep 1347867 = 2021801) B2021801
theorem B2879801 : Blo 1346992 2879801 := bstep (se 2 (by rfl) ⟨1079925, by rfl⟩ : syracuseStep 2879801 = 2159851) B2159851
theorem B1347911 : Blo 1346992 1347911 := bstep (se 1 (by rfl) ⟨1010933, by rfl⟩ : syracuseStep 1347911 = 2021867) B2021867
theorem B5837615 : Blo 1346992 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B2020535 : Blo 1346992 2020535 := bstep (se 1 (by rfl) ⟨1515401, by rfl⟩ : syracuseStep 2020535 = 3030803) B3030803
theorem B2274871 : Blo 1346992 2274871 := bstep (se 1 (by rfl) ⟨1706153, by rfl⟩ : syracuseStep 2274871 = 3412307) B3412307
theorem B16390471 : Blo 1346992 16390471 := bstep (se 1 (by rfl) ⟨12292853, by rfl⟩ : syracuseStep 16390471 = 24585707) B24585707
theorem B12303515 : Blo 1346992 12303515 := bstep (se 1 (by rfl) ⟨9227636, by rfl⟩ : syracuseStep 12303515 = 18455273) B18455273
theorem B37395923 : Blo 1346992 37395923 := bstep (se 1 (by rfl) ⟨28046942, by rfl⟩ : syracuseStep 37395923 = 56093885) B56093885
theorem B3030875 : Blo 1346992 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B2023403 : Blo 1346992 2023403 := bstep (se 1 (by rfl) ⟨1517552, by rfl⟩ : syracuseStep 2023403 = 3035105) B3035105
theorem B3891743 : Blo 1346992 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B99722461 : Blo 1346992 99722461 := bstep (se 3 (by rfl) ⟨18697961, by rfl⟩ : syracuseStep 99722461 = 37395923) B37395923
theorem B1918831 : Blo 1346992 1918831 := bstep (se 1 (by rfl) ⟨1439123, by rfl⟩ : syracuseStep 1918831 = 2878247) B2878247
theorem B3033161 : Blo 1346992 3033161 := bstep (se 2 (by rfl) ⟨1137435, by rfl⟩ : syracuseStep 3033161 = 2274871) B2274871
theorem B8202343 : Blo 1346992 8202343 := bstep (se 1 (by rfl) ⟨6151757, by rfl⟩ : syracuseStep 8202343 = 12303515) B12303515
theorem B1919867 : Blo 1346992 1919867 := bstep (se 1 (by rfl) ⟨1439900, by rfl⟩ : syracuseStep 1919867 = 2879801) B2879801
theorem B27667457 : Blo 1346992 27667457 := bstep (se 2 (by rfl) ⟨10375296, by rfl⟩ : syracuseStep 27667457 = 20750593) B20750593
theorem B1347023 : Blo 1346992 1347023 := bstep (se 1 (by rfl) ⟨1010267, by rfl⟩ : syracuseStep 1347023 = 2020535) B2020535
theorem B7778015 : Blo 1346992 7778015 := bstep (se 1 (by rfl) ⟨5833511, by rfl⟩ : syracuseStep 7778015 = 11667023) B11667023
theorem B4550471 : Blo 1346992 4550471 := bstep (se 1 (by rfl) ⟨3412853, by rfl⟩ : syracuseStep 4550471 = 6825707) B6825707
theorem B25899911 : Blo 1346992 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B2274473 : Blo 1346992 2274473 := bstep (se 2 (by rfl) ⟨852927, by rfl⟩ : syracuseStep 2274473 = 1705855) B1705855
theorem B2020583 : Blo 1346992 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B4551983 : Blo 1346992 4551983 := bstep (se 1 (by rfl) ⟨3413987, by rfl⟩ : syracuseStep 4551983 = 6827975) B6827975
theorem B1348935 : Blo 1346992 1348935 := bstep (se 1 (by rfl) ⟨1011701, by rfl⟩ : syracuseStep 1348935 = 2023403) B2023403
theorem B36894325 : Blo 1346992 36894325 := bstep (se 5 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 36894325 = 3458843) B3458843
theorem B21853961 : Blo 1346992 21853961 := bstep (se 2 (by rfl) ⟨8195235, by rfl⟩ : syracuseStep 21853961 = 16390471) B16390471
theorem B51845021 : Blo 1346992 51845021 := bstep (se 3 (by rfl) ⟨9720941, by rfl⟩ : syracuseStep 51845021 = 19441883) B19441883
theorem B2023295 : Blo 1346992 2023295 := bstep (se 1 (by rfl) ⟨1517471, by rfl⟩ : syracuseStep 2023295 = 3034943) B3034943
theorem B10936457 : Blo 1346992 10936457 := bstep (se 2 (by rfl) ⟨4101171, by rfl⟩ : syracuseStep 10936457 = 8202343) B8202343
theorem B1516315 : Blo 1346992 1516315 := bstep (se 1 (by rfl) ⟨1137236, by rfl⟩ : syracuseStep 1516315 = 2274473) B2274473
theorem B34563347 : Blo 1346992 34563347 := bstep (se 1 (by rfl) ⟨25922510, by rfl⟩ : syracuseStep 34563347 = 51845021) B51845021
theorem B2558441 : Blo 1346992 2558441 := bstep (se 2 (by rfl) ⟨959415, by rfl⟩ : syracuseStep 2558441 = 1918831) B1918831
theorem B3033647 : Blo 1346992 3033647 := bstep (se 1 (by rfl) ⟨2275235, by rfl⟩ : syracuseStep 3033647 = 4550471) B4550471
theorem B1347055 : Blo 1346992 1347055 := bstep (se 1 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 1347055 = 2020583) B2020583
theorem B3034655 : Blo 1346992 3034655 := bstep (se 1 (by rfl) ⟨2275991, by rfl⟩ : syracuseStep 3034655 = 4551983) B4551983
theorem B14569307 : Blo 1346992 14569307 := bstep (se 1 (by rfl) ⟨10926980, by rfl⟩ : syracuseStep 14569307 = 21853961) B21853961
theorem B18444971 : Blo 1346992 18444971 := bstep (se 1 (by rfl) ⟨13833728, by rfl⟩ : syracuseStep 18444971 = 27667457) B27667457
theorem B1348863 : Blo 1346992 1348863 := bstep (se 1 (by rfl) ⟨1011647, by rfl⟩ : syracuseStep 1348863 = 2023295) B2023295
theorem B2594495 : Blo 1346992 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B17266607 : Blo 1346992 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B2022107 : Blo 1346992 2022107 := bstep (se 1 (by rfl) ⟨1516580, by rfl⟩ : syracuseStep 2022107 = 3033161) B3033161
theorem B132963281 : Blo 1346992 132963281 := bstep (se 2 (by rfl) ⟨49861230, by rfl⟩ : syracuseStep 132963281 = 99722461) B99722461
theorem B49192433 : Blo 1346992 49192433 := bstep (se 2 (by rfl) ⟨18447162, by rfl⟩ : syracuseStep 49192433 = 36894325) B36894325
theorem B5119645 : Blo 1346992 5119645 := bstep (se 3 (by rfl) ⟨959933, by rfl⟩ : syracuseStep 5119645 = 1919867) B1919867
theorem B5185343 : Blo 1346992 5185343 := bstep (se 1 (by rfl) ⟨3889007, by rfl⟩ : syracuseStep 5185343 = 7778015) B7778015
theorem B7290971 : Blo 1346992 7290971 := bstep (se 1 (by rfl) ⟨5468228, by rfl⟩ : syracuseStep 7290971 = 10936457) B10936457
theorem B12296647 : Blo 1346992 12296647 := bstep (se 1 (by rfl) ⟨9222485, by rfl⟩ : syracuseStep 12296647 = 18444971) B18444971
theorem B1729663 : Blo 1346992 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B11511071 : Blo 1346992 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B1705627 : Blo 1346992 1705627 := bstep (se 1 (by rfl) ⟨1279220, by rfl⟩ : syracuseStep 1705627 = 2558441) B2558441
theorem B6826193 : Blo 1346992 6826193 := bstep (se 2 (by rfl) ⟨2559822, by rfl⟩ : syracuseStep 6826193 = 5119645) B5119645
theorem B32794955 : Blo 1346992 32794955 := bstep (se 1 (by rfl) ⟨24596216, by rfl⟩ : syracuseStep 32794955 = 49192433) B49192433
theorem B1348071 : Blo 1346992 1348071 := bstep (se 1 (by rfl) ⟨1011053, by rfl⟩ : syracuseStep 1348071 = 2022107) B2022107
theorem B88642187 : Blo 1346992 88642187 := bstep (se 1 (by rfl) ⟨66481640, by rfl⟩ : syracuseStep 88642187 = 132963281) B132963281
theorem B9712871 : Blo 1346992 9712871 := bstep (se 1 (by rfl) ⟨7284653, by rfl⟩ : syracuseStep 9712871 = 14569307) B14569307
theorem B23042231 : Blo 1346992 23042231 := bstep (se 1 (by rfl) ⟨17281673, by rfl⟩ : syracuseStep 23042231 = 34563347) B34563347
theorem B2021753 : Blo 1346992 2021753 := bstep (se 2 (by rfl) ⟨758157, by rfl⟩ : syracuseStep 2021753 = 1516315) B1516315
theorem B2022431 : Blo 1346992 2022431 := bstep (se 1 (by rfl) ⟨1516823, by rfl⟩ : syracuseStep 2022431 = 3033647) B3033647
theorem B13827581 : Blo 1346992 13827581 := bstep (se 3 (by rfl) ⟨2592671, by rfl⟩ : syracuseStep 13827581 = 5185343) B5185343
theorem B2023103 : Blo 1346992 2023103 := bstep (se 1 (by rfl) ⟨1517327, by rfl⟩ : syracuseStep 2023103 = 3034655) B3034655
theorem B9224869 : Blo 1346992 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B15361487 : Blo 1346992 15361487 := bstep (se 1 (by rfl) ⟨11521115, by rfl⟩ : syracuseStep 15361487 = 23042231) B23042231
theorem B9218387 : Blo 1346992 9218387 := bstep (se 1 (by rfl) ⟨6913790, by rfl⟩ : syracuseStep 9218387 = 13827581) B13827581
theorem B4860647 : Blo 1346992 4860647 := bstep (se 1 (by rfl) ⟨3645485, by rfl⟩ : syracuseStep 4860647 = 7290971) B7290971
theorem B16395529 : Blo 1346992 16395529 := bstep (se 2 (by rfl) ⟨6148323, by rfl⟩ : syracuseStep 16395529 = 12296647) B12296647
theorem B6475247 : Blo 1346992 6475247 := bstep (se 1 (by rfl) ⟨4856435, by rfl⟩ : syracuseStep 6475247 = 9712871) B9712871
theorem B4550795 : Blo 1346992 4550795 := bstep (se 1 (by rfl) ⟨3413096, by rfl⟩ : syracuseStep 4550795 = 6826193) B6826193
theorem B1347835 : Blo 1346992 1347835 := bstep (se 1 (by rfl) ⟨1010876, by rfl⟩ : syracuseStep 1347835 = 2021753) B2021753
theorem B1348287 : Blo 1346992 1348287 := bstep (se 1 (by rfl) ⟨1011215, by rfl⟩ : syracuseStep 1348287 = 2022431) B2022431
theorem B2274169 : Blo 1346992 2274169 := bstep (se 2 (by rfl) ⟨852813, by rfl⟩ : syracuseStep 2274169 = 1705627) B1705627
theorem B1348735 : Blo 1346992 1348735 := bstep (se 1 (by rfl) ⟨1011551, by rfl⟩ : syracuseStep 1348735 = 2023103) B2023103
theorem B59094791 : Blo 1346992 59094791 := bstep (se 1 (by rfl) ⟨44321093, by rfl⟩ : syracuseStep 59094791 = 88642187) B88642187
theorem B7674047 : Blo 1346992 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B21863303 : Blo 1346992 21863303 := bstep (se 1 (by rfl) ⟨16397477, by rfl⟩ : syracuseStep 21863303 = 32794955) B32794955
theorem B10240991 : Blo 1346992 10240991 := bstep (se 1 (by rfl) ⟨7680743, by rfl⟩ : syracuseStep 10240991 = 15361487) B15361487
theorem B3032225 : Blo 1346992 3032225 := bstep (se 2 (by rfl) ⟨1137084, by rfl⟩ : syracuseStep 3032225 = 2274169) B2274169
theorem B39396527 : Blo 1346992 39396527 := bstep (se 1 (by rfl) ⟨29547395, by rfl⟩ : syracuseStep 39396527 = 59094791) B59094791
theorem B6145591 : Blo 1346992 6145591 := bstep (se 1 (by rfl) ⟨4609193, by rfl⟩ : syracuseStep 6145591 = 9218387) B9218387
theorem B14575535 : Blo 1346992 14575535 := bstep (se 1 (by rfl) ⟨10931651, by rfl⟩ : syracuseStep 14575535 = 21863303) B21863303
theorem B3033863 : Blo 1346992 3033863 := bstep (se 1 (by rfl) ⟨2275397, by rfl⟩ : syracuseStep 3033863 = 4550795) B4550795
theorem B12299825 : Blo 1346992 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B5116031 : Blo 1346992 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B21860705 : Blo 1346992 21860705 := bstep (se 2 (by rfl) ⟨8197764, by rfl⟩ : syracuseStep 21860705 = 16395529) B16395529
theorem B3240431 : Blo 1346992 3240431 := bstep (se 1 (by rfl) ⟨2430323, by rfl⟩ : syracuseStep 3240431 = 4860647) B4860647
theorem B4316831 : Blo 1346992 4316831 := bstep (se 1 (by rfl) ⟨3237623, by rfl⟩ : syracuseStep 4316831 = 6475247) B6475247
theorem B14573803 : Blo 1346992 14573803 := bstep (se 1 (by rfl) ⟨10930352, by rfl⟩ : syracuseStep 14573803 = 21860705) B21860705
theorem B26264351 : Blo 1346992 26264351 := bstep (se 1 (by rfl) ⟨19698263, by rfl⟩ : syracuseStep 26264351 = 39396527) B39396527
theorem B9717023 : Blo 1346992 9717023 := bstep (se 1 (by rfl) ⟨7287767, by rfl⟩ : syracuseStep 9717023 = 14575535) B14575535
theorem B8194121 : Blo 1346992 8194121 := bstep (se 2 (by rfl) ⟨3072795, by rfl⟩ : syracuseStep 8194121 = 6145591) B6145591
theorem B2877887 : Blo 1346992 2877887 := bstep (se 1 (by rfl) ⟨2158415, by rfl⟩ : syracuseStep 2877887 = 4316831) B4316831
theorem B3410687 : Blo 1346992 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B6827327 : Blo 1346992 6827327 := bstep (se 1 (by rfl) ⟨5120495, by rfl⟩ : syracuseStep 6827327 = 10240991) B10240991
theorem B2160287 : Blo 1346992 2160287 := bstep (se 1 (by rfl) ⟨1620215, by rfl⟩ : syracuseStep 2160287 = 3240431) B3240431
theorem B2021483 : Blo 1346992 2021483 := bstep (se 1 (by rfl) ⟨1516112, by rfl⟩ : syracuseStep 2021483 = 3032225) B3032225
theorem B2022575 : Blo 1346992 2022575 := bstep (se 1 (by rfl) ⟨1516931, by rfl⟩ : syracuseStep 2022575 = 3033863) B3033863
theorem B8199883 : Blo 1346992 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B19431737 : Blo 1346992 19431737 := bstep (se 2 (by rfl) ⟨7286901, by rfl⟩ : syracuseStep 19431737 = 14573803) B14573803
theorem B17509567 : Blo 1346992 17509567 := bstep (se 1 (by rfl) ⟨13132175, by rfl⟩ : syracuseStep 17509567 = 26264351) B26264351
theorem B43732709 : Blo 1346992 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B1347655 : Blo 1346992 1347655 := bstep (se 1 (by rfl) ⟨1010741, by rfl⟩ : syracuseStep 1347655 = 2021483) B2021483
theorem B2273791 : Blo 1346992 2273791 := bstep (se 1 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 2273791 = 3410687) B3410687
theorem B1348383 : Blo 1346992 1348383 := bstep (se 1 (by rfl) ⟨1011287, by rfl⟩ : syracuseStep 1348383 = 2022575) B2022575
theorem B4551551 : Blo 1346992 4551551 := bstep (se 1 (by rfl) ⟨3413663, by rfl⟩ : syracuseStep 4551551 = 6827327) B6827327
theorem B6478015 : Blo 1346992 6478015 := bstep (se 1 (by rfl) ⟨4858511, by rfl⟩ : syracuseStep 6478015 = 9717023) B9717023
theorem B1440191 : Blo 1346992 1440191 := bstep (se 1 (by rfl) ⟨1080143, by rfl⟩ : syracuseStep 1440191 = 2160287) B2160287
theorem B7674365 : Blo 1346992 7674365 := bstep (se 3 (by rfl) ⟨1438943, by rfl⟩ : syracuseStep 7674365 = 2877887) B2877887
theorem B5462747 : Blo 1346992 5462747 := bstep (se 1 (by rfl) ⟨4097060, by rfl⟩ : syracuseStep 5462747 = 8194121) B8194121
theorem B3031721 : Blo 1346992 3031721 := bstep (se 2 (by rfl) ⟨1136895, by rfl⟩ : syracuseStep 3031721 = 2273791) B2273791
theorem B12954491 : Blo 1346992 12954491 := bstep (se 1 (by rfl) ⟨9715868, by rfl⟩ : syracuseStep 12954491 = 19431737) B19431737
theorem B8637353 : Blo 1346992 8637353 := bstep (se 2 (by rfl) ⟨3239007, by rfl⟩ : syracuseStep 8637353 = 6478015) B6478015
theorem B3034367 : Blo 1346992 3034367 := bstep (se 1 (by rfl) ⟨2275775, by rfl⟩ : syracuseStep 3034367 = 4551551) B4551551
theorem B5116243 : Blo 1346992 5116243 := bstep (se 1 (by rfl) ⟨3837182, by rfl⟩ : syracuseStep 5116243 = 7674365) B7674365
theorem B3641831 : Blo 1346992 3641831 := bstep (se 1 (by rfl) ⟨2731373, by rfl⟩ : syracuseStep 3641831 = 5462747) B5462747
theorem B3840509 : Blo 1346992 3840509 := bstep (se 3 (by rfl) ⟨720095, by rfl⟩ : syracuseStep 3840509 = 1440191) B1440191
theorem B23346089 : Blo 1346992 23346089 := bstep (se 2 (by rfl) ⟨8754783, by rfl⟩ : syracuseStep 23346089 = 17509567) B17509567
theorem B29155139 : Blo 1346992 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B8636327 : Blo 1346992 8636327 := bstep (se 1 (by rfl) ⟨6477245, by rfl⟩ : syracuseStep 8636327 = 12954491) B12954491
theorem B2427887 : Blo 1346992 2427887 := bstep (se 1 (by rfl) ⟨1820915, by rfl⟩ : syracuseStep 2427887 = 3641831) B3641831
theorem B2560339 : Blo 1346992 2560339 := bstep (se 1 (by rfl) ⟨1920254, by rfl⟩ : syracuseStep 2560339 = 3840509) B3840509
theorem B19436759 : Blo 1346992 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B6821657 : Blo 1346992 6821657 := bstep (se 2 (by rfl) ⟨2558121, by rfl⟩ : syracuseStep 6821657 = 5116243) B5116243
theorem B2021147 : Blo 1346992 2021147 := bstep (se 1 (by rfl) ⟨1515860, by rfl⟩ : syracuseStep 2021147 = 3031721) B3031721
theorem B15564059 : Blo 1346992 15564059 := bstep (se 1 (by rfl) ⟨11673044, by rfl⟩ : syracuseStep 15564059 = 23346089) B23346089
theorem B5758235 : Blo 1346992 5758235 := bstep (se 1 (by rfl) ⟨4318676, by rfl⟩ : syracuseStep 5758235 = 8637353) B8637353
theorem B2022911 : Blo 1346992 2022911 := bstep (se 1 (by rfl) ⟨1517183, by rfl⟩ : syracuseStep 2022911 = 3034367) B3034367
theorem B4547771 : Blo 1346992 4547771 := bstep (se 1 (by rfl) ⟨3410828, by rfl⟩ : syracuseStep 4547771 = 6821657) B6821657
theorem B1347431 : Blo 1346992 1347431 := bstep (se 1 (by rfl) ⟨1010573, by rfl⟩ : syracuseStep 1347431 = 2021147) B2021147
theorem B1618591 : Blo 1346992 1618591 := bstep (se 1 (by rfl) ⟨1213943, by rfl⟩ : syracuseStep 1618591 = 2427887) B2427887
theorem B10376039 : Blo 1346992 10376039 := bstep (se 1 (by rfl) ⟨7782029, by rfl⟩ : syracuseStep 10376039 = 15564059) B15564059
theorem B3838823 : Blo 1346992 3838823 := bstep (se 1 (by rfl) ⟨2879117, by rfl⟩ : syracuseStep 3838823 = 5758235) B5758235
theorem B1348607 : Blo 1346992 1348607 := bstep (se 1 (by rfl) ⟨1011455, by rfl⟩ : syracuseStep 1348607 = 2022911) B2022911
theorem B3413785 : Blo 1346992 3413785 := bstep (se 2 (by rfl) ⟨1280169, by rfl⟩ : syracuseStep 3413785 = 2560339) B2560339
theorem B12957839 : Blo 1346992 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B5757551 : Blo 1346992 5757551 := bstep (se 1 (by rfl) ⟨4318163, by rfl⟩ : syracuseStep 5757551 = 8636327) B8636327
theorem B3031847 : Blo 1346992 3031847 := bstep (se 1 (by rfl) ⟨2273885, by rfl⟩ : syracuseStep 3031847 = 4547771) B4547771
theorem B6917359 : Blo 1346992 6917359 := bstep (se 1 (by rfl) ⟨5188019, by rfl⟩ : syracuseStep 6917359 = 10376039) B10376039
theorem B2559215 : Blo 1346992 2559215 := bstep (se 1 (by rfl) ⟨1919411, by rfl⟩ : syracuseStep 2559215 = 3838823) B3838823
theorem B2158121 : Blo 1346992 2158121 := bstep (se 2 (by rfl) ⟨809295, by rfl⟩ : syracuseStep 2158121 = 1618591) B1618591
theorem B8638559 : Blo 1346992 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B3838367 : Blo 1346992 3838367 := bstep (se 1 (by rfl) ⟨2878775, by rfl⟩ : syracuseStep 3838367 = 5757551) B5757551
theorem B4551713 : Blo 1346992 4551713 := bstep (se 2 (by rfl) ⟨1706892, by rfl⟩ : syracuseStep 4551713 = 3413785) B3413785
theorem B5759039 : Blo 1346992 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B6824573 : Blo 1346992 6824573 := bstep (se 3 (by rfl) ⟨1279607, by rfl⟩ : syracuseStep 6824573 = 2559215) B2559215
theorem B3034475 : Blo 1346992 3034475 := bstep (se 1 (by rfl) ⟨2275856, by rfl⟩ : syracuseStep 3034475 = 4551713) B4551713
theorem B10235645 : Blo 1346992 10235645 := bstep (se 3 (by rfl) ⟨1919183, by rfl⟩ : syracuseStep 10235645 = 3838367) B3838367
theorem B5754989 : Blo 1346992 5754989 := bstep (se 3 (by rfl) ⟨1079060, by rfl⟩ : syracuseStep 5754989 = 2158121) B2158121
theorem B2021231 : Blo 1346992 2021231 := bstep (se 1 (by rfl) ⟨1515923, by rfl⟩ : syracuseStep 2021231 = 3031847) B3031847
theorem B9223145 : Blo 1346992 9223145 := bstep (se 2 (by rfl) ⟨3458679, by rfl⟩ : syracuseStep 9223145 = 6917359) B6917359
theorem B3836659 : Blo 1346992 3836659 := bstep (se 1 (by rfl) ⟨2877494, by rfl⟩ : syracuseStep 3836659 = 5754989) B5754989
theorem B4549715 : Blo 1346992 4549715 := bstep (se 1 (by rfl) ⟨3412286, by rfl⟩ : syracuseStep 4549715 = 6824573) B6824573
theorem B1347487 : Blo 1346992 1347487 := bstep (se 1 (by rfl) ⟨1010615, by rfl⟩ : syracuseStep 1347487 = 2021231) B2021231
theorem B6148763 : Blo 1346992 6148763 := bstep (se 1 (by rfl) ⟨4611572, by rfl⟩ : syracuseStep 6148763 = 9223145) B9223145
theorem B3839359 : Blo 1346992 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B2022983 : Blo 1346992 2022983 := bstep (se 1 (by rfl) ⟨1517237, by rfl⟩ : syracuseStep 2022983 = 3034475) B3034475
theorem B6823763 : Blo 1346992 6823763 := bstep (se 1 (by rfl) ⟨5117822, by rfl⟩ : syracuseStep 6823763 = 10235645) B10235645
theorem B3033143 : Blo 1346992 3033143 := bstep (se 1 (by rfl) ⟨2274857, by rfl⟩ : syracuseStep 3033143 = 4549715) B4549715
theorem B4549175 : Blo 1346992 4549175 := bstep (se 1 (by rfl) ⟨3411881, by rfl⟩ : syracuseStep 4549175 = 6823763) B6823763
theorem B4099175 : Blo 1346992 4099175 := bstep (se 1 (by rfl) ⟨3074381, by rfl⟩ : syracuseStep 4099175 = 6148763) B6148763
theorem B5115545 : Blo 1346992 5115545 := bstep (se 2 (by rfl) ⟨1918329, by rfl⟩ : syracuseStep 5115545 = 3836659) B3836659
theorem B1348655 : Blo 1346992 1348655 := bstep (se 1 (by rfl) ⟨1011491, by rfl⟩ : syracuseStep 1348655 = 2022983) B2022983
theorem B5119145 : Blo 1346992 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B3032783 : Blo 1346992 3032783 := bstep (se 1 (by rfl) ⟨2274587, by rfl⟩ : syracuseStep 3032783 = 4549175) B4549175
theorem B3410363 : Blo 1346992 3410363 := bstep (se 1 (by rfl) ⟨2557772, by rfl⟩ : syracuseStep 3410363 = 5115545) B5115545
theorem B2732783 : Blo 1346992 2732783 := bstep (se 1 (by rfl) ⟨2049587, by rfl⟩ : syracuseStep 2732783 = 4099175) B4099175
theorem B3412763 : Blo 1346992 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B2022095 : Blo 1346992 2022095 := bstep (se 1 (by rfl) ⟨1516571, by rfl⟩ : syracuseStep 2022095 = 3033143) B3033143
theorem B2273575 : Blo 1346992 2273575 := bstep (se 1 (by rfl) ⟨1705181, by rfl⟩ : syracuseStep 2273575 = 3410363) B3410363
theorem B1348063 : Blo 1346992 1348063 := bstep (se 1 (by rfl) ⟨1011047, by rfl⟩ : syracuseStep 1348063 = 2022095) B2022095
theorem B7287421 : Blo 1346992 7287421 := bstep (se 3 (by rfl) ⟨1366391, by rfl⟩ : syracuseStep 7287421 = 2732783) B2732783
theorem B2275175 : Blo 1346992 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B2021855 : Blo 1346992 2021855 := bstep (se 1 (by rfl) ⟨1516391, by rfl⟩ : syracuseStep 2021855 = 3032783) B3032783
theorem B3031433 : Blo 1346992 3031433 := bstep (se 2 (by rfl) ⟨1136787, by rfl⟩ : syracuseStep 3031433 = 2273575) B2273575
theorem B9716561 : Blo 1346992 9716561 := bstep (se 2 (by rfl) ⟨3643710, by rfl⟩ : syracuseStep 9716561 = 7287421) B7287421
theorem B1516783 : Blo 1346992 1516783 := bstep (se 1 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 1516783 = 2275175) B2275175
theorem B1347903 : Blo 1346992 1347903 := bstep (se 1 (by rfl) ⟨1010927, by rfl⟩ : syracuseStep 1347903 = 2021855) B2021855
theorem B2020955 : Blo 1346992 2020955 := bstep (se 1 (by rfl) ⟨1515716, by rfl⟩ : syracuseStep 2020955 = 3031433) B3031433
theorem B6477707 : Blo 1346992 6477707 := bstep (se 1 (by rfl) ⟨4858280, by rfl⟩ : syracuseStep 6477707 = 9716561) B9716561
theorem B2022377 : Blo 1346992 2022377 := bstep (se 2 (by rfl) ⟨758391, by rfl⟩ : syracuseStep 2022377 = 1516783) B1516783
theorem B4318471 : Blo 1346992 4318471 := bstep (se 1 (by rfl) ⟨3238853, by rfl⟩ : syracuseStep 4318471 = 6477707) B6477707
theorem B1347303 : Blo 1346992 1347303 := bstep (se 1 (by rfl) ⟨1010477, by rfl⟩ : syracuseStep 1347303 = 2020955) B2020955
theorem B1348251 : Blo 1346992 1348251 := bstep (se 1 (by rfl) ⟨1011188, by rfl⟩ : syracuseStep 1348251 = 2022377) B2022377
theorem B5757961 : Blo 1346992 5757961 := bstep (se 2 (by rfl) ⟨2159235, by rfl⟩ : syracuseStep 5757961 = 4318471) B4318471
theorem B7677281 : Blo 1346992 7677281 := bstep (se 2 (by rfl) ⟨2878980, by rfl⟩ : syracuseStep 7677281 = 5757961) B5757961
theorem B5118187 : Blo 1346992 5118187 := bstep (se 1 (by rfl) ⟨3838640, by rfl⟩ : syracuseStep 5118187 = 7677281) B7677281
theorem B6824249 : Blo 1346992 6824249 := bstep (se 2 (by rfl) ⟨2559093, by rfl⟩ : syracuseStep 6824249 = 5118187) B5118187
theorem B4549499 : Blo 1346992 4549499 := bstep (se 1 (by rfl) ⟨3412124, by rfl⟩ : syracuseStep 4549499 = 6824249) B6824249
theorem B3032999 : Blo 1346992 3032999 := bstep (se 1 (by rfl) ⟨2274749, by rfl⟩ : syracuseStep 3032999 = 4549499) B4549499
theorem B2021999 : Blo 1346992 2021999 := bstep (se 1 (by rfl) ⟨1516499, by rfl⟩ : syracuseStep 2021999 = 3032999) B3032999
theorem B1347999 : Blo 1346992 1347999 := bstep (se 1 (by rfl) ⟨1010999, by rfl⟩ : syracuseStep 1347999 = 2021999) B2021999

theorem C0 (j : ℕ) (h1 : 336748 ≤ j) (h2 : j ≤ 337247) : Blo 1346992 (4 * j + 3) := by
  interval_cases j
  · exact B1346995
  · exact B1346999
  · exact B1347003
  · exact B1347007
  · exact B1347011
  · exact B1347015
  · exact B1347019
  · exact B1347023
  · exact B1347027
  · exact B1347031
  · exact B1347035
  · exact B1347039
  · exact B1347043
  · exact B1347047
  · exact B1347051
  · exact B1347055
  · exact B1347059
  · exact B1347063
  · exact B1347067
  · exact B1347071
  · exact B1347075
  · exact B1347079
  · exact B1347083
  · exact B1347087
  · exact B1347091
  · exact B1347095
  · exact B1347099
  · exact B1347103
  · exact B1347107
  · exact B1347111
  · exact B1347115
  · exact B1347119
  · exact B1347123
  · exact B1347127
  · exact B1347131
  · exact B1347135
  · exact B1347139
  · exact B1347143
  · exact B1347147
  · exact B1347151
  · exact B1347155
  · exact B1347159
  · exact B1347163
  · exact B1347167
  · exact B1347171
  · exact B1347175
  · exact B1347179
  · exact B1347183
  · exact B1347187
  · exact B1347191
  · exact B1347195
  · exact B1347199
  · exact B1347203
  · exact B1347207
  · exact B1347211
  · exact B1347215
  · exact B1347219
  · exact B1347223
  · exact B1347227
  · exact B1347231
  · exact B1347235
  · exact B1347239
  · exact B1347243
  · exact B1347247
  · exact B1347251
  · exact B1347255
  · exact B1347259
  · exact B1347263
  · exact B1347267
  · exact B1347271
  · exact B1347275
  · exact B1347279
  · exact B1347283
  · exact B1347287
  · exact B1347291
  · exact B1347295
  · exact B1347299
  · exact B1347303
  · exact B1347307
  · exact B1347311
  · exact B1347315
  · exact B1347319
  · exact B1347323
  · exact B1347327
  · exact B1347331
  · exact B1347335
  · exact B1347339
  · exact B1347343
  · exact B1347347
  · exact B1347351
  · exact B1347355
  · exact B1347359
  · exact B1347363
  · exact B1347367
  · exact B1347371
  · exact B1347375
  · exact B1347379
  · exact B1347383
  · exact B1347387
  · exact B1347391
  · exact B1347395
  · exact B1347399
  · exact B1347403
  · exact B1347407
  · exact B1347411
  · exact B1347415
  · exact B1347419
  · exact B1347423
  · exact B1347427
  · exact B1347431
  · exact B1347435
  · exact B1347439
  · exact B1347443
  · exact B1347447
  · exact B1347451
  · exact B1347455
  · exact B1347459
  · exact B1347463
  · exact B1347467
  · exact B1347471
  · exact B1347475
  · exact B1347479
  · exact B1347483
  · exact B1347487
  · exact B1347491
  · exact B1347495
  · exact B1347499
  · exact B1347503
  · exact B1347507
  · exact B1347511
  · exact B1347515
  · exact B1347519
  · exact B1347523
  · exact B1347527
  · exact B1347531
  · exact B1347535
  · exact B1347539
  · exact B1347543
  · exact B1347547
  · exact B1347551
  · exact B1347555
  · exact B1347559
  · exact B1347563
  · exact B1347567
  · exact B1347571
  · exact B1347575
  · exact B1347579
  · exact B1347583
  · exact B1347587
  · exact B1347591
  · exact B1347595
  · exact B1347599
  · exact B1347603
  · exact B1347607
  · exact B1347611
  · exact B1347615
  · exact B1347619
  · exact B1347623
  · exact B1347627
  · exact B1347631
  · exact B1347635
  · exact B1347639
  · exact B1347643
  · exact B1347647
  · exact B1347651
  · exact B1347655
  · exact B1347659
  · exact B1347663
  · exact B1347667
  · exact B1347671
  · exact B1347675
  · exact B1347679
  · exact B1347683
  · exact B1347687
  · exact B1347691
  · exact B1347695
  · exact B1347699
  · exact B1347703
  · exact B1347707
  · exact B1347711
  · exact B1347715
  · exact B1347719
  · exact B1347723
  · exact B1347727
  · exact B1347731
  · exact B1347735
  · exact B1347739
  · exact B1347743
  · exact B1347747
  · exact B1347751
  · exact B1347755
  · exact B1347759
  · exact B1347763
  · exact B1347767
  · exact B1347771
  · exact B1347775
  · exact B1347779
  · exact B1347783
  · exact B1347787
  · exact B1347791
  · exact B1347795
  · exact B1347799
  · exact B1347803
  · exact B1347807
  · exact B1347811
  · exact B1347815
  · exact B1347819
  · exact B1347823
  · exact B1347827
  · exact B1347831
  · exact B1347835
  · exact B1347839
  · exact B1347843
  · exact B1347847
  · exact B1347851
  · exact B1347855
  · exact B1347859
  · exact B1347863
  · exact B1347867
  · exact B1347871
  · exact B1347875
  · exact B1347879
  · exact B1347883
  · exact B1347887
  · exact B1347891
  · exact B1347895
  · exact B1347899
  · exact B1347903
  · exact B1347907
  · exact B1347911
  · exact B1347915
  · exact B1347919
  · exact B1347923
  · exact B1347927
  · exact B1347931
  · exact B1347935
  · exact B1347939
  · exact B1347943
  · exact B1347947
  · exact B1347951
  · exact B1347955
  · exact B1347959
  · exact B1347963
  · exact B1347967
  · exact B1347971
  · exact B1347975
  · exact B1347979
  · exact B1347983
  · exact B1347987
  · exact B1347991
  · exact B1347995
  · exact B1347999
  · exact B1348003
  · exact B1348007
  · exact B1348011
  · exact B1348015
  · exact B1348019
  · exact B1348023
  · exact B1348027
  · exact B1348031
  · exact B1348035
  · exact B1348039
  · exact B1348043
  · exact B1348047
  · exact B1348051
  · exact B1348055
  · exact B1348059
  · exact B1348063
  · exact B1348067
  · exact B1348071
  · exact B1348075
  · exact B1348079
  · exact B1348083
  · exact B1348087
  · exact B1348091
  · exact B1348095
  · exact B1348099
  · exact B1348103
  · exact B1348107
  · exact B1348111
  · exact B1348115
  · exact B1348119
  · exact B1348123
  · exact B1348127
  · exact B1348131
  · exact B1348135
  · exact B1348139
  · exact B1348143
  · exact B1348147
  · exact B1348151
  · exact B1348155
  · exact B1348159
  · exact B1348163
  · exact B1348167
  · exact B1348171
  · exact B1348175
  · exact B1348179
  · exact B1348183
  · exact B1348187
  · exact B1348191
  · exact B1348195
  · exact B1348199
  · exact B1348203
  · exact B1348207
  · exact B1348211
  · exact B1348215
  · exact B1348219
  · exact B1348223
  · exact B1348227
  · exact B1348231
  · exact B1348235
  · exact B1348239
  · exact B1348243
  · exact B1348247
  · exact B1348251
  · exact B1348255
  · exact B1348259
  · exact B1348263
  · exact B1348267
  · exact B1348271
  · exact B1348275
  · exact B1348279
  · exact B1348283
  · exact B1348287
  · exact B1348291
  · exact B1348295
  · exact B1348299
  · exact B1348303
  · exact B1348307
  · exact B1348311
  · exact B1348315
  · exact B1348319
  · exact B1348323
  · exact B1348327
  · exact B1348331
  · exact B1348335
  · exact B1348339
  · exact B1348343
  · exact B1348347
  · exact B1348351
  · exact B1348355
  · exact B1348359
  · exact B1348363
  · exact B1348367
  · exact B1348371
  · exact B1348375
  · exact B1348379
  · exact B1348383
  · exact B1348387
  · exact B1348391
  · exact B1348395
  · exact B1348399
  · exact B1348403
  · exact B1348407
  · exact B1348411
  · exact B1348415
  · exact B1348419
  · exact B1348423
  · exact B1348427
  · exact B1348431
  · exact B1348435
  · exact B1348439
  · exact B1348443
  · exact B1348447
  · exact B1348451
  · exact B1348455
  · exact B1348459
  · exact B1348463
  · exact B1348467
  · exact B1348471
  · exact B1348475
  · exact B1348479
  · exact B1348483
  · exact B1348487
  · exact B1348491
  · exact B1348495
  · exact B1348499
  · exact B1348503
  · exact B1348507
  · exact B1348511
  · exact B1348515
  · exact B1348519
  · exact B1348523
  · exact B1348527
  · exact B1348531
  · exact B1348535
  · exact B1348539
  · exact B1348543
  · exact B1348547
  · exact B1348551
  · exact B1348555
  · exact B1348559
  · exact B1348563
  · exact B1348567
  · exact B1348571
  · exact B1348575
  · exact B1348579
  · exact B1348583
  · exact B1348587
  · exact B1348591
  · exact B1348595
  · exact B1348599
  · exact B1348603
  · exact B1348607
  · exact B1348611
  · exact B1348615
  · exact B1348619
  · exact B1348623
  · exact B1348627
  · exact B1348631
  · exact B1348635
  · exact B1348639
  · exact B1348643
  · exact B1348647
  · exact B1348651
  · exact B1348655
  · exact B1348659
  · exact B1348663
  · exact B1348667
  · exact B1348671
  · exact B1348675
  · exact B1348679
  · exact B1348683
  · exact B1348687
  · exact B1348691
  · exact B1348695
  · exact B1348699
  · exact B1348703
  · exact B1348707
  · exact B1348711
  · exact B1348715
  · exact B1348719
  · exact B1348723
  · exact B1348727
  · exact B1348731
  · exact B1348735
  · exact B1348739
  · exact B1348743
  · exact B1348747
  · exact B1348751
  · exact B1348755
  · exact B1348759
  · exact B1348763
  · exact B1348767
  · exact B1348771
  · exact B1348775
  · exact B1348779
  · exact B1348783
  · exact B1348787
  · exact B1348791
  · exact B1348795
  · exact B1348799
  · exact B1348803
  · exact B1348807
  · exact B1348811
  · exact B1348815
  · exact B1348819
  · exact B1348823
  · exact B1348827
  · exact B1348831
  · exact B1348835
  · exact B1348839
  · exact B1348843
  · exact B1348847
  · exact B1348851
  · exact B1348855
  · exact B1348859
  · exact B1348863
  · exact B1348867
  · exact B1348871
  · exact B1348875
  · exact B1348879
  · exact B1348883
  · exact B1348887
  · exact B1348891
  · exact B1348895
  · exact B1348899
  · exact B1348903
  · exact B1348907
  · exact B1348911
  · exact B1348915
  · exact B1348919
  · exact B1348923
  · exact B1348927
  · exact B1348931
  · exact B1348935
  · exact B1348939
  · exact B1348943
  · exact B1348947
  · exact B1348951
  · exact B1348955
  · exact B1348959
  · exact B1348963
  · exact B1348967
  · exact B1348971
  · exact B1348975
  · exact B1348979
  · exact B1348983
  · exact B1348987
  · exact B1348991

theorem solution (m : ℕ) (hlo : 1346992 ≤ m) (hhi : m ≤ 1348992) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 336748 ≤ j := by omega
    have hj2 : j ≤ 337247 := by omega
    have hb : Blo 1346992 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
