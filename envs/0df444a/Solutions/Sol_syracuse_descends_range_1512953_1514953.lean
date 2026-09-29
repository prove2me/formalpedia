-- Prove2me | solution 1 for syracuse_descends_range_1512953_1514953
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:13.255611+00:00
-- url     : https://prove2.me/submissions/782d0923-853b-48b5-813b-b3e65b681085

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


theorem B3407885 : Blo 1512953 3407885 := bbase (se 3 (by rfl) ⟨638978, by rfl⟩ : syracuseStep 3407885 = 1277957) (by norm_num)
theorem B1916941 : Blo 1512953 1916941 := bbase (se 3 (by rfl) ⟨359426, by rfl⟩ : syracuseStep 1916941 = 718853) (by norm_num)
theorem B1703965 : Blo 1512953 1703965 := bbase (se 3 (by rfl) ⟨319493, by rfl⟩ : syracuseStep 1703965 = 638987) (by norm_num)
theorem B2555941 : Blo 1512953 2555941 := bbase (se 4 (by rfl) ⟨239619, by rfl⟩ : syracuseStep 2555941 = 479239) (by norm_num)
theorem B1704001 : Blo 1512953 1704001 := bbase (se 2 (by rfl) ⟨639000, by rfl⟩ : syracuseStep 1704001 = 1278001) (by norm_num)
theorem B4849733 : Blo 1512953 4849733 := bbase (se 4 (by rfl) ⟨454662, by rfl⟩ : syracuseStep 4849733 = 909325) (by norm_num)
theorem B3407957 : Blo 1512953 3407957 := bbase (se 8 (by rfl) ⟨19968, by rfl⟩ : syracuseStep 3407957 = 39937) (by norm_num)
theorem B1818713 : Blo 1512953 1818713 := bbase (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) (by norm_num)
theorem B5111909 : Blo 1512953 5111909 := bbase (se 4 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 5111909 = 958483) (by norm_num)
theorem B1704037 : Blo 1512953 1704037 := bbase (se 4 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 1704037 = 319507) (by norm_num)
theorem B1638505 : Blo 1512953 1638505 := bbase (se 2 (by rfl) ⟨614439, by rfl⟩ : syracuseStep 1638505 = 1228879) (by norm_num)
theorem B2154605 : Blo 1512953 2154605 := bbase (se 3 (by rfl) ⟨403988, by rfl⟩ : syracuseStep 2154605 = 807977) (by norm_num)
theorem B1917037 : Blo 1512953 1917037 := bbase (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) (by norm_num)
theorem B4309109 : Blo 1512953 4309109 := bbase (se 5 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 4309109 = 403979) (by norm_num)
theorem B12935285 : Blo 1512953 12935285 := bbase (se 5 (by rfl) ⟨606341, by rfl⟩ : syracuseStep 12935285 = 1212683) (by norm_num)
theorem B2556029 : Blo 1512953 2556029 := bbase (se 3 (by rfl) ⟨479255, by rfl⟩ : syracuseStep 2556029 = 958511) (by norm_num)
theorem B1704073 : Blo 1512953 1704073 := bbase (se 2 (by rfl) ⟨639027, by rfl⟩ : syracuseStep 1704073 = 1278055) (by norm_num)
theorem B3834013 : Blo 1512953 3834013 := bbase (se 3 (by rfl) ⟨718877, by rfl⟩ : syracuseStep 3834013 = 1437755) (by norm_num)
theorem B3408029 : Blo 1512953 3408029 := bbase (se 3 (by rfl) ⟨639005, by rfl⟩ : syracuseStep 3408029 = 1278011) (by norm_num)
theorem B1704109 : Blo 1512953 1704109 := bbase (se 3 (by rfl) ⟨319520, by rfl⟩ : syracuseStep 1704109 = 639041) (by norm_num)
theorem B1704145 : Blo 1512953 1704145 := bbase (se 2 (by rfl) ⟨639054, by rfl⟩ : syracuseStep 1704145 = 1278109) (by norm_num)
theorem B3408101 : Blo 1512953 3408101 := bbase (se 4 (by rfl) ⟨319509, by rfl⟩ : syracuseStep 3408101 = 639019) (by norm_num)
theorem B12927221 : Blo 1512953 12927221 := bbase (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) (by norm_num)
theorem B1704181 : Blo 1512953 1704181 := bbase (se 5 (by rfl) ⟨79883, by rfl⟩ : syracuseStep 1704181 = 159767) (by norm_num)
theorem B2556157 : Blo 1512953 2556157 := bbase (se 3 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 2556157 = 958559) (by norm_num)
theorem B2269445 : Blo 1512953 2269445 := bbase (se 4 (by rfl) ⟨212760, by rfl⟩ : syracuseStep 2269445 = 425521) (by norm_num)
theorem B3834125 : Blo 1512953 3834125 := bbase (se 3 (by rfl) ⟨718898, by rfl⟩ : syracuseStep 3834125 = 1437797) (by norm_num)
theorem B1917209 : Blo 1512953 1917209 := bbase (se 2 (by rfl) ⟨718953, by rfl⟩ : syracuseStep 1917209 = 1437907) (by norm_num)
theorem B1704217 : Blo 1512953 1704217 := bbase (se 2 (by rfl) ⟨639081, by rfl⟩ : syracuseStep 1704217 = 1278163) (by norm_num)
theorem B2269469 : Blo 1512953 2269469 := bbase (se 3 (by rfl) ⟨425525, by rfl⟩ : syracuseStep 2269469 = 851051) (by norm_num)
theorem B2302253 : Blo 1512953 2302253 := bbase (se 3 (by rfl) ⟨431672, by rfl⟩ : syracuseStep 2302253 = 863345) (by norm_num)
theorem B3408173 : Blo 1512953 3408173 := bbase (se 3 (by rfl) ⟨639032, by rfl⟩ : syracuseStep 3408173 = 1278065) (by norm_num)
theorem B2269493 : Blo 1512953 2269493 := bbase (se 5 (by rfl) ⟨106382, by rfl⟩ : syracuseStep 2269493 = 212765) (by norm_num)
theorem B4309301 : Blo 1512953 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B1704253 : Blo 1512953 1704253 := bbase (se 3 (by rfl) ⟨319547, by rfl⟩ : syracuseStep 1704253 = 639095) (by norm_num)
theorem B7659845 : Blo 1512953 7659845 := bbase (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) (by norm_num)
theorem B2302277 : Blo 1512953 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B2269517 : Blo 1512953 2269517 := bbase (se 3 (by rfl) ⟨425534, by rfl⟩ : syracuseStep 2269517 = 851069) (by norm_num)
theorem B1917265 : Blo 1512953 1917265 := bbase (se 2 (by rfl) ⟨718974, by rfl⟩ : syracuseStep 1917265 = 1437949) (by norm_num)
theorem B2556245 : Blo 1512953 2556245 := bbase (se 10 (by rfl) ⟨3744, by rfl⟩ : syracuseStep 2556245 = 7489) (by norm_num)
theorem B1704289 : Blo 1512953 1704289 := bbase (se 2 (by rfl) ⟨639108, by rfl⟩ : syracuseStep 1704289 = 1278217) (by norm_num)
theorem B2269541 : Blo 1512953 2269541 := bbase (se 4 (by rfl) ⟨212769, by rfl⟩ : syracuseStep 2269541 = 425539) (by norm_num)
theorem B3408245 : Blo 1512953 3408245 := bbase (se 5 (by rfl) ⟨159761, by rfl⟩ : syracuseStep 3408245 = 319523) (by norm_num)
theorem B2269565 : Blo 1512953 2269565 := bbase (se 3 (by rfl) ⟨425543, by rfl⟩ : syracuseStep 2269565 = 851087) (by norm_num)
theorem B3277181 : Blo 1512953 3277181 := bbase (se 3 (by rfl) ⟨614471, by rfl⟩ : syracuseStep 3277181 = 1228943) (by norm_num)
theorem B2302349 : Blo 1512953 2302349 := bbase (se 3 (by rfl) ⟨431690, by rfl⟩ : syracuseStep 2302349 = 863381) (by norm_num)
theorem B2269589 : Blo 1512953 2269589 := bbase (se 6 (by rfl) ⟨53193, by rfl⟩ : syracuseStep 2269589 = 106387) (by norm_num)
theorem B2269613 : Blo 1512953 2269613 := bbase (se 3 (by rfl) ⟨425552, by rfl⟩ : syracuseStep 2269613 = 851105) (by norm_num)
theorem B1917361 : Blo 1512953 1917361 := bbase (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) (by norm_num)
theorem B2425277 : Blo 1512953 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B3408317 : Blo 1512953 3408317 := bbase (se 3 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 3408317 = 1278119) (by norm_num)
theorem B2875837 : Blo 1512953 2875837 := bbase (se 3 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 2875837 = 1078439) (by norm_num)
theorem B2269637 : Blo 1512953 2269637 := bbase (se 4 (by rfl) ⟨212778, by rfl⟩ : syracuseStep 2269637 = 425557) (by norm_num)
theorem B3834317 : Blo 1512953 3834317 := bbase (se 3 (by rfl) ⟨718934, by rfl⟩ : syracuseStep 3834317 = 1437869) (by norm_num)
theorem B22110677 : Blo 1512953 22110677 := bbase (se 7 (by rfl) ⟨259109, by rfl⟩ : syracuseStep 22110677 = 518219) (by norm_num)
theorem B2556373 : Blo 1512953 2556373 := bbase (se 7 (by rfl) ⟨29957, by rfl⟩ : syracuseStep 2556373 = 59915) (by norm_num)
theorem B2269661 : Blo 1512953 2269661 := bbase (se 3 (by rfl) ⟨425561, by rfl⟩ : syracuseStep 2269661 = 851123) (by norm_num)
theorem B2269685 : Blo 1512953 2269685 := bbase (se 5 (by rfl) ⟨106391, by rfl⟩ : syracuseStep 2269685 = 212783) (by norm_num)
theorem B3408389 : Blo 1512953 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B2269709 : Blo 1512953 2269709 := bbase (se 3 (by rfl) ⟨425570, by rfl⟩ : syracuseStep 2269709 = 851141) (by norm_num)
theorem B3637781 : Blo 1512953 3637781 := bbase (se 6 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 3637781 = 170521) (by norm_num)
theorem B5112341 : Blo 1512953 5112341 := bbase (se 6 (by rfl) ⟨119820, by rfl⟩ : syracuseStep 5112341 = 239641) (by norm_num)
theorem B2269733 : Blo 1512953 2269733 := bbase (se 4 (by rfl) ⟨212787, by rfl⟩ : syracuseStep 2269733 = 425575) (by norm_num)
theorem B6136357 : Blo 1512953 6136357 := bbase (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) (by norm_num)
theorem B2556461 : Blo 1512953 2556461 := bbase (se 3 (by rfl) ⟨479336, by rfl⟩ : syracuseStep 2556461 = 958673) (by norm_num)
theorem B2269757 : Blo 1512953 2269757 := bbase (se 3 (by rfl) ⟨425579, by rfl⟩ : syracuseStep 2269757 = 851159) (by norm_num)
theorem B3408461 : Blo 1512953 3408461 := bbase (se 3 (by rfl) ⟨639086, by rfl⟩ : syracuseStep 3408461 = 1278173) (by norm_num)
theorem B2875981 : Blo 1512953 2875981 := bbase (se 3 (by rfl) ⟨539246, by rfl⟩ : syracuseStep 2875981 = 1078493) (by norm_num)
theorem B1819217 : Blo 1512953 1819217 := bbase (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) (by norm_num)
theorem B2269781 : Blo 1512953 2269781 := bbase (se 8 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 2269781 = 26599) (by norm_num)
theorem B2269805 : Blo 1512953 2269805 := bbase (se 3 (by rfl) ⟨425588, by rfl⟩ : syracuseStep 2269805 = 851177) (by norm_num)
theorem B1819265 : Blo 1512953 1819265 := bbase (se 2 (by rfl) ⟨682224, by rfl⟩ : syracuseStep 1819265 = 1364449) (by norm_num)
theorem B2269829 : Blo 1512953 2269829 := bbase (se 4 (by rfl) ⟨212796, by rfl⟩ : syracuseStep 2269829 = 425593) (by norm_num)
theorem B5751445 : Blo 1512953 5751445 := bbase (se 6 (by rfl) ⟨134799, by rfl⟩ : syracuseStep 5751445 = 269599) (by norm_num)
theorem B3408533 : Blo 1512953 3408533 := bbase (se 6 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 3408533 = 159775) (by norm_num)
theorem B2269853 : Blo 1512953 2269853 := bbase (se 3 (by rfl) ⟨425597, by rfl⟩ : syracuseStep 2269853 = 851195) (by norm_num)
theorem B2269877 : Blo 1512953 2269877 := bbase (se 5 (by rfl) ⟨106400, by rfl⟩ : syracuseStep 2269877 = 212801) (by norm_num)
theorem B2269901 : Blo 1512953 2269901 := bbase (se 3 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 2269901 = 851213) (by norm_num)
theorem B3408605 : Blo 1512953 3408605 := bbase (se 3 (by rfl) ⟨639113, by rfl⟩ : syracuseStep 3408605 = 1278227) (by norm_num)
theorem B2269925 : Blo 1512953 2269925 := bbase (se 4 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 2269925 = 425611) (by norm_num)
theorem B7275253 : Blo 1512953 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B2269949 : Blo 1512953 2269949 := bbase (se 3 (by rfl) ⟨425615, by rfl⟩ : syracuseStep 2269949 = 851231) (by norm_num)
theorem B2269973 : Blo 1512953 2269973 := bbase (se 6 (by rfl) ⟨53202, by rfl⟩ : syracuseStep 2269973 = 106405) (by norm_num)
theorem B3834661 : Blo 1512953 3834661 := bbase (se 4 (by rfl) ⟨359499, by rfl⟩ : syracuseStep 3834661 = 718999) (by norm_num)
theorem B2269997 : Blo 1512953 2269997 := bbase (se 3 (by rfl) ⟨425624, by rfl⟩ : syracuseStep 2269997 = 851249) (by norm_num)
theorem B2270021 : Blo 1512953 2270021 := bbase (se 4 (by rfl) ⟨212814, by rfl⟩ : syracuseStep 2270021 = 425629) (by norm_num)
theorem B2270045 : Blo 1512953 2270045 := bbase (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) (by norm_num)
theorem B2155357 : Blo 1512953 2155357 := bbase (se 3 (by rfl) ⟨404129, by rfl⟩ : syracuseStep 2155357 = 808259) (by norm_num)
theorem B2270069 : Blo 1512953 2270069 := bbase (se 5 (by rfl) ⟨106409, by rfl⟩ : syracuseStep 2270069 = 212819) (by norm_num)
theorem B1819525 : Blo 1512953 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B2270093 : Blo 1512953 2270093 := bbase (se 3 (by rfl) ⟨425642, by rfl⟩ : syracuseStep 2270093 = 851285) (by norm_num)
theorem B2270117 : Blo 1512953 2270117 := bbase (se 4 (by rfl) ⟨212823, by rfl⟩ : syracuseStep 2270117 = 425647) (by norm_num)
theorem B2270141 : Blo 1512953 2270141 := bbase (se 3 (by rfl) ⟨425651, by rfl⟩ : syracuseStep 2270141 = 851303) (by norm_num)
theorem B5751749 : Blo 1512953 5751749 := bbase (se 4 (by rfl) ⟨539226, by rfl⟩ : syracuseStep 5751749 = 1078453) (by norm_num)
theorem B5112773 : Blo 1512953 5112773 := bbase (se 4 (by rfl) ⟨479322, by rfl⟩ : syracuseStep 5112773 = 958645) (by norm_num)
theorem B2270165 : Blo 1512953 2270165 := bbase (se 7 (by rfl) ⟨26603, by rfl⟩ : syracuseStep 2270165 = 53207) (by norm_num)
theorem B2270189 : Blo 1512953 2270189 := bbase (se 3 (by rfl) ⟨425660, by rfl⟩ : syracuseStep 2270189 = 851321) (by norm_num)
theorem B2270213 : Blo 1512953 2270213 := bbase (se 4 (by rfl) ⟨212832, by rfl⟩ : syracuseStep 2270213 = 425665) (by norm_num)
theorem B6554645 : Blo 1512953 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B2270237 : Blo 1512953 2270237 := bbase (se 3 (by rfl) ⟨425669, by rfl⟩ : syracuseStep 2270237 = 851339) (by norm_num)
theorem B2270261 : Blo 1512953 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B2425925 : Blo 1512953 2425925 := bbase (se 4 (by rfl) ⟨227430, by rfl⟩ : syracuseStep 2425925 = 454861) (by norm_num)
theorem B2270285 : Blo 1512953 2270285 := bbase (se 3 (by rfl) ⟨425678, by rfl⟩ : syracuseStep 2270285 = 851357) (by norm_num)
theorem B2270309 : Blo 1512953 2270309 := bbase (se 4 (by rfl) ⟨212841, by rfl⟩ : syracuseStep 2270309 = 425683) (by norm_num)
theorem B2270333 : Blo 1512953 2270333 := bbase (se 3 (by rfl) ⟨425687, by rfl⟩ : syracuseStep 2270333 = 851375) (by norm_num)
theorem B1819789 : Blo 1512953 1819789 := bbase (se 3 (by rfl) ⟨341210, by rfl⟩ : syracuseStep 1819789 = 682421) (by norm_num)
theorem B2270357 : Blo 1512953 2270357 := bbase (se 6 (by rfl) ⟨53211, by rfl⟩ : syracuseStep 2270357 = 106423) (by norm_num)
theorem B5457061 : Blo 1512953 5457061 := bbase (se 4 (by rfl) ⟨511599, by rfl⟩ : syracuseStep 5457061 = 1023199) (by norm_num)
theorem B2270381 : Blo 1512953 2270381 := bbase (se 3 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 2270381 = 851393) (by norm_num)
theorem B7668917 : Blo 1512953 7668917 := bbase (se 5 (by rfl) ⟨359480, by rfl⟩ : syracuseStep 7668917 = 718961) (by norm_num)
theorem B2270405 : Blo 1512953 2270405 := bbase (se 4 (by rfl) ⟨212850, by rfl⟩ : syracuseStep 2270405 = 425701) (by norm_num)
theorem B46613717 : Blo 1512953 46613717 := bbase (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) (by norm_num)
theorem B2270429 : Blo 1512953 2270429 := bbase (se 3 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 2270429 = 851411) (by norm_num)
theorem B2245853 : Blo 1512953 2245853 := bbase (se 3 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 2245853 = 842195) (by norm_num)
theorem B2270453 : Blo 1512953 2270453 := bbase (se 5 (by rfl) ⟨106427, by rfl⟩ : syracuseStep 2270453 = 212855) (by norm_num)
theorem B2073853 : Blo 1512953 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B1819909 : Blo 1512953 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B2270477 : Blo 1512953 2270477 := bbase (se 3 (by rfl) ⟨425714, by rfl⟩ : syracuseStep 2270477 = 851429) (by norm_num)
theorem B4310293 : Blo 1512953 4310293 := bbase (se 6 (by rfl) ⟨101022, by rfl⟩ : syracuseStep 4310293 = 202045) (by norm_num)
theorem B2270501 : Blo 1512953 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B3278117 : Blo 1512953 3278117 := bbase (se 4 (by rfl) ⟨307323, by rfl⟩ : syracuseStep 3278117 = 614647) (by norm_num)
theorem B2270525 : Blo 1512953 2270525 := bbase (se 3 (by rfl) ⟨425723, by rfl⟩ : syracuseStep 2270525 = 851447) (by norm_num)
theorem B2270549 : Blo 1512953 2270549 := bbase (se 12 (by rfl) ⟨831, by rfl⟩ : syracuseStep 2270549 = 1663) (by norm_num)
theorem B4851029 : Blo 1512953 4851029 := bbase (se 12 (by rfl) ⟨1776, by rfl⟩ : syracuseStep 4851029 = 3553) (by norm_num)
theorem B2270573 : Blo 1512953 2270573 := bbase (se 3 (by rfl) ⟨425732, by rfl⟩ : syracuseStep 2270573 = 851465) (by norm_num)
theorem B8624981 : Blo 1512953 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B2270597 : Blo 1512953 2270597 := bbase (se 4 (by rfl) ⟨212868, by rfl⟩ : syracuseStep 2270597 = 425737) (by norm_num)
theorem B2270621 : Blo 1512953 2270621 := bbase (se 3 (by rfl) ⟨425741, by rfl⟩ : syracuseStep 2270621 = 851483) (by norm_num)
theorem B1639837 : Blo 1512953 1639837 := bbase (se 3 (by rfl) ⟨307469, by rfl⟩ : syracuseStep 1639837 = 614939) (by norm_num)
theorem B2270645 : Blo 1512953 2270645 := bbase (se 5 (by rfl) ⟨106436, by rfl⟩ : syracuseStep 2270645 = 212873) (by norm_num)
theorem B2270669 : Blo 1512953 2270669 := bbase (se 3 (by rfl) ⟨425750, by rfl⟩ : syracuseStep 2270669 = 851501) (by norm_num)
theorem B3638741 : Blo 1512953 3638741 := bbase (se 7 (by rfl) ⟨42641, by rfl⟩ : syracuseStep 3638741 = 85283) (by norm_num)
theorem B2270693 : Blo 1512953 2270693 := bbase (se 4 (by rfl) ⟨212877, by rfl⟩ : syracuseStep 2270693 = 425755) (by norm_num)
theorem B2270717 : Blo 1512953 2270717 := bbase (se 3 (by rfl) ⟨425759, by rfl⟩ : syracuseStep 2270717 = 851519) (by norm_num)
theorem B2270741 : Blo 1512953 2270741 := bbase (se 6 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 2270741 = 106441) (by norm_num)
theorem B2270765 : Blo 1512953 2270765 := bbase (se 3 (by rfl) ⟨425768, by rfl⟩ : syracuseStep 2270765 = 851537) (by norm_num)
theorem B2270789 : Blo 1512953 2270789 := bbase (se 4 (by rfl) ⟨212886, by rfl⟩ : syracuseStep 2270789 = 425773) (by norm_num)
theorem B7661141 : Blo 1512953 7661141 := bbase (se 8 (by rfl) ⟨44889, by rfl⟩ : syracuseStep 7661141 = 89779) (by norm_num)
theorem B8619605 : Blo 1512953 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B2270813 : Blo 1512953 2270813 := bbase (se 3 (by rfl) ⟨425777, by rfl⟩ : syracuseStep 2270813 = 851555) (by norm_num)
theorem B1943137 : Blo 1512953 1943137 := bbase (se 2 (by rfl) ⟨728676, by rfl⟩ : syracuseStep 1943137 = 1457353) (by norm_num)
theorem B1943141 : Blo 1512953 1943141 := bbase (se 4 (by rfl) ⟨182169, by rfl⟩ : syracuseStep 1943141 = 364339) (by norm_num)
theorem B2270837 : Blo 1512953 2270837 := bbase (se 5 (by rfl) ⟨106445, by rfl⟩ : syracuseStep 2270837 = 212891) (by norm_num)
theorem B2156149 : Blo 1512953 2156149 := bbase (se 5 (by rfl) ⟨101069, by rfl⟩ : syracuseStep 2156149 = 202139) (by norm_num)
theorem B2270861 : Blo 1512953 2270861 := bbase (se 3 (by rfl) ⟨425786, by rfl⟩ : syracuseStep 2270861 = 851573) (by norm_num)
theorem B2270885 : Blo 1512953 2270885 := bbase (se 4 (by rfl) ⟨212895, by rfl⟩ : syracuseStep 2270885 = 425791) (by norm_num)
theorem B2270909 : Blo 1512953 2270909 := bbase (se 3 (by rfl) ⟨425795, by rfl⟩ : syracuseStep 2270909 = 851591) (by norm_num)
theorem B2270933 : Blo 1512953 2270933 := bbase (se 7 (by rfl) ⟨26612, by rfl⟩ : syracuseStep 2270933 = 53225) (by norm_num)
theorem B2270957 : Blo 1512953 2270957 := bbase (se 3 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 2270957 = 851609) (by norm_num)
theorem B2270981 : Blo 1512953 2270981 := bbase (se 4 (by rfl) ⟨212904, by rfl⟩ : syracuseStep 2270981 = 425809) (by norm_num)
theorem B2271005 : Blo 1512953 2271005 := bbase (se 3 (by rfl) ⟨425813, by rfl⟩ : syracuseStep 2271005 = 851627) (by norm_num)
theorem B2271029 : Blo 1512953 2271029 := bbase (se 5 (by rfl) ⟨106454, by rfl⟩ : syracuseStep 2271029 = 212909) (by norm_num)
theorem B2271053 : Blo 1512953 2271053 := bbase (se 3 (by rfl) ⟨425822, by rfl⟩ : syracuseStep 2271053 = 851645) (by norm_num)
theorem B2271077 : Blo 1512953 2271077 := bbase (se 4 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 2271077 = 425827) (by norm_num)
theorem B2271101 : Blo 1512953 2271101 := bbase (se 3 (by rfl) ⟨425831, by rfl⟩ : syracuseStep 2271101 = 851663) (by norm_num)
theorem B2074493 : Blo 1512953 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B1615745 : Blo 1512953 1615745 := bbase (se 2 (by rfl) ⟨605904, by rfl⟩ : syracuseStep 1615745 = 1211809) (by norm_num)
theorem B2074501 : Blo 1512953 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B2271125 : Blo 1512953 2271125 := bbase (se 6 (by rfl) ⟨53229, by rfl⟩ : syracuseStep 2271125 = 106459) (by norm_num)
theorem B2271149 : Blo 1512953 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B2271173 : Blo 1512953 2271173 := bbase (se 4 (by rfl) ⟨212922, by rfl⟩ : syracuseStep 2271173 = 425845) (by norm_num)
theorem B2156485 : Blo 1512953 2156485 := bbase (se 4 (by rfl) ⟨202170, by rfl⟩ : syracuseStep 2156485 = 404341) (by norm_num)
theorem B2271197 : Blo 1512953 2271197 := bbase (se 3 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 2271197 = 851699) (by norm_num)
theorem B2271221 : Blo 1512953 2271221 := bbase (se 5 (by rfl) ⟨106463, by rfl⟩ : syracuseStep 2271221 = 212927) (by norm_num)
theorem B2271245 : Blo 1512953 2271245 := bbase (se 3 (by rfl) ⟨425858, by rfl⟩ : syracuseStep 2271245 = 851717) (by norm_num)
theorem B2271269 : Blo 1512953 2271269 := bbase (se 4 (by rfl) ⟨212931, by rfl⟩ : syracuseStep 2271269 = 425863) (by norm_num)
theorem B4605989 : Blo 1512953 4605989 := bbase (se 4 (by rfl) ⟨431811, by rfl⟩ : syracuseStep 4605989 = 863623) (by norm_num)
theorem B2271293 : Blo 1512953 2271293 := bbase (se 3 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 2271293 = 851735) (by norm_num)
theorem B2271317 : Blo 1512953 2271317 := bbase (se 8 (by rfl) ⟨13308, by rfl⟩ : syracuseStep 2271317 = 26617) (by norm_num)
theorem B2271341 : Blo 1512953 2271341 := bbase (se 3 (by rfl) ⟨425876, by rfl⟩ : syracuseStep 2271341 = 851753) (by norm_num)
theorem B1615997 : Blo 1512953 1615997 := bbase (se 3 (by rfl) ⟨302999, by rfl⟩ : syracuseStep 1615997 = 605999) (by norm_num)
theorem B2271365 : Blo 1512953 2271365 := bbase (se 4 (by rfl) ⟨212940, by rfl⟩ : syracuseStep 2271365 = 425881) (by norm_num)
theorem B2271389 : Blo 1512953 2271389 := bbase (se 3 (by rfl) ⟨425885, by rfl⟩ : syracuseStep 2271389 = 851771) (by norm_num)
theorem B2156701 : Blo 1512953 2156701 := bbase (se 3 (by rfl) ⟨404381, by rfl⟩ : syracuseStep 2156701 = 808763) (by norm_num)
theorem B2271413 : Blo 1512953 2271413 := bbase (se 5 (by rfl) ⟨106472, by rfl⟩ : syracuseStep 2271413 = 212945) (by norm_num)
theorem B2271437 : Blo 1512953 2271437 := bbase (se 3 (by rfl) ⟨425894, by rfl⟩ : syracuseStep 2271437 = 851789) (by norm_num)
theorem B2271461 : Blo 1512953 2271461 := bbase (se 4 (by rfl) ⟨212949, by rfl⟩ : syracuseStep 2271461 = 425899) (by norm_num)
theorem B2271485 : Blo 1512953 2271485 := bbase (se 3 (by rfl) ⟨425903, by rfl⟩ : syracuseStep 2271485 = 851807) (by norm_num)
theorem B2271509 : Blo 1512953 2271509 := bbase (se 6 (by rfl) ⟨53238, by rfl⟩ : syracuseStep 2271509 = 106477) (by norm_num)
theorem B2271533 : Blo 1512953 2271533 := bbase (se 3 (by rfl) ⟨425912, by rfl⟩ : syracuseStep 2271533 = 851825) (by norm_num)
theorem B5458229 : Blo 1512953 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B2271557 : Blo 1512953 2271557 := bbase (se 4 (by rfl) ⟨212958, by rfl⟩ : syracuseStep 2271557 = 425917) (by norm_num)
theorem B2271581 : Blo 1512953 2271581 := bbase (se 3 (by rfl) ⟨425921, by rfl⟩ : syracuseStep 2271581 = 851843) (by norm_num)
theorem B4311397 : Blo 1512953 4311397 := bbase (se 4 (by rfl) ⟨404193, by rfl⟩ : syracuseStep 4311397 = 808387) (by norm_num)
theorem B2271605 : Blo 1512953 2271605 := bbase (se 5 (by rfl) ⟨106481, by rfl⟩ : syracuseStep 2271605 = 212963) (by norm_num)
theorem B1534349 : Blo 1512953 1534349 := bbase (se 3 (by rfl) ⟨287690, by rfl⟩ : syracuseStep 1534349 = 575381) (by norm_num)
theorem B2271629 : Blo 1512953 2271629 := bbase (se 3 (by rfl) ⟨425930, by rfl⟩ : syracuseStep 2271629 = 851861) (by norm_num)
theorem B3279253 : Blo 1512953 3279253 := bbase (se 6 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 3279253 = 153715) (by norm_num)
theorem B2271653 : Blo 1512953 2271653 := bbase (se 4 (by rfl) ⟨212967, by rfl⟩ : syracuseStep 2271653 = 425935) (by norm_num)
theorem B2271677 : Blo 1512953 2271677 := bbase (se 3 (by rfl) ⟨425939, by rfl⟩ : syracuseStep 2271677 = 851879) (by norm_num)
theorem B2075069 : Blo 1512953 2075069 := bbase (se 3 (by rfl) ⟨389075, by rfl⟩ : syracuseStep 2075069 = 778151) (by norm_num)
theorem B2271701 : Blo 1512953 2271701 := bbase (se 7 (by rfl) ⟨26621, by rfl⟩ : syracuseStep 2271701 = 53243) (by norm_num)
theorem B2271725 : Blo 1512953 2271725 := bbase (se 3 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 2271725 = 851897) (by norm_num)
theorem B2271749 : Blo 1512953 2271749 := bbase (se 4 (by rfl) ⟨212976, by rfl⟩ : syracuseStep 2271749 = 425953) (by norm_num)
theorem B2271773 : Blo 1512953 2271773 := bbase (se 3 (by rfl) ⟨425957, by rfl⟩ : syracuseStep 2271773 = 851915) (by norm_num)
theorem B2951725 : Blo 1512953 2951725 := bbase (se 3 (by rfl) ⟨553448, by rfl⟩ : syracuseStep 2951725 = 1106897) (by norm_num)
theorem B2271797 : Blo 1512953 2271797 := bbase (se 5 (by rfl) ⟨106490, by rfl⟩ : syracuseStep 2271797 = 212981) (by norm_num)
theorem B1616441 : Blo 1512953 1616441 := bbase (se 2 (by rfl) ⟨606165, by rfl⟩ : syracuseStep 1616441 = 1212331) (by norm_num)
theorem B2271821 : Blo 1512953 2271821 := bbase (se 3 (by rfl) ⟨425966, by rfl⟩ : syracuseStep 2271821 = 851933) (by norm_num)
theorem B2271845 : Blo 1512953 2271845 := bbase (se 4 (by rfl) ⟨212985, by rfl⟩ : syracuseStep 2271845 = 425971) (by norm_num)
theorem B5106293 : Blo 1512953 5106293 := bbase (se 5 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 5106293 = 478715) (by norm_num)
theorem B2271869 : Blo 1512953 2271869 := bbase (se 3 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 2271869 = 851951) (by norm_num)
theorem B2271893 : Blo 1512953 2271893 := bbase (se 6 (by rfl) ⟨53247, by rfl⟩ : syracuseStep 2271893 = 106495) (by norm_num)
theorem B2271917 : Blo 1512953 2271917 := bbase (se 3 (by rfl) ⟨425984, by rfl⟩ : syracuseStep 2271917 = 851969) (by norm_num)
theorem B2271941 : Blo 1512953 2271941 := bbase (se 4 (by rfl) ⟨212994, by rfl⟩ : syracuseStep 2271941 = 425989) (by norm_num)
theorem B38775509 : Blo 1512953 38775509 := bbase (se 7 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 38775509 = 908801) (by norm_num)
theorem B2271965 : Blo 1512953 2271965 := bbase (se 3 (by rfl) ⟨425993, by rfl⟩ : syracuseStep 2271965 = 851987) (by norm_num)
theorem B8620789 : Blo 1512953 8620789 := bbase (se 5 (by rfl) ⟨404099, by rfl⟩ : syracuseStep 8620789 = 808199) (by norm_num)
theorem B2271989 : Blo 1512953 2271989 := bbase (se 5 (by rfl) ⟨106499, by rfl⟩ : syracuseStep 2271989 = 212999) (by norm_num)
theorem B2272013 : Blo 1512953 2272013 := bbase (se 3 (by rfl) ⟨426002, by rfl⟩ : syracuseStep 2272013 = 852005) (by norm_num)
theorem B2272037 : Blo 1512953 2272037 := bbase (se 4 (by rfl) ⟨213003, by rfl⟩ : syracuseStep 2272037 = 426007) (by norm_num)
theorem B1616689 : Blo 1512953 1616689 := bbase (se 2 (by rfl) ⟨606258, by rfl⟩ : syracuseStep 1616689 = 1212517) (by norm_num)
theorem B2272061 : Blo 1512953 2272061 := bbase (se 3 (by rfl) ⟨426011, by rfl⟩ : syracuseStep 2272061 = 852023) (by norm_num)
theorem B2272085 : Blo 1512953 2272085 := bbase (se 9 (by rfl) ⟨6656, by rfl⟩ : syracuseStep 2272085 = 13313) (by norm_num)
theorem B7662437 : Blo 1512953 7662437 := bbase (se 4 (by rfl) ⟨718353, by rfl⟩ : syracuseStep 7662437 = 1436707) (by norm_num)
theorem B2272109 : Blo 1512953 2272109 := bbase (se 3 (by rfl) ⟨426020, by rfl⟩ : syracuseStep 2272109 = 852041) (by norm_num)
theorem B2272133 : Blo 1512953 2272133 := bbase (se 4 (by rfl) ⟨213012, by rfl⟩ : syracuseStep 2272133 = 426025) (by norm_num)
theorem B2272157 : Blo 1512953 2272157 := bbase (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) (by norm_num)
theorem B2272181 : Blo 1512953 2272181 := bbase (se 5 (by rfl) ⟨106508, by rfl⟩ : syracuseStep 2272181 = 213017) (by norm_num)
theorem B2272205 : Blo 1512953 2272205 := bbase (se 3 (by rfl) ⟨426038, by rfl⟩ : syracuseStep 2272205 = 852077) (by norm_num)
theorem B2272229 : Blo 1512953 2272229 := bbase (se 4 (by rfl) ⟨213021, by rfl⟩ : syracuseStep 2272229 = 426043) (by norm_num)
theorem B6466549 : Blo 1512953 6466549 := bbase (se 5 (by rfl) ⟨303119, by rfl⟩ : syracuseStep 6466549 = 606239) (by norm_num)
theorem B2272253 : Blo 1512953 2272253 := bbase (se 3 (by rfl) ⟨426047, by rfl⟩ : syracuseStep 2272253 = 852095) (by norm_num)
theorem B2272277 : Blo 1512953 2272277 := bbase (se 6 (by rfl) ⟨53256, by rfl⟩ : syracuseStep 2272277 = 106513) (by norm_num)
theorem B5106725 : Blo 1512953 5106725 := bbase (se 4 (by rfl) ⟨478755, by rfl⟩ : syracuseStep 5106725 = 957511) (by norm_num)
theorem B2272301 : Blo 1512953 2272301 := bbase (se 3 (by rfl) ⟨426056, by rfl⟩ : syracuseStep 2272301 = 852113) (by norm_num)
theorem B2272325 : Blo 1512953 2272325 := bbase (se 4 (by rfl) ⟨213030, by rfl⟩ : syracuseStep 2272325 = 426061) (by norm_num)
theorem B2272349 : Blo 1512953 2272349 := bbase (se 3 (by rfl) ⟨426065, by rfl⟩ : syracuseStep 2272349 = 852131) (by norm_num)
theorem B4090981 : Blo 1512953 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B6220901 : Blo 1512953 6220901 := bbase (se 4 (by rfl) ⟨583209, by rfl⟩ : syracuseStep 6220901 = 1166419) (by norm_num)
theorem B2272373 : Blo 1512953 2272373 := bbase (se 5 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 2272373 = 213035) (by norm_num)
theorem B2272397 : Blo 1512953 2272397 := bbase (se 3 (by rfl) ⟨426074, by rfl⟩ : syracuseStep 2272397 = 852149) (by norm_num)
theorem B5827733 : Blo 1512953 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B4852885 : Blo 1512953 4852885 := bbase (se 6 (by rfl) ⟨113739, by rfl⟩ : syracuseStep 4852885 = 227479) (by norm_num)
theorem B2272421 : Blo 1512953 2272421 := bbase (se 4 (by rfl) ⟨213039, by rfl⟩ : syracuseStep 2272421 = 426079) (by norm_num)
theorem B1617133 : Blo 1512953 1617133 := bbase (se 3 (by rfl) ⟨303212, by rfl⟩ : syracuseStep 1617133 = 606425) (by norm_num)
theorem B1617193 : Blo 1512953 1617193 := bbase (se 2 (by rfl) ⟨606447, by rfl⟩ : syracuseStep 1617193 = 1212895) (by norm_num)
theorem B5746085 : Blo 1512953 5746085 := bbase (se 4 (by rfl) ⟨538695, by rfl⟩ : syracuseStep 5746085 = 1077391) (by norm_num)
theorem B3452357 : Blo 1512953 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B5107157 : Blo 1512953 5107157 := bbase (se 7 (by rfl) ⟨59849, by rfl⟩ : syracuseStep 5107157 = 119699) (by norm_num)
theorem B1535581 : Blo 1512953 1535581 := bbase (se 3 (by rfl) ⟨287921, by rfl⟩ : syracuseStep 1535581 = 575843) (by norm_num)
theorem B1617509 : Blo 1512953 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B5746373 : Blo 1512953 5746373 := bbase (se 4 (by rfl) ⟨538722, by rfl⟩ : syracuseStep 5746373 = 1077445) (by norm_num)
theorem B9211637 : Blo 1512953 9211637 := bbase (se 5 (by rfl) ⟨431795, by rfl⟩ : syracuseStep 9211637 = 863591) (by norm_num)
theorem B19402517 : Blo 1512953 19402517 := bbase (se 6 (by rfl) ⟨454746, by rfl⟩ : syracuseStep 19402517 = 909493) (by norm_num)
theorem B4312901 : Blo 1512953 4312901 := bbase (se 4 (by rfl) ⟨404334, by rfl⟩ : syracuseStep 4312901 = 808669) (by norm_num)
theorem B11497301 : Blo 1512953 11497301 := bbase (se 9 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 11497301 = 67367) (by norm_num)
theorem B5107589 : Blo 1512953 5107589 := bbase (se 4 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 5107589 = 957673) (by norm_num)
theorem B3829781 : Blo 1512953 3829781 := bbase (se 6 (by rfl) ⟨89760, by rfl⟩ : syracuseStep 3829781 = 179521) (by norm_num)
theorem B7663733 : Blo 1512953 7663733 := bbase (se 5 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 7663733 = 718475) (by norm_num)
theorem B6140117 : Blo 1512953 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B11489525 : Blo 1512953 11489525 := bbase (se 5 (by rfl) ⟨538571, by rfl⟩ : syracuseStep 11489525 = 1077143) (by norm_num)
theorem B3232037 : Blo 1512953 3232037 := bbase (se 4 (by rfl) ⟨303003, by rfl⟩ : syracuseStep 3232037 = 606007) (by norm_num)
theorem B5108021 : Blo 1512953 5108021 := bbase (se 5 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 5108021 = 478877) (by norm_num)
theorem B3830125 : Blo 1512953 3830125 := bbase (se 3 (by rfl) ⟨718148, by rfl⟩ : syracuseStep 3830125 = 1436297) (by norm_num)
theorem B3404213 : Blo 1512953 3404213 := bbase (se 5 (by rfl) ⟨159572, by rfl⟩ : syracuseStep 3404213 = 319145) (by norm_num)
theorem B3232181 : Blo 1512953 3232181 := bbase (se 5 (by rfl) ⟨151508, by rfl⟩ : syracuseStep 3232181 = 303017) (by norm_num)
theorem B3830237 : Blo 1512953 3830237 := bbase (se 3 (by rfl) ⟨718169, by rfl⟩ : syracuseStep 3830237 = 1436339) (by norm_num)
theorem B9703925 : Blo 1512953 9703925 := bbase (se 5 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 9703925 = 909743) (by norm_num)
theorem B3404285 : Blo 1512953 3404285 := bbase (se 3 (by rfl) ⟨638303, by rfl⟩ : syracuseStep 3404285 = 1276607) (by norm_num)
theorem B1684009 : Blo 1512953 1684009 := bbase (se 2 (by rfl) ⟨631503, by rfl⟩ : syracuseStep 1684009 = 1263007) (by norm_num)
theorem B3404357 : Blo 1512953 3404357 := bbase (se 4 (by rfl) ⟨319158, by rfl⟩ : syracuseStep 3404357 = 638317) (by norm_num)
theorem B3404429 : Blo 1512953 3404429 := bbase (se 3 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 3404429 = 1276661) (by norm_num)
theorem B7279253 : Blo 1512953 7279253 := bbase (se 6 (by rfl) ⟨170607, by rfl⟩ : syracuseStep 7279253 = 341215) (by norm_num)
theorem B3830429 : Blo 1512953 3830429 := bbase (se 3 (by rfl) ⟨718205, by rfl⟩ : syracuseStep 3830429 = 1436411) (by norm_num)
theorem B8622773 : Blo 1512953 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B3404501 : Blo 1512953 3404501 := bbase (se 7 (by rfl) ⟨39896, by rfl⟩ : syracuseStep 3404501 = 79793) (by norm_num)
theorem B5108453 : Blo 1512953 5108453 := bbase (se 4 (by rfl) ⟨478917, by rfl⟩ : syracuseStep 5108453 = 957835) (by norm_num)
theorem B4092677 : Blo 1512953 4092677 := bbase (se 4 (by rfl) ⟨383688, by rfl⟩ : syracuseStep 4092677 = 767377) (by norm_num)
theorem B3404573 : Blo 1512953 3404573 := bbase (se 3 (by rfl) ⟨638357, by rfl⟩ : syracuseStep 3404573 = 1276715) (by norm_num)
theorem B3232541 : Blo 1512953 3232541 := bbase (se 3 (by rfl) ⟨606101, by rfl⟩ : syracuseStep 3232541 = 1212203) (by norm_num)
theorem B6558517 : Blo 1512953 6558517 := bbase (se 5 (by rfl) ⟨307430, by rfl⟩ : syracuseStep 6558517 = 614861) (by norm_num)
theorem B3404645 : Blo 1512953 3404645 := bbase (se 4 (by rfl) ⟨319185, by rfl⟩ : syracuseStep 3404645 = 638371) (by norm_num)
theorem B5747557 : Blo 1512953 5747557 := bbase (se 4 (by rfl) ⟨538833, by rfl⟩ : syracuseStep 5747557 = 1077667) (by norm_num)
theorem B3404717 : Blo 1512953 3404717 := bbase (se 3 (by rfl) ⟨638384, by rfl⟩ : syracuseStep 3404717 = 1276769) (by norm_num)
theorem B2872253 : Blo 1512953 2872253 := bbase (se 3 (by rfl) ⟨538547, by rfl⟩ : syracuseStep 2872253 = 1077095) (by norm_num)
theorem B3404789 : Blo 1512953 3404789 := bbase (se 5 (by rfl) ⟨159599, by rfl⟩ : syracuseStep 3404789 = 319199) (by norm_num)
theorem B3830773 : Blo 1512953 3830773 := bbase (se 5 (by rfl) ⟨179567, by rfl⟩ : syracuseStep 3830773 = 359135) (by norm_num)
theorem B9204725 : Blo 1512953 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B3404861 : Blo 1512953 3404861 := bbase (se 3 (by rfl) ⟨638411, by rfl⟩ : syracuseStep 3404861 = 1276823) (by norm_num)
theorem B2872397 : Blo 1512953 2872397 := bbase (se 3 (by rfl) ⟨538574, by rfl⟩ : syracuseStep 2872397 = 1077149) (by norm_num)
theorem B7271525 : Blo 1512953 7271525 := bbase (se 4 (by rfl) ⟨681705, by rfl⟩ : syracuseStep 7271525 = 1363411) (by norm_num)
theorem B3830885 : Blo 1512953 3830885 := bbase (se 4 (by rfl) ⟨359145, by rfl⟩ : syracuseStep 3830885 = 718291) (by norm_num)
theorem B3404933 : Blo 1512953 3404933 := bbase (se 4 (by rfl) ⟨319212, by rfl⟩ : syracuseStep 3404933 = 638425) (by norm_num)
theorem B5108885 : Blo 1512953 5108885 := bbase (se 6 (by rfl) ⟨119739, by rfl⟩ : syracuseStep 5108885 = 239479) (by norm_num)
theorem B5747861 : Blo 1512953 5747861 := bbase (se 6 (by rfl) ⟨134715, by rfl⟩ : syracuseStep 5747861 = 269431) (by norm_num)
theorem B3405005 : Blo 1512953 3405005 := bbase (se 3 (by rfl) ⟨638438, by rfl⟩ : syracuseStep 3405005 = 1276877) (by norm_num)
theorem B3405077 : Blo 1512953 3405077 := bbase (se 6 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 3405077 = 159613) (by norm_num)
theorem B3831077 : Blo 1512953 3831077 := bbase (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) (by norm_num)
theorem B2553133 : Blo 1512953 2553133 := bbase (se 3 (by rfl) ⟨478712, by rfl⟩ : syracuseStep 2553133 = 957425) (by norm_num)
theorem B3405149 : Blo 1512953 3405149 := bbase (se 3 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 3405149 = 1276931) (by norm_num)
theorem B6550885 : Blo 1512953 6550885 := bbase (se 4 (by rfl) ⟨614145, by rfl⟩ : syracuseStep 6550885 = 1228291) (by norm_num)
theorem B2872685 : Blo 1512953 2872685 := bbase (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) (by norm_num)
theorem B2553221 : Blo 1512953 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B7665029 : Blo 1512953 7665029 := bbase (se 4 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 7665029 = 1437193) (by norm_num)
theorem B3405221 : Blo 1512953 3405221 := bbase (se 4 (by rfl) ⟨319239, by rfl⟩ : syracuseStep 3405221 = 638479) (by norm_num)
theorem B3405293 : Blo 1512953 3405293 := bbase (se 3 (by rfl) ⟨638492, by rfl⟩ : syracuseStep 3405293 = 1276985) (by norm_num)
theorem B2553349 : Blo 1512953 2553349 := bbase (se 4 (by rfl) ⟨239376, by rfl⟩ : syracuseStep 2553349 = 478753) (by norm_num)
theorem B2872837 : Blo 1512953 2872837 := bbase (se 4 (by rfl) ⟨269328, by rfl⟩ : syracuseStep 2872837 = 538657) (by norm_num)
theorem B8189461 : Blo 1512953 8189461 := bbase (se 6 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 8189461 = 383881) (by norm_num)
theorem B3405365 : Blo 1512953 3405365 := bbase (se 5 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 3405365 = 319253) (by norm_num)
theorem B5109317 : Blo 1512953 5109317 := bbase (se 4 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 5109317 = 957997) (by norm_num)
theorem B2553437 : Blo 1512953 2553437 := bbase (se 3 (by rfl) ⟨478769, by rfl⟩ : syracuseStep 2553437 = 957539) (by norm_num)
theorem B1726069 : Blo 1512953 1726069 := bbase (se 5 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 1726069 = 161819) (by norm_num)
theorem B3405437 : Blo 1512953 3405437 := bbase (se 3 (by rfl) ⟨638519, by rfl⟩ : syracuseStep 3405437 = 1277039) (by norm_num)
theorem B3831421 : Blo 1512953 3831421 := bbase (se 3 (by rfl) ⟨718391, by rfl⟩ : syracuseStep 3831421 = 1436783) (by norm_num)
theorem B3233429 : Blo 1512953 3233429 := bbase (se 6 (by rfl) ⟨75783, by rfl⟩ : syracuseStep 3233429 = 151567) (by norm_num)
theorem B3405509 : Blo 1512953 3405509 := bbase (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) (by norm_num)
theorem B2553565 : Blo 1512953 2553565 := bbase (se 3 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 2553565 = 957587) (by norm_num)
theorem B3831533 : Blo 1512953 3831533 := bbase (se 3 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 3831533 = 1436825) (by norm_num)
theorem B1750765 : Blo 1512953 1750765 := bbase (se 3 (by rfl) ⟨328268, by rfl⟩ : syracuseStep 1750765 = 656537) (by norm_num)
theorem B3405581 : Blo 1512953 3405581 := bbase (se 3 (by rfl) ⟨638546, by rfl⟩ : syracuseStep 3405581 = 1277093) (by norm_num)
theorem B2553653 : Blo 1512953 2553653 := bbase (se 5 (by rfl) ⟨119702, by rfl⟩ : syracuseStep 2553653 = 239405) (by norm_num)
theorem B2873141 : Blo 1512953 2873141 := bbase (se 5 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 2873141 = 269357) (by norm_num)
theorem B3405653 : Blo 1512953 3405653 := bbase (se 9 (by rfl) ⟨9977, by rfl⟩ : syracuseStep 3405653 = 19955) (by norm_num)
theorem B3233677 : Blo 1512953 3233677 := bbase (se 3 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 3233677 = 1212629) (by norm_num)
theorem B3405725 : Blo 1512953 3405725 := bbase (se 3 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 3405725 = 1277147) (by norm_num)
theorem B6469541 : Blo 1512953 6469541 := bbase (se 4 (by rfl) ⟨606519, by rfl⟩ : syracuseStep 6469541 = 1213039) (by norm_num)
theorem B3831725 : Blo 1512953 3831725 := bbase (se 3 (by rfl) ⟨718448, by rfl⟩ : syracuseStep 3831725 = 1436897) (by norm_num)
theorem B2553781 : Blo 1512953 2553781 := bbase (se 5 (by rfl) ⟨119708, by rfl⟩ : syracuseStep 2553781 = 239417) (by norm_num)
theorem B3405797 : Blo 1512953 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B5109749 : Blo 1512953 5109749 := bbase (se 5 (by rfl) ⟨239519, by rfl⟩ : syracuseStep 5109749 = 479039) (by norm_num)
theorem B2553869 : Blo 1512953 2553869 := bbase (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) (by norm_num)
theorem B3405869 : Blo 1512953 3405869 := bbase (se 3 (by rfl) ⟨638600, by rfl⟩ : syracuseStep 3405869 = 1277201) (by norm_num)
theorem B10500149 : Blo 1512953 10500149 := bbase (se 5 (by rfl) ⟨492194, by rfl⟩ : syracuseStep 10500149 = 984389) (by norm_num)
theorem B1914941 : Blo 1512953 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B3323965 : Blo 1512953 3323965 := bbase (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) (by norm_num)
theorem B1914997 : Blo 1512953 1914997 := bbase (se 5 (by rfl) ⟨89765, by rfl⟩ : syracuseStep 1914997 = 179531) (by norm_num)
theorem B3405941 : Blo 1512953 3405941 := bbase (se 5 (by rfl) ⟨159653, by rfl⟩ : syracuseStep 3405941 = 319307) (by norm_num)
theorem B2553997 : Blo 1512953 2553997 := bbase (se 3 (by rfl) ⟨478874, by rfl⟩ : syracuseStep 2553997 = 957749) (by norm_num)
theorem B9828533 : Blo 1512953 9828533 := bbase (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) (by norm_num)
theorem B3406013 : Blo 1512953 3406013 := bbase (se 3 (by rfl) ⟨638627, by rfl⟩ : syracuseStep 3406013 = 1277255) (by norm_num)
theorem B1702093 : Blo 1512953 1702093 := bbase (se 3 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 1702093 = 638285) (by norm_num)
theorem B1915093 : Blo 1512953 1915093 := bbase (se 7 (by rfl) ⟨22442, by rfl⟩ : syracuseStep 1915093 = 44885) (by norm_num)
theorem B2554085 : Blo 1512953 2554085 := bbase (se 4 (by rfl) ⟨239445, by rfl⟩ : syracuseStep 2554085 = 478891) (by norm_num)
theorem B1702129 : Blo 1512953 1702129 := bbase (se 2 (by rfl) ⟨638298, by rfl⟩ : syracuseStep 1702129 = 1276597) (by norm_num)
theorem B12613877 : Blo 1512953 12613877 := bbase (se 5 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 12613877 = 1182551) (by norm_num)
theorem B3406085 : Blo 1512953 3406085 := bbase (se 4 (by rfl) ⟨319320, by rfl⟩ : syracuseStep 3406085 = 638641) (by norm_num)
theorem B3832069 : Blo 1512953 3832069 := bbase (se 4 (by rfl) ⟨359256, by rfl⟩ : syracuseStep 3832069 = 718513) (by norm_num)
theorem B1702165 : Blo 1512953 1702165 := bbase (se 6 (by rfl) ⟨39894, by rfl⟩ : syracuseStep 1702165 = 79789) (by norm_num)
theorem B1702201 : Blo 1512953 1702201 := bbase (se 2 (by rfl) ⟨638325, by rfl⟩ : syracuseStep 1702201 = 1276651) (by norm_num)
theorem B3406157 : Blo 1512953 3406157 := bbase (se 3 (by rfl) ⟨638654, by rfl⟩ : syracuseStep 3406157 = 1277309) (by norm_num)
theorem B1702237 : Blo 1512953 1702237 := bbase (se 3 (by rfl) ⟨319169, by rfl⟩ : syracuseStep 1702237 = 638339) (by norm_num)
theorem B2554213 : Blo 1512953 2554213 := bbase (se 4 (by rfl) ⟨239457, by rfl⟩ : syracuseStep 2554213 = 478915) (by norm_num)
theorem B8182133 : Blo 1512953 8182133 := bbase (se 5 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 8182133 = 767075) (by norm_num)
theorem B3832181 : Blo 1512953 3832181 := bbase (se 5 (by rfl) ⟨179633, by rfl⟩ : syracuseStep 3832181 = 359267) (by norm_num)
theorem B1702273 : Blo 1512953 1702273 := bbase (se 2 (by rfl) ⟨638352, by rfl⟩ : syracuseStep 1702273 = 1276705) (by norm_num)
theorem B1915265 : Blo 1512953 1915265 := bbase (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) (by norm_num)
theorem B3234181 : Blo 1512953 3234181 := bbase (se 4 (by rfl) ⟨303204, by rfl⟩ : syracuseStep 3234181 = 606409) (by norm_num)
theorem B3406229 : Blo 1512953 3406229 := bbase (se 6 (by rfl) ⟨79833, by rfl⟩ : syracuseStep 3406229 = 159667) (by norm_num)
theorem B1702309 : Blo 1512953 1702309 := bbase (se 4 (by rfl) ⟨159591, by rfl⟩ : syracuseStep 1702309 = 319183) (by norm_num)
theorem B5110181 : Blo 1512953 5110181 := bbase (se 4 (by rfl) ⟨479079, by rfl⟩ : syracuseStep 5110181 = 958159) (by norm_num)
theorem B1915321 : Blo 1512953 1915321 := bbase (se 2 (by rfl) ⟨718245, by rfl⟩ : syracuseStep 1915321 = 1436491) (by norm_num)
theorem B2554301 : Blo 1512953 2554301 := bbase (se 3 (by rfl) ⟨478931, by rfl⟩ : syracuseStep 2554301 = 957863) (by norm_num)
theorem B1702345 : Blo 1512953 1702345 := bbase (se 2 (by rfl) ⟨638379, by rfl⟩ : syracuseStep 1702345 = 1276759) (by norm_num)
theorem B3406301 : Blo 1512953 3406301 := bbase (se 3 (by rfl) ⟨638681, by rfl⟩ : syracuseStep 3406301 = 1277363) (by norm_num)
theorem B6224357 : Blo 1512953 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B1702381 : Blo 1512953 1702381 := bbase (se 3 (by rfl) ⟨319196, by rfl⟩ : syracuseStep 1702381 = 638393) (by norm_num)
theorem B1702417 : Blo 1512953 1702417 := bbase (se 2 (by rfl) ⟨638406, by rfl⟩ : syracuseStep 1702417 = 1276813) (by norm_num)
theorem B1915417 : Blo 1512953 1915417 := bbase (se 2 (by rfl) ⟨718281, by rfl⟩ : syracuseStep 1915417 = 1436563) (by norm_num)
theorem B2873893 : Blo 1512953 2873893 := bbase (se 4 (by rfl) ⟨269427, by rfl⟩ : syracuseStep 2873893 = 538855) (by norm_num)
theorem B3406373 : Blo 1512953 3406373 := bbase (se 4 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 3406373 = 638695) (by norm_num)
theorem B1702453 : Blo 1512953 1702453 := bbase (se 5 (by rfl) ⟨79802, by rfl⟩ : syracuseStep 1702453 = 159605) (by norm_num)
theorem B3832373 : Blo 1512953 3832373 := bbase (se 5 (by rfl) ⟨179642, by rfl⟩ : syracuseStep 3832373 = 359285) (by norm_num)
theorem B2554429 : Blo 1512953 2554429 := bbase (se 3 (by rfl) ⟨478955, by rfl⟩ : syracuseStep 2554429 = 957911) (by norm_num)
theorem B9697877 : Blo 1512953 9697877 := bbase (se 8 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 9697877 = 113647) (by norm_num)
theorem B1702489 : Blo 1512953 1702489 := bbase (se 2 (by rfl) ⟨638433, by rfl⟩ : syracuseStep 1702489 = 1276867) (by norm_num)
theorem B3406445 : Blo 1512953 3406445 := bbase (se 3 (by rfl) ⟨638708, by rfl⟩ : syracuseStep 3406445 = 1277417) (by norm_num)
theorem B1702525 : Blo 1512953 1702525 := bbase (se 3 (by rfl) ⟨319223, by rfl⟩ : syracuseStep 1702525 = 638447) (by norm_num)
theorem B2554517 : Blo 1512953 2554517 := bbase (se 6 (by rfl) ⟨59871, by rfl⟩ : syracuseStep 2554517 = 119743) (by norm_num)
theorem B7666325 : Blo 1512953 7666325 := bbase (se 6 (by rfl) ⟨179679, by rfl⟩ : syracuseStep 7666325 = 359359) (by norm_num)
theorem B1702561 : Blo 1512953 1702561 := bbase (se 2 (by rfl) ⟨638460, by rfl⟩ : syracuseStep 1702561 = 1276921) (by norm_num)
theorem B2874037 : Blo 1512953 2874037 := bbase (se 5 (by rfl) ⟨134720, by rfl⟩ : syracuseStep 2874037 = 269441) (by norm_num)
theorem B3406517 : Blo 1512953 3406517 := bbase (se 5 (by rfl) ⟨159680, by rfl⟩ : syracuseStep 3406517 = 319361) (by norm_num)
theorem B1702597 : Blo 1512953 1702597 := bbase (se 4 (by rfl) ⟨159618, by rfl⟩ : syracuseStep 1702597 = 319237) (by norm_num)
theorem B1915589 : Blo 1512953 1915589 := bbase (se 4 (by rfl) ⟨179586, by rfl⟩ : syracuseStep 1915589 = 359173) (by norm_num)
theorem B1727173 : Blo 1512953 1727173 := bbase (se 4 (by rfl) ⟨161922, by rfl⟩ : syracuseStep 1727173 = 323845) (by norm_num)
theorem B27605717 : Blo 1512953 27605717 := bbase (se 7 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 27605717 = 647009) (by norm_num)
theorem B1702633 : Blo 1512953 1702633 := bbase (se 2 (by rfl) ⟨638487, by rfl⟩ : syracuseStep 1702633 = 1276975) (by norm_num)
theorem B1915645 : Blo 1512953 1915645 := bbase (se 3 (by rfl) ⟨359183, by rfl⟩ : syracuseStep 1915645 = 718367) (by norm_num)
theorem B3406589 : Blo 1512953 3406589 := bbase (se 3 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 3406589 = 1277471) (by norm_num)
theorem B1702669 : Blo 1512953 1702669 := bbase (se 3 (by rfl) ⟨319250, by rfl⟩ : syracuseStep 1702669 = 638501) (by norm_num)
theorem B2554645 : Blo 1512953 2554645 := bbase (se 6 (by rfl) ⟨59874, by rfl⟩ : syracuseStep 2554645 = 119749) (by norm_num)
theorem B1702705 : Blo 1512953 1702705 := bbase (se 2 (by rfl) ⟨638514, by rfl⟩ : syracuseStep 1702705 = 1277029) (by norm_num)
theorem B3406661 : Blo 1512953 3406661 := bbase (se 4 (by rfl) ⟨319374, by rfl⟩ : syracuseStep 3406661 = 638749) (by norm_num)
theorem B3275605 : Blo 1512953 3275605 := bbase (se 9 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 3275605 = 19193) (by norm_num)
theorem B1702741 : Blo 1512953 1702741 := bbase (se 9 (by rfl) ⟨4988, by rfl⟩ : syracuseStep 1702741 = 9977) (by norm_num)
theorem B2874197 : Blo 1512953 2874197 := bbase (se 9 (by rfl) ⟨8420, by rfl⟩ : syracuseStep 2874197 = 16841) (by norm_num)
theorem B5110613 : Blo 1512953 5110613 := bbase (se 9 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 5110613 = 29945) (by norm_num)
theorem B1915741 : Blo 1512953 1915741 := bbase (se 3 (by rfl) ⟨359201, by rfl⟩ : syracuseStep 1915741 = 718403) (by norm_num)
theorem B2554733 : Blo 1512953 2554733 := bbase (se 3 (by rfl) ⟨479012, by rfl⟩ : syracuseStep 2554733 = 958025) (by norm_num)
theorem B1702777 : Blo 1512953 1702777 := bbase (se 2 (by rfl) ⟨638541, by rfl⟩ : syracuseStep 1702777 = 1277083) (by norm_num)
theorem B3406733 : Blo 1512953 3406733 := bbase (se 3 (by rfl) ⟨638762, by rfl⟩ : syracuseStep 3406733 = 1277525) (by norm_num)
theorem B3832717 : Blo 1512953 3832717 := bbase (se 3 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 3832717 = 1437269) (by norm_num)
theorem B1555345 : Blo 1512953 1555345 := bbase (se 2 (by rfl) ⟨583254, by rfl⟩ : syracuseStep 1555345 = 1166509) (by norm_num)
theorem B6470549 : Blo 1512953 6470549 := bbase (se 6 (by rfl) ⟨151653, by rfl⟩ : syracuseStep 6470549 = 303307) (by norm_num)
theorem B1702813 : Blo 1512953 1702813 := bbase (se 3 (by rfl) ⟨319277, by rfl⟩ : syracuseStep 1702813 = 638555) (by norm_num)
theorem B1702849 : Blo 1512953 1702849 := bbase (se 2 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 1702849 = 1277137) (by norm_num)
theorem B2046917 : Blo 1512953 2046917 := bbase (se 4 (by rfl) ⟨191898, by rfl⟩ : syracuseStep 2046917 = 383797) (by norm_num)
theorem B3406805 : Blo 1512953 3406805 := bbase (se 7 (by rfl) ⟨39923, by rfl⟩ : syracuseStep 3406805 = 79847) (by norm_num)
theorem B1702885 : Blo 1512953 1702885 := bbase (se 4 (by rfl) ⟨159645, by rfl⟩ : syracuseStep 1702885 = 319291) (by norm_num)
theorem B2874341 : Blo 1512953 2874341 := bbase (se 4 (by rfl) ⟨269469, by rfl⟩ : syracuseStep 2874341 = 538939) (by norm_num)
theorem B2554861 : Blo 1512953 2554861 := bbase (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) (by norm_num)
theorem B3832829 : Blo 1512953 3832829 := bbase (se 3 (by rfl) ⟨718655, by rfl⟩ : syracuseStep 3832829 = 1437311) (by norm_num)
theorem B1702921 : Blo 1512953 1702921 := bbase (se 2 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 1702921 = 1277191) (by norm_num)
theorem B1915913 : Blo 1512953 1915913 := bbase (se 2 (by rfl) ⟨718467, by rfl⟩ : syracuseStep 1915913 = 1436935) (by norm_num)
theorem B3406877 : Blo 1512953 3406877 := bbase (se 3 (by rfl) ⟨638789, by rfl⟩ : syracuseStep 3406877 = 1277579) (by norm_num)
theorem B1727525 : Blo 1512953 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B1817641 : Blo 1512953 1817641 := bbase (se 2 (by rfl) ⟨681615, by rfl⟩ : syracuseStep 1817641 = 1363231) (by norm_num)
theorem B1702957 : Blo 1512953 1702957 := bbase (se 3 (by rfl) ⟨319304, by rfl⟩ : syracuseStep 1702957 = 638609) (by norm_num)
theorem B1915969 : Blo 1512953 1915969 := bbase (se 2 (by rfl) ⟨718488, by rfl⟩ : syracuseStep 1915969 = 1436977) (by norm_num)
theorem B2554949 : Blo 1512953 2554949 := bbase (se 4 (by rfl) ⟨239526, by rfl⟩ : syracuseStep 2554949 = 479053) (by norm_num)
theorem B1702993 : Blo 1512953 1702993 := bbase (se 2 (by rfl) ⟨638622, by rfl⟩ : syracuseStep 1702993 = 1277245) (by norm_num)
theorem B3406949 : Blo 1512953 3406949 := bbase (se 4 (by rfl) ⟨319401, by rfl⟩ : syracuseStep 3406949 = 638803) (by norm_num)
theorem B4602997 : Blo 1512953 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B1703029 : Blo 1512953 1703029 := bbase (se 5 (by rfl) ⟨79829, by rfl⟩ : syracuseStep 1703029 = 159659) (by norm_num)
theorem B1703065 : Blo 1512953 1703065 := bbase (se 2 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 1703065 = 1277299) (by norm_num)
theorem B2301085 : Blo 1512953 2301085 := bbase (se 3 (by rfl) ⟨431453, by rfl⟩ : syracuseStep 2301085 = 862907) (by norm_num)
theorem B1916065 : Blo 1512953 1916065 := bbase (se 2 (by rfl) ⟨718524, by rfl⟩ : syracuseStep 1916065 = 1437049) (by norm_num)
theorem B3407021 : Blo 1512953 3407021 := bbase (se 3 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 3407021 = 1277633) (by norm_num)
theorem B1703101 : Blo 1512953 1703101 := bbase (se 3 (by rfl) ⟨319331, by rfl⟩ : syracuseStep 1703101 = 638663) (by norm_num)
theorem B3833021 : Blo 1512953 3833021 := bbase (se 3 (by rfl) ⟨718691, by rfl⟩ : syracuseStep 3833021 = 1437383) (by norm_num)
theorem B2555077 : Blo 1512953 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B5823701 : Blo 1512953 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B5749973 : Blo 1512953 5749973 := bbase (se 7 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 5749973 = 134765) (by norm_num)
theorem B1703137 : Blo 1512953 1703137 := bbase (se 2 (by rfl) ⟨638676, by rfl⟩ : syracuseStep 1703137 = 1277353) (by norm_num)
theorem B1817833 : Blo 1512953 1817833 := bbase (se 2 (by rfl) ⟨681687, by rfl⟩ : syracuseStep 1817833 = 1363375) (by norm_num)
theorem B3407093 : Blo 1512953 3407093 := bbase (se 5 (by rfl) ⟨159707, by rfl⟩ : syracuseStep 3407093 = 319415) (by norm_num)
theorem B3235069 : Blo 1512953 3235069 := bbase (se 3 (by rfl) ⟨606575, by rfl⟩ : syracuseStep 3235069 = 1213151) (by norm_num)
theorem B1703173 : Blo 1512953 1703173 := bbase (se 4 (by rfl) ⟨159672, by rfl⟩ : syracuseStep 1703173 = 319345) (by norm_num)
theorem B2874629 : Blo 1512953 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B5111045 : Blo 1512953 5111045 := bbase (se 4 (by rfl) ⟨479160, by rfl⟩ : syracuseStep 5111045 = 958321) (by norm_num)
theorem B2555165 : Blo 1512953 2555165 := bbase (se 3 (by rfl) ⟨479093, by rfl⟩ : syracuseStep 2555165 = 958187) (by norm_num)
theorem B1703209 : Blo 1512953 1703209 := bbase (se 2 (by rfl) ⟨638703, by rfl⟩ : syracuseStep 1703209 = 1277407) (by norm_num)
theorem B3407165 : Blo 1512953 3407165 := bbase (se 3 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 3407165 = 1277687) (by norm_num)
theorem B1703245 : Blo 1512953 1703245 := bbase (se 3 (by rfl) ⟨319358, by rfl⟩ : syracuseStep 1703245 = 638717) (by norm_num)
theorem B1916237 : Blo 1512953 1916237 := bbase (se 3 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 1916237 = 718589) (by norm_num)
theorem B3882341 : Blo 1512953 3882341 := bbase (se 4 (by rfl) ⟨363969, by rfl⟩ : syracuseStep 3882341 = 727939) (by norm_num)
theorem B3636589 : Blo 1512953 3636589 := bbase (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) (by norm_num)
theorem B1703281 : Blo 1512953 1703281 := bbase (se 2 (by rfl) ⟨638730, by rfl⟩ : syracuseStep 1703281 = 1277461) (by norm_num)
theorem B1916293 : Blo 1512953 1916293 := bbase (se 4 (by rfl) ⟨179652, by rfl⟩ : syracuseStep 1916293 = 359305) (by norm_num)
theorem B3407237 : Blo 1512953 3407237 := bbase (se 4 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 3407237 = 638857) (by norm_num)
theorem B9829781 : Blo 1512953 9829781 := bbase (se 6 (by rfl) ⟨230385, by rfl⟩ : syracuseStep 9829781 = 460771) (by norm_num)
theorem B10911125 : Blo 1512953 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B1703317 : Blo 1512953 1703317 := bbase (se 6 (by rfl) ⟨39921, by rfl⟩ : syracuseStep 1703317 = 79843) (by norm_num)
theorem B2555293 : Blo 1512953 2555293 := bbase (se 3 (by rfl) ⟨479117, by rfl⟩ : syracuseStep 2555293 = 958235) (by norm_num)
theorem B2874781 : Blo 1512953 2874781 := bbase (se 3 (by rfl) ⟨539021, by rfl⟩ : syracuseStep 2874781 = 1078043) (by norm_num)
theorem B1703353 : Blo 1512953 1703353 := bbase (se 2 (by rfl) ⟨638757, by rfl⟩ : syracuseStep 1703353 = 1277515) (by norm_num)
theorem B3636685 : Blo 1512953 3636685 := bbase (se 3 (by rfl) ⟨681878, by rfl⟩ : syracuseStep 3636685 = 1363757) (by norm_num)
theorem B3407309 : Blo 1512953 3407309 := bbase (se 3 (by rfl) ⟨638870, by rfl⟩ : syracuseStep 3407309 = 1277741) (by norm_num)
theorem B1703389 : Blo 1512953 1703389 := bbase (se 3 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 1703389 = 638771) (by norm_num)
theorem B1916389 : Blo 1512953 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B2555381 : Blo 1512953 2555381 := bbase (se 5 (by rfl) ⟨119783, by rfl⟩ : syracuseStep 2555381 = 239567) (by norm_num)
theorem B5750261 : Blo 1512953 5750261 := bbase (se 5 (by rfl) ⟨269543, by rfl⟩ : syracuseStep 5750261 = 539087) (by norm_num)
theorem B1703425 : Blo 1512953 1703425 := bbase (se 2 (by rfl) ⟨638784, by rfl⟩ : syracuseStep 1703425 = 1277569) (by norm_num)
theorem B3276301 : Blo 1512953 3276301 := bbase (se 3 (by rfl) ⟨614306, by rfl⟩ : syracuseStep 3276301 = 1228613) (by norm_num)
theorem B20708885 : Blo 1512953 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B2424341 : Blo 1512953 2424341 := bbase (se 6 (by rfl) ⟨56820, by rfl⟩ : syracuseStep 2424341 = 113641) (by norm_num)
theorem B3407381 : Blo 1512953 3407381 := bbase (se 6 (by rfl) ⟨79860, by rfl⟩ : syracuseStep 3407381 = 159721) (by norm_num)
theorem B3833365 : Blo 1512953 3833365 := bbase (se 6 (by rfl) ⟨89844, by rfl⟩ : syracuseStep 3833365 = 179689) (by norm_num)
theorem B1703461 : Blo 1512953 1703461 := bbase (se 4 (by rfl) ⟨159699, by rfl⟩ : syracuseStep 1703461 = 319399) (by norm_num)
theorem B1703497 : Blo 1512953 1703497 := bbase (se 2 (by rfl) ⟨638811, by rfl⟩ : syracuseStep 1703497 = 1277623) (by norm_num)
theorem B3407453 : Blo 1512953 3407453 := bbase (se 3 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 3407453 = 1277795) (by norm_num)
theorem B1703533 : Blo 1512953 1703533 := bbase (se 3 (by rfl) ⟨319412, by rfl⟩ : syracuseStep 1703533 = 638825) (by norm_num)
theorem B2555509 : Blo 1512953 2555509 := bbase (se 5 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 2555509 = 239579) (by norm_num)
theorem B2727557 : Blo 1512953 2727557 := bbase (se 4 (by rfl) ⟨255708, by rfl⟩ : syracuseStep 2727557 = 511417) (by norm_num)
theorem B3833477 : Blo 1512953 3833477 := bbase (se 4 (by rfl) ⟨359388, by rfl⟩ : syracuseStep 3833477 = 718777) (by norm_num)
theorem B1703569 : Blo 1512953 1703569 := bbase (se 2 (by rfl) ⟨638838, by rfl⟩ : syracuseStep 1703569 = 1277677) (by norm_num)
theorem B1916561 : Blo 1512953 1916561 := bbase (se 2 (by rfl) ⟨718710, by rfl⟩ : syracuseStep 1916561 = 1437421) (by norm_num)
theorem B6135445 : Blo 1512953 6135445 := bbase (se 6 (by rfl) ⟨143799, by rfl⟩ : syracuseStep 6135445 = 287599) (by norm_num)
theorem B3407525 : Blo 1512953 3407525 := bbase (se 4 (by rfl) ⟨319455, by rfl⟩ : syracuseStep 3407525 = 638911) (by norm_num)
theorem B1703605 : Blo 1512953 1703605 := bbase (se 5 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 1703605 = 159713) (by norm_num)
theorem B5111477 : Blo 1512953 5111477 := bbase (se 5 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 5111477 = 479201) (by norm_num)
theorem B3546821 : Blo 1512953 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B1916617 : Blo 1512953 1916617 := bbase (se 2 (by rfl) ⟨718731, by rfl⟩ : syracuseStep 1916617 = 1437463) (by norm_num)
theorem B2555597 : Blo 1512953 2555597 := bbase (se 3 (by rfl) ⟨479174, by rfl⟩ : syracuseStep 2555597 = 958349) (by norm_num)
theorem B2875085 : Blo 1512953 2875085 := bbase (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) (by norm_num)
theorem B1703641 : Blo 1512953 1703641 := bbase (se 2 (by rfl) ⟨638865, by rfl⟩ : syracuseStep 1703641 = 1277731) (by norm_num)
theorem B4308709 : Blo 1512953 4308709 := bbase (se 4 (by rfl) ⟨403941, by rfl⟩ : syracuseStep 4308709 = 807883) (by norm_num)
theorem B3407597 : Blo 1512953 3407597 := bbase (se 3 (by rfl) ⟨638924, by rfl⟩ : syracuseStep 3407597 = 1277849) (by norm_num)
theorem B1703677 : Blo 1512953 1703677 := bbase (se 3 (by rfl) ⟨319439, by rfl⟩ : syracuseStep 1703677 = 638879) (by norm_num)
theorem B6463253 : Blo 1512953 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1703713 : Blo 1512953 1703713 := bbase (se 2 (by rfl) ⟨638892, by rfl⟩ : syracuseStep 1703713 = 1277785) (by norm_num)
theorem B1916713 : Blo 1512953 1916713 := bbase (se 2 (by rfl) ⟨718767, by rfl⟩ : syracuseStep 1916713 = 1437535) (by norm_num)
theorem B5177141 : Blo 1512953 5177141 := bbase (se 5 (by rfl) ⟨242678, by rfl⟩ : syracuseStep 5177141 = 485357) (by norm_num)
theorem B3407669 : Blo 1512953 3407669 := bbase (se 5 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 3407669 = 319469) (by norm_num)
theorem B1703749 : Blo 1512953 1703749 := bbase (se 4 (by rfl) ⟨159726, by rfl⟩ : syracuseStep 1703749 = 319453) (by norm_num)
theorem B3833669 : Blo 1512953 3833669 := bbase (se 4 (by rfl) ⟨359406, by rfl⟩ : syracuseStep 3833669 = 718813) (by norm_num)
theorem B2555725 : Blo 1512953 2555725 := bbase (se 3 (by rfl) ⟨479198, by rfl⟩ : syracuseStep 2555725 = 958397) (by norm_num)
theorem B1703785 : Blo 1512953 1703785 := bbase (se 2 (by rfl) ⟨638919, by rfl⟩ : syracuseStep 1703785 = 1277839) (by norm_num)
theorem B3407741 : Blo 1512953 3407741 := bbase (se 3 (by rfl) ⟨638951, by rfl⟩ : syracuseStep 3407741 = 1277903) (by norm_num)
theorem B4308869 : Blo 1512953 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B1703821 : Blo 1512953 1703821 := bbase (se 3 (by rfl) ⟨319466, by rfl⟩ : syracuseStep 1703821 = 638933) (by norm_num)
theorem B2555813 : Blo 1512953 2555813 := bbase (se 4 (by rfl) ⟨239607, by rfl⟩ : syracuseStep 2555813 = 479215) (by norm_num)
theorem B7667621 : Blo 1512953 7667621 := bbase (se 4 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 7667621 = 1437679) (by norm_num)
theorem B1703857 : Blo 1512953 1703857 := bbase (se 2 (by rfl) ⟨638946, by rfl⟩ : syracuseStep 1703857 = 1277893) (by norm_num)
theorem B3407813 : Blo 1512953 3407813 := bbase (se 4 (by rfl) ⟨319482, by rfl⟩ : syracuseStep 3407813 = 638965) (by norm_num)
theorem B1703893 : Blo 1512953 1703893 := bbase (se 7 (by rfl) ⟨19967, by rfl⟩ : syracuseStep 1703893 = 39935) (by norm_num)
theorem B1916885 : Blo 1512953 1916885 := bbase (se 7 (by rfl) ⟨22463, by rfl⟩ : syracuseStep 1916885 = 44927) (by norm_num)
theorem B1703929 : Blo 1512953 1703929 := bbase (se 2 (by rfl) ⟨638973, by rfl⟩ : syracuseStep 1703929 = 1277947) (by norm_num)
theorem B2555921 : Blo 1512953 2555921 := bstep (se 2 (by rfl) ⟨958470, by rfl⟩ : syracuseStep 2555921 = 1916941) B1916941
theorem B3407921 : Blo 1512953 3407921 := bstep (se 2 (by rfl) ⟨1277970, by rfl⟩ : syracuseStep 3407921 = 2555941) B2555941
theorem B3407939 : Blo 1512953 3407939 := bstep (se 1 (by rfl) ⟨2555954, by rfl⟩ : syracuseStep 3407939 = 5111909) B5111909
theorem B4431953 : Blo 1512953 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B1704019 : Blo 1512953 1704019 := bstep (se 1 (by rfl) ⟨1278014, by rfl⟩ : syracuseStep 1704019 = 2556029) B2556029
theorem B28000397 : Blo 1512953 28000397 := bstep (se 3 (by rfl) ⟨5250074, by rfl⟩ : syracuseStep 28000397 = 10500149) B10500149
theorem B2556049 : Blo 1512953 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B7659683 : Blo 1512953 7659683 := bstep (se 1 (by rfl) ⟨5744762, by rfl⟩ : syracuseStep 7659683 = 11489525) B11489525
theorem B8618147 : Blo 1512953 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B2556083 : Blo 1512953 2556083 := bstep (se 1 (by rfl) ⟨1917062, by rfl⟩ : syracuseStep 2556083 = 3834125) B3834125
theorem B2154691 : Blo 1512953 2154691 := bstep (se 1 (by rfl) ⟨1616018, by rfl⟩ : syracuseStep 2154691 = 3232037) B3232037
theorem B5112017 : Blo 1512953 5112017 := bstep (se 2 (by rfl) ⟨1917006, by rfl⟩ : syracuseStep 5112017 = 3834013) B3834013
theorem B2875601 : Blo 1512953 2875601 := bstep (se 2 (by rfl) ⟨1078350, by rfl⟩ : syracuseStep 2875601 = 2156701) B2156701
theorem B1704163 : Blo 1512953 1704163 := bstep (se 1 (by rfl) ⟨1278122, by rfl⟩ : syracuseStep 1704163 = 2556245) B2556245
theorem B4849901 : Blo 1512953 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B16589069 : Blo 1512953 16589069 := bstep (se 3 (by rfl) ⟨3110450, by rfl⟩ : syracuseStep 16589069 = 6220901) B6220901
theorem B2269457 : Blo 1512953 2269457 := bstep (se 2 (by rfl) ⟨851046, by rfl⟩ : syracuseStep 2269457 = 1702093) B1702093
theorem B2269475 : Blo 1512953 2269475 := bstep (se 1 (by rfl) ⟨1702106, by rfl⟩ : syracuseStep 2269475 = 3404213) B3404213
theorem B2556211 : Blo 1512953 2556211 := bstep (se 1 (by rfl) ⟨1917158, by rfl⟩ : syracuseStep 2556211 = 3834317) B3834317
theorem B2269505 : Blo 1512953 2269505 := bstep (se 2 (by rfl) ⟨851064, by rfl⟩ : syracuseStep 2269505 = 1702129) B1702129
theorem B4309325 : Blo 1512953 4309325 := bstep (se 3 (by rfl) ⟨807998, by rfl⟩ : syracuseStep 4309325 = 1615997) B1615997
theorem B3408209 : Blo 1512953 3408209 := bstep (se 2 (by rfl) ⟨1278078, by rfl⟩ : syracuseStep 3408209 = 2556157) B2556157
theorem B2269523 : Blo 1512953 2269523 := bstep (se 1 (by rfl) ⟨1702142, by rfl⟩ : syracuseStep 2269523 = 3404285) B3404285
theorem B2425187 : Blo 1512953 2425187 := bstep (se 1 (by rfl) ⟨1818890, by rfl⟩ : syracuseStep 2425187 = 3637781) B3637781
theorem B3408227 : Blo 1512953 3408227 := bstep (se 1 (by rfl) ⟨2556170, by rfl⟩ : syracuseStep 3408227 = 5112341) B5112341
theorem B2269553 : Blo 1512953 2269553 := bstep (se 2 (by rfl) ⟨851082, by rfl⟩ : syracuseStep 2269553 = 1702165) B1702165
theorem B1704307 : Blo 1512953 1704307 := bstep (se 1 (by rfl) ⟨1278230, by rfl⟩ : syracuseStep 1704307 = 2556461) B2556461
theorem B2269571 : Blo 1512953 2269571 := bstep (se 1 (by rfl) ⟨1702178, by rfl⟩ : syracuseStep 2269571 = 3404357) B3404357
theorem B2269601 : Blo 1512953 2269601 := bstep (se 2 (by rfl) ⟨851100, by rfl⟩ : syracuseStep 2269601 = 1702201) B1702201
theorem B2269619 : Blo 1512953 2269619 := bstep (se 1 (by rfl) ⟨1702214, by rfl⟩ : syracuseStep 2269619 = 3404429) B3404429
theorem B2556353 : Blo 1512953 2556353 := bstep (se 2 (by rfl) ⟨958632, by rfl⟩ : syracuseStep 2556353 = 1917265) B1917265
theorem B2269649 : Blo 1512953 2269649 := bstep (se 2 (by rfl) ⟨851118, by rfl⟩ : syracuseStep 2269649 = 1702237) B1702237
theorem B2269667 : Blo 1512953 2269667 := bstep (se 1 (by rfl) ⟨1702250, by rfl⟩ : syracuseStep 2269667 = 3404501) B3404501
theorem B2269697 : Blo 1512953 2269697 := bstep (se 2 (by rfl) ⟨851136, by rfl⟩ : syracuseStep 2269697 = 1702273) B1702273
theorem B2728451 : Blo 1512953 2728451 := bstep (se 1 (by rfl) ⟨2046338, by rfl⟩ : syracuseStep 2728451 = 4092677) B4092677
theorem B2269715 : Blo 1512953 2269715 := bstep (se 1 (by rfl) ⟨1702286, by rfl⟩ : syracuseStep 2269715 = 3404573) B3404573
theorem B2155027 : Blo 1512953 2155027 := bstep (se 1 (by rfl) ⟨1616270, by rfl⟩ : syracuseStep 2155027 = 3232541) B3232541
theorem B2269745 : Blo 1512953 2269745 := bstep (se 2 (by rfl) ⟨851154, by rfl⟩ : syracuseStep 2269745 = 1702309) B1702309
theorem B2556481 : Blo 1512953 2556481 := bstep (se 2 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 2556481 = 1917361) B1917361
theorem B2269763 : Blo 1512953 2269763 := bstep (se 1 (by rfl) ⟨1702322, by rfl⟩ : syracuseStep 2269763 = 3404645) B3404645
theorem B5988941 : Blo 1512953 5988941 := bstep (se 3 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 5988941 = 2245853) B2245853
theorem B3834449 : Blo 1512953 3834449 := bstep (se 2 (by rfl) ⟨1437918, by rfl⟩ : syracuseStep 3834449 = 2875837) B2875837
theorem B2269793 : Blo 1512953 2269793 := bstep (se 2 (by rfl) ⟨851172, by rfl⟩ : syracuseStep 2269793 = 1702345) B1702345
theorem B3408497 : Blo 1512953 3408497 := bstep (se 2 (by rfl) ⟨1278186, by rfl⟩ : syracuseStep 3408497 = 2556373) B2556373
theorem B2269811 : Blo 1512953 2269811 := bstep (se 1 (by rfl) ⟨1702358, by rfl⟩ : syracuseStep 2269811 = 3404717) B3404717
theorem B3834499 : Blo 1512953 3834499 := bstep (se 1 (by rfl) ⟨2875874, by rfl⟩ : syracuseStep 3834499 = 5751749) B5751749
theorem B3408515 : Blo 1512953 3408515 := bstep (se 1 (by rfl) ⟨2556386, by rfl⟩ : syracuseStep 3408515 = 5112773) B5112773
theorem B2269841 : Blo 1512953 2269841 := bstep (se 2 (by rfl) ⟨851190, by rfl⟩ : syracuseStep 2269841 = 1702381) B1702381
theorem B2269859 : Blo 1512953 2269859 := bstep (se 1 (by rfl) ⟨1702394, by rfl⟩ : syracuseStep 2269859 = 3404789) B3404789
theorem B6136483 : Blo 1512953 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B2269889 : Blo 1512953 2269889 := bstep (se 2 (by rfl) ⟨851208, by rfl⟩ : syracuseStep 2269889 = 1702417) B1702417
theorem B2269907 : Blo 1512953 2269907 := bstep (se 1 (by rfl) ⟨1702430, by rfl⟩ : syracuseStep 2269907 = 3404861) B3404861
theorem B5112557 : Blo 1512953 5112557 := bstep (se 3 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 5112557 = 1917209) B1917209
theorem B2269937 : Blo 1512953 2269937 := bstep (se 2 (by rfl) ⟨851226, by rfl⟩ : syracuseStep 2269937 = 1702453) B1702453
theorem B2269955 : Blo 1512953 2269955 := bstep (se 1 (by rfl) ⟨1702466, by rfl⟩ : syracuseStep 2269955 = 3404933) B3404933
theorem B8741645 : Blo 1512953 8741645 := bstep (se 3 (by rfl) ⟨1639058, by rfl⟩ : syracuseStep 8741645 = 3278117) B3278117
theorem B3834641 : Blo 1512953 3834641 := bstep (se 2 (by rfl) ⟨1437990, by rfl⟩ : syracuseStep 3834641 = 2875981) B2875981
theorem B2269985 : Blo 1512953 2269985 := bstep (se 2 (by rfl) ⟨851244, by rfl⟩ : syracuseStep 2269985 = 1702489) B1702489
theorem B5112611 : Blo 1512953 5112611 := bstep (se 1 (by rfl) ⟨3834458, by rfl⟩ : syracuseStep 5112611 = 7668917) B7668917
theorem B2270003 : Blo 1512953 2270003 := bstep (se 1 (by rfl) ⟨1702502, by rfl⟩ : syracuseStep 2270003 = 3405005) B3405005
theorem B2270033 : Blo 1512953 2270033 := bstep (se 2 (by rfl) ⟨851262, by rfl⟩ : syracuseStep 2270033 = 1702525) B1702525
theorem B2270051 : Blo 1512953 2270051 := bstep (se 1 (by rfl) ⟨1702538, by rfl⟩ : syracuseStep 2270051 = 3405077) B3405077
theorem B7668593 : Blo 1512953 7668593 := bstep (se 2 (by rfl) ⟨2875722, by rfl⟩ : syracuseStep 7668593 = 5751445) B5751445
theorem B2270081 : Blo 1512953 2270081 := bstep (se 2 (by rfl) ⟨851280, by rfl⟩ : syracuseStep 2270081 = 1702561) B1702561
theorem B2270099 : Blo 1512953 2270099 := bstep (se 1 (by rfl) ⟨1702574, by rfl⟩ : syracuseStep 2270099 = 3405149) B3405149
theorem B2270129 : Blo 1512953 2270129 := bstep (se 2 (by rfl) ⟨851298, by rfl⟩ : syracuseStep 2270129 = 1702597) B1702597
theorem B2270147 : Blo 1512953 2270147 := bstep (se 1 (by rfl) ⟨1702610, by rfl⟩ : syracuseStep 2270147 = 3405221) B3405221
theorem B7660493 : Blo 1512953 7660493 := bstep (se 3 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 7660493 = 2872685) B2872685
theorem B2270177 : Blo 1512953 2270177 := bstep (se 2 (by rfl) ⟨851316, by rfl⟩ : syracuseStep 2270177 = 1702633) B1702633
theorem B11494385 : Blo 1512953 11494385 := bstep (se 2 (by rfl) ⟨4310394, by rfl⟩ : syracuseStep 11494385 = 8620789) B8620789
theorem B9700337 : Blo 1512953 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B2270195 : Blo 1512953 2270195 := bstep (se 1 (by rfl) ⟨1702646, by rfl⟩ : syracuseStep 2270195 = 3405293) B3405293
theorem B2270225 : Blo 1512953 2270225 := bstep (se 2 (by rfl) ⟨851334, by rfl⟩ : syracuseStep 2270225 = 1702669) B1702669
theorem B2270243 : Blo 1512953 2270243 := bstep (se 1 (by rfl) ⟨1702682, by rfl⟩ : syracuseStep 2270243 = 3405365) B3405365
theorem B5112881 : Blo 1512953 5112881 := bstep (se 2 (by rfl) ⟨1917330, by rfl⟩ : syracuseStep 5112881 = 3834661) B3834661
theorem B20726837 : Blo 1512953 20726837 := bstep (se 5 (by rfl) ⟨971570, by rfl⟩ : syracuseStep 20726837 = 1943141) B1943141
theorem B2270273 : Blo 1512953 2270273 := bstep (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) B1702705
theorem B2155585 : Blo 1512953 2155585 := bstep (se 2 (by rfl) ⟨808344, by rfl⟩ : syracuseStep 2155585 = 1616689) B1616689
theorem B2270291 : Blo 1512953 2270291 := bstep (se 1 (by rfl) ⟨1702718, by rfl⟩ : syracuseStep 2270291 = 3405437) B3405437
theorem B2155619 : Blo 1512953 2155619 := bstep (se 1 (by rfl) ⟨1616714, by rfl⟩ : syracuseStep 2155619 = 3233429) B3233429
theorem B2270321 : Blo 1512953 2270321 := bstep (se 2 (by rfl) ⟨851370, by rfl⟩ : syracuseStep 2270321 = 1702741) B1702741
theorem B2270339 : Blo 1512953 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B8619149 : Blo 1512953 8619149 := bstep (se 3 (by rfl) ⟨1616090, by rfl⟩ : syracuseStep 8619149 = 3232181) B3232181
theorem B2270369 : Blo 1512953 2270369 := bstep (se 2 (by rfl) ⟨851388, by rfl⟩ : syracuseStep 2270369 = 1702777) B1702777
theorem B2426033 : Blo 1512953 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B2270387 : Blo 1512953 2270387 := bstep (se 1 (by rfl) ⟨1702790, by rfl⟩ : syracuseStep 2270387 = 3405581) B3405581
theorem B2270417 : Blo 1512953 2270417 := bstep (se 2 (by rfl) ⟨851406, by rfl⟩ : syracuseStep 2270417 = 1702813) B1702813
theorem B2270435 : Blo 1512953 2270435 := bstep (se 1 (by rfl) ⟨1702826, by rfl⟩ : syracuseStep 2270435 = 3405653) B3405653
theorem B2270465 : Blo 1512953 2270465 := bstep (se 2 (by rfl) ⟨851424, by rfl⟩ : syracuseStep 2270465 = 1702849) B1702849
theorem B2270483 : Blo 1512953 2270483 := bstep (se 1 (by rfl) ⟨1702862, by rfl⟩ : syracuseStep 2270483 = 3405725) B3405725
theorem B2270513 : Blo 1512953 2270513 := bstep (se 2 (by rfl) ⟨851442, by rfl⟩ : syracuseStep 2270513 = 1702885) B1702885
theorem B2270531 : Blo 1512953 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B2270561 : Blo 1512953 2270561 := bstep (se 2 (by rfl) ⟨851460, by rfl⟩ : syracuseStep 2270561 = 1702921) B1702921
theorem B2270579 : Blo 1512953 2270579 := bstep (se 1 (by rfl) ⟨1702934, by rfl⟩ : syracuseStep 2270579 = 3405869) B3405869
theorem B6464909 : Blo 1512953 6464909 := bstep (se 3 (by rfl) ⟨1212170, by rfl⟩ : syracuseStep 6464909 = 2424341) B2424341
theorem B2270609 : Blo 1512953 2270609 := bstep (se 2 (by rfl) ⟨851478, by rfl⟩ : syracuseStep 2270609 = 1702957) B1702957
theorem B2270627 : Blo 1512953 2270627 := bstep (se 1 (by rfl) ⟨1702970, by rfl⟩ : syracuseStep 2270627 = 3405941) B3405941
theorem B2270657 : Blo 1512953 2270657 := bstep (se 2 (by rfl) ⟨851496, by rfl⟩ : syracuseStep 2270657 = 1702993) B1702993
theorem B2270675 : Blo 1512953 2270675 := bstep (se 1 (by rfl) ⟨1703006, by rfl⟩ : syracuseStep 2270675 = 3406013) B3406013
theorem B4310509 : Blo 1512953 4310509 := bstep (se 3 (by rfl) ⟨808220, by rfl⟩ : syracuseStep 4310509 = 1616441) B1616441
theorem B2270705 : Blo 1512953 2270705 := bstep (se 2 (by rfl) ⟨851514, by rfl⟩ : syracuseStep 2270705 = 1703029) B1703029
theorem B2270723 : Blo 1512953 2270723 := bstep (se 1 (by rfl) ⟨1703042, by rfl⟩ : syracuseStep 2270723 = 3406085) B3406085
theorem B2270753 : Blo 1512953 2270753 := bstep (se 2 (by rfl) ⟨851532, by rfl⟩ : syracuseStep 2270753 = 1703065) B1703065
theorem B3638819 : Blo 1512953 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B4851245 : Blo 1512953 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B7276081 : Blo 1512953 7276081 := bstep (se 2 (by rfl) ⟨2728530, by rfl⟩ : syracuseStep 7276081 = 5457061) B5457061
theorem B2270771 : Blo 1512953 2270771 := bstep (se 1 (by rfl) ⟨1703078, by rfl⟩ : syracuseStep 2270771 = 3406157) B3406157
theorem B2270801 : Blo 1512953 2270801 := bstep (se 2 (by rfl) ⟨851550, by rfl⟩ : syracuseStep 2270801 = 1703101) B1703101
theorem B2270819 : Blo 1512953 2270819 := bstep (se 1 (by rfl) ⟨1703114, by rfl⟩ : syracuseStep 2270819 = 3406229) B3406229
theorem B2270849 : Blo 1512953 2270849 := bstep (se 2 (by rfl) ⟨851568, by rfl⟩ : syracuseStep 2270849 = 1703137) B1703137
theorem B2156177 : Blo 1512953 2156177 := bstep (se 2 (by rfl) ⟨808566, by rfl⟩ : syracuseStep 2156177 = 1617133) B1617133
theorem B2270867 : Blo 1512953 2270867 := bstep (se 1 (by rfl) ⟨1703150, by rfl⟩ : syracuseStep 2270867 = 3406301) B3406301
theorem B2270897 : Blo 1512953 2270897 := bstep (se 2 (by rfl) ⟨851586, by rfl⟩ : syracuseStep 2270897 = 1703173) B1703173
theorem B2426545 : Blo 1512953 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B2270915 : Blo 1512953 2270915 := bstep (se 1 (by rfl) ⟨1703186, by rfl⟩ : syracuseStep 2270915 = 3406373) B3406373
theorem B2270945 : Blo 1512953 2270945 := bstep (se 2 (by rfl) ⟨851604, by rfl⟩ : syracuseStep 2270945 = 1703209) B1703209
theorem B2156257 : Blo 1512953 2156257 := bstep (se 2 (by rfl) ⟨808596, by rfl⟩ : syracuseStep 2156257 = 1617193) B1617193
theorem B6465251 : Blo 1512953 6465251 := bstep (se 1 (by rfl) ⟨4848938, by rfl⟩ : syracuseStep 6465251 = 9697877) B9697877
theorem B2270963 : Blo 1512953 2270963 := bstep (se 1 (by rfl) ⟨1703222, by rfl⟩ : syracuseStep 2270963 = 3406445) B3406445
theorem B2270993 : Blo 1512953 2270993 := bstep (se 2 (by rfl) ⟨851622, by rfl⟩ : syracuseStep 2270993 = 1703245) B1703245
theorem B2271011 : Blo 1512953 2271011 := bstep (se 1 (by rfl) ⟨1703258, by rfl⟩ : syracuseStep 2271011 = 3406517) B3406517
theorem B8734513 : Blo 1512953 8734513 := bstep (se 2 (by rfl) ⟨3275442, by rfl⟩ : syracuseStep 8734513 = 6550885) B6550885
theorem B2271041 : Blo 1512953 2271041 := bstep (se 2 (by rfl) ⟨851640, by rfl⟩ : syracuseStep 2271041 = 1703281) B1703281
theorem B2271059 : Blo 1512953 2271059 := bstep (se 1 (by rfl) ⟨1703294, by rfl⟩ : syracuseStep 2271059 = 3406589) B3406589
theorem B2271089 : Blo 1512953 2271089 := bstep (se 2 (by rfl) ⟨851658, by rfl⟩ : syracuseStep 2271089 = 1703317) B1703317
theorem B2271107 : Blo 1512953 2271107 := bstep (se 1 (by rfl) ⟨1703330, by rfl⟩ : syracuseStep 2271107 = 3406661) B3406661
theorem B2271137 : Blo 1512953 2271137 := bstep (se 2 (by rfl) ⟨851676, by rfl⟩ : syracuseStep 2271137 = 1703353) B1703353
theorem B2271155 : Blo 1512953 2271155 := bstep (se 1 (by rfl) ⟨1703366, by rfl⟩ : syracuseStep 2271155 = 3406733) B3406733
theorem B2271185 : Blo 1512953 2271185 := bstep (se 2 (by rfl) ⟨851694, by rfl⟩ : syracuseStep 2271185 = 1703389) B1703389
theorem B2271203 : Blo 1512953 2271203 := bstep (se 1 (by rfl) ⟨1703402, by rfl⟩ : syracuseStep 2271203 = 3406805) B3406805
theorem B2271233 : Blo 1512953 2271233 := bstep (se 2 (by rfl) ⟨851712, by rfl⟩ : syracuseStep 2271233 = 1703425) B1703425
theorem B4368401 : Blo 1512953 4368401 := bstep (se 2 (by rfl) ⟨1638150, by rfl⟩ : syracuseStep 4368401 = 3276301) B3276301
theorem B2271251 : Blo 1512953 2271251 := bstep (se 1 (by rfl) ⟨1703438, by rfl⟩ : syracuseStep 2271251 = 3406877) B3406877
theorem B2271281 : Blo 1512953 2271281 := bstep (se 2 (by rfl) ⟨851730, by rfl⟩ : syracuseStep 2271281 = 1703461) B1703461
theorem B2271299 : Blo 1512953 2271299 := bstep (se 1 (by rfl) ⟨1703474, by rfl⟩ : syracuseStep 2271299 = 3406949) B3406949
theorem B2271329 : Blo 1512953 2271329 := bstep (se 2 (by rfl) ⟨851748, by rfl⟩ : syracuseStep 2271329 = 1703497) B1703497
theorem B3885155 : Blo 1512953 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B2271347 : Blo 1512953 2271347 := bstep (se 1 (by rfl) ⟨1703510, by rfl⟩ : syracuseStep 2271347 = 3407021) B3407021
theorem B2590849 : Blo 1512953 2590849 := bstep (se 2 (by rfl) ⟨971568, by rfl⟩ : syracuseStep 2590849 = 1943137) B1943137
theorem B2271377 : Blo 1512953 2271377 := bstep (se 2 (by rfl) ⟨851766, by rfl⟩ : syracuseStep 2271377 = 1703533) B1703533
theorem B2271395 : Blo 1512953 2271395 := bstep (se 1 (by rfl) ⟨1703546, by rfl⟩ : syracuseStep 2271395 = 3407093) B3407093
theorem B2271425 : Blo 1512953 2271425 := bstep (se 2 (by rfl) ⟨851784, by rfl⟩ : syracuseStep 2271425 = 1703569) B1703569
theorem B2271443 : Blo 1512953 2271443 := bstep (se 1 (by rfl) ⟨1703582, by rfl⟩ : syracuseStep 2271443 = 3407165) B3407165
theorem B2271473 : Blo 1512953 2271473 := bstep (se 2 (by rfl) ⟨851802, by rfl⟩ : syracuseStep 2271473 = 1703605) B1703605
theorem B2271491 : Blo 1512953 2271491 := bstep (se 1 (by rfl) ⟨1703618, by rfl⟩ : syracuseStep 2271491 = 3407237) B3407237
theorem B2271521 : Blo 1512953 2271521 := bstep (se 2 (by rfl) ⟨851820, by rfl⟩ : syracuseStep 2271521 = 1703641) B1703641
theorem B5744945 : Blo 1512953 5744945 := bstep (se 2 (by rfl) ⟨2154354, by rfl⟩ : syracuseStep 5744945 = 4308709) B4308709
theorem B2271539 : Blo 1512953 2271539 := bstep (se 1 (by rfl) ⟨1703654, by rfl⟩ : syracuseStep 2271539 = 3407309) B3407309
theorem B5531981 : Blo 1512953 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B2271569 : Blo 1512953 2271569 := bstep (se 2 (by rfl) ⟨851838, by rfl⟩ : syracuseStep 2271569 = 1703677) B1703677
theorem B13805923 : Blo 1512953 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B2271587 : Blo 1512953 2271587 := bstep (se 1 (by rfl) ⟨1703690, by rfl⟩ : syracuseStep 2271587 = 3407381) B3407381
theorem B2271617 : Blo 1512953 2271617 := bstep (se 2 (by rfl) ⟨851856, by rfl⟩ : syracuseStep 2271617 = 1703713) B1703713
theorem B2271635 : Blo 1512953 2271635 := bstep (se 1 (by rfl) ⟨1703726, by rfl⟩ : syracuseStep 2271635 = 3407453) B3407453
theorem B2271665 : Blo 1512953 2271665 := bstep (se 2 (by rfl) ⟨851874, by rfl⟩ : syracuseStep 2271665 = 1703749) B1703749
theorem B2271683 : Blo 1512953 2271683 := bstep (se 1 (by rfl) ⟨1703762, by rfl⟩ : syracuseStep 2271683 = 3407525) B3407525
theorem B2271713 : Blo 1512953 2271713 := bstep (se 2 (by rfl) ⟨851892, by rfl⟩ : syracuseStep 2271713 = 1703785) B1703785
theorem B2271731 : Blo 1512953 2271731 := bstep (se 1 (by rfl) ⟨1703798, by rfl⟩ : syracuseStep 2271731 = 3407597) B3407597
theorem B5458445 : Blo 1512953 5458445 := bstep (se 3 (by rfl) ⟨1023458, by rfl⟩ : syracuseStep 5458445 = 2046917) B2046917
theorem B4311569 : Blo 1512953 4311569 := bstep (se 2 (by rfl) ⟨1616838, by rfl⟩ : syracuseStep 4311569 = 3233677) B3233677
theorem B2271761 : Blo 1512953 2271761 := bstep (se 2 (by rfl) ⟨851910, by rfl⟩ : syracuseStep 2271761 = 1703821) B1703821
theorem B3451427 : Blo 1512953 3451427 := bstep (se 1 (by rfl) ⟨2588570, by rfl⟩ : syracuseStep 3451427 = 5177141) B5177141
theorem B2271779 : Blo 1512953 2271779 := bstep (se 1 (by rfl) ⟨1703834, by rfl⟩ : syracuseStep 2271779 = 3407669) B3407669
theorem B2271809 : Blo 1512953 2271809 := bstep (se 2 (by rfl) ⟨851928, by rfl⟩ : syracuseStep 2271809 = 1703857) B1703857
theorem B2271827 : Blo 1512953 2271827 := bstep (se 1 (by rfl) ⟨1703870, by rfl⟩ : syracuseStep 2271827 = 3407741) B3407741
theorem B2271857 : Blo 1512953 2271857 := bstep (se 2 (by rfl) ⟨851946, by rfl⟩ : syracuseStep 2271857 = 1703893) B1703893
theorem B2271875 : Blo 1512953 2271875 := bstep (se 1 (by rfl) ⟨1703906, by rfl⟩ : syracuseStep 2271875 = 3407813) B3407813
theorem B2271905 : Blo 1512953 2271905 := bstep (se 2 (by rfl) ⟨851964, by rfl⟩ : syracuseStep 2271905 = 1703929) B1703929
theorem B2271923 : Blo 1512953 2271923 := bstep (se 1 (by rfl) ⟨1703942, by rfl⟩ : syracuseStep 2271923 = 3407885) B3407885
theorem B2271953 : Blo 1512953 2271953 := bstep (se 2 (by rfl) ⟨851982, by rfl⟩ : syracuseStep 2271953 = 1703965) B1703965
theorem B2271971 : Blo 1512953 2271971 := bstep (se 1 (by rfl) ⟨1703978, by rfl⟩ : syracuseStep 2271971 = 3407957) B3407957
theorem B2272001 : Blo 1512953 2272001 := bstep (se 2 (by rfl) ⟨852000, by rfl⟩ : syracuseStep 2272001 = 1704001) B1704001
theorem B12282637 : Blo 1512953 12282637 := bstep (se 3 (by rfl) ⟨2302994, by rfl⟩ : syracuseStep 12282637 = 4605989) B4605989
theorem B4606733 : Blo 1512953 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B2272019 : Blo 1512953 2272019 := bstep (se 1 (by rfl) ⟨1704014, by rfl⟩ : syracuseStep 2272019 = 3408029) B3408029
theorem B2272049 : Blo 1512953 2272049 := bstep (se 2 (by rfl) ⟨852018, by rfl⟩ : syracuseStep 2272049 = 1704037) B1704037
theorem B2272067 : Blo 1512953 2272067 := bstep (se 1 (by rfl) ⟨1704050, by rfl⟩ : syracuseStep 2272067 = 3408101) B3408101
theorem B5106509 : Blo 1512953 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B2272097 : Blo 1512953 2272097 := bstep (se 2 (by rfl) ⟨852036, by rfl⟩ : syracuseStep 2272097 = 1704073) B1704073
theorem B1534835 : Blo 1512953 1534835 := bstep (se 1 (by rfl) ⟨1151126, by rfl⟩ : syracuseStep 1534835 = 2302253) B2302253
theorem B2272115 : Blo 1512953 2272115 := bstep (se 1 (by rfl) ⟨1704086, by rfl⟩ : syracuseStep 2272115 = 3408173) B3408173
theorem B5106563 : Blo 1512953 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B8981381 : Blo 1512953 8981381 := bstep (se 4 (by rfl) ⟨842004, by rfl⟩ : syracuseStep 8981381 = 1684009) B1684009
theorem B2272145 : Blo 1512953 2272145 := bstep (se 2 (by rfl) ⟨852054, by rfl⟩ : syracuseStep 2272145 = 1704109) B1704109
theorem B2272163 : Blo 1512953 2272163 := bstep (se 1 (by rfl) ⟨1704122, by rfl⟩ : syracuseStep 2272163 = 3408245) B3408245
theorem B2272193 : Blo 1512953 2272193 := bstep (se 2 (by rfl) ⟨852072, by rfl⟩ : syracuseStep 2272193 = 1704145) B1704145
theorem B5745613 : Blo 1512953 5745613 := bstep (se 3 (by rfl) ⟨1077302, by rfl⟩ : syracuseStep 5745613 = 2154605) B2154605
theorem B1616851 : Blo 1512953 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B2272211 : Blo 1512953 2272211 := bstep (se 1 (by rfl) ⟨1704158, by rfl⟩ : syracuseStep 2272211 = 3408317) B3408317
theorem B14740451 : Blo 1512953 14740451 := bstep (se 1 (by rfl) ⟨11055338, by rfl⟩ : syracuseStep 14740451 = 22110677) B22110677
theorem B2272241 : Blo 1512953 2272241 := bstep (se 2 (by rfl) ⟨852090, by rfl⟩ : syracuseStep 2272241 = 1704181) B1704181
theorem B2272259 : Blo 1512953 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B2272289 : Blo 1512953 2272289 := bstep (se 2 (by rfl) ⟨852108, by rfl⟩ : syracuseStep 2272289 = 1704217) B1704217
theorem B2272307 : Blo 1512953 2272307 := bstep (se 1 (by rfl) ⟨1704230, by rfl⟩ : syracuseStep 2272307 = 3408461) B3408461
theorem B2272337 : Blo 1512953 2272337 := bstep (se 2 (by rfl) ⟨852126, by rfl⟩ : syracuseStep 2272337 = 1704253) B1704253
theorem B4852835 : Blo 1512953 4852835 := bstep (se 1 (by rfl) ⟨3639626, by rfl⟩ : syracuseStep 4852835 = 7279253) B7279253
theorem B2272355 : Blo 1512953 2272355 := bstep (se 1 (by rfl) ⟨1704266, by rfl⟩ : syracuseStep 2272355 = 3408533) B3408533
theorem B2272385 : Blo 1512953 2272385 := bstep (se 2 (by rfl) ⟨852144, by rfl⟩ : syracuseStep 2272385 = 1704289) B1704289
theorem B5106833 : Blo 1512953 5106833 := bstep (se 2 (by rfl) ⟨1915062, by rfl⟩ : syracuseStep 5106833 = 3830125) B3830125
theorem B2272403 : Blo 1512953 2272403 := bstep (se 1 (by rfl) ⟨1704302, by rfl⟩ : syracuseStep 2272403 = 3408605) B3408605
theorem B4312241 : Blo 1512953 4312241 := bstep (se 2 (by rfl) ⟨1617090, by rfl⟩ : syracuseStep 4312241 = 3234181) B3234181
theorem B4369763 : Blo 1512953 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B1617283 : Blo 1512953 1617283 := bstep (se 1 (by rfl) ⟨1212962, by rfl⟩ : syracuseStep 1617283 = 2425925) B2425925
theorem B3935633 : Blo 1512953 3935633 := bstep (se 2 (by rfl) ⟨1475862, by rfl⟩ : syracuseStep 3935633 = 2951725) B2951725
theorem B32722373 : Blo 1512953 32722373 := bstep (se 4 (by rfl) ⟨3067722, by rfl⟩ : syracuseStep 32722373 = 6135445) B6135445
theorem B31075811 : Blo 1512953 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B6139405 : Blo 1512953 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B5107373 : Blo 1512953 5107373 := bstep (se 3 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 5107373 = 1915265) B1915265
theorem B9211589 : Blo 1512953 9211589 := bstep (se 4 (by rfl) ⟨863586, by rfl⟩ : syracuseStep 9211589 = 1727173) B1727173
theorem B4091597 : Blo 1512953 4091597 := bstep (se 3 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 4091597 = 1534349) B1534349
theorem B5107427 : Blo 1512953 5107427 := bstep (se 1 (by rfl) ⟨3830570, by rfl⟩ : syracuseStep 5107427 = 7661141) B7661141
theorem B5746403 : Blo 1512953 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B8744689 : Blo 1512953 8744689 := bstep (se 2 (by rfl) ⟨3279258, by rfl⟩ : syracuseStep 8744689 = 6558517) B6558517
theorem B7663409 : Blo 1512953 7663409 := bstep (se 2 (by rfl) ⟨2873778, by rfl⟩ : syracuseStep 7663409 = 5747557) B5747557
theorem B5533517 : Blo 1512953 5533517 := bstep (se 3 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 5533517 = 2075069) B2075069
theorem B9703309 : Blo 1512953 9703309 := bstep (se 3 (by rfl) ⟨1819370, by rfl⟩ : syracuseStep 9703309 = 3638741) B3638741
theorem B4313027 : Blo 1512953 4313027 := bstep (se 1 (by rfl) ⟨3234770, by rfl⟩ : syracuseStep 4313027 = 6469541) B6469541
theorem B5107697 : Blo 1512953 5107697 := bstep (se 2 (by rfl) ⟨1915386, by rfl⟩ : syracuseStep 5107697 = 3830773) B3830773
theorem B8622065 : Blo 1512953 8622065 := bstep (se 2 (by rfl) ⟨3233274, by rfl⟩ : syracuseStep 8622065 = 6466549) B6466549
theorem B8409251 : Blo 1512953 8409251 := bstep (se 1 (by rfl) ⟨6306938, by rfl⟩ : syracuseStep 8409251 = 12613877) B12613877
theorem B3068113 : Blo 1512953 3068113 := bstep (se 2 (by rfl) ⟨1150542, by rfl⟩ : syracuseStep 3068113 = 2301085) B2301085
theorem B4313357 : Blo 1512953 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B4149571 : Blo 1512953 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B2765137 : Blo 1512953 2765137 := bstep (se 2 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 2765137 = 2073853) B2073853
theorem B4313425 : Blo 1512953 4313425 := bstep (se 2 (by rfl) ⟨1617534, by rfl⟩ : syracuseStep 4313425 = 3235069) B3235069
theorem B5747057 : Blo 1512953 5747057 := bstep (se 2 (by rfl) ⟨2155146, by rfl⟩ : syracuseStep 5747057 = 4310293) B4310293
theorem B3404177 : Blo 1512953 3404177 := bstep (se 2 (by rfl) ⟨1276566, by rfl⟩ : syracuseStep 3404177 = 2553133) B2553133
theorem B3404195 : Blo 1512953 3404195 := bstep (se 1 (by rfl) ⟨2553146, by rfl⟩ : syracuseStep 3404195 = 5106293) B5106293
theorem B17469893 : Blo 1512953 17469893 := bstep (se 4 (by rfl) ⟨1637802, by rfl⟩ : syracuseStep 17469893 = 3275605) B3275605
theorem B25850339 : Blo 1512953 25850339 := bstep (se 1 (by rfl) ⟨19387754, by rfl⟩ : syracuseStep 25850339 = 38775509) B38775509
theorem B18403811 : Blo 1512953 18403811 := bstep (se 1 (by rfl) ⟨13802858, by rfl⟩ : syracuseStep 18403811 = 27605717) B27605717
theorem B5108237 : Blo 1512953 5108237 := bstep (se 3 (by rfl) ⟨957794, by rfl⟩ : syracuseStep 5108237 = 1915589) B1915589
theorem B5108291 : Blo 1512953 5108291 := bstep (se 1 (by rfl) ⟨3831218, by rfl⟩ : syracuseStep 5108291 = 7662437) B7662437
theorem B4313699 : Blo 1512953 4313699 := bstep (se 1 (by rfl) ⟨3235274, by rfl⟩ : syracuseStep 4313699 = 6470549) B6470549
theorem B3404465 : Blo 1512953 3404465 := bstep (se 2 (by rfl) ⟨1276674, by rfl⟩ : syracuseStep 3404465 = 2553349) B2553349
theorem B3830449 : Blo 1512953 3830449 := bstep (se 2 (by rfl) ⟨1436418, by rfl⟩ : syracuseStep 3830449 = 2872837) B2872837
theorem B3404483 : Blo 1512953 3404483 := bstep (se 1 (by rfl) ⟨2553362, by rfl⟩ : syracuseStep 3404483 = 5106725) B5106725
theorem B8295173 : Blo 1512953 8295173 := bstep (se 4 (by rfl) ⟨777672, by rfl⟩ : syracuseStep 8295173 = 1555345) B1555345
theorem B5108561 : Blo 1512953 5108561 := bstep (se 2 (by rfl) ⟨1915710, by rfl⟩ : syracuseStep 5108561 = 3831421) B3831421
theorem B3830723 : Blo 1512953 3830723 := bstep (se 1 (by rfl) ⟨2873042, by rfl⟩ : syracuseStep 3830723 = 5746085) B5746085
theorem B3404753 : Blo 1512953 3404753 := bstep (se 2 (by rfl) ⟨1276782, by rfl⟩ : syracuseStep 3404753 = 2553565) B2553565
theorem B3404771 : Blo 1512953 3404771 := bstep (se 1 (by rfl) ⟨2553578, by rfl⟩ : syracuseStep 3404771 = 5107157) B5107157
theorem B3830915 : Blo 1512953 3830915 := bstep (se 1 (by rfl) ⟨2873186, by rfl⟩ : syracuseStep 3830915 = 5746373) B5746373
theorem B2364547 : Blo 1512953 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B6141091 : Blo 1512953 6141091 := bstep (se 1 (by rfl) ⟨4605818, by rfl⟩ : syracuseStep 6141091 = 9211637) B9211637
theorem B2766001 : Blo 1512953 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B7664867 : Blo 1512953 7664867 := bstep (se 1 (by rfl) ⟨5748650, by rfl⟩ : syracuseStep 7664867 = 11497301) B11497301
theorem B3405041 : Blo 1512953 3405041 := bstep (se 2 (by rfl) ⟨1276890, by rfl⟩ : syracuseStep 3405041 = 2553781) B2553781
theorem B2872579 : Blo 1512953 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B3405059 : Blo 1512953 3405059 := bstep (se 1 (by rfl) ⟨2553794, by rfl⟩ : syracuseStep 3405059 = 5107589) B5107589
theorem B2553187 : Blo 1512953 2553187 := bstep (se 1 (by rfl) ⟨1914890, by rfl⟩ : syracuseStep 2553187 = 3829781) B3829781
theorem B5109101 : Blo 1512953 5109101 := bstep (se 3 (by rfl) ⟨957956, by rfl⟩ : syracuseStep 5109101 = 1915913) B1915913
theorem B2872739 : Blo 1512953 2872739 := bstep (se 1 (by rfl) ⟨2154554, by rfl⟩ : syracuseStep 2872739 = 4309109) B4309109
theorem B5109155 : Blo 1512953 5109155 := bstep (se 1 (by rfl) ⟨3831866, by rfl⟩ : syracuseStep 5109155 = 7663733) B7663733
theorem B8623523 : Blo 1512953 8623523 := bstep (se 1 (by rfl) ⟨6467642, by rfl⟩ : syracuseStep 8623523 = 12935285) B12935285
theorem B2184673 : Blo 1512953 2184673 := bstep (se 2 (by rfl) ⟨819252, by rfl⟩ : syracuseStep 2184673 = 1638505) B1638505
theorem B4093411 : Blo 1512953 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B2553329 : Blo 1512953 2553329 := bstep (se 2 (by rfl) ⟨957498, by rfl⟩ : syracuseStep 2553329 = 1914997) B1914997
theorem B1512963 : Blo 1512953 1512963 := bstep (se 1 (by rfl) ⟨1134722, by rfl⟩ : syracuseStep 1512963 = 2269445) B2269445
theorem B12932621 : Blo 1512953 12932621 := bstep (se 3 (by rfl) ⟨2424866, by rfl⟩ : syracuseStep 12932621 = 4849733) B4849733
theorem B3405329 : Blo 1512953 3405329 := bstep (se 2 (by rfl) ⟨1276998, by rfl⟩ : syracuseStep 3405329 = 2553997) B2553997
theorem B1512979 : Blo 1512953 1512979 := bstep (se 1 (by rfl) ⟨1134734, by rfl⟩ : syracuseStep 1512979 = 2269469) B2269469
theorem B1512995 : Blo 1512953 1512995 := bstep (se 1 (by rfl) ⟨1134746, by rfl⟩ : syracuseStep 1512995 = 2269493) B2269493
theorem B3405347 : Blo 1512953 3405347 := bstep (se 1 (by rfl) ⟨2554010, by rfl⟩ : syracuseStep 3405347 = 5108021) B5108021
theorem B1513011 : Blo 1512953 1513011 := bstep (se 1 (by rfl) ⟨1134758, by rfl⟩ : syracuseStep 1513011 = 2269517) B2269517
theorem B1513027 : Blo 1512953 1513027 := bstep (se 1 (by rfl) ⟨1134770, by rfl⟩ : syracuseStep 1513027 = 2269541) B2269541
theorem B1513043 : Blo 1512953 1513043 := bstep (se 1 (by rfl) ⟨1134782, by rfl⟩ : syracuseStep 1513043 = 2269565) B2269565
theorem B2184787 : Blo 1512953 2184787 := bstep (se 1 (by rfl) ⟨1638590, by rfl⟩ : syracuseStep 2184787 = 3277181) B3277181
theorem B1513059 : Blo 1512953 1513059 := bstep (se 1 (by rfl) ⟨1134794, by rfl⟩ : syracuseStep 1513059 = 2269589) B2269589
theorem B2553457 : Blo 1512953 2553457 := bstep (se 2 (by rfl) ⟨957546, by rfl⟩ : syracuseStep 2553457 = 1915093) B1915093
theorem B1513075 : Blo 1512953 1513075 := bstep (se 1 (by rfl) ⟨1134806, by rfl⟩ : syracuseStep 1513075 = 2269613) B2269613
theorem B1513091 : Blo 1512953 1513091 := bstep (se 1 (by rfl) ⟨1134818, by rfl⟩ : syracuseStep 1513091 = 2269637) B2269637
theorem B1513107 : Blo 1512953 1513107 := bstep (se 1 (by rfl) ⟨1134830, by rfl⟩ : syracuseStep 1513107 = 2269661) B2269661
theorem B2553491 : Blo 1512953 2553491 := bstep (se 1 (by rfl) ⟨1915118, by rfl⟩ : syracuseStep 2553491 = 3830237) B3830237
theorem B1513123 : Blo 1512953 1513123 := bstep (se 1 (by rfl) ⟨1134842, by rfl⟩ : syracuseStep 1513123 = 2269685) B2269685
theorem B6469283 : Blo 1512953 6469283 := bstep (se 1 (by rfl) ⟨4851962, by rfl⟩ : syracuseStep 6469283 = 9703925) B9703925
theorem B5109425 : Blo 1512953 5109425 := bstep (se 2 (by rfl) ⟨1916034, by rfl⟩ : syracuseStep 5109425 = 3832069) B3832069
theorem B1513139 : Blo 1512953 1513139 := bstep (se 1 (by rfl) ⟨1134854, by rfl⟩ : syracuseStep 1513139 = 2269709) B2269709
theorem B1513155 : Blo 1512953 1513155 := bstep (se 1 (by rfl) ⟨1134866, by rfl⟩ : syracuseStep 1513155 = 2269733) B2269733
theorem B1513171 : Blo 1512953 1513171 := bstep (se 1 (by rfl) ⟨1134878, by rfl⟩ : syracuseStep 1513171 = 2269757) B2269757
theorem B1513187 : Blo 1512953 1513187 := bstep (se 1 (by rfl) ⟨1134890, by rfl⟩ : syracuseStep 1513187 = 2269781) B2269781
theorem B1513203 : Blo 1512953 1513203 := bstep (se 1 (by rfl) ⟨1134902, by rfl⟩ : syracuseStep 1513203 = 2269805) B2269805
theorem B1513219 : Blo 1512953 1513219 := bstep (se 1 (by rfl) ⟨1134914, by rfl⟩ : syracuseStep 1513219 = 2269829) B2269829
theorem B1513235 : Blo 1512953 1513235 := bstep (se 1 (by rfl) ⟨1134926, by rfl⟩ : syracuseStep 1513235 = 2269853) B2269853
theorem B2553619 : Blo 1512953 2553619 := bstep (se 1 (by rfl) ⟨1915214, by rfl⟩ : syracuseStep 2553619 = 3830429) B3830429
theorem B1513251 : Blo 1512953 1513251 := bstep (se 1 (by rfl) ⟨1134938, by rfl⟩ : syracuseStep 1513251 = 2269877) B2269877
theorem B5748515 : Blo 1512953 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B3405617 : Blo 1512953 3405617 := bstep (se 2 (by rfl) ⟨1277106, by rfl⟩ : syracuseStep 3405617 = 2554213) B2554213
theorem B5748529 : Blo 1512953 5748529 := bstep (se 2 (by rfl) ⟨2155698, by rfl⟩ : syracuseStep 5748529 = 4311397) B4311397
theorem B1513267 : Blo 1512953 1513267 := bstep (se 1 (by rfl) ⟨1134950, by rfl⟩ : syracuseStep 1513267 = 2269901) B2269901
theorem B1513283 : Blo 1512953 1513283 := bstep (se 1 (by rfl) ⟨1134962, by rfl⟩ : syracuseStep 1513283 = 2269925) B2269925
theorem B3405635 : Blo 1512953 3405635 := bstep (se 1 (by rfl) ⟨2554226, by rfl⟩ : syracuseStep 3405635 = 5108453) B5108453
theorem B1513299 : Blo 1512953 1513299 := bstep (se 1 (by rfl) ⟨1134974, by rfl⟩ : syracuseStep 1513299 = 2269949) B2269949
theorem B1513315 : Blo 1512953 1513315 := bstep (se 1 (by rfl) ⟨1134986, by rfl⟩ : syracuseStep 1513315 = 2269973) B2269973
theorem B4372337 : Blo 1512953 4372337 := bstep (se 2 (by rfl) ⟨1639626, by rfl⟩ : syracuseStep 4372337 = 3279253) B3279253
theorem B1513331 : Blo 1512953 1513331 := bstep (se 1 (by rfl) ⟨1134998, by rfl⟩ : syracuseStep 1513331 = 2269997) B2269997
theorem B1513347 : Blo 1512953 1513347 := bstep (se 1 (by rfl) ⟨1135010, by rfl⟩ : syracuseStep 1513347 = 2270021) B2270021
theorem B1513363 : Blo 1512953 1513363 := bstep (se 1 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 1513363 = 2270045) B2270045
theorem B2553761 : Blo 1512953 2553761 := bstep (se 2 (by rfl) ⟨957660, by rfl⟩ : syracuseStep 2553761 = 1915321) B1915321
theorem B1513379 : Blo 1512953 1513379 := bstep (se 1 (by rfl) ⟨1135034, by rfl⟩ : syracuseStep 1513379 = 2270069) B2270069
theorem B1513395 : Blo 1512953 1513395 := bstep (se 1 (by rfl) ⟨1135046, by rfl⟩ : syracuseStep 1513395 = 2270093) B2270093
theorem B1513411 : Blo 1512953 1513411 := bstep (se 1 (by rfl) ⟨1135058, by rfl⟩ : syracuseStep 1513411 = 2270117) B2270117
theorem B24549317 : Blo 1512953 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B1914835 : Blo 1512953 1914835 := bstep (se 1 (by rfl) ⟨1436126, by rfl⟩ : syracuseStep 1914835 = 2872253) B2872253
theorem B1513427 : Blo 1512953 1513427 := bstep (se 1 (by rfl) ⟨1135070, by rfl⟩ : syracuseStep 1513427 = 2270141) B2270141
theorem B1513443 : Blo 1512953 1513443 := bstep (se 1 (by rfl) ⟨1135082, by rfl⟩ : syracuseStep 1513443 = 2270165) B2270165
theorem B1513459 : Blo 1512953 1513459 := bstep (se 1 (by rfl) ⟨1135094, by rfl⟩ : syracuseStep 1513459 = 2270189) B2270189
theorem B1513475 : Blo 1512953 1513475 := bstep (se 1 (by rfl) ⟨1135106, by rfl⟩ : syracuseStep 1513475 = 2270213) B2270213
theorem B7665677 : Blo 1512953 7665677 := bstep (se 3 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 7665677 = 2874629) B2874629
theorem B1513491 : Blo 1512953 1513491 := bstep (se 1 (by rfl) ⟨1135118, by rfl⟩ : syracuseStep 1513491 = 2270237) B2270237
theorem B2553889 : Blo 1512953 2553889 := bstep (se 2 (by rfl) ⟨957708, by rfl⟩ : syracuseStep 2553889 = 1915417) B1915417
theorem B1513507 : Blo 1512953 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B8181809 : Blo 1512953 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B3831857 : Blo 1512953 3831857 := bstep (se 2 (by rfl) ⟨1436946, by rfl⟩ : syracuseStep 3831857 = 2873893) B2873893
theorem B1914931 : Blo 1512953 1914931 := bstep (se 1 (by rfl) ⟨1436198, by rfl⟩ : syracuseStep 1914931 = 2872397) B2872397
theorem B1513523 : Blo 1512953 1513523 := bstep (se 1 (by rfl) ⟨1135142, by rfl⟩ : syracuseStep 1513523 = 2270285) B2270285
theorem B4847683 : Blo 1512953 4847683 := bstep (se 1 (by rfl) ⟨3635762, by rfl⟩ : syracuseStep 4847683 = 7271525) B7271525
theorem B2553923 : Blo 1512953 2553923 := bstep (se 1 (by rfl) ⟨1915442, by rfl⟩ : syracuseStep 2553923 = 3830885) B3830885
theorem B1513539 : Blo 1512953 1513539 := bstep (se 1 (by rfl) ⟨1135154, by rfl⟩ : syracuseStep 1513539 = 2270309) B2270309
theorem B9705541 : Blo 1512953 9705541 := bstep (se 4 (by rfl) ⟨909894, by rfl⟩ : syracuseStep 9705541 = 1819789) B1819789
theorem B3405905 : Blo 1512953 3405905 := bstep (se 2 (by rfl) ⟨1277214, by rfl⟩ : syracuseStep 3405905 = 2554429) B2554429
theorem B1513555 : Blo 1512953 1513555 := bstep (se 1 (by rfl) ⟨1135166, by rfl⟩ : syracuseStep 1513555 = 2270333) B2270333
theorem B1513571 : Blo 1512953 1513571 := bstep (se 1 (by rfl) ⟨1135178, by rfl⟩ : syracuseStep 1513571 = 2270357) B2270357
theorem B3405923 : Blo 1512953 3405923 := bstep (se 1 (by rfl) ⟨2554442, by rfl⟩ : syracuseStep 3405923 = 5108885) B5108885
theorem B3831907 : Blo 1512953 3831907 := bstep (se 1 (by rfl) ⟨2873930, by rfl⟩ : syracuseStep 3831907 = 5747861) B5747861
theorem B1513587 : Blo 1512953 1513587 := bstep (se 1 (by rfl) ⟨1135190, by rfl⟩ : syracuseStep 1513587 = 2270381) B2270381
theorem B1513603 : Blo 1512953 1513603 := bstep (se 1 (by rfl) ⟨1135202, by rfl⟩ : syracuseStep 1513603 = 2270405) B2270405
theorem B11491469 : Blo 1512953 11491469 := bstep (se 3 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 11491469 = 4309301) B4309301
theorem B1513619 : Blo 1512953 1513619 := bstep (se 1 (by rfl) ⟨1135214, by rfl⟩ : syracuseStep 1513619 = 2270429) B2270429
theorem B1513635 : Blo 1512953 1513635 := bstep (se 1 (by rfl) ⟨1135226, by rfl⟩ : syracuseStep 1513635 = 2270453) B2270453
theorem B1513651 : Blo 1512953 1513651 := bstep (se 1 (by rfl) ⟨1135238, by rfl⟩ : syracuseStep 1513651 = 2270477) B2270477
theorem B2554051 : Blo 1512953 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B1513667 : Blo 1512953 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B5109965 : Blo 1512953 5109965 := bstep (se 3 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 5109965 = 1916237) B1916237
theorem B1513683 : Blo 1512953 1513683 := bstep (se 1 (by rfl) ⟨1135262, by rfl⟩ : syracuseStep 1513683 = 2270525) B2270525
theorem B1513699 : Blo 1512953 1513699 := bstep (se 1 (by rfl) ⟨1135274, by rfl⟩ : syracuseStep 1513699 = 2270549) B2270549
theorem B3234019 : Blo 1512953 3234019 := bstep (se 1 (by rfl) ⟨2425514, by rfl⟩ : syracuseStep 3234019 = 4851029) B4851029
theorem B3832049 : Blo 1512953 3832049 := bstep (se 2 (by rfl) ⟨1437018, by rfl⟩ : syracuseStep 3832049 = 2874037) B2874037
theorem B1513715 : Blo 1512953 1513715 := bstep (se 1 (by rfl) ⟨1135286, by rfl⟩ : syracuseStep 1513715 = 2270573) B2270573
theorem B1702147 : Blo 1512953 1702147 := bstep (se 1 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 1702147 = 2553221) B2553221
theorem B1513731 : Blo 1512953 1513731 := bstep (se 1 (by rfl) ⟨1135298, by rfl⟩ : syracuseStep 1513731 = 2270597) B2270597
theorem B5110019 : Blo 1512953 5110019 := bstep (se 1 (by rfl) ⟨3832514, by rfl⟩ : syracuseStep 5110019 = 7665029) B7665029
theorem B10352909 : Blo 1512953 10352909 := bstep (se 3 (by rfl) ⟨1941170, by rfl⟩ : syracuseStep 10352909 = 3882341) B3882341
theorem B1513747 : Blo 1512953 1513747 := bstep (se 1 (by rfl) ⟨1135310, by rfl⟩ : syracuseStep 1513747 = 2270621) B2270621
theorem B1513763 : Blo 1512953 1513763 := bstep (se 1 (by rfl) ⟨1135322, by rfl⟩ : syracuseStep 1513763 = 2270645) B2270645
theorem B1513779 : Blo 1512953 1513779 := bstep (se 1 (by rfl) ⟨1135334, by rfl⟩ : syracuseStep 1513779 = 2270669) B2270669
theorem B1513795 : Blo 1512953 1513795 := bstep (se 1 (by rfl) ⟨1135346, by rfl⟩ : syracuseStep 1513795 = 2270693) B2270693
theorem B2554193 : Blo 1512953 2554193 := bstep (se 2 (by rfl) ⟨957822, by rfl⟩ : syracuseStep 2554193 = 1915645) B1915645
theorem B1513811 : Blo 1512953 1513811 := bstep (se 1 (by rfl) ⟨1135358, by rfl⟩ : syracuseStep 1513811 = 2270717) B2270717
theorem B1513827 : Blo 1512953 1513827 := bstep (se 1 (by rfl) ⟨1135370, by rfl⟩ : syracuseStep 1513827 = 2270741) B2270741
theorem B1513843 : Blo 1512953 1513843 := bstep (se 1 (by rfl) ⟨1135382, by rfl⟩ : syracuseStep 1513843 = 2270765) B2270765
theorem B3406193 : Blo 1512953 3406193 := bstep (se 2 (by rfl) ⟨1277322, by rfl⟩ : syracuseStep 3406193 = 2554645) B2554645
theorem B1513859 : Blo 1512953 1513859 := bstep (se 1 (by rfl) ⟨1135394, by rfl⟩ : syracuseStep 1513859 = 2270789) B2270789
theorem B3406211 : Blo 1512953 3406211 := bstep (se 1 (by rfl) ⟨2554658, by rfl⟩ : syracuseStep 3406211 = 5109317) B5109317
theorem B1702291 : Blo 1512953 1702291 := bstep (se 1 (by rfl) ⟨1276718, by rfl⟩ : syracuseStep 1702291 = 2553437) B2553437
theorem B1513875 : Blo 1512953 1513875 := bstep (se 1 (by rfl) ⟨1135406, by rfl⟩ : syracuseStep 1513875 = 2270813) B2270813
theorem B1513891 : Blo 1512953 1513891 := bstep (se 1 (by rfl) ⟨1135418, by rfl⟩ : syracuseStep 1513891 = 2270837) B2270837
theorem B1513907 : Blo 1512953 1513907 := bstep (se 1 (by rfl) ⟨1135430, by rfl⟩ : syracuseStep 1513907 = 2270861) B2270861
theorem B1513923 : Blo 1512953 1513923 := bstep (se 1 (by rfl) ⟨1135442, by rfl⟩ : syracuseStep 1513923 = 2270885) B2270885
theorem B2554321 : Blo 1512953 2554321 := bstep (se 2 (by rfl) ⟨957870, by rfl⟩ : syracuseStep 2554321 = 1915741) B1915741
theorem B2873809 : Blo 1512953 2873809 := bstep (se 2 (by rfl) ⟨1077678, by rfl⟩ : syracuseStep 2873809 = 2155357) B2155357
theorem B1513939 : Blo 1512953 1513939 := bstep (se 1 (by rfl) ⟨1135454, by rfl⟩ : syracuseStep 1513939 = 2270909) B2270909
theorem B1513955 : Blo 1512953 1513955 := bstep (se 1 (by rfl) ⟨1135466, by rfl⟩ : syracuseStep 1513955 = 2270933) B2270933
theorem B2554355 : Blo 1512953 2554355 := bstep (se 1 (by rfl) ⟨1915766, by rfl⟩ : syracuseStep 2554355 = 3831533) B3831533
theorem B1513971 : Blo 1512953 1513971 := bstep (se 1 (by rfl) ⟨1135478, by rfl⟩ : syracuseStep 1513971 = 2270957) B2270957
theorem B1513987 : Blo 1512953 1513987 := bstep (se 1 (by rfl) ⟨1135490, by rfl⟩ : syracuseStep 1513987 = 2270981) B2270981
theorem B5110289 : Blo 1512953 5110289 := bstep (se 2 (by rfl) ⟨1916358, by rfl⟩ : syracuseStep 5110289 = 3832717) B3832717
theorem B1514003 : Blo 1512953 1514003 := bstep (se 1 (by rfl) ⟨1135502, by rfl⟩ : syracuseStep 1514003 = 2271005) B2271005
theorem B1702435 : Blo 1512953 1702435 := bstep (se 1 (by rfl) ⟨1276826, by rfl⟩ : syracuseStep 1702435 = 2553653) B2553653
theorem B1915427 : Blo 1512953 1915427 := bstep (se 1 (by rfl) ⟨1436570, by rfl⟩ : syracuseStep 1915427 = 2873141) B2873141
theorem B1514019 : Blo 1512953 1514019 := bstep (se 1 (by rfl) ⟨1135514, by rfl⟩ : syracuseStep 1514019 = 2271029) B2271029
theorem B1514035 : Blo 1512953 1514035 := bstep (se 1 (by rfl) ⟨1135526, by rfl⟩ : syracuseStep 1514035 = 2271053) B2271053
theorem B1514051 : Blo 1512953 1514051 := bstep (se 1 (by rfl) ⟨1135538, by rfl⟩ : syracuseStep 1514051 = 2271077) B2271077
theorem B1514067 : Blo 1512953 1514067 := bstep (se 1 (by rfl) ⟨1135550, by rfl⟩ : syracuseStep 1514067 = 2271101) B2271101
theorem B1514083 : Blo 1512953 1514083 := bstep (se 1 (by rfl) ⟨1135562, by rfl⟩ : syracuseStep 1514083 = 2271125) B2271125
theorem B2554483 : Blo 1512953 2554483 := bstep (se 1 (by rfl) ⟨1915862, by rfl⟩ : syracuseStep 2554483 = 3831725) B3831725
theorem B1514099 : Blo 1512953 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B1514115 : Blo 1512953 1514115 := bstep (se 1 (by rfl) ⟨1135586, by rfl⟩ : syracuseStep 1514115 = 2271173) B2271173
theorem B3406481 : Blo 1512953 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B1514131 : Blo 1512953 1514131 := bstep (se 1 (by rfl) ⟨1135598, by rfl⟩ : syracuseStep 1514131 = 2271197) B2271197
theorem B3406499 : Blo 1512953 3406499 := bstep (se 1 (by rfl) ⟨2554874, by rfl⟩ : syracuseStep 3406499 = 5109749) B5109749
theorem B1514147 : Blo 1512953 1514147 := bstep (se 1 (by rfl) ⟨1135610, by rfl⟩ : syracuseStep 1514147 = 2271221) B2271221
theorem B1702579 : Blo 1512953 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B1514163 : Blo 1512953 1514163 := bstep (se 1 (by rfl) ⟨1135622, by rfl⟩ : syracuseStep 1514163 = 2271245) B2271245
theorem B19405493 : Blo 1512953 19405493 := bstep (se 5 (by rfl) ⟨909632, by rfl⟩ : syracuseStep 19405493 = 1819265) B1819265
theorem B1514179 : Blo 1512953 1514179 := bstep (se 1 (by rfl) ⟨1135634, by rfl⟩ : syracuseStep 1514179 = 2271269) B2271269
theorem B1514195 : Blo 1512953 1514195 := bstep (se 1 (by rfl) ⟨1135646, by rfl⟩ : syracuseStep 1514195 = 2271293) B2271293
theorem B2423521 : Blo 1512953 2423521 := bstep (se 2 (by rfl) ⟨908820, by rfl⟩ : syracuseStep 2423521 = 1817641) B1817641
theorem B1514211 : Blo 1512953 1514211 := bstep (se 1 (by rfl) ⟨1135658, by rfl⟩ : syracuseStep 1514211 = 2271317) B2271317
theorem B1514227 : Blo 1512953 1514227 := bstep (se 1 (by rfl) ⟨1135670, by rfl⟩ : syracuseStep 1514227 = 2271341) B2271341
theorem B2554625 : Blo 1512953 2554625 := bstep (se 2 (by rfl) ⟨957984, by rfl⟩ : syracuseStep 2554625 = 1915969) B1915969
theorem B1514243 : Blo 1512953 1514243 := bstep (se 1 (by rfl) ⟨1135682, by rfl⟩ : syracuseStep 1514243 = 2271365) B2271365
theorem B1514259 : Blo 1512953 1514259 := bstep (se 1 (by rfl) ⟨1135694, by rfl⟩ : syracuseStep 1514259 = 2271389) B2271389
theorem B6552355 : Blo 1512953 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B1514275 : Blo 1512953 1514275 := bstep (se 1 (by rfl) ⟨1135706, by rfl⟩ : syracuseStep 1514275 = 2271413) B2271413
theorem B5454641 : Blo 1512953 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B1514291 : Blo 1512953 1514291 := bstep (se 1 (by rfl) ⟨1135718, by rfl⟩ : syracuseStep 1514291 = 2271437) B2271437
theorem B24558389 : Blo 1512953 24558389 := bstep (se 5 (by rfl) ⟨1151174, by rfl⟩ : syracuseStep 24558389 = 2302349) B2302349
theorem B1702723 : Blo 1512953 1702723 := bstep (se 1 (by rfl) ⟨1277042, by rfl⟩ : syracuseStep 1702723 = 2554085) B2554085
theorem B1514307 : Blo 1512953 1514307 := bstep (se 1 (by rfl) ⟨1135730, by rfl⟩ : syracuseStep 1514307 = 2271461) B2271461
theorem B1514323 : Blo 1512953 1514323 := bstep (se 1 (by rfl) ⟨1135742, by rfl⟩ : syracuseStep 1514323 = 2271485) B2271485
theorem B1514339 : Blo 1512953 1514339 := bstep (se 1 (by rfl) ⟨1135754, by rfl⟩ : syracuseStep 1514339 = 2271509) B2271509
theorem B6470513 : Blo 1512953 6470513 := bstep (se 2 (by rfl) ⟨2426442, by rfl⟩ : syracuseStep 6470513 = 4852885) B4852885
theorem B1514355 : Blo 1512953 1514355 := bstep (se 1 (by rfl) ⟨1135766, by rfl⟩ : syracuseStep 1514355 = 2271533) B2271533
theorem B2554753 : Blo 1512953 2554753 := bstep (se 2 (by rfl) ⟨958032, by rfl⟩ : syracuseStep 2554753 = 1916065) B1916065
theorem B1514371 : Blo 1512953 1514371 := bstep (se 1 (by rfl) ⟨1135778, by rfl⟩ : syracuseStep 1514371 = 2271557) B2271557
theorem B1514387 : Blo 1512953 1514387 := bstep (se 1 (by rfl) ⟨1135790, by rfl⟩ : syracuseStep 1514387 = 2271581) B2271581
theorem B5454755 : Blo 1512953 5454755 := bstep (se 1 (by rfl) ⟨4091066, by rfl⟩ : syracuseStep 5454755 = 8182133) B8182133
theorem B2554787 : Blo 1512953 2554787 := bstep (se 1 (by rfl) ⟨1916090, by rfl⟩ : syracuseStep 2554787 = 3832181) B3832181
theorem B1514403 : Blo 1512953 1514403 := bstep (se 1 (by rfl) ⟨1135802, by rfl⟩ : syracuseStep 1514403 = 2271605) B2271605
theorem B3406769 : Blo 1512953 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B1514419 : Blo 1512953 1514419 := bstep (se 1 (by rfl) ⟨1135814, by rfl⟩ : syracuseStep 1514419 = 2271629) B2271629
theorem B3406787 : Blo 1512953 3406787 := bstep (se 1 (by rfl) ⟨2555090, by rfl⟩ : syracuseStep 3406787 = 5110181) B5110181
theorem B1514435 : Blo 1512953 1514435 := bstep (se 1 (by rfl) ⟨1135826, by rfl⟩ : syracuseStep 1514435 = 2271653) B2271653
theorem B1702867 : Blo 1512953 1702867 := bstep (se 1 (by rfl) ⟨1277150, by rfl⟩ : syracuseStep 1702867 = 2554301) B2554301
theorem B1514451 : Blo 1512953 1514451 := bstep (se 1 (by rfl) ⟨1135838, by rfl⟩ : syracuseStep 1514451 = 2271677) B2271677
theorem B2423777 : Blo 1512953 2423777 := bstep (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) B1817833
theorem B1514467 : Blo 1512953 1514467 := bstep (se 1 (by rfl) ⟨1135850, by rfl⟩ : syracuseStep 1514467 = 2271701) B2271701
theorem B1514483 : Blo 1512953 1514483 := bstep (se 1 (by rfl) ⟨1135862, by rfl⟩ : syracuseStep 1514483 = 2271725) B2271725
theorem B1514499 : Blo 1512953 1514499 := bstep (se 1 (by rfl) ⟨1135874, by rfl⟩ : syracuseStep 1514499 = 2271749) B2271749
theorem B1514515 : Blo 1512953 1514515 := bstep (se 1 (by rfl) ⟨1135886, by rfl⟩ : syracuseStep 1514515 = 2271773) B2271773
theorem B2554915 : Blo 1512953 2554915 := bstep (se 1 (by rfl) ⟨1916186, by rfl⟩ : syracuseStep 2554915 = 3832373) B3832373
theorem B1514531 : Blo 1512953 1514531 := bstep (se 1 (by rfl) ⟨1135898, by rfl⟩ : syracuseStep 1514531 = 2271797) B2271797
theorem B5110829 : Blo 1512953 5110829 := bstep (se 3 (by rfl) ⟨958280, by rfl⟩ : syracuseStep 5110829 = 1916561) B1916561
theorem B1514547 : Blo 1512953 1514547 := bstep (se 1 (by rfl) ⟨1135910, by rfl⟩ : syracuseStep 1514547 = 2271821) B2271821
theorem B1514563 : Blo 1512953 1514563 := bstep (se 1 (by rfl) ⟨1135922, by rfl⟩ : syracuseStep 1514563 = 2271845) B2271845
theorem B1514579 : Blo 1512953 1514579 := bstep (se 1 (by rfl) ⟨1135934, by rfl⟩ : syracuseStep 1514579 = 2271869) B2271869
theorem B1703011 : Blo 1512953 1703011 := bstep (se 1 (by rfl) ⟨1277258, by rfl⟩ : syracuseStep 1703011 = 2554517) B2554517
theorem B5110883 : Blo 1512953 5110883 := bstep (se 1 (by rfl) ⟨3833162, by rfl⟩ : syracuseStep 5110883 = 7666325) B7666325
theorem B1514595 : Blo 1512953 1514595 := bstep (se 1 (by rfl) ⟨1135946, by rfl⟩ : syracuseStep 1514595 = 2271893) B2271893
theorem B1514611 : Blo 1512953 1514611 := bstep (se 1 (by rfl) ⟨1135958, by rfl⟩ : syracuseStep 1514611 = 2271917) B2271917
theorem B1514627 : Blo 1512953 1514627 := bstep (se 1 (by rfl) ⟨1135970, by rfl⟩ : syracuseStep 1514627 = 2271941) B2271941
theorem B4848785 : Blo 1512953 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B1514643 : Blo 1512953 1514643 := bstep (se 1 (by rfl) ⟨1135982, by rfl⟩ : syracuseStep 1514643 = 2271965) B2271965
theorem B1514659 : Blo 1512953 1514659 := bstep (se 1 (by rfl) ⟨1135994, by rfl⟩ : syracuseStep 1514659 = 2271989) B2271989
theorem B2555057 : Blo 1512953 2555057 := bstep (se 2 (by rfl) ⟨958146, by rfl⟩ : syracuseStep 2555057 = 1916293) B1916293
theorem B1514675 : Blo 1512953 1514675 := bstep (se 1 (by rfl) ⟨1136006, by rfl⟩ : syracuseStep 1514675 = 2272013) B2272013
theorem B1514691 : Blo 1512953 1514691 := bstep (se 1 (by rfl) ⟨1136018, by rfl⟩ : syracuseStep 1514691 = 2272037) B2272037
theorem B3407057 : Blo 1512953 3407057 := bstep (se 2 (by rfl) ⟨1277646, by rfl⟩ : syracuseStep 3407057 = 2555293) B2555293
theorem B3833041 : Blo 1512953 3833041 := bstep (se 2 (by rfl) ⟨1437390, by rfl⟩ : syracuseStep 3833041 = 2874781) B2874781
theorem B1514707 : Blo 1512953 1514707 := bstep (se 1 (by rfl) ⟨1136030, by rfl⟩ : syracuseStep 1514707 = 2272061) B2272061
theorem B2186449 : Blo 1512953 2186449 := bstep (se 2 (by rfl) ⟨819918, by rfl⟩ : syracuseStep 2186449 = 1639837) B1639837
theorem B1916131 : Blo 1512953 1916131 := bstep (se 1 (by rfl) ⟨1437098, by rfl⟩ : syracuseStep 1916131 = 2874197) B2874197
theorem B3407075 : Blo 1512953 3407075 := bstep (se 1 (by rfl) ⟨2555306, by rfl⟩ : syracuseStep 3407075 = 5110613) B5110613
theorem B5749987 : Blo 1512953 5749987 := bstep (se 1 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 5749987 = 8624981) B8624981
theorem B1514723 : Blo 1512953 1514723 := bstep (se 1 (by rfl) ⟨1136042, by rfl⟩ : syracuseStep 1514723 = 2272085) B2272085
theorem B1703155 : Blo 1512953 1703155 := bstep (se 1 (by rfl) ⟨1277366, by rfl⟩ : syracuseStep 1703155 = 2554733) B2554733
theorem B1514739 : Blo 1512953 1514739 := bstep (se 1 (by rfl) ⟨1136054, by rfl⟩ : syracuseStep 1514739 = 2272109) B2272109
theorem B1514755 : Blo 1512953 1514755 := bstep (se 1 (by rfl) ⟨1136066, by rfl⟩ : syracuseStep 1514755 = 2272133) B2272133
theorem B4848913 : Blo 1512953 4848913 := bstep (se 2 (by rfl) ⟨1818342, by rfl⟩ : syracuseStep 4848913 = 3636685) B3636685
theorem B1514771 : Blo 1512953 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B1514787 : Blo 1512953 1514787 := bstep (se 1 (by rfl) ⟨1136090, by rfl⟩ : syracuseStep 1514787 = 2272181) B2272181
theorem B2555185 : Blo 1512953 2555185 := bstep (se 2 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 2555185 = 1916389) B1916389
theorem B1514803 : Blo 1512953 1514803 := bstep (se 1 (by rfl) ⟨1136102, by rfl⟩ : syracuseStep 1514803 = 2272205) B2272205
theorem B1916227 : Blo 1512953 1916227 := bstep (se 1 (by rfl) ⟨1437170, by rfl⟩ : syracuseStep 1916227 = 2874341) B2874341
theorem B1514819 : Blo 1512953 1514819 := bstep (se 1 (by rfl) ⟨1136114, by rfl⟩ : syracuseStep 1514819 = 2272229) B2272229
theorem B2555219 : Blo 1512953 2555219 := bstep (se 1 (by rfl) ⟨1916414, by rfl⟩ : syracuseStep 2555219 = 3832829) B3832829
theorem B1514835 : Blo 1512953 1514835 := bstep (se 1 (by rfl) ⟨1136126, by rfl⟩ : syracuseStep 1514835 = 2272253) B2272253
theorem B1514851 : Blo 1512953 1514851 := bstep (se 1 (by rfl) ⟨1136138, by rfl⟩ : syracuseStep 1514851 = 2272277) B2272277
theorem B5111153 : Blo 1512953 5111153 := bstep (se 2 (by rfl) ⟨1916682, by rfl⟩ : syracuseStep 5111153 = 3833365) B3833365
theorem B10919281 : Blo 1512953 10919281 := bstep (se 2 (by rfl) ⟨4094730, by rfl⟩ : syracuseStep 10919281 = 8189461) B8189461
theorem B1514867 : Blo 1512953 1514867 := bstep (se 1 (by rfl) ⟨1136150, by rfl⟩ : syracuseStep 1514867 = 2272301) B2272301
theorem B1703299 : Blo 1512953 1703299 := bstep (se 1 (by rfl) ⟨1277474, by rfl⟩ : syracuseStep 1703299 = 2554949) B2554949
theorem B1514883 : Blo 1512953 1514883 := bstep (se 1 (by rfl) ⟨1136162, by rfl⟩ : syracuseStep 1514883 = 2272325) B2272325
theorem B1514899 : Blo 1512953 1514899 := bstep (se 1 (by rfl) ⟨1136174, by rfl⟩ : syracuseStep 1514899 = 2272349) B2272349
theorem B1514915 : Blo 1512953 1514915 := bstep (se 1 (by rfl) ⟨1136186, by rfl⟩ : syracuseStep 1514915 = 2272373) B2272373
theorem B1514931 : Blo 1512953 1514931 := bstep (se 1 (by rfl) ⟨1136198, by rfl⟩ : syracuseStep 1514931 = 2272397) B2272397
theorem B1514947 : Blo 1512953 1514947 := bstep (se 1 (by rfl) ⟨1136210, by rfl⟩ : syracuseStep 1514947 = 2272421) B2272421
theorem B2047441 : Blo 1512953 2047441 := bstep (se 2 (by rfl) ⟨767790, by rfl⟩ : syracuseStep 2047441 = 1535581) B1535581
theorem B2555347 : Blo 1512953 2555347 := bstep (se 1 (by rfl) ⟨1916510, by rfl⟩ : syracuseStep 2555347 = 3833021) B3833021
theorem B3882467 : Blo 1512953 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B3833315 : Blo 1512953 3833315 := bstep (se 1 (by rfl) ⟨2874986, by rfl⟩ : syracuseStep 3833315 = 5749973) B5749973
theorem B2301425 : Blo 1512953 2301425 := bstep (se 2 (by rfl) ⟨863034, by rfl⟩ : syracuseStep 2301425 = 1726069) B1726069
theorem B2874865 : Blo 1512953 2874865 := bstep (se 2 (by rfl) ⟨1078074, by rfl⟩ : syracuseStep 2874865 = 2156149) B2156149
theorem B3407345 : Blo 1512953 3407345 := bstep (se 2 (by rfl) ⟨1277754, by rfl⟩ : syracuseStep 3407345 = 2555509) B2555509
theorem B3407363 : Blo 1512953 3407363 := bstep (se 1 (by rfl) ⟨2555522, by rfl⟩ : syracuseStep 3407363 = 5111045) B5111045
theorem B1703443 : Blo 1512953 1703443 := bstep (se 1 (by rfl) ⟨1277582, by rfl⟩ : syracuseStep 1703443 = 2555165) B2555165
theorem B2555489 : Blo 1512953 2555489 := bstep (se 2 (by rfl) ⟨958308, by rfl⟩ : syracuseStep 2555489 = 1916617) B1916617
theorem B6553187 : Blo 1512953 6553187 := bstep (se 1 (by rfl) ⟨4914890, by rfl⟩ : syracuseStep 6553187 = 9829781) B9829781
theorem B7274083 : Blo 1512953 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B2301571 : Blo 1512953 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B2334353 : Blo 1512953 2334353 := bstep (se 2 (by rfl) ⟨875382, by rfl⟩ : syracuseStep 2334353 = 1750765) B1750765
theorem B1703587 : Blo 1512953 1703587 := bstep (se 1 (by rfl) ⟨1277690, by rfl⟩ : syracuseStep 1703587 = 2555381) B2555381
theorem B3833507 : Blo 1512953 3833507 := bstep (se 1 (by rfl) ⟨2875130, by rfl⟩ : syracuseStep 3833507 = 5750261) B5750261
theorem B4308653 : Blo 1512953 4308653 := bstep (se 3 (by rfl) ⟨807872, by rfl⟩ : syracuseStep 4308653 = 1615745) B1615745
theorem B2555617 : Blo 1512953 2555617 := bstep (se 2 (by rfl) ⟨958356, by rfl⟩ : syracuseStep 2555617 = 1916713) B1916713
theorem B1818371 : Blo 1512953 1818371 := bstep (se 1 (by rfl) ⟨1363778, by rfl⟩ : syracuseStep 1818371 = 2727557) B2727557
theorem B2555651 : Blo 1512953 2555651 := bstep (se 1 (by rfl) ⟨1916738, by rfl⟩ : syracuseStep 2555651 = 3833477) B3833477
theorem B3407633 : Blo 1512953 3407633 := bstep (se 2 (by rfl) ⟨1277862, by rfl⟩ : syracuseStep 3407633 = 2555725) B2555725
theorem B3407651 : Blo 1512953 3407651 := bstep (se 1 (by rfl) ⟨2555738, by rfl⟩ : syracuseStep 3407651 = 5111477) B5111477
theorem B1703731 : Blo 1512953 1703731 := bstep (se 1 (by rfl) ⟨1277798, by rfl⟩ : syracuseStep 1703731 = 2555597) B2555597
theorem B1916723 : Blo 1512953 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B4308835 : Blo 1512953 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B12935011 : Blo 1512953 12935011 := bstep (se 1 (by rfl) ⟨9701258, by rfl⟩ : syracuseStep 12935011 = 19402517) B19402517
theorem B2555779 : Blo 1512953 2555779 := bstep (se 1 (by rfl) ⟨1916834, by rfl⟩ : syracuseStep 2555779 = 3833669) B3833669
theorem B2875267 : Blo 1512953 2875267 := bstep (se 1 (by rfl) ⟨2156450, by rfl⟩ : syracuseStep 2875267 = 4312901) B4312901
theorem B5111693 : Blo 1512953 5111693 := bstep (se 3 (by rfl) ⟨958442, by rfl⟩ : syracuseStep 5111693 = 1916885) B1916885
theorem B2875313 : Blo 1512953 2875313 := bstep (se 2 (by rfl) ⟨1078242, by rfl⟩ : syracuseStep 2875313 = 2156485) B2156485
theorem B1703875 : Blo 1512953 1703875 := bstep (se 1 (by rfl) ⟨1277906, by rfl⟩ : syracuseStep 1703875 = 2555813) B2555813
theorem B5111747 : Blo 1512953 5111747 := bstep (se 1 (by rfl) ⟨3833810, by rfl⟩ : syracuseStep 5111747 = 7667621) B7667621
theorem B1703947 : Blo 1512953 1703947 := bstep (se 1 (by rfl) ⟨1277960, by rfl⟩ : syracuseStep 1703947 = 2555921) B2555921
theorem B6463577 : Blo 1512953 6463577 := bstep (se 2 (by rfl) ⟨2423841, by rfl⟩ : syracuseStep 6463577 = 4847683) B4847683
theorem B1704055 : Blo 1512953 1704055 := bstep (se 1 (by rfl) ⟨1278041, by rfl⟩ : syracuseStep 1704055 = 2556083) B2556083
theorem B3408011 : Blo 1512953 3408011 := bstep (se 1 (by rfl) ⟨2556008, by rfl⟩ : syracuseStep 3408011 = 5112017) B5112017
theorem B11059379 : Blo 1512953 11059379 := bstep (se 1 (by rfl) ⟨8294534, by rfl⟩ : syracuseStep 11059379 = 16589069) B16589069
theorem B2875571 : Blo 1512953 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B3408065 : Blo 1512953 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B2269451 : Blo 1512953 2269451 := bstep (se 1 (by rfl) ⟨1702088, by rfl⟩ : syracuseStep 2269451 = 3404177) B3404177
theorem B2269463 : Blo 1512953 2269463 := bstep (se 1 (by rfl) ⟨1702097, by rfl⟩ : syracuseStep 2269463 = 3404195) B3404195
theorem B1704235 : Blo 1512953 1704235 := bstep (se 1 (by rfl) ⟨1278176, by rfl⟩ : syracuseStep 1704235 = 2556353) B2556353
theorem B2269529 : Blo 1512953 2269529 := bstep (se 2 (by rfl) ⟨851073, by rfl⟩ : syracuseStep 2269529 = 1702147) B1702147
theorem B2556299 : Blo 1512953 2556299 := bstep (se 1 (by rfl) ⟨1917224, by rfl⟩ : syracuseStep 2556299 = 3834449) B3834449
theorem B2875799 : Blo 1512953 2875799 := bstep (se 1 (by rfl) ⟨2156849, by rfl⟩ : syracuseStep 2875799 = 4313699) B4313699
theorem B3408281 : Blo 1512953 3408281 := bstep (se 2 (by rfl) ⟨1278105, by rfl⟩ : syracuseStep 3408281 = 2556211) B2556211
theorem B3686849 : Blo 1512953 3686849 := bstep (se 2 (by rfl) ⟨1382568, by rfl⟩ : syracuseStep 3686849 = 2765137) B2765137
theorem B5751233 : Blo 1512953 5751233 := bstep (se 2 (by rfl) ⟨2156712, by rfl⟩ : syracuseStep 5751233 = 4313425) B4313425
theorem B2269643 : Blo 1512953 2269643 := bstep (se 1 (by rfl) ⟨1702232, by rfl⟩ : syracuseStep 2269643 = 3404465) B3404465
theorem B2269655 : Blo 1512953 2269655 := bstep (se 1 (by rfl) ⟨1702241, by rfl⟩ : syracuseStep 2269655 = 3404483) B3404483
theorem B18407897 : Blo 1512953 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B3408371 : Blo 1512953 3408371 := bstep (se 1 (by rfl) ⟨2556278, by rfl⟩ : syracuseStep 3408371 = 5112557) B5112557
theorem B5530115 : Blo 1512953 5530115 := bstep (se 1 (by rfl) ⟨4147586, by rfl⟩ : syracuseStep 5530115 = 8295173) B8295173
theorem B2556427 : Blo 1512953 2556427 := bstep (se 1 (by rfl) ⟨1917320, by rfl⟩ : syracuseStep 2556427 = 3834641) B3834641
theorem B3408407 : Blo 1512953 3408407 := bstep (se 1 (by rfl) ⟨2556305, by rfl⟩ : syracuseStep 3408407 = 5112611) B5112611
theorem B2269721 : Blo 1512953 2269721 := bstep (se 2 (by rfl) ⟨851145, by rfl⟩ : syracuseStep 2269721 = 1702291) B1702291
theorem B7668269 : Blo 1512953 7668269 := bstep (se 3 (by rfl) ⟨1437800, by rfl⟩ : syracuseStep 7668269 = 2875601) B2875601
theorem B5112395 : Blo 1512953 5112395 := bstep (se 1 (by rfl) ⟨3834296, by rfl⟩ : syracuseStep 5112395 = 7668593) B7668593
theorem B2269835 : Blo 1512953 2269835 := bstep (se 1 (by rfl) ⟨1702376, by rfl⟩ : syracuseStep 2269835 = 3404753) B3404753
theorem B2269847 : Blo 1512953 2269847 := bstep (se 1 (by rfl) ⟨1702385, by rfl⟩ : syracuseStep 2269847 = 3404771) B3404771
theorem B3408587 : Blo 1512953 3408587 := bstep (se 1 (by rfl) ⟨2556440, by rfl⟩ : syracuseStep 3408587 = 5112881) B5112881
theorem B2269913 : Blo 1512953 2269913 := bstep (se 2 (by rfl) ⟨851217, by rfl⟩ : syracuseStep 2269913 = 1702435) B1702435
theorem B3408641 : Blo 1512953 3408641 := bstep (se 2 (by rfl) ⟨1278240, by rfl⟩ : syracuseStep 3408641 = 2556481) B2556481
theorem B59007797 : Blo 1512953 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B2270027 : Blo 1512953 2270027 := bstep (se 1 (by rfl) ⟨1702520, by rfl⟩ : syracuseStep 2270027 = 3405041) B3405041
theorem B2270039 : Blo 1512953 2270039 := bstep (se 1 (by rfl) ⟨1702529, by rfl⟩ : syracuseStep 2270039 = 3405059) B3405059
theorem B5112665 : Blo 1512953 5112665 := bstep (se 2 (by rfl) ⟨1917249, by rfl⟩ : syracuseStep 5112665 = 3834499) B3834499
theorem B2270105 : Blo 1512953 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B4309939 : Blo 1512953 4309939 := bstep (se 1 (by rfl) ⟨3232454, by rfl⟩ : syracuseStep 4309939 = 6464909) B6464909
theorem B2270219 : Blo 1512953 2270219 := bstep (se 1 (by rfl) ⟨1702664, by rfl⟩ : syracuseStep 2270219 = 3405329) B3405329
theorem B16376849 : Blo 1512953 16376849 := bstep (se 2 (by rfl) ⟨6141318, by rfl⟩ : syracuseStep 16376849 = 12282637) B12282637
theorem B2270231 : Blo 1512953 2270231 := bstep (se 1 (by rfl) ⟨1702673, by rfl⟩ : syracuseStep 2270231 = 3405347) B3405347
theorem B2425879 : Blo 1512953 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B10495021 : Blo 1512953 10495021 := bstep (se 3 (by rfl) ⟨1967816, by rfl⟩ : syracuseStep 10495021 = 3935633) B3935633
theorem B2270297 : Blo 1512953 2270297 := bstep (se 2 (by rfl) ⟨851361, by rfl⟩ : syracuseStep 2270297 = 1702723) B1702723
theorem B4310167 : Blo 1512953 4310167 := bstep (se 1 (by rfl) ⟨3232625, by rfl⟩ : syracuseStep 4310167 = 6465251) B6465251
theorem B2270411 : Blo 1512953 2270411 := bstep (se 1 (by rfl) ⟨1702808, by rfl⟩ : syracuseStep 2270411 = 3405617) B3405617
theorem B2270423 : Blo 1512953 2270423 := bstep (se 1 (by rfl) ⟨1702817, by rfl⟩ : syracuseStep 2270423 = 3405635) B3405635
theorem B7660817 : Blo 1512953 7660817 := bstep (se 2 (by rfl) ⟨2872806, by rfl⟩ : syracuseStep 7660817 = 5745613) B5745613
theorem B2270489 : Blo 1512953 2270489 := bstep (se 2 (by rfl) ⟨851433, by rfl⟩ : syracuseStep 2270489 = 1702867) B1702867
theorem B7275869 : Blo 1512953 7275869 := bstep (se 3 (by rfl) ⟨1364225, by rfl⟩ : syracuseStep 7275869 = 2728451) B2728451
theorem B2270603 : Blo 1512953 2270603 := bstep (se 1 (by rfl) ⟨1702952, by rfl⟩ : syracuseStep 2270603 = 3405905) B3405905
theorem B2270615 : Blo 1512953 2270615 := bstep (se 1 (by rfl) ⟨1702961, by rfl⟩ : syracuseStep 2270615 = 3405923) B3405923
theorem B2590103 : Blo 1512953 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B7660979 : Blo 1512953 7660979 := bstep (se 1 (by rfl) ⟨5745734, by rfl⟩ : syracuseStep 7660979 = 11491469) B11491469
theorem B2270681 : Blo 1512953 2270681 := bstep (se 2 (by rfl) ⟨851505, by rfl⟩ : syracuseStep 2270681 = 1703011) B1703011
theorem B3688001 : Blo 1512953 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B2270795 : Blo 1512953 2270795 := bstep (se 1 (by rfl) ⟨1703096, by rfl⟩ : syracuseStep 2270795 = 3406193) B3406193
theorem B2270807 : Blo 1512953 2270807 := bstep (se 1 (by rfl) ⟨1703105, by rfl⟩ : syracuseStep 2270807 = 3406211) B3406211
theorem B2270873 : Blo 1512953 2270873 := bstep (se 2 (by rfl) ⟨851577, by rfl⟩ : syracuseStep 2270873 = 1703155) B1703155
theorem B3638963 : Blo 1512953 3638963 := bstep (se 1 (by rfl) ⟨2729222, by rfl⟩ : syracuseStep 3638963 = 5458445) B5458445
theorem B6465217 : Blo 1512953 6465217 := bstep (se 2 (by rfl) ⟨2424456, by rfl⟩ : syracuseStep 6465217 = 4848913) B4848913
theorem B2270987 : Blo 1512953 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B2270999 : Blo 1512953 2270999 := bstep (se 1 (by rfl) ⟨1703249, by rfl⟩ : syracuseStep 2270999 = 3406499) B3406499
theorem B12936995 : Blo 1512953 12936995 := bstep (se 1 (by rfl) ⟨9702746, by rfl⟩ : syracuseStep 12936995 = 19405493) B19405493
theorem B14559041 : Blo 1512953 14559041 := bstep (se 2 (by rfl) ⟨5459640, by rfl⟩ : syracuseStep 14559041 = 10919281) B10919281
theorem B2271065 : Blo 1512953 2271065 := bstep (se 2 (by rfl) ⟨851649, by rfl⟩ : syracuseStep 2271065 = 1703299) B1703299
theorem B2156377 : Blo 1512953 2156377 := bstep (se 2 (by rfl) ⟨808641, by rfl⟩ : syracuseStep 2156377 = 1617283) B1617283
theorem B2729921 : Blo 1512953 2729921 := bstep (se 2 (by rfl) ⟨1023720, by rfl⟩ : syracuseStep 2729921 = 2047441) B2047441
theorem B2271179 : Blo 1512953 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B2271191 : Blo 1512953 2271191 := bstep (se 1 (by rfl) ⟨1703393, by rfl⟩ : syracuseStep 2271191 = 3406787) B3406787
theorem B5457881 : Blo 1512953 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B8185873 : Blo 1512953 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B2271257 : Blo 1512953 2271257 := bstep (se 2 (by rfl) ⟨851721, by rfl⟩ : syracuseStep 2271257 = 1703443) B1703443
theorem B9701441 : Blo 1512953 9701441 := bstep (se 2 (by rfl) ⟨3638040, by rfl⟩ : syracuseStep 9701441 = 7276081) B7276081
theorem B2271371 : Blo 1512953 2271371 := bstep (se 1 (by rfl) ⟨1703528, by rfl⟩ : syracuseStep 2271371 = 3407057) B3407057
theorem B2271383 : Blo 1512953 2271383 := bstep (se 1 (by rfl) ⟨1703537, by rfl⟩ : syracuseStep 2271383 = 3407075) B3407075
theorem B2271449 : Blo 1512953 2271449 := bstep (se 2 (by rfl) ⟨851793, by rfl⟩ : syracuseStep 2271449 = 1703587) B1703587
theorem B11659565 : Blo 1512953 11659565 := bstep (se 3 (by rfl) ⟨2186168, by rfl⟩ : syracuseStep 11659565 = 4372337) B4372337
theorem B11659585 : Blo 1512953 11659585 := bstep (se 2 (by rfl) ⟨4372344, by rfl⟩ : syracuseStep 11659585 = 8744689) B8744689
theorem B1534283 : Blo 1512953 1534283 := bstep (se 1 (by rfl) ⟨1150712, by rfl⟩ : syracuseStep 1534283 = 2301425) B2301425
theorem B2271563 : Blo 1512953 2271563 := bstep (se 1 (by rfl) ⟨1703672, by rfl⟩ : syracuseStep 2271563 = 3407345) B3407345
theorem B2271575 : Blo 1512953 2271575 := bstep (se 1 (by rfl) ⟨1703681, by rfl⟩ : syracuseStep 2271575 = 3407363) B3407363
theorem B4368791 : Blo 1512953 4368791 := bstep (se 1 (by rfl) ⟨3276593, by rfl⟩ : syracuseStep 4368791 = 6553187) B6553187
theorem B2271641 : Blo 1512953 2271641 := bstep (se 2 (by rfl) ⟨851865, by rfl⟩ : syracuseStep 2271641 = 1703731) B1703731
theorem B5745113 : Blo 1512953 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B17246681 : Blo 1512953 17246681 := bstep (se 2 (by rfl) ⟨6467505, by rfl⟩ : syracuseStep 17246681 = 12935011) B12935011
theorem B2271755 : Blo 1512953 2271755 := bstep (se 1 (by rfl) ⟨1703816, by rfl⟩ : syracuseStep 2271755 = 3407633) B3407633
theorem B12937745 : Blo 1512953 12937745 := bstep (se 2 (by rfl) ⟨4851654, by rfl⟩ : syracuseStep 12937745 = 9703309) B9703309
theorem B2271767 : Blo 1512953 2271767 := bstep (se 1 (by rfl) ⟨1703825, by rfl⟩ : syracuseStep 2271767 = 3407651) B3407651
theorem B3689011 : Blo 1512953 3689011 := bstep (se 1 (by rfl) ⟨2766758, by rfl⟩ : syracuseStep 3689011 = 5533517) B5533517
theorem B2271833 : Blo 1512953 2271833 := bstep (se 2 (by rfl) ⟨851937, by rfl⟩ : syracuseStep 2271833 = 1703875) B1703875
theorem B2271947 : Blo 1512953 2271947 := bstep (se 1 (by rfl) ⟨1703960, by rfl⟩ : syracuseStep 2271947 = 3407921) B3407921
theorem B2271959 : Blo 1512953 2271959 := bstep (se 1 (by rfl) ⟨1703969, by rfl⟩ : syracuseStep 2271959 = 3407939) B3407939
theorem B5106455 : Blo 1512953 5106455 := bstep (se 1 (by rfl) ⟨3829841, by rfl⟩ : syracuseStep 5106455 = 7659683) B7659683
theorem B5745431 : Blo 1512953 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B5606167 : Blo 1512953 5606167 := bstep (se 1 (by rfl) ⟨4204625, by rfl⟩ : syracuseStep 5606167 = 8409251) B8409251
theorem B2272025 : Blo 1512953 2272025 := bstep (se 2 (by rfl) ⟨852009, by rfl⟩ : syracuseStep 2272025 = 1704019) B1704019
theorem B2272139 : Blo 1512953 2272139 := bstep (se 1 (by rfl) ⟨1704104, by rfl⟩ : syracuseStep 2272139 = 3408209) B3408209
theorem B2272151 : Blo 1512953 2272151 := bstep (se 1 (by rfl) ⟨1704113, by rfl⟩ : syracuseStep 2272151 = 3408227) B3408227
theorem B4090817 : Blo 1512953 4090817 := bstep (se 2 (by rfl) ⟨1534056, by rfl⟩ : syracuseStep 4090817 = 3068113) B3068113
theorem B4312025 : Blo 1512953 4312025 := bstep (se 2 (by rfl) ⟨1617009, by rfl⟩ : syracuseStep 4312025 = 3234019) B3234019
theorem B2272217 : Blo 1512953 2272217 := bstep (se 2 (by rfl) ⟨852081, by rfl⟩ : syracuseStep 2272217 = 1704163) B1704163
theorem B3992627 : Blo 1512953 3992627 := bstep (se 1 (by rfl) ⟨2994470, by rfl⟩ : syracuseStep 3992627 = 5988941) B5988941
theorem B2272331 : Blo 1512953 2272331 := bstep (se 1 (by rfl) ⟨1704248, by rfl⟩ : syracuseStep 2272331 = 3408497) B3408497
theorem B2272343 : Blo 1512953 2272343 := bstep (se 1 (by rfl) ⟨1704257, by rfl⟩ : syracuseStep 2272343 = 3408515) B3408515
theorem B5532761 : Blo 1512953 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B2272409 : Blo 1512953 2272409 := bstep (se 2 (by rfl) ⟨852153, by rfl⟩ : syracuseStep 2272409 = 1704307) B1704307
theorem B5827763 : Blo 1512953 5827763 := bstep (se 1 (by rfl) ⟨4370822, by rfl⟩ : syracuseStep 5827763 = 8741645) B8741645
theorem B5106995 : Blo 1512953 5106995 := bstep (se 1 (by rfl) ⟨3830246, by rfl⟩ : syracuseStep 5106995 = 7660493) B7660493
theorem B7662923 : Blo 1512953 7662923 := bstep (se 1 (by rfl) ⟨5747192, by rfl⟩ : syracuseStep 7662923 = 11494385) B11494385
theorem B6466891 : Blo 1512953 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B5746099 : Blo 1512953 5746099 := bstep (se 1 (by rfl) ⟨4309574, by rfl⟩ : syracuseStep 5746099 = 8619149) B8619149
theorem B1617355 : Blo 1512953 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B5107265 : Blo 1512953 5107265 := bstep (se 2 (by rfl) ⟨1915224, by rfl⟩ : syracuseStep 5107265 = 3830449) B3830449
theorem B6467165 : Blo 1512953 6467165 := bstep (se 3 (by rfl) ⟨1212593, by rfl⟩ : syracuseStep 6467165 = 2425187) B2425187
theorem B3231361 : Blo 1512953 3231361 := bstep (se 2 (by rfl) ⟨1211760, by rfl⟩ : syracuseStep 3231361 = 2423521) B2423521
theorem B8621747 : Blo 1512953 8621747 := bstep (se 1 (by rfl) ⟨6466310, by rfl⟩ : syracuseStep 8621747 = 12932621) B12932621
theorem B8736473 : Blo 1512953 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B4312855 : Blo 1512953 4312855 := bstep (se 1 (by rfl) ⟨3234641, by rfl⟩ : syracuseStep 4312855 = 6469283) B6469283
theorem B2912267 : Blo 1512953 2912267 := bstep (se 1 (by rfl) ⟨2184200, by rfl⟩ : syracuseStep 2912267 = 4368401) B4368401
theorem B5107805 : Blo 1512953 5107805 := bstep (se 3 (by rfl) ⟨957713, by rfl⟩ : syracuseStep 5107805 = 1915427) B1915427
theorem B6901939 : Blo 1512953 6901939 := bstep (se 1 (by rfl) ⟨5176454, by rfl⟩ : syracuseStep 6901939 = 10352909) B10352909
theorem B3829963 : Blo 1512953 3829963 := bstep (se 1 (by rfl) ⟨2872472, by rfl⟩ : syracuseStep 3829963 = 5744945) B5744945
theorem B8188121 : Blo 1512953 8188121 := bstep (se 2 (by rfl) ⟨3070545, by rfl⟩ : syracuseStep 8188121 = 6141091) B6141091
theorem B3830105 : Blo 1512953 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B3404249 : Blo 1512953 3404249 := bstep (se 2 (by rfl) ⟨1276593, by rfl⟩ : syracuseStep 3404249 = 2553187) B2553187
theorem B16372259 : Blo 1512953 16372259 := bstep (se 1 (by rfl) ⟨12279194, by rfl⟩ : syracuseStep 16372259 = 24558389) B24558389
theorem B3404339 : Blo 1512953 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B4313675 : Blo 1512953 4313675 := bstep (se 1 (by rfl) ⟨3235256, by rfl⟩ : syracuseStep 4313675 = 6470513) B6470513
theorem B3404375 : Blo 1512953 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B2912897 : Blo 1512953 2912897 := bstep (se 2 (by rfl) ⟨1092336, by rfl⟩ : syracuseStep 2912897 = 2184673) B2184673
theorem B5747345 : Blo 1512953 5747345 := bstep (se 2 (by rfl) ⟨2155254, by rfl⟩ : syracuseStep 5747345 = 4310509) B4310509
theorem B9826967 : Blo 1512953 9826967 := bstep (se 1 (by rfl) ⟨7370225, by rfl⟩ : syracuseStep 9826967 = 14740451) B14740451
theorem B12284621 : Blo 1512953 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B3404555 : Blo 1512953 3404555 := bstep (se 1 (by rfl) ⟨2553416, by rfl⟩ : syracuseStep 3404555 = 5106833) B5106833
theorem B3232523 : Blo 1512953 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B2913049 : Blo 1512953 2913049 := bstep (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) B2184787
theorem B3404609 : Blo 1512953 3404609 := bstep (se 2 (by rfl) ⟨1276728, by rfl⟩ : syracuseStep 3404609 = 2553457) B2553457
theorem B3068761 : Blo 1512953 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B2913175 : Blo 1512953 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B4092893 : Blo 1512953 4092893 := bstep (se 3 (by rfl) ⟨767417, by rfl⟩ : syracuseStep 4092893 = 1534835) B1534835
theorem B23950349 : Blo 1512953 23950349 := bstep (se 3 (by rfl) ⟨4490690, by rfl⟩ : syracuseStep 23950349 = 8981381) B8981381
theorem B3404825 : Blo 1512953 3404825 := bstep (se 2 (by rfl) ⟨1276809, by rfl⟩ : syracuseStep 3404825 = 2553619) B2553619
theorem B11646017 : Blo 1512953 11646017 := bstep (se 2 (by rfl) ⟨4367256, by rfl⟩ : syracuseStep 11646017 = 8734513) B8734513
theorem B7664705 : Blo 1512953 7664705 := bstep (se 2 (by rfl) ⟨2874264, by rfl⟩ : syracuseStep 7664705 = 5748529) B5748529
theorem B8623205 : Blo 1512953 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B2872435 : Blo 1512953 2872435 := bstep (se 1 (by rfl) ⟨2154326, by rfl⟩ : syracuseStep 2872435 = 4308653) B4308653
theorem B3404915 : Blo 1512953 3404915 := bstep (se 1 (by rfl) ⟨2553686, by rfl⟩ : syracuseStep 3404915 = 5107373) B5107373
theorem B6141059 : Blo 1512953 6141059 := bstep (se 1 (by rfl) ⟨4605794, by rfl⟩ : syracuseStep 6141059 = 9211589) B9211589
theorem B3404951 : Blo 1512953 3404951 := bstep (se 1 (by rfl) ⟨2553713, by rfl⟩ : syracuseStep 3404951 = 5107427) B5107427
theorem B3830935 : Blo 1512953 3830935 := bstep (se 1 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 3830935 = 5746403) B5746403
theorem B5108939 : Blo 1512953 5108939 := bstep (se 1 (by rfl) ⟨3831704, by rfl⟩ : syracuseStep 5108939 = 7663409) B7663409
theorem B2553113 : Blo 1512953 2553113 := bstep (se 2 (by rfl) ⟨957417, by rfl⟩ : syracuseStep 2553113 = 1914835) B1914835
theorem B3405131 : Blo 1512953 3405131 := bstep (se 1 (by rfl) ⟨2553848, by rfl⟩ : syracuseStep 3405131 = 5107697) B5107697
theorem B5748043 : Blo 1512953 5748043 := bstep (se 1 (by rfl) ⟨4311032, by rfl⟩ : syracuseStep 5748043 = 8622065) B8622065
theorem B3405185 : Blo 1512953 3405185 := bstep (se 2 (by rfl) ⟨1276944, by rfl⟩ : syracuseStep 3405185 = 2553889) B2553889
theorem B2553241 : Blo 1512953 2553241 := bstep (se 2 (by rfl) ⟨957465, by rfl⟩ : syracuseStep 2553241 = 1914931) B1914931
theorem B12940721 : Blo 1512953 12940721 := bstep (se 2 (by rfl) ⟨4852770, by rfl⟩ : syracuseStep 12940721 = 9705541) B9705541
theorem B18666931 : Blo 1512953 18666931 := bstep (se 1 (by rfl) ⟨14000198, by rfl⟩ : syracuseStep 18666931 = 28000397) B28000397
theorem B5109209 : Blo 1512953 5109209 := bstep (se 2 (by rfl) ⟨1915953, by rfl⟩ : syracuseStep 5109209 = 3831907) B3831907
theorem B3233267 : Blo 1512953 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1512971 : Blo 1512953 1512971 := bstep (se 1 (by rfl) ⟨1134728, by rfl⟩ : syracuseStep 1512971 = 2269457) B2269457
theorem B1512983 : Blo 1512953 1512983 := bstep (se 1 (by rfl) ⟨1134737, by rfl⟩ : syracuseStep 1512983 = 2269475) B2269475
theorem B1513003 : Blo 1512953 1513003 := bstep (se 1 (by rfl) ⟨1134752, by rfl⟩ : syracuseStep 1513003 = 2269505) B2269505
theorem B11818541 : Blo 1512953 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B2872883 : Blo 1512953 2872883 := bstep (se 1 (by rfl) ⟨2154662, by rfl⟩ : syracuseStep 2872883 = 4309325) B4309325
theorem B1513015 : Blo 1512953 1513015 := bstep (se 1 (by rfl) ⟨1134761, by rfl⟩ : syracuseStep 1513015 = 2269523) B2269523
theorem B1513035 : Blo 1512953 1513035 := bstep (se 1 (by rfl) ⟨1134776, by rfl⟩ : syracuseStep 1513035 = 2269553) B2269553
theorem B3831371 : Blo 1512953 3831371 := bstep (se 1 (by rfl) ⟨2873528, by rfl⟩ : syracuseStep 3831371 = 5747057) B5747057
theorem B1513047 : Blo 1512953 1513047 := bstep (se 1 (by rfl) ⟨1134785, by rfl⟩ : syracuseStep 1513047 = 2269571) B2269571
theorem B2872921 : Blo 1512953 2872921 := bstep (se 2 (by rfl) ⟨1077345, by rfl⟩ : syracuseStep 2872921 = 2154691) B2154691
theorem B3405401 : Blo 1512953 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B5748317 : Blo 1512953 5748317 := bstep (se 3 (by rfl) ⟨1077809, by rfl⟩ : syracuseStep 5748317 = 2155619) B2155619
theorem B1513067 : Blo 1512953 1513067 := bstep (se 1 (by rfl) ⟨1134800, by rfl⟩ : syracuseStep 1513067 = 2269601) B2269601
theorem B1513079 : Blo 1512953 1513079 := bstep (se 1 (by rfl) ⟨1134809, by rfl⟩ : syracuseStep 1513079 = 2269619) B2269619
theorem B11646595 : Blo 1512953 11646595 := bstep (se 1 (by rfl) ⟨8734946, by rfl⟩ : syracuseStep 11646595 = 17469893) B17469893
theorem B1513099 : Blo 1512953 1513099 := bstep (se 1 (by rfl) ⟨1134824, by rfl⟩ : syracuseStep 1513099 = 2269649) B2269649
theorem B17233559 : Blo 1512953 17233559 := bstep (se 1 (by rfl) ⟨12925169, by rfl⟩ : syracuseStep 17233559 = 25850339) B25850339
theorem B12269207 : Blo 1512953 12269207 := bstep (se 1 (by rfl) ⟨9201905, by rfl⟩ : syracuseStep 12269207 = 18403811) B18403811
theorem B1513111 : Blo 1512953 1513111 := bstep (se 1 (by rfl) ⟨1134833, by rfl⟩ : syracuseStep 1513111 = 2269667) B2269667
theorem B1513131 : Blo 1512953 1513131 := bstep (se 1 (by rfl) ⟨1134848, by rfl⟩ : syracuseStep 1513131 = 2269697) B2269697
theorem B3405491 : Blo 1512953 3405491 := bstep (se 1 (by rfl) ⟨2554118, by rfl⟩ : syracuseStep 3405491 = 5108237) B5108237
theorem B1513143 : Blo 1512953 1513143 := bstep (se 1 (by rfl) ⟨1134857, by rfl⟩ : syracuseStep 1513143 = 2269715) B2269715
theorem B1513163 : Blo 1512953 1513163 := bstep (se 1 (by rfl) ⟨1134872, by rfl⟩ : syracuseStep 1513163 = 2269745) B2269745
theorem B1513175 : Blo 1512953 1513175 := bstep (se 1 (by rfl) ⟨1134881, by rfl⟩ : syracuseStep 1513175 = 2269763) B2269763
theorem B3405527 : Blo 1512953 3405527 := bstep (se 1 (by rfl) ⟨2554145, by rfl⟩ : syracuseStep 3405527 = 5108291) B5108291
theorem B1513195 : Blo 1512953 1513195 := bstep (se 1 (by rfl) ⟨1134896, by rfl⟩ : syracuseStep 1513195 = 2269793) B2269793
theorem B1513207 : Blo 1512953 1513207 := bstep (se 1 (by rfl) ⟨1134905, by rfl⟩ : syracuseStep 1513207 = 2269811) B2269811
theorem B1513227 : Blo 1512953 1513227 := bstep (se 1 (by rfl) ⟨1134920, by rfl⟩ : syracuseStep 1513227 = 2269841) B2269841
theorem B1513239 : Blo 1512953 1513239 := bstep (se 1 (by rfl) ⟨1134929, by rfl⟩ : syracuseStep 1513239 = 2269859) B2269859
theorem B1513259 : Blo 1512953 1513259 := bstep (se 1 (by rfl) ⟨1134944, by rfl⟩ : syracuseStep 1513259 = 2269889) B2269889
theorem B1513271 : Blo 1512953 1513271 := bstep (se 1 (by rfl) ⟨1134953, by rfl⟩ : syracuseStep 1513271 = 2269907) B2269907
theorem B1513291 : Blo 1512953 1513291 := bstep (se 1 (by rfl) ⟨1134968, by rfl⟩ : syracuseStep 1513291 = 2269937) B2269937
theorem B1513303 : Blo 1512953 1513303 := bstep (se 1 (by rfl) ⟨1134977, by rfl⟩ : syracuseStep 1513303 = 2269955) B2269955
theorem B1513323 : Blo 1512953 1513323 := bstep (se 1 (by rfl) ⟨1134992, by rfl⟩ : syracuseStep 1513323 = 2269985) B2269985
theorem B1513335 : Blo 1512953 1513335 := bstep (se 1 (by rfl) ⟨1135001, by rfl⟩ : syracuseStep 1513335 = 2270003) B2270003
theorem B1513355 : Blo 1512953 1513355 := bstep (se 1 (by rfl) ⟨1135016, by rfl⟩ : syracuseStep 1513355 = 2270033) B2270033
theorem B3405707 : Blo 1512953 3405707 := bstep (se 1 (by rfl) ⟨2554280, by rfl⟩ : syracuseStep 3405707 = 5108561) B5108561
theorem B1513367 : Blo 1512953 1513367 := bstep (se 1 (by rfl) ⟨1135025, by rfl⟩ : syracuseStep 1513367 = 2270051) B2270051
theorem B1513387 : Blo 1512953 1513387 := bstep (se 1 (by rfl) ⟨1135040, by rfl⟩ : syracuseStep 1513387 = 2270081) B2270081
theorem B1513399 : Blo 1512953 1513399 := bstep (se 1 (by rfl) ⟨1135049, by rfl⟩ : syracuseStep 1513399 = 2270099) B2270099
theorem B3405761 : Blo 1512953 3405761 := bstep (se 2 (by rfl) ⟨1277160, by rfl⟩ : syracuseStep 3405761 = 2554321) B2554321
theorem B3831745 : Blo 1512953 3831745 := bstep (se 2 (by rfl) ⟨1436904, by rfl⟩ : syracuseStep 3831745 = 2873809) B2873809
theorem B1513419 : Blo 1512953 1513419 := bstep (se 1 (by rfl) ⟨1135064, by rfl⟩ : syracuseStep 1513419 = 2270129) B2270129
theorem B2553815 : Blo 1512953 2553815 := bstep (se 1 (by rfl) ⟨1915361, by rfl⟩ : syracuseStep 2553815 = 3830723) B3830723
theorem B1513431 : Blo 1512953 1513431 := bstep (se 1 (by rfl) ⟨1135073, by rfl⟩ : syracuseStep 1513431 = 2270147) B2270147
theorem B1513451 : Blo 1512953 1513451 := bstep (se 1 (by rfl) ⟨1135088, by rfl⟩ : syracuseStep 1513451 = 2270177) B2270177
theorem B1513463 : Blo 1512953 1513463 := bstep (se 1 (by rfl) ⟨1135097, by rfl⟩ : syracuseStep 1513463 = 2270195) B2270195
theorem B13817861 : Blo 1512953 13817861 := bstep (se 4 (by rfl) ⟨1295424, by rfl⟩ : syracuseStep 13817861 = 2590849) B2590849
theorem B1513483 : Blo 1512953 1513483 := bstep (se 1 (by rfl) ⟨1135112, by rfl⟩ : syracuseStep 1513483 = 2270225) B2270225
theorem B1513495 : Blo 1512953 1513495 := bstep (se 1 (by rfl) ⟨1135121, by rfl⟩ : syracuseStep 1513495 = 2270243) B2270243
theorem B2873369 : Blo 1512953 2873369 := bstep (se 2 (by rfl) ⟨1077513, by rfl⟩ : syracuseStep 2873369 = 2155027) B2155027
theorem B13817891 : Blo 1512953 13817891 := bstep (se 1 (by rfl) ⟨10363418, by rfl⟩ : syracuseStep 13817891 = 20726837) B20726837
theorem B1513515 : Blo 1512953 1513515 := bstep (se 1 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 1513515 = 2270273) B2270273
theorem B1513527 : Blo 1512953 1513527 := bstep (se 1 (by rfl) ⟨1135145, by rfl⟩ : syracuseStep 1513527 = 2270291) B2270291
theorem B1513547 : Blo 1512953 1513547 := bstep (se 1 (by rfl) ⟨1135160, by rfl⟩ : syracuseStep 1513547 = 2270321) B2270321
theorem B2553943 : Blo 1512953 2553943 := bstep (se 1 (by rfl) ⟨1915457, by rfl⟩ : syracuseStep 2553943 = 3830915) B3830915
theorem B1513559 : Blo 1512953 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B1513579 : Blo 1512953 1513579 := bstep (se 1 (by rfl) ⟨1135184, by rfl⟩ : syracuseStep 1513579 = 2270369) B2270369
theorem B1513591 : Blo 1512953 1513591 := bstep (se 1 (by rfl) ⟨1135193, by rfl⟩ : syracuseStep 1513591 = 2270387) B2270387
theorem B1513611 : Blo 1512953 1513611 := bstep (se 1 (by rfl) ⟨1135208, by rfl⟩ : syracuseStep 1513611 = 2270417) B2270417
theorem B1513623 : Blo 1512953 1513623 := bstep (se 1 (by rfl) ⟨1135217, by rfl⟩ : syracuseStep 1513623 = 2270435) B2270435
theorem B5109911 : Blo 1512953 5109911 := bstep (se 1 (by rfl) ⟨3832433, by rfl⟩ : syracuseStep 5109911 = 7664867) B7664867
theorem B3405977 : Blo 1512953 3405977 := bstep (se 2 (by rfl) ⟨1277241, by rfl⟩ : syracuseStep 3405977 = 2554483) B2554483
theorem B1513643 : Blo 1512953 1513643 := bstep (se 1 (by rfl) ⟨1135232, by rfl⟩ : syracuseStep 1513643 = 2270465) B2270465
theorem B1513655 : Blo 1512953 1513655 := bstep (se 1 (by rfl) ⟨1135241, by rfl⟩ : syracuseStep 1513655 = 2270483) B2270483
theorem B1513675 : Blo 1512953 1513675 := bstep (se 1 (by rfl) ⟨1135256, by rfl⟩ : syracuseStep 1513675 = 2270513) B2270513
theorem B1513687 : Blo 1512953 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B8181977 : Blo 1512953 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B1513707 : Blo 1512953 1513707 := bstep (se 1 (by rfl) ⟨1135280, by rfl⟩ : syracuseStep 1513707 = 2270561) B2270561
theorem B3406067 : Blo 1512953 3406067 := bstep (se 1 (by rfl) ⟨2554550, by rfl⟩ : syracuseStep 3406067 = 5109101) B5109101
theorem B1513719 : Blo 1512953 1513719 := bstep (se 1 (by rfl) ⟨1135289, by rfl⟩ : syracuseStep 1513719 = 2270579) B2270579
theorem B1513739 : Blo 1512953 1513739 := bstep (se 1 (by rfl) ⟨1135304, by rfl⟩ : syracuseStep 1513739 = 2270609) B2270609
theorem B1915159 : Blo 1512953 1915159 := bstep (se 1 (by rfl) ⟨1436369, by rfl⟩ : syracuseStep 1915159 = 2872739) B2872739
theorem B1513751 : Blo 1512953 1513751 := bstep (se 1 (by rfl) ⟨1135313, by rfl⟩ : syracuseStep 1513751 = 2270627) B2270627
theorem B3406103 : Blo 1512953 3406103 := bstep (se 1 (by rfl) ⟨2554577, by rfl⟩ : syracuseStep 3406103 = 5109155) B5109155
theorem B5749015 : Blo 1512953 5749015 := bstep (se 1 (by rfl) ⟨4311761, by rfl⟩ : syracuseStep 5749015 = 8623523) B8623523
theorem B1513771 : Blo 1512953 1513771 := bstep (se 1 (by rfl) ⟨1135328, by rfl⟩ : syracuseStep 1513771 = 2270657) B2270657
theorem B1513783 : Blo 1512953 1513783 := bstep (se 1 (by rfl) ⟨1135337, by rfl⟩ : syracuseStep 1513783 = 2270675) B2270675
theorem B1702219 : Blo 1512953 1702219 := bstep (se 1 (by rfl) ⟨1276664, by rfl⟩ : syracuseStep 1702219 = 2553329) B2553329
theorem B1513803 : Blo 1512953 1513803 := bstep (se 1 (by rfl) ⟨1135352, by rfl⟩ : syracuseStep 1513803 = 2270705) B2270705
theorem B1513815 : Blo 1512953 1513815 := bstep (se 1 (by rfl) ⟨1135361, by rfl⟩ : syracuseStep 1513815 = 2270723) B2270723
theorem B1513835 : Blo 1512953 1513835 := bstep (se 1 (by rfl) ⟨1135376, by rfl⟩ : syracuseStep 1513835 = 2270753) B2270753
theorem B1513847 : Blo 1512953 1513847 := bstep (se 1 (by rfl) ⟨1135385, by rfl⟩ : syracuseStep 1513847 = 2270771) B2270771
theorem B3234163 : Blo 1512953 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B1513867 : Blo 1512953 1513867 := bstep (se 1 (by rfl) ⟨1135400, by rfl⟩ : syracuseStep 1513867 = 2270801) B2270801
theorem B1513879 : Blo 1512953 1513879 := bstep (se 1 (by rfl) ⟨1135409, by rfl⟩ : syracuseStep 1513879 = 2270819) B2270819
theorem B1513899 : Blo 1512953 1513899 := bstep (se 1 (by rfl) ⟨1135424, by rfl⟩ : syracuseStep 1513899 = 2270849) B2270849
theorem B1702327 : Blo 1512953 1702327 := bstep (se 1 (by rfl) ⟨1276745, by rfl⟩ : syracuseStep 1702327 = 2553491) B2553491
theorem B1513911 : Blo 1512953 1513911 := bstep (se 1 (by rfl) ⟨1135433, by rfl⟩ : syracuseStep 1513911 = 2270867) B2270867
theorem B3406283 : Blo 1512953 3406283 := bstep (se 1 (by rfl) ⟨2554712, by rfl⟩ : syracuseStep 3406283 = 5109425) B5109425
theorem B1513931 : Blo 1512953 1513931 := bstep (se 1 (by rfl) ⟨1135448, by rfl⟩ : syracuseStep 1513931 = 2270897) B2270897
theorem B1513943 : Blo 1512953 1513943 := bstep (se 1 (by rfl) ⟨1135457, by rfl⟩ : syracuseStep 1513943 = 2270915) B2270915
theorem B1513963 : Blo 1512953 1513963 := bstep (se 1 (by rfl) ⟨1135472, by rfl⟩ : syracuseStep 1513963 = 2270945) B2270945
theorem B1513975 : Blo 1512953 1513975 := bstep (se 1 (by rfl) ⟨1135481, by rfl⟩ : syracuseStep 1513975 = 2270963) B2270963
theorem B3406337 : Blo 1512953 3406337 := bstep (se 2 (by rfl) ⟨1277376, by rfl⟩ : syracuseStep 3406337 = 2554753) B2554753
theorem B1513995 : Blo 1512953 1513995 := bstep (se 1 (by rfl) ⟨1135496, by rfl⟩ : syracuseStep 1513995 = 2270993) B2270993
theorem B1514007 : Blo 1512953 1514007 := bstep (se 1 (by rfl) ⟨1135505, by rfl⟩ : syracuseStep 1514007 = 2271011) B2271011
theorem B3832343 : Blo 1512953 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B1514027 : Blo 1512953 1514027 := bstep (se 1 (by rfl) ⟨1135520, by rfl⟩ : syracuseStep 1514027 = 2271041) B2271041
theorem B1514039 : Blo 1512953 1514039 := bstep (se 1 (by rfl) ⟨1135529, by rfl⟩ : syracuseStep 1514039 = 2271059) B2271059
theorem B1514059 : Blo 1512953 1514059 := bstep (se 1 (by rfl) ⟨1135544, by rfl⟩ : syracuseStep 1514059 = 2271089) B2271089
theorem B1514071 : Blo 1512953 1514071 := bstep (se 1 (by rfl) ⟨1135553, by rfl⟩ : syracuseStep 1514071 = 2271107) B2271107
theorem B1702507 : Blo 1512953 1702507 := bstep (se 1 (by rfl) ⟨1276880, by rfl⟩ : syracuseStep 1702507 = 2553761) B2553761
theorem B1514091 : Blo 1512953 1514091 := bstep (se 1 (by rfl) ⟨1135568, by rfl⟩ : syracuseStep 1514091 = 2271137) B2271137
theorem B1514103 : Blo 1512953 1514103 := bstep (se 1 (by rfl) ⟨1135577, by rfl⟩ : syracuseStep 1514103 = 2271155) B2271155
theorem B16366211 : Blo 1512953 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B1514123 : Blo 1512953 1514123 := bstep (se 1 (by rfl) ⟨1135592, by rfl⟩ : syracuseStep 1514123 = 2271185) B2271185
theorem B1514135 : Blo 1512953 1514135 := bstep (se 1 (by rfl) ⟨1135601, by rfl⟩ : syracuseStep 1514135 = 2271203) B2271203
theorem B1514155 : Blo 1512953 1514155 := bstep (se 1 (by rfl) ⟨1135616, by rfl⟩ : syracuseStep 1514155 = 2271233) B2271233
theorem B1514167 : Blo 1512953 1514167 := bstep (se 1 (by rfl) ⟨1135625, by rfl⟩ : syracuseStep 1514167 = 2271251) B2271251
theorem B5110451 : Blo 1512953 5110451 := bstep (se 1 (by rfl) ⟨3832838, by rfl⟩ : syracuseStep 5110451 = 7665677) B7665677
theorem B5454539 : Blo 1512953 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B2554571 : Blo 1512953 2554571 := bstep (se 1 (by rfl) ⟨1915928, by rfl⟩ : syracuseStep 2554571 = 3831857) B3831857
theorem B1514187 : Blo 1512953 1514187 := bstep (se 1 (by rfl) ⟨1135640, by rfl⟩ : syracuseStep 1514187 = 2271281) B2271281
theorem B1702615 : Blo 1512953 1702615 := bstep (se 1 (by rfl) ⟨1276961, by rfl⟩ : syracuseStep 1702615 = 2553923) B2553923
theorem B3406553 : Blo 1512953 3406553 := bstep (se 2 (by rfl) ⟨1277457, by rfl⟩ : syracuseStep 3406553 = 2554915) B2554915
theorem B1514199 : Blo 1512953 1514199 := bstep (se 1 (by rfl) ⟨1135649, by rfl⟩ : syracuseStep 1514199 = 2271299) B2271299
theorem B1514219 : Blo 1512953 1514219 := bstep (se 1 (by rfl) ⟨1135664, by rfl⟩ : syracuseStep 1514219 = 2271329) B2271329
theorem B1514231 : Blo 1512953 1514231 := bstep (se 1 (by rfl) ⟨1135673, by rfl⟩ : syracuseStep 1514231 = 2271347) B2271347
theorem B2874113 : Blo 1512953 2874113 := bstep (se 2 (by rfl) ⟨1077792, by rfl⟩ : syracuseStep 2874113 = 2155585) B2155585
theorem B1514251 : Blo 1512953 1514251 := bstep (se 1 (by rfl) ⟨1135688, by rfl⟩ : syracuseStep 1514251 = 2271377) B2271377
theorem B1514263 : Blo 1512953 1514263 := bstep (se 1 (by rfl) ⟨1135697, by rfl⟩ : syracuseStep 1514263 = 2271395) B2271395
theorem B1514283 : Blo 1512953 1514283 := bstep (se 1 (by rfl) ⟨1135712, by rfl⟩ : syracuseStep 1514283 = 2271425) B2271425
theorem B3406643 : Blo 1512953 3406643 := bstep (se 1 (by rfl) ⟨2554982, by rfl⟩ : syracuseStep 3406643 = 5109965) B5109965
theorem B1514295 : Blo 1512953 1514295 := bstep (se 1 (by rfl) ⟨1135721, by rfl⟩ : syracuseStep 1514295 = 2271443) B2271443
theorem B2554699 : Blo 1512953 2554699 := bstep (se 1 (by rfl) ⟨1916024, by rfl⟩ : syracuseStep 2554699 = 3832049) B3832049
theorem B1514315 : Blo 1512953 1514315 := bstep (se 1 (by rfl) ⟨1135736, by rfl⟩ : syracuseStep 1514315 = 2271473) B2271473
theorem B3406679 : Blo 1512953 3406679 := bstep (se 1 (by rfl) ⟨2555009, by rfl⟩ : syracuseStep 3406679 = 5110019) B5110019
theorem B3152729 : Blo 1512953 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B1514327 : Blo 1512953 1514327 := bstep (se 1 (by rfl) ⟨1135745, by rfl⟩ : syracuseStep 1514327 = 2271491) B2271491
theorem B1514347 : Blo 1512953 1514347 := bstep (se 1 (by rfl) ⟨1135760, by rfl⟩ : syracuseStep 1514347 = 2271521) B2271521
theorem B1514359 : Blo 1512953 1514359 := bstep (se 1 (by rfl) ⟨1135769, by rfl⟩ : syracuseStep 1514359 = 2271539) B2271539
theorem B1702795 : Blo 1512953 1702795 := bstep (se 1 (by rfl) ⟨1277096, by rfl⟩ : syracuseStep 1702795 = 2554193) B2554193
theorem B1514379 : Blo 1512953 1514379 := bstep (se 1 (by rfl) ⟨1135784, by rfl⟩ : syracuseStep 1514379 = 2271569) B2271569
theorem B1514391 : Blo 1512953 1514391 := bstep (se 1 (by rfl) ⟨1135793, by rfl⟩ : syracuseStep 1514391 = 2271587) B2271587
theorem B1514411 : Blo 1512953 1514411 := bstep (se 1 (by rfl) ⟨1135808, by rfl⟩ : syracuseStep 1514411 = 2271617) B2271617
theorem B1514423 : Blo 1512953 1514423 := bstep (se 1 (by rfl) ⟨1135817, by rfl⟩ : syracuseStep 1514423 = 2271635) B2271635
theorem B5110721 : Blo 1512953 5110721 := bstep (se 2 (by rfl) ⟨1916520, by rfl⟩ : syracuseStep 5110721 = 3833041) B3833041
theorem B1514443 : Blo 1512953 1514443 := bstep (se 1 (by rfl) ⟨1135832, by rfl⟩ : syracuseStep 1514443 = 2271665) B2271665
theorem B1514455 : Blo 1512953 1514455 := bstep (se 1 (by rfl) ⟨1135841, by rfl⟩ : syracuseStep 1514455 = 2271683) B2271683
theorem B2554841 : Blo 1512953 2554841 := bstep (se 2 (by rfl) ⟨958065, by rfl⟩ : syracuseStep 2554841 = 1916131) B1916131
theorem B7666649 : Blo 1512953 7666649 := bstep (se 2 (by rfl) ⟨2874993, by rfl⟩ : syracuseStep 7666649 = 5749987) B5749987
theorem B1514475 : Blo 1512953 1514475 := bstep (se 1 (by rfl) ⟨1135856, by rfl⟩ : syracuseStep 1514475 = 2271713) B2271713
theorem B1702903 : Blo 1512953 1702903 := bstep (se 1 (by rfl) ⟨1277177, by rfl⟩ : syracuseStep 1702903 = 2554355) B2554355
theorem B1514487 : Blo 1512953 1514487 := bstep (se 1 (by rfl) ⟨1135865, by rfl⟩ : syracuseStep 1514487 = 2271731) B2271731
theorem B2874379 : Blo 1512953 2874379 := bstep (se 1 (by rfl) ⟨2155784, by rfl⟩ : syracuseStep 2874379 = 4311569) B4311569
theorem B3406859 : Blo 1512953 3406859 := bstep (se 1 (by rfl) ⟨2555144, by rfl⟩ : syracuseStep 3406859 = 5110289) B5110289
theorem B1514507 : Blo 1512953 1514507 := bstep (se 1 (by rfl) ⟨1135880, by rfl⟩ : syracuseStep 1514507 = 2271761) B2271761
theorem B46644245 : Blo 1512953 46644245 := bstep (se 6 (by rfl) ⟨1093224, by rfl⟩ : syracuseStep 46644245 = 2186449) B2186449
theorem B2300951 : Blo 1512953 2300951 := bstep (se 1 (by rfl) ⟨1725713, by rfl⟩ : syracuseStep 2300951 = 3451427) B3451427
theorem B1514519 : Blo 1512953 1514519 := bstep (se 1 (by rfl) ⟨1135889, by rfl⟩ : syracuseStep 1514519 = 2271779) B2271779
theorem B1514539 : Blo 1512953 1514539 := bstep (se 1 (by rfl) ⟨1135904, by rfl⟩ : syracuseStep 1514539 = 2271809) B2271809
theorem B5749805 : Blo 1512953 5749805 := bstep (se 3 (by rfl) ⟨1078088, by rfl⟩ : syracuseStep 5749805 = 2156177) B2156177
theorem B6224941 : Blo 1512953 6224941 := bstep (se 3 (by rfl) ⟨1167176, by rfl⟩ : syracuseStep 6224941 = 2334353) B2334353
theorem B1514551 : Blo 1512953 1514551 := bstep (se 1 (by rfl) ⟨1135913, by rfl⟩ : syracuseStep 1514551 = 2271827) B2271827
theorem B3406913 : Blo 1512953 3406913 := bstep (se 2 (by rfl) ⟨1277592, by rfl⟩ : syracuseStep 3406913 = 2555185) B2555185
theorem B1514571 : Blo 1512953 1514571 := bstep (se 1 (by rfl) ⟨1135928, by rfl⟩ : syracuseStep 1514571 = 2271857) B2271857
theorem B1514583 : Blo 1512953 1514583 := bstep (se 1 (by rfl) ⟨1135937, by rfl⟩ : syracuseStep 1514583 = 2271875) B2271875
theorem B2554969 : Blo 1512953 2554969 := bstep (se 2 (by rfl) ⟨958113, by rfl⟩ : syracuseStep 2554969 = 1916227) B1916227
theorem B1514603 : Blo 1512953 1514603 := bstep (se 1 (by rfl) ⟨1135952, by rfl⟩ : syracuseStep 1514603 = 2271905) B2271905
theorem B1514615 : Blo 1512953 1514615 := bstep (se 1 (by rfl) ⟨1135961, by rfl⟩ : syracuseStep 1514615 = 2271923) B2271923
theorem B1514635 : Blo 1512953 1514635 := bstep (se 1 (by rfl) ⟨1135976, by rfl⟩ : syracuseStep 1514635 = 2271953) B2271953
theorem B1514647 : Blo 1512953 1514647 := bstep (se 1 (by rfl) ⟨1135985, by rfl⟩ : syracuseStep 1514647 = 2271971) B2271971
theorem B1703083 : Blo 1512953 1703083 := bstep (se 1 (by rfl) ⟨1277312, by rfl⟩ : syracuseStep 1703083 = 2554625) B2554625
theorem B1514667 : Blo 1512953 1514667 := bstep (se 1 (by rfl) ⟨1136000, by rfl⟩ : syracuseStep 1514667 = 2272001) B2272001
theorem B1514679 : Blo 1512953 1514679 := bstep (se 1 (by rfl) ⟨1136009, by rfl⟩ : syracuseStep 1514679 = 2272019) B2272019
theorem B3636427 : Blo 1512953 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B1514699 : Blo 1512953 1514699 := bstep (se 1 (by rfl) ⟨1136024, by rfl⟩ : syracuseStep 1514699 = 2272049) B2272049
theorem B1514711 : Blo 1512953 1514711 := bstep (se 1 (by rfl) ⟨1136033, by rfl⟩ : syracuseStep 1514711 = 2272067) B2272067
theorem B1514731 : Blo 1512953 1514731 := bstep (se 1 (by rfl) ⟨1136048, by rfl⟩ : syracuseStep 1514731 = 2272097) B2272097
theorem B1514743 : Blo 1512953 1514743 := bstep (se 1 (by rfl) ⟨1136057, by rfl⟩ : syracuseStep 1514743 = 2272115) B2272115
theorem B1514763 : Blo 1512953 1514763 := bstep (se 1 (by rfl) ⟨1136072, by rfl⟩ : syracuseStep 1514763 = 2272145) B2272145
theorem B3636503 : Blo 1512953 3636503 := bstep (se 1 (by rfl) ⟨2727377, by rfl⟩ : syracuseStep 3636503 = 5454755) B5454755
theorem B1703191 : Blo 1512953 1703191 := bstep (se 1 (by rfl) ⟨1277393, by rfl⟩ : syracuseStep 1703191 = 2554787) B2554787
theorem B3407129 : Blo 1512953 3407129 := bstep (se 2 (by rfl) ⟨1277673, by rfl⟩ : syracuseStep 3407129 = 2555347) B2555347
theorem B1514775 : Blo 1512953 1514775 := bstep (se 1 (by rfl) ⟨1136081, by rfl⟩ : syracuseStep 1514775 = 2272163) B2272163
theorem B1514795 : Blo 1512953 1514795 := bstep (se 1 (by rfl) ⟨1136096, by rfl⟩ : syracuseStep 1514795 = 2272193) B2272193
theorem B1514807 : Blo 1512953 1514807 := bstep (se 1 (by rfl) ⟨1136105, by rfl⟩ : syracuseStep 1514807 = 2272211) B2272211
theorem B3833153 : Blo 1512953 3833153 := bstep (se 2 (by rfl) ⟨1437432, by rfl⟩ : syracuseStep 3833153 = 2874865) B2874865
theorem B1514827 : Blo 1512953 1514827 := bstep (se 1 (by rfl) ⟨1136120, by rfl⟩ : syracuseStep 1514827 = 2272241) B2272241
theorem B1514839 : Blo 1512953 1514839 := bstep (se 1 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 1514839 = 2272259) B2272259
theorem B4848989 : Blo 1512953 4848989 := bstep (se 3 (by rfl) ⟨909185, by rfl⟩ : syracuseStep 4848989 = 1818371) B1818371
theorem B1514859 : Blo 1512953 1514859 := bstep (se 1 (by rfl) ⟨1136144, by rfl⟩ : syracuseStep 1514859 = 2272289) B2272289
theorem B3407219 : Blo 1512953 3407219 := bstep (se 1 (by rfl) ⟨2555414, by rfl⟩ : syracuseStep 3407219 = 5110829) B5110829
theorem B1514871 : Blo 1512953 1514871 := bstep (se 1 (by rfl) ⟨1136153, by rfl⟩ : syracuseStep 1514871 = 2272307) B2272307
theorem B1514891 : Blo 1512953 1514891 := bstep (se 1 (by rfl) ⟨1136168, by rfl⟩ : syracuseStep 1514891 = 2272337) B2272337
theorem B3407255 : Blo 1512953 3407255 := bstep (se 1 (by rfl) ⟨2555441, by rfl⟩ : syracuseStep 3407255 = 5110883) B5110883
theorem B3235223 : Blo 1512953 3235223 := bstep (se 1 (by rfl) ⟨2426417, by rfl⟩ : syracuseStep 3235223 = 4852835) B4852835
theorem B1514903 : Blo 1512953 1514903 := bstep (se 1 (by rfl) ⟨1136177, by rfl⟩ : syracuseStep 1514903 = 2272355) B2272355
theorem B1514923 : Blo 1512953 1514923 := bstep (se 1 (by rfl) ⟨1136192, by rfl⟩ : syracuseStep 1514923 = 2272385) B2272385
theorem B1514935 : Blo 1512953 1514935 := bstep (se 1 (by rfl) ⟨1136201, by rfl⟩ : syracuseStep 1514935 = 2272403) B2272403
theorem B1703371 : Blo 1512953 1703371 := bstep (se 1 (by rfl) ⟨1277528, by rfl⟩ : syracuseStep 1703371 = 2555057) B2555057
theorem B2874827 : Blo 1512953 2874827 := bstep (se 1 (by rfl) ⟨2156120, by rfl⟩ : syracuseStep 2874827 = 4312241) B4312241
theorem B9698777 : Blo 1512953 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B5111261 : Blo 1512953 5111261 := bstep (se 3 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 5111261 = 1916723) B1916723
theorem B1703479 : Blo 1512953 1703479 := bstep (se 1 (by rfl) ⟨1277609, by rfl⟩ : syracuseStep 1703479 = 2555219) B2555219
theorem B3235393 : Blo 1512953 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B3407435 : Blo 1512953 3407435 := bstep (se 1 (by rfl) ⟨2555576, by rfl⟩ : syracuseStep 3407435 = 5111153) B5111153
theorem B2875009 : Blo 1512953 2875009 := bstep (se 2 (by rfl) ⟨1078128, by rfl⟩ : syracuseStep 2875009 = 2156257) B2156257
theorem B3407489 : Blo 1512953 3407489 := bstep (se 2 (by rfl) ⟨1277808, by rfl⟩ : syracuseStep 3407489 = 2555617) B2555617
theorem B21814915 : Blo 1512953 21814915 := bstep (se 1 (by rfl) ⟨16361186, by rfl⟩ : syracuseStep 21814915 = 32722373) B32722373
theorem B2588311 : Blo 1512953 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B20717207 : Blo 1512953 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B2555543 : Blo 1512953 2555543 := bstep (se 1 (by rfl) ⟨1916657, by rfl⟩ : syracuseStep 2555543 = 3833315) B3833315
theorem B1703659 : Blo 1512953 1703659 := bstep (se 1 (by rfl) ⟨1277744, by rfl⟩ : syracuseStep 1703659 = 2555489) B2555489
theorem B2555671 : Blo 1512953 2555671 := bstep (se 1 (by rfl) ⟨1916753, by rfl⟩ : syracuseStep 2555671 = 3833507) B3833507
theorem B2727731 : Blo 1512953 2727731 := bstep (se 1 (by rfl) ⟨2045798, by rfl⟩ : syracuseStep 2727731 = 4091597) B4091597
theorem B1703767 : Blo 1512953 1703767 := bstep (se 1 (by rfl) ⟨1277825, by rfl⟩ : syracuseStep 1703767 = 2555651) B2555651
theorem B3407705 : Blo 1512953 3407705 := bstep (se 2 (by rfl) ⟨1277889, by rfl⟩ : syracuseStep 3407705 = 2555779) B2555779
theorem B3833689 : Blo 1512953 3833689 := bstep (se 2 (by rfl) ⟨1437633, by rfl⟩ : syracuseStep 3833689 = 2875267) B2875267
theorem B6463405 : Blo 1512953 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B3407795 : Blo 1512953 3407795 := bstep (se 1 (by rfl) ⟨2555846, by rfl⟩ : syracuseStep 3407795 = 5111693) B5111693
theorem B1916875 : Blo 1512953 1916875 := bstep (se 1 (by rfl) ⟨1437656, by rfl⟩ : syracuseStep 1916875 = 2875313) B2875313
theorem B2875351 : Blo 1512953 2875351 := bstep (se 1 (by rfl) ⟨2156513, by rfl⟩ : syracuseStep 2875351 = 4313027) B4313027
theorem B3407831 : Blo 1512953 3407831 := bstep (se 1 (by rfl) ⟨2555873, by rfl⟩ : syracuseStep 3407831 = 5111747) B5111747
theorem B1941511 : Blo 1512953 1941511 := bstep (se 1 (by rfl) ⟨1456133, by rfl⟩ : syracuseStep 1941511 = 2912267) B2912267
theorem B4309051 : Blo 1512953 4309051 := bstep (se 1 (by rfl) ⟨3231788, by rfl⟩ : syracuseStep 4309051 = 6463577) B6463577
theorem B7372919 : Blo 1512953 7372919 := bstep (se 1 (by rfl) ⟨5529689, by rfl⟩ : syracuseStep 7372919 = 11059379) B11059379
theorem B1917047 : Blo 1512953 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1704199 : Blo 1512953 1704199 := bstep (se 1 (by rfl) ⟨1278149, by rfl⟩ : syracuseStep 1704199 = 2556299) B2556299
theorem B1917199 : Blo 1512953 1917199 := bstep (se 1 (by rfl) ⟨1437899, by rfl⟩ : syracuseStep 1917199 = 2875799) B2875799
theorem B2457899 : Blo 1512953 2457899 := bstep (se 1 (by rfl) ⟨1843424, by rfl⟩ : syracuseStep 2457899 = 3686849) B3686849
theorem B3834155 : Blo 1512953 3834155 := bstep (se 1 (by rfl) ⟨2875616, by rfl⟩ : syracuseStep 3834155 = 5751233) B5751233
theorem B2269499 : Blo 1512953 2269499 := bstep (se 1 (by rfl) ⟨1702124, by rfl⟩ : syracuseStep 2269499 = 3404249) B3404249
theorem B12271931 : Blo 1512953 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B3686743 : Blo 1512953 3686743 := bstep (se 1 (by rfl) ⟨2765057, by rfl⟩ : syracuseStep 3686743 = 5530115) B5530115
theorem B5112179 : Blo 1512953 5112179 := bstep (se 1 (by rfl) ⟨3834134, by rfl⟩ : syracuseStep 5112179 = 7668269) B7668269
theorem B2269559 : Blo 1512953 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B3408263 : Blo 1512953 3408263 := bstep (se 1 (by rfl) ⟨2556197, by rfl⟩ : syracuseStep 3408263 = 5112395) B5112395
theorem B2269583 : Blo 1512953 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B1941931 : Blo 1512953 1941931 := bstep (se 1 (by rfl) ⟨1456448, by rfl⟩ : syracuseStep 1941931 = 2912897) B2912897
theorem B2269625 : Blo 1512953 2269625 := bstep (se 2 (by rfl) ⟨851109, by rfl⟩ : syracuseStep 2269625 = 1702219) B1702219
theorem B65462741 : Blo 1512953 65462741 := bstep (se 7 (by rfl) ⟨767141, by rfl⟩ : syracuseStep 65462741 = 1534283) B1534283
theorem B2269703 : Blo 1512953 2269703 := bstep (se 1 (by rfl) ⟨1702277, by rfl⟩ : syracuseStep 2269703 = 3404555) B3404555
theorem B2155015 : Blo 1512953 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B39338531 : Blo 1512953 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B2269739 : Blo 1512953 2269739 := bstep (se 1 (by rfl) ⟨1702304, by rfl⟩ : syracuseStep 2269739 = 3404609) B3404609
theorem B3408443 : Blo 1512953 3408443 := bstep (se 1 (by rfl) ⟨2556332, by rfl⟩ : syracuseStep 3408443 = 5112665) B5112665
theorem B2269769 : Blo 1512953 2269769 := bstep (se 2 (by rfl) ⟨851163, by rfl⟩ : syracuseStep 2269769 = 1702327) B1702327
theorem B2728595 : Blo 1512953 2728595 := bstep (se 1 (by rfl) ⟨2046446, by rfl⟩ : syracuseStep 2728595 = 4092893) B4092893
theorem B15966899 : Blo 1512953 15966899 := bstep (se 1 (by rfl) ⟨11975174, by rfl⟩ : syracuseStep 15966899 = 23950349) B23950349
theorem B3408569 : Blo 1512953 3408569 := bstep (se 2 (by rfl) ⟨1278213, by rfl⟩ : syracuseStep 3408569 = 2556427) B2556427
theorem B2269883 : Blo 1512953 2269883 := bstep (se 1 (by rfl) ⟨1702412, by rfl⟩ : syracuseStep 2269883 = 3404825) B3404825
theorem B2269943 : Blo 1512953 2269943 := bstep (se 1 (by rfl) ⟨1702457, by rfl⟩ : syracuseStep 2269943 = 3404915) B3404915
theorem B2269967 : Blo 1512953 2269967 := bstep (se 1 (by rfl) ⟨1702475, by rfl⟩ : syracuseStep 2269967 = 3404951) B3404951
theorem B2270009 : Blo 1512953 2270009 := bstep (se 2 (by rfl) ⟨851253, by rfl⟩ : syracuseStep 2270009 = 1702507) B1702507
theorem B2270087 : Blo 1512953 2270087 := bstep (se 1 (by rfl) ⟨1702565, by rfl⟩ : syracuseStep 2270087 = 3405131) B3405131
theorem B4850579 : Blo 1512953 4850579 := bstep (se 1 (by rfl) ⟨3637934, by rfl⟩ : syracuseStep 4850579 = 7275869) B7275869
theorem B2270123 : Blo 1512953 2270123 := bstep (se 1 (by rfl) ⟨1702592, by rfl⟩ : syracuseStep 2270123 = 3405185) B3405185
theorem B2270153 : Blo 1512953 2270153 := bstep (se 2 (by rfl) ⟨851307, by rfl⟩ : syracuseStep 2270153 = 1702615) B1702615
theorem B8627147 : Blo 1512953 8627147 := bstep (se 1 (by rfl) ⟨6470360, by rfl⟩ : syracuseStep 8627147 = 12940721) B12940721
theorem B2155511 : Blo 1512953 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B2458667 : Blo 1512953 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B2270267 : Blo 1512953 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B2270327 : Blo 1512953 2270327 := bstep (se 1 (by rfl) ⟨1702745, by rfl⟩ : syracuseStep 2270327 = 3405491) B3405491
theorem B2270351 : Blo 1512953 2270351 := bstep (se 1 (by rfl) ⟨1702763, by rfl⟩ : syracuseStep 2270351 = 3405527) B3405527
theorem B2270393 : Blo 1512953 2270393 := bstep (se 2 (by rfl) ⟨851397, by rfl⟩ : syracuseStep 2270393 = 1702795) B1702795
theorem B3884233 : Blo 1512953 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B2270471 : Blo 1512953 2270471 := bstep (se 1 (by rfl) ⟨1702853, by rfl⟩ : syracuseStep 2270471 = 3405707) B3405707
theorem B2270507 : Blo 1512953 2270507 := bstep (se 1 (by rfl) ⟨1702880, by rfl⟩ : syracuseStep 2270507 = 3405761) B3405761
theorem B2270537 : Blo 1512953 2270537 := bstep (se 2 (by rfl) ⟨851451, by rfl⟩ : syracuseStep 2270537 = 1702903) B1702903
theorem B13993361 : Blo 1512953 13993361 := bstep (se 2 (by rfl) ⟨5247510, by rfl⟩ : syracuseStep 13993361 = 10495021) B10495021
theorem B8299921 : Blo 1512953 8299921 := bstep (se 2 (by rfl) ⟨3112470, by rfl⟩ : syracuseStep 8299921 = 6224941) B6224941
theorem B2270651 : Blo 1512953 2270651 := bstep (se 1 (by rfl) ⟨1702988, by rfl⟩ : syracuseStep 2270651 = 3405977) B3405977
theorem B2270711 : Blo 1512953 2270711 := bstep (se 1 (by rfl) ⟨1703033, by rfl⟩ : syracuseStep 2270711 = 3406067) B3406067
theorem B2270735 : Blo 1512953 2270735 := bstep (se 1 (by rfl) ⟨1703051, by rfl⟩ : syracuseStep 2270735 = 3406103) B3406103
theorem B11503133 : Blo 1512953 11503133 := bstep (se 3 (by rfl) ⟨2156837, by rfl⟩ : syracuseStep 11503133 = 4313675) B4313675
theorem B2270777 : Blo 1512953 2270777 := bstep (se 2 (by rfl) ⟨851541, by rfl⟩ : syracuseStep 2270777 = 1703083) B1703083
theorem B2270855 : Blo 1512953 2270855 := bstep (se 1 (by rfl) ⟨1703141, by rfl⟩ : syracuseStep 2270855 = 3406283) B3406283
theorem B2270891 : Blo 1512953 2270891 := bstep (se 1 (by rfl) ⟨1703168, by rfl⟩ : syracuseStep 2270891 = 3406337) B3406337
theorem B2270921 : Blo 1512953 2270921 := bstep (se 2 (by rfl) ⟨851595, by rfl⟩ : syracuseStep 2270921 = 1703191) B1703191
theorem B2271035 : Blo 1512953 2271035 := bstep (se 1 (by rfl) ⟨1703276, by rfl⟩ : syracuseStep 2271035 = 3406553) B3406553
theorem B2271095 : Blo 1512953 2271095 := bstep (se 1 (by rfl) ⟨1703321, by rfl⟩ : syracuseStep 2271095 = 3406643) B3406643
theorem B2271119 : Blo 1512953 2271119 := bstep (se 1 (by rfl) ⟨1703339, by rfl⟩ : syracuseStep 2271119 = 3406679) B3406679
theorem B7661465 : Blo 1512953 7661465 := bstep (se 2 (by rfl) ⟨2873049, by rfl⟩ : syracuseStep 7661465 = 5746099) B5746099
theorem B24889241 : Blo 1512953 24889241 := bstep (se 2 (by rfl) ⟨9333465, by rfl⟩ : syracuseStep 24889241 = 18666931) B18666931
theorem B2271161 : Blo 1512953 2271161 := bstep (se 2 (by rfl) ⟨851685, by rfl⟩ : syracuseStep 2271161 = 1703371) B1703371
theorem B2156473 : Blo 1512953 2156473 := bstep (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) B1617355
theorem B2271239 : Blo 1512953 2271239 := bstep (se 1 (by rfl) ⟨1703429, by rfl⟩ : syracuseStep 2271239 = 3406859) B3406859
theorem B1533967 : Blo 1512953 1533967 := bstep (se 1 (by rfl) ⟨1150475, by rfl⟩ : syracuseStep 1533967 = 2300951) B2300951
theorem B2271275 : Blo 1512953 2271275 := bstep (se 1 (by rfl) ⟨1703456, by rfl⟩ : syracuseStep 2271275 = 3406913) B3406913
theorem B3688507 : Blo 1512953 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B2271305 : Blo 1512953 2271305 := bstep (se 2 (by rfl) ⟨851739, by rfl⟩ : syracuseStep 2271305 = 1703479) B1703479
theorem B3885175 : Blo 1512953 3885175 := bstep (se 1 (by rfl) ⟨2913881, by rfl⟩ : syracuseStep 3885175 = 5827763) B5827763
theorem B2271419 : Blo 1512953 2271419 := bstep (se 1 (by rfl) ⟨1703564, by rfl⟩ : syracuseStep 2271419 = 3407129) B3407129
theorem B3451081 : Blo 1512953 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B8407277 : Blo 1512953 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B2271479 : Blo 1512953 2271479 := bstep (se 1 (by rfl) ⟨1703609, by rfl⟩ : syracuseStep 2271479 = 3407219) B3407219
theorem B8620289 : Blo 1512953 8620289 := bstep (se 2 (by rfl) ⟨3232608, by rfl⟩ : syracuseStep 8620289 = 6465217) B6465217
theorem B2271503 : Blo 1512953 2271503 := bstep (se 1 (by rfl) ⟨1703627, by rfl⟩ : syracuseStep 2271503 = 3407255) B3407255
theorem B2156815 : Blo 1512953 2156815 := bstep (se 1 (by rfl) ⟨1617611, by rfl⟩ : syracuseStep 2156815 = 3235223) B3235223
theorem B2271545 : Blo 1512953 2271545 := bstep (se 2 (by rfl) ⟨851829, by rfl⟩ : syracuseStep 2271545 = 1703659) B1703659
theorem B6465851 : Blo 1512953 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B2271623 : Blo 1512953 2271623 := bstep (se 1 (by rfl) ⟨1703717, by rfl⟩ : syracuseStep 2271623 = 3407435) B3407435
theorem B4311443 : Blo 1512953 4311443 := bstep (se 1 (by rfl) ⟨3233582, by rfl⟩ : syracuseStep 4311443 = 6467165) B6467165
theorem B2271659 : Blo 1512953 2271659 := bstep (se 1 (by rfl) ⟨1703744, by rfl⟩ : syracuseStep 2271659 = 3407489) B3407489
theorem B2271689 : Blo 1512953 2271689 := bstep (se 2 (by rfl) ⟨851883, by rfl⟩ : syracuseStep 2271689 = 1703767) B1703767
theorem B2271803 : Blo 1512953 2271803 := bstep (se 1 (by rfl) ⟨1703852, by rfl⟩ : syracuseStep 2271803 = 3407705) B3407705
theorem B2271863 : Blo 1512953 2271863 := bstep (se 1 (by rfl) ⟨1703897, by rfl⟩ : syracuseStep 2271863 = 3407795) B3407795
theorem B2271887 : Blo 1512953 2271887 := bstep (se 1 (by rfl) ⟨1703915, by rfl⟩ : syracuseStep 2271887 = 3407831) B3407831
theorem B2271929 : Blo 1512953 2271929 := bstep (se 2 (by rfl) ⟨851973, by rfl⟩ : syracuseStep 2271929 = 1703947) B1703947
theorem B10914497 : Blo 1512953 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B2272007 : Blo 1512953 2272007 := bstep (se 1 (by rfl) ⟨1704005, by rfl⟩ : syracuseStep 2272007 = 3408011) B3408011
theorem B2272043 : Blo 1512953 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B5458747 : Blo 1512953 5458747 := bstep (se 1 (by rfl) ⟨4094060, by rfl⟩ : syracuseStep 5458747 = 8188121) B8188121
theorem B2272073 : Blo 1512953 2272073 := bstep (se 2 (by rfl) ⟨852027, by rfl⟩ : syracuseStep 2272073 = 1704055) B1704055
theorem B9202585 : Blo 1512953 9202585 := bstep (se 2 (by rfl) ⟨3450969, by rfl⟩ : syracuseStep 9202585 = 6901939) B6901939
theorem B5106617 : Blo 1512953 5106617 := bstep (se 2 (by rfl) ⟨1914981, by rfl⟩ : syracuseStep 5106617 = 3829963) B3829963
theorem B2272187 : Blo 1512953 2272187 := bstep (se 1 (by rfl) ⟨1704140, by rfl⟩ : syracuseStep 2272187 = 3408281) B3408281
theorem B2272247 : Blo 1512953 2272247 := bstep (se 1 (by rfl) ⟨1704185, by rfl⟩ : syracuseStep 2272247 = 3408371) B3408371
theorem B17255429 : Blo 1512953 17255429 := bstep (se 4 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 17255429 = 3235393) B3235393
theorem B2272271 : Blo 1512953 2272271 := bstep (se 1 (by rfl) ⟨1704203, by rfl⟩ : syracuseStep 2272271 = 3408407) B3408407
theorem B10914839 : Blo 1512953 10914839 := bstep (se 1 (by rfl) ⟨8186129, by rfl⟩ : syracuseStep 10914839 = 16372259) B16372259
theorem B2272313 : Blo 1512953 2272313 := bstep (se 2 (by rfl) ⟨852117, by rfl⟩ : syracuseStep 2272313 = 1704235) B1704235
theorem B2272391 : Blo 1512953 2272391 := bstep (se 1 (by rfl) ⟨1704293, by rfl⟩ : syracuseStep 2272391 = 3408587) B3408587
theorem B4312217 : Blo 1512953 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B2272427 : Blo 1512953 2272427 := bstep (se 1 (by rfl) ⟨1704320, by rfl⟩ : syracuseStep 2272427 = 3408641) B3408641
theorem B62115173 : Blo 1512953 62115173 := bstep (se 4 (by rfl) ⟨5823297, by rfl⟩ : syracuseStep 62115173 = 11646595) B11646595
theorem B4918681 : Blo 1512953 4918681 := bstep (se 2 (by rfl) ⟨1844505, by rfl⟩ : syracuseStep 4918681 = 3689011) B3689011
theorem B5107211 : Blo 1512953 5107211 := bstep (se 1 (by rfl) ⟨3830408, by rfl⟩ : syracuseStep 5107211 = 7660817) B7660817
theorem B12930637 : Blo 1512953 12930637 := bstep (se 3 (by rfl) ⟨2424494, by rfl⟩ : syracuseStep 12930637 = 4848989) B4848989
theorem B5107319 : Blo 1512953 5107319 := bstep (se 1 (by rfl) ⟨3830489, by rfl⟩ : syracuseStep 5107319 = 7660979) B7660979
theorem B7474889 : Blo 1512953 7474889 := bstep (se 2 (by rfl) ⟨2803083, by rfl⟩ : syracuseStep 7474889 = 5606167) B5606167
theorem B11489039 : Blo 1512953 11489039 := bstep (se 1 (by rfl) ⟨8616779, by rfl⟩ : syracuseStep 11489039 = 17233559) B17233559
theorem B8179471 : Blo 1512953 8179471 := bstep (se 1 (by rfl) ⟨6134603, by rfl⟩ : syracuseStep 8179471 = 12269207) B12269207
theorem B4091681 : Blo 1512953 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B5746585 : Blo 1512953 5746585 := bstep (se 2 (by rfl) ⟨2154969, by rfl⟩ : syracuseStep 5746585 = 4309939) B4309939
theorem B9211907 : Blo 1512953 9211907 := bstep (se 1 (by rfl) ⟨6908930, by rfl⟩ : syracuseStep 9211907 = 13817861) B13817861
theorem B9211927 : Blo 1512953 9211927 := bstep (se 1 (by rfl) ⟨6908945, by rfl⟩ : syracuseStep 9211927 = 13817891) B13817891
theorem B6467627 : Blo 1512953 6467627 := bstep (se 1 (by rfl) ⟨4850720, by rfl⟩ : syracuseStep 6467627 = 9701441) B9701441
theorem B15536261 : Blo 1512953 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B3829913 : Blo 1512953 3829913 := bstep (se 2 (by rfl) ⟨1436217, by rfl⟩ : syracuseStep 3829913 = 2872435) B2872435
theorem B5107913 : Blo 1512953 5107913 := bstep (se 2 (by rfl) ⟨1915467, by rfl⟩ : syracuseStep 5107913 = 3830935) B3830935
theorem B5746889 : Blo 1512953 5746889 := bstep (se 2 (by rfl) ⟨2155083, by rfl⟩ : syracuseStep 5746889 = 4310167) B4310167
theorem B2912527 : Blo 1512953 2912527 := bstep (se 1 (by rfl) ⟨2184395, by rfl⟩ : syracuseStep 2912527 = 4368791) B4368791
theorem B3830075 : Blo 1512953 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B11497787 : Blo 1512953 11497787 := bstep (se 1 (by rfl) ⟨8623340, by rfl⟩ : syracuseStep 11497787 = 17246681) B17246681
theorem B7664057 : Blo 1512953 7664057 := bstep (se 2 (by rfl) ⟨2874021, by rfl⟩ : syracuseStep 7664057 = 5748043) B5748043
theorem B8622521 : Blo 1512953 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B9703901 : Blo 1512953 9703901 := bstep (se 3 (by rfl) ⟨1819481, by rfl⟩ : syracuseStep 9703901 = 3638963) B3638963
theorem B3404303 : Blo 1512953 3404303 := bstep (se 1 (by rfl) ⟨2553227, by rfl⟩ : syracuseStep 3404303 = 5106455) B5106455
theorem B3830287 : Blo 1512953 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B3404321 : Blo 1512953 3404321 := bstep (se 2 (by rfl) ⟨1276620, by rfl⟩ : syracuseStep 3404321 = 2553241) B2553241
theorem B3830561 : Blo 1512953 3830561 := bstep (se 2 (by rfl) ⟨1436460, by rfl⟩ : syracuseStep 3830561 = 2872921) B2872921
theorem B29086553 : Blo 1512953 29086553 := bstep (se 2 (by rfl) ⟨10907457, by rfl⟩ : syracuseStep 29086553 = 21814915) B21814915
theorem B3404663 : Blo 1512953 3404663 := bstep (se 1 (by rfl) ⟨2553497, by rfl⟩ : syracuseStep 3404663 = 5106995) B5106995
theorem B5108615 : Blo 1512953 5108615 := bstep (se 1 (by rfl) ⟨3831461, by rfl⟩ : syracuseStep 5108615 = 7662923) B7662923
theorem B87274421 : Blo 1512953 87274421 := bstep (se 5 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 87274421 = 8181977) B8181977
theorem B3404843 : Blo 1512953 3404843 := bstep (se 1 (by rfl) ⟨2553632, by rfl⟩ : syracuseStep 3404843 = 5107265) B5107265
theorem B5747831 : Blo 1512953 5747831 := bstep (se 1 (by rfl) ⟨4310873, by rfl⟩ : syracuseStep 5747831 = 8621747) B8621747
theorem B7279789 : Blo 1512953 7279789 := bstep (se 3 (by rfl) ⟨1364960, by rfl⟩ : syracuseStep 7279789 = 2729921) B2729921
theorem B14554349 : Blo 1512953 14554349 := bstep (se 3 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 14554349 = 5457881) B5457881
theorem B5108993 : Blo 1512953 5108993 := bstep (se 2 (by rfl) ⟨1915872, by rfl⟩ : syracuseStep 5108993 = 3831745) B3831745
theorem B3405203 : Blo 1512953 3405203 := bstep (se 1 (by rfl) ⟨2553902, by rfl⟩ : syracuseStep 3405203 = 5107805) B5107805
theorem B3405257 : Blo 1512953 3405257 := bstep (se 2 (by rfl) ⟨1276971, by rfl⟩ : syracuseStep 3405257 = 2553943) B2553943
theorem B1512967 : Blo 1512953 1512967 := bstep (se 1 (by rfl) ⟨1134725, by rfl⟩ : syracuseStep 1512967 = 2269451) B2269451
theorem B1512975 : Blo 1512953 1512975 := bstep (se 1 (by rfl) ⟨1134731, by rfl⟩ : syracuseStep 1512975 = 2269463) B2269463
theorem B1513019 : Blo 1512953 1513019 := bstep (se 1 (by rfl) ⟨1134764, by rfl⟩ : syracuseStep 1513019 = 2269529) B2269529
theorem B2553403 : Blo 1512953 2553403 := bstep (se 1 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 2553403 = 3830105) B3830105
theorem B1513095 : Blo 1512953 1513095 := bstep (se 1 (by rfl) ⟨1134821, by rfl⟩ : syracuseStep 1513095 = 2269643) B2269643
theorem B1513103 : Blo 1512953 1513103 := bstep (se 1 (by rfl) ⟨1134827, by rfl⟩ : syracuseStep 1513103 = 2269655) B2269655
theorem B1513147 : Blo 1512953 1513147 := bstep (se 1 (by rfl) ⟨1134860, by rfl⟩ : syracuseStep 1513147 = 2269721) B2269721
theorem B2553545 : Blo 1512953 2553545 := bstep (se 2 (by rfl) ⟨957579, by rfl⟩ : syracuseStep 2553545 = 1915159) B1915159
theorem B7665353 : Blo 1512953 7665353 := bstep (se 2 (by rfl) ⟨2874507, by rfl⟩ : syracuseStep 7665353 = 5749015) B5749015
theorem B15546113 : Blo 1512953 15546113 := bstep (se 2 (by rfl) ⟨5829792, by rfl⟩ : syracuseStep 15546113 = 11659585) B11659585
theorem B1513223 : Blo 1512953 1513223 := bstep (se 1 (by rfl) ⟨1134917, by rfl⟩ : syracuseStep 1513223 = 2269835) B2269835
theorem B3831563 : Blo 1512953 3831563 := bstep (se 1 (by rfl) ⟨2873672, by rfl⟩ : syracuseStep 3831563 = 5747345) B5747345
theorem B1513231 : Blo 1512953 1513231 := bstep (se 1 (by rfl) ⟨1134923, by rfl⟩ : syracuseStep 1513231 = 2269847) B2269847
theorem B8189747 : Blo 1512953 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B1513275 : Blo 1512953 1513275 := bstep (se 1 (by rfl) ⟨1134956, by rfl⟩ : syracuseStep 1513275 = 2269913) B2269913
theorem B1513351 : Blo 1512953 1513351 := bstep (se 1 (by rfl) ⟨1135013, by rfl⟩ : syracuseStep 1513351 = 2270027) B2270027
theorem B1513359 : Blo 1512953 1513359 := bstep (se 1 (by rfl) ⟨1135019, by rfl⟩ : syracuseStep 1513359 = 2270039) B2270039
theorem B1513403 : Blo 1512953 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B1513479 : Blo 1512953 1513479 := bstep (se 1 (by rfl) ⟨1135109, by rfl⟩ : syracuseStep 1513479 = 2270219) B2270219
theorem B10917899 : Blo 1512953 10917899 := bstep (se 1 (by rfl) ⟨8188424, by rfl⟩ : syracuseStep 10917899 = 16376849) B16376849
theorem B1513487 : Blo 1512953 1513487 := bstep (se 1 (by rfl) ⟨1135115, by rfl⟩ : syracuseStep 1513487 = 2270231) B2270231
theorem B7764011 : Blo 1512953 7764011 := bstep (se 1 (by rfl) ⟨5823008, by rfl⟩ : syracuseStep 7764011 = 11646017) B11646017
theorem B5109803 : Blo 1512953 5109803 := bstep (se 1 (by rfl) ⟨3832352, by rfl⟩ : syracuseStep 5109803 = 7664705) B7664705
theorem B1513531 : Blo 1512953 1513531 := bstep (se 1 (by rfl) ⟨1135148, by rfl⟩ : syracuseStep 1513531 = 2270297) B2270297
theorem B5748803 : Blo 1512953 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B4094039 : Blo 1512953 4094039 := bstep (se 1 (by rfl) ⟨3070529, by rfl⟩ : syracuseStep 4094039 = 6141059) B6141059
theorem B1513607 : Blo 1512953 1513607 := bstep (se 1 (by rfl) ⟨1135205, by rfl⟩ : syracuseStep 1513607 = 2270411) B2270411
theorem B3405959 : Blo 1512953 3405959 := bstep (se 1 (by rfl) ⟨2554469, by rfl⟩ : syracuseStep 3405959 = 5108939) B5108939
theorem B1513615 : Blo 1512953 1513615 := bstep (se 1 (by rfl) ⟨1135211, by rfl⟩ : syracuseStep 1513615 = 2270423) B2270423
theorem B1702075 : Blo 1512953 1702075 := bstep (se 1 (by rfl) ⟨1276556, by rfl⟩ : syracuseStep 1702075 = 2553113) B2553113
theorem B1513659 : Blo 1512953 1513659 := bstep (se 1 (by rfl) ⟨1135244, by rfl⟩ : syracuseStep 1513659 = 2270489) B2270489
theorem B1513735 : Blo 1512953 1513735 := bstep (se 1 (by rfl) ⟨1135301, by rfl⟩ : syracuseStep 1513735 = 2270603) B2270603
theorem B1513743 : Blo 1512953 1513743 := bstep (se 1 (by rfl) ⟨1135307, by rfl⟩ : syracuseStep 1513743 = 2270615) B2270615
theorem B1726735 : Blo 1512953 1726735 := bstep (se 1 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 1726735 = 2590103) B2590103
theorem B1513787 : Blo 1512953 1513787 := bstep (se 1 (by rfl) ⟨1135340, by rfl⟩ : syracuseStep 1513787 = 2270681) B2270681
theorem B3406139 : Blo 1512953 3406139 := bstep (se 1 (by rfl) ⟨2554604, by rfl⟩ : syracuseStep 3406139 = 5109209) B5109209
theorem B1915255 : Blo 1512953 1915255 := bstep (se 1 (by rfl) ⟨1436441, by rfl⟩ : syracuseStep 1915255 = 2872883) B2872883
theorem B7879027 : Blo 1512953 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B2554247 : Blo 1512953 2554247 := bstep (se 1 (by rfl) ⟨1915685, by rfl⟩ : syracuseStep 2554247 = 3831371) B3831371
theorem B1513863 : Blo 1512953 1513863 := bstep (se 1 (by rfl) ⟨1135397, by rfl⟩ : syracuseStep 1513863 = 2270795) B2270795
theorem B1513871 : Blo 1512953 1513871 := bstep (se 1 (by rfl) ⟨1135403, by rfl⟩ : syracuseStep 1513871 = 2270807) B2270807
theorem B3832211 : Blo 1512953 3832211 := bstep (se 1 (by rfl) ⟨2874158, by rfl⟩ : syracuseStep 3832211 = 5748317) B5748317
theorem B3406265 : Blo 1512953 3406265 := bstep (se 2 (by rfl) ⟨1277349, by rfl⟩ : syracuseStep 3406265 = 2554699) B2554699
theorem B1513915 : Blo 1512953 1513915 := bstep (se 1 (by rfl) ⟨1135436, by rfl⟩ : syracuseStep 1513915 = 2270873) B2270873
theorem B1513991 : Blo 1512953 1513991 := bstep (se 1 (by rfl) ⟨1135493, by rfl⟩ : syracuseStep 1513991 = 2270987) B2270987
theorem B1513999 : Blo 1512953 1513999 := bstep (se 1 (by rfl) ⟨1135499, by rfl⟩ : syracuseStep 1513999 = 2270999) B2270999
theorem B8624663 : Blo 1512953 8624663 := bstep (se 1 (by rfl) ⟨6468497, by rfl⟩ : syracuseStep 8624663 = 12936995) B12936995
theorem B9706027 : Blo 1512953 9706027 := bstep (se 1 (by rfl) ⟨7279520, by rfl⟩ : syracuseStep 9706027 = 14559041) B14559041
theorem B1514043 : Blo 1512953 1514043 := bstep (se 1 (by rfl) ⟨1135532, by rfl⟩ : syracuseStep 1514043 = 2271065) B2271065
theorem B1514119 : Blo 1512953 1514119 := bstep (se 1 (by rfl) ⟨1135589, by rfl⟩ : syracuseStep 1514119 = 2271179) B2271179
theorem B1702543 : Blo 1512953 1702543 := bstep (se 1 (by rfl) ⟨1276907, by rfl⟩ : syracuseStep 1702543 = 2553815) B2553815
theorem B1514127 : Blo 1512953 1514127 := bstep (se 1 (by rfl) ⟨1135595, by rfl⟩ : syracuseStep 1514127 = 2271191) B2271191
theorem B3832505 : Blo 1512953 3832505 := bstep (se 2 (by rfl) ⟨1437189, by rfl⟩ : syracuseStep 3832505 = 2874379) B2874379
theorem B1915579 : Blo 1512953 1915579 := bstep (se 1 (by rfl) ⟨1436684, by rfl⟩ : syracuseStep 1915579 = 2873369) B2873369
theorem B1514171 : Blo 1512953 1514171 := bstep (se 1 (by rfl) ⟨1135628, by rfl⟩ : syracuseStep 1514171 = 2271257) B2271257
theorem B3234505 : Blo 1512953 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B1514247 : Blo 1512953 1514247 := bstep (se 1 (by rfl) ⟨1135685, by rfl⟩ : syracuseStep 1514247 = 2271371) B2271371
theorem B3406607 : Blo 1512953 3406607 := bstep (se 1 (by rfl) ⟨2554955, by rfl⟩ : syracuseStep 3406607 = 5109911) B5109911
theorem B1514255 : Blo 1512953 1514255 := bstep (se 1 (by rfl) ⟨1135691, by rfl⟩ : syracuseStep 1514255 = 2271383) B2271383
theorem B3406625 : Blo 1512953 3406625 := bstep (se 2 (by rfl) ⟨1277484, by rfl⟩ : syracuseStep 3406625 = 2554969) B2554969
theorem B1514299 : Blo 1512953 1514299 := bstep (se 1 (by rfl) ⟨1135724, by rfl⟩ : syracuseStep 1514299 = 2271449) B2271449
theorem B7773043 : Blo 1512953 7773043 := bstep (se 1 (by rfl) ⟨5829782, by rfl⟩ : syracuseStep 7773043 = 11659565) B11659565
theorem B1514375 : Blo 1512953 1514375 := bstep (se 1 (by rfl) ⟨1135781, by rfl⟩ : syracuseStep 1514375 = 2271563) B2271563
theorem B1514383 : Blo 1512953 1514383 := bstep (se 1 (by rfl) ⟨1135787, by rfl⟩ : syracuseStep 1514383 = 2271575) B2271575
theorem B4848569 : Blo 1512953 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B1514427 : Blo 1512953 1514427 := bstep (se 1 (by rfl) ⟨1135820, by rfl⟩ : syracuseStep 1514427 = 2271641) B2271641
theorem B1514503 : Blo 1512953 1514503 := bstep (se 1 (by rfl) ⟨1135877, by rfl⟩ : syracuseStep 1514503 = 2271755) B2271755
theorem B8625163 : Blo 1512953 8625163 := bstep (se 1 (by rfl) ⟨6468872, by rfl⟩ : syracuseStep 8625163 = 12937745) B12937745
theorem B2554895 : Blo 1512953 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B1514511 : Blo 1512953 1514511 := bstep (se 1 (by rfl) ⟨1135883, by rfl⟩ : syracuseStep 1514511 = 2271767) B2271767
theorem B1514555 : Blo 1512953 1514555 := bstep (se 1 (by rfl) ⟨1135916, by rfl⟩ : syracuseStep 1514555 = 2271833) B2271833
theorem B26205245 : Blo 1512953 26205245 := bstep (se 3 (by rfl) ⟨4913483, by rfl⟩ : syracuseStep 26205245 = 9826967) B9826967
theorem B10910807 : Blo 1512953 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B3406967 : Blo 1512953 3406967 := bstep (se 1 (by rfl) ⟨2555225, by rfl⟩ : syracuseStep 3406967 = 5110451) B5110451
theorem B3636359 : Blo 1512953 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B1703047 : Blo 1512953 1703047 := bstep (se 1 (by rfl) ⟨1277285, by rfl⟩ : syracuseStep 1703047 = 2554571) B2554571
theorem B1514631 : Blo 1512953 1514631 := bstep (se 1 (by rfl) ⟨1135973, by rfl⟩ : syracuseStep 1514631 = 2271947) B2271947
theorem B1514639 : Blo 1512953 1514639 := bstep (se 1 (by rfl) ⟨1135979, by rfl⟩ : syracuseStep 1514639 = 2271959) B2271959
theorem B1916075 : Blo 1512953 1916075 := bstep (se 1 (by rfl) ⟨1437056, by rfl⟩ : syracuseStep 1916075 = 2874113) B2874113
theorem B1514683 : Blo 1512953 1514683 := bstep (se 1 (by rfl) ⟨1136012, by rfl⟩ : syracuseStep 1514683 = 2272025) B2272025
theorem B1514759 : Blo 1512953 1514759 := bstep (se 1 (by rfl) ⟨1136069, by rfl⟩ : syracuseStep 1514759 = 2272139) B2272139
theorem B1514767 : Blo 1512953 1514767 := bstep (se 1 (by rfl) ⟨1136075, by rfl⟩ : syracuseStep 1514767 = 2272151) B2272151
theorem B2727211 : Blo 1512953 2727211 := bstep (se 1 (by rfl) ⟨2045408, by rfl⟩ : syracuseStep 2727211 = 4090817) B4090817
theorem B3407147 : Blo 1512953 3407147 := bstep (se 1 (by rfl) ⟨2555360, by rfl⟩ : syracuseStep 3407147 = 5110721) B5110721
theorem B1703227 : Blo 1512953 1703227 := bstep (se 1 (by rfl) ⟨1277420, by rfl⟩ : syracuseStep 1703227 = 2554841) B2554841
theorem B2874683 : Blo 1512953 2874683 := bstep (se 1 (by rfl) ⟨2156012, by rfl⟩ : syracuseStep 2874683 = 4312025) B4312025
theorem B5111099 : Blo 1512953 5111099 := bstep (se 1 (by rfl) ⟨3833324, by rfl⟩ : syracuseStep 5111099 = 7666649) B7666649
theorem B1514811 : Blo 1512953 1514811 := bstep (se 1 (by rfl) ⟨1136108, by rfl⟩ : syracuseStep 1514811 = 2272217) B2272217
theorem B31096163 : Blo 1512953 31096163 := bstep (se 1 (by rfl) ⟨23322122, by rfl⟩ : syracuseStep 31096163 = 46644245) B46644245
theorem B3833203 : Blo 1512953 3833203 := bstep (se 1 (by rfl) ⟨2874902, by rfl⟩ : syracuseStep 3833203 = 5749805) B5749805
theorem B2661751 : Blo 1512953 2661751 := bstep (se 1 (by rfl) ⟨1996313, by rfl⟩ : syracuseStep 2661751 = 3992627) B3992627
theorem B1514887 : Blo 1512953 1514887 := bstep (se 1 (by rfl) ⟨1136165, by rfl⟩ : syracuseStep 1514887 = 2272331) B2272331
theorem B1514895 : Blo 1512953 1514895 := bstep (se 1 (by rfl) ⟨1136171, by rfl⟩ : syracuseStep 1514895 = 2272343) B2272343
theorem B1514939 : Blo 1512953 1514939 := bstep (se 1 (by rfl) ⟨1136204, by rfl⟩ : syracuseStep 1514939 = 2272409) B2272409
theorem B4308481 : Blo 1512953 4308481 := bstep (se 2 (by rfl) ⟨1615680, by rfl⟩ : syracuseStep 4308481 = 3231361) B3231361
theorem B3833345 : Blo 1512953 3833345 := bstep (se 2 (by rfl) ⟨1437504, by rfl⟩ : syracuseStep 3833345 = 2875009) B2875009
theorem B2424335 : Blo 1512953 2424335 := bstep (se 1 (by rfl) ⟨1818251, by rfl⟩ : syracuseStep 2424335 = 3636503) B3636503
theorem B2555435 : Blo 1512953 2555435 := bstep (se 1 (by rfl) ⟨1916576, by rfl⟩ : syracuseStep 2555435 = 3833153) B3833153
theorem B1916551 : Blo 1512953 1916551 := bstep (se 1 (by rfl) ⟨1437413, by rfl⟩ : syracuseStep 1916551 = 2874827) B2874827
theorem B3407507 : Blo 1512953 3407507 := bstep (se 1 (by rfl) ⟨2555630, by rfl⟩ : syracuseStep 3407507 = 5111261) B5111261
theorem B3407561 : Blo 1512953 3407561 := bstep (se 2 (by rfl) ⟨1277835, by rfl⟩ : syracuseStep 3407561 = 2555671) B2555671
theorem B5750473 : Blo 1512953 5750473 := bstep (se 2 (by rfl) ⟨2156427, by rfl⟩ : syracuseStep 5750473 = 4312855) B4312855
theorem B13811471 : Blo 1512953 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B1703695 : Blo 1512953 1703695 := bstep (se 1 (by rfl) ⟨1277771, by rfl⟩ : syracuseStep 1703695 = 2555543) B2555543
theorem B2875169 : Blo 1512953 2875169 := bstep (se 2 (by rfl) ⟨1078188, by rfl⟩ : syracuseStep 2875169 = 2156377) B2156377
theorem B5111585 : Blo 1512953 5111585 := bstep (se 2 (by rfl) ⟨1916844, by rfl⟩ : syracuseStep 5111585 = 3833689) B3833689
theorem B5824315 : Blo 1512953 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B1818487 : Blo 1512953 1818487 := bstep (se 1 (by rfl) ⟨1363865, by rfl⟩ : syracuseStep 1818487 = 2727731) B2727731
theorem B8617873 : Blo 1512953 8617873 := bstep (se 2 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 8617873 = 6463405) B6463405
theorem B2555833 : Blo 1512953 2555833 := bstep (se 2 (by rfl) ⟨958437, by rfl⟩ : syracuseStep 2555833 = 1916875) B1916875
theorem B3833801 : Blo 1512953 3833801 := bstep (se 2 (by rfl) ⟨1437675, by rfl⟩ : syracuseStep 3833801 = 2875351) B2875351
theorem B2588681 : Blo 1512953 2588681 := bstep (se 2 (by rfl) ⟨970755, by rfl⟩ : syracuseStep 2588681 = 1941511) B1941511
theorem B11493413 : Blo 1512953 11493413 := bstep (se 4 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 11493413 = 2155015) B2155015
theorem B4915279 : Blo 1512953 4915279 := bstep (se 1 (by rfl) ⟨3686459, by rfl⟩ : syracuseStep 4915279 = 7372919) B7372919
theorem B1638599 : Blo 1512953 1638599 := bstep (se 1 (by rfl) ⟨1228949, by rfl⟩ : syracuseStep 1638599 = 2457899) B2457899
theorem B2556103 : Blo 1512953 2556103 := bstep (se 1 (by rfl) ⟨1917077, by rfl⟩ : syracuseStep 2556103 = 3834155) B3834155
theorem B3408119 : Blo 1512953 3408119 := bstep (se 1 (by rfl) ⟨2556089, by rfl⟩ : syracuseStep 3408119 = 5112179) B5112179
theorem B2269433 : Blo 1512953 2269433 := bstep (se 2 (by rfl) ⟨851037, by rfl⟩ : syracuseStep 2269433 = 1702075) B1702075
theorem B5112125 : Blo 1512953 5112125 := bstep (se 3 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 5112125 = 1917047) B1917047
theorem B2269535 : Blo 1512953 2269535 := bstep (se 1 (by rfl) ⟨1702151, by rfl⟩ : syracuseStep 2269535 = 3404303) B3404303
theorem B2302313 : Blo 1512953 2302313 := bstep (se 2 (by rfl) ⟨863367, by rfl⟩ : syracuseStep 2302313 = 1726735) B1726735
theorem B2875753 : Blo 1512953 2875753 := bstep (se 2 (by rfl) ⟨1078407, by rfl⟩ : syracuseStep 2875753 = 2156815) B2156815
theorem B2269547 : Blo 1512953 2269547 := bstep (se 1 (by rfl) ⟨1702160, by rfl⟩ : syracuseStep 2269547 = 3404321) B3404321
theorem B2556265 : Blo 1512953 2556265 := bstep (se 2 (by rfl) ⟨958599, by rfl⟩ : syracuseStep 2556265 = 1917199) B1917199
theorem B1819063 : Blo 1512953 1819063 := bstep (se 1 (by rfl) ⟨1364297, by rfl⟩ : syracuseStep 1819063 = 2728595) B2728595
theorem B4915657 : Blo 1512953 4915657 := bstep (se 2 (by rfl) ⟨1843371, by rfl⟩ : syracuseStep 4915657 = 3686743) B3686743
theorem B2589241 : Blo 1512953 2589241 := bstep (se 2 (by rfl) ⟨970965, by rfl⟩ : syracuseStep 2589241 = 1941931) B1941931
theorem B19391035 : Blo 1512953 19391035 := bstep (se 1 (by rfl) ⟨14543276, by rfl⟩ : syracuseStep 19391035 = 29086553) B29086553
theorem B2269775 : Blo 1512953 2269775 := bstep (se 1 (by rfl) ⟨1702331, by rfl⟩ : syracuseStep 2269775 = 3404663) B3404663
theorem B5751431 : Blo 1512953 5751431 := bstep (se 1 (by rfl) ⟨4313573, by rfl⟩ : syracuseStep 5751431 = 8627147) B8627147
theorem B2269895 : Blo 1512953 2269895 := bstep (se 1 (by rfl) ⟨1702421, by rfl⟩ : syracuseStep 2269895 = 3404843) B3404843
theorem B1639111 : Blo 1512953 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B2270057 : Blo 1512953 2270057 := bstep (se 2 (by rfl) ⟨851271, by rfl⟩ : syracuseStep 2270057 = 1702543) B1702543
theorem B2270135 : Blo 1512953 2270135 := bstep (se 1 (by rfl) ⟨1702601, by rfl⟩ : syracuseStep 2270135 = 3405203) B3405203
theorem B2270171 : Blo 1512953 2270171 := bstep (se 1 (by rfl) ⟨1702628, by rfl⟩ : syracuseStep 2270171 = 3405257) B3405257
theorem B7668755 : Blo 1512953 7668755 := bstep (se 1 (by rfl) ⟨5751566, by rfl⟩ : syracuseStep 7668755 = 11503133) B11503133
theorem B10364057 : Blo 1512953 10364057 := bstep (se 2 (by rfl) ⟨3886521, by rfl⟩ : syracuseStep 10364057 = 7773043) B7773043
theorem B10364075 : Blo 1512953 10364075 := bstep (se 1 (by rfl) ⟨7773056, by rfl⟩ : syracuseStep 10364075 = 15546113) B15546113
theorem B6464893 : Blo 1512953 6464893 := bstep (se 3 (by rfl) ⟨1212167, by rfl⟩ : syracuseStep 6464893 = 2424335) B2424335
theorem B2729359 : Blo 1512953 2729359 := bstep (se 1 (by rfl) ⟨2047019, by rfl⟩ : syracuseStep 2729359 = 4094039) B4094039
theorem B15533477 : Blo 1512953 15533477 := bstep (se 4 (by rfl) ⟨1456263, by rfl⟩ : syracuseStep 15533477 = 2912527) B2912527
theorem B2270639 : Blo 1512953 2270639 := bstep (se 1 (by rfl) ⟨1702979, by rfl⟩ : syracuseStep 2270639 = 3405959) B3405959
theorem B5604851 : Blo 1512953 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B2270729 : Blo 1512953 2270729 := bstep (se 2 (by rfl) ⟨851523, by rfl⟩ : syracuseStep 2270729 = 1703047) B1703047
theorem B4310567 : Blo 1512953 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B2270759 : Blo 1512953 2270759 := bstep (se 1 (by rfl) ⟨1703069, by rfl⟩ : syracuseStep 2270759 = 3406139) B3406139
theorem B5178977 : Blo 1512953 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B2270843 : Blo 1512953 2270843 := bstep (se 1 (by rfl) ⟨1703132, by rfl⟩ : syracuseStep 2270843 = 3406265) B3406265
theorem B2270969 : Blo 1512953 2270969 := bstep (se 2 (by rfl) ⟨851613, by rfl⟩ : syracuseStep 2270969 = 1703227) B1703227
theorem B7276331 : Blo 1512953 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B2271071 : Blo 1512953 2271071 := bstep (se 1 (by rfl) ⟨1703303, by rfl⟩ : syracuseStep 2271071 = 3406607) B3406607
theorem B2271083 : Blo 1512953 2271083 := bstep (se 1 (by rfl) ⟨1703312, by rfl⟩ : syracuseStep 2271083 = 3406625) B3406625
theorem B19933037 : Blo 1512953 19933037 := bstep (se 3 (by rfl) ⟨3737444, by rfl⟩ : syracuseStep 19933037 = 7474889) B7474889
theorem B5744641 : Blo 1512953 5744641 := bstep (se 2 (by rfl) ⟨2154240, by rfl⟩ : syracuseStep 5744641 = 4308481) B4308481
theorem B11503619 : Blo 1512953 11503619 := bstep (se 1 (by rfl) ⟨8627714, by rfl⟩ : syracuseStep 11503619 = 17255429) B17255429
theorem B7276559 : Blo 1512953 7276559 := bstep (se 1 (by rfl) ⟨5457419, by rfl⟩ : syracuseStep 7276559 = 10914839) B10914839
theorem B2271311 : Blo 1512953 2271311 := bstep (se 1 (by rfl) ⟨1703483, by rfl⟩ : syracuseStep 2271311 = 3406967) B3406967
theorem B2271431 : Blo 1512953 2271431 := bstep (se 1 (by rfl) ⟨1703573, by rfl⟩ : syracuseStep 2271431 = 3407147) B3407147
theorem B10905961 : Blo 1512953 10905961 := bstep (se 2 (by rfl) ⟨4089735, by rfl⟩ : syracuseStep 10905961 = 8179471) B8179471
theorem B2271593 : Blo 1512953 2271593 := bstep (se 2 (by rfl) ⟨851847, by rfl⟩ : syracuseStep 2271593 = 1703695) B1703695
theorem B2271671 : Blo 1512953 2271671 := bstep (se 1 (by rfl) ⟨1703753, by rfl⟩ : syracuseStep 2271671 = 3407507) B3407507
theorem B2271707 : Blo 1512953 2271707 := bstep (se 1 (by rfl) ⟨1703780, by rfl⟩ : syracuseStep 2271707 = 3407561) B3407561
theorem B7662113 : Blo 1512953 7662113 := bstep (se 2 (by rfl) ⟨2873292, by rfl⟩ : syracuseStep 7662113 = 5746585) B5746585
theorem B4311751 : Blo 1512953 4311751 := bstep (se 1 (by rfl) ⟨3233813, by rfl⟩ : syracuseStep 4311751 = 6467627) B6467627
theorem B12282569 : Blo 1512953 12282569 := bstep (se 2 (by rfl) ⟨4605963, by rfl⟩ : syracuseStep 12282569 = 9211927) B9211927
theorem B5745401 : Blo 1512953 5745401 := bstep (se 2 (by rfl) ⟨2154525, by rfl⟩ : syracuseStep 5745401 = 4309051) B4309051
theorem B4918009 : Blo 1512953 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B10357507 : Blo 1512953 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B5180233 : Blo 1512953 5180233 := bstep (se 2 (by rfl) ⟨1942587, by rfl⟩ : syracuseStep 5180233 = 3885175) B3885175
theorem B2272175 : Blo 1512953 2272175 := bstep (se 1 (by rfl) ⟨1704131, by rfl⟩ : syracuseStep 2272175 = 3408263) B3408263
theorem B43641827 : Blo 1512953 43641827 := bstep (se 1 (by rfl) ⟨32731370, by rfl⟩ : syracuseStep 43641827 = 65462741) B65462741
theorem B2272265 : Blo 1512953 2272265 := bstep (se 2 (by rfl) ⟨852099, by rfl⟩ : syracuseStep 2272265 = 1704199) B1704199
theorem B26225687 : Blo 1512953 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B2272295 : Blo 1512953 2272295 := bstep (se 1 (by rfl) ⟨1704221, by rfl⟩ : syracuseStep 2272295 = 3408443) B3408443
theorem B10644599 : Blo 1512953 10644599 := bstep (se 1 (by rfl) ⟨7983449, by rfl⟩ : syracuseStep 10644599 = 15966899) B15966899
theorem B2272379 : Blo 1512953 2272379 := bstep (se 1 (by rfl) ⟨1704284, by rfl⟩ : syracuseStep 2272379 = 3408569) B3408569
theorem B10505369 : Blo 1512953 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B58182947 : Blo 1512953 58182947 := bstep (se 1 (by rfl) ⟨43637210, by rfl⟩ : syracuseStep 58182947 = 87274421) B87274421
theorem B5107049 : Blo 1512953 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B9702899 : Blo 1512953 9702899 := bstep (se 1 (by rfl) ⟨7277174, by rfl⟩ : syracuseStep 9702899 = 14554349) B14554349
theorem B4312673 : Blo 1512953 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B7278329 : Blo 1512953 7278329 := bstep (se 2 (by rfl) ⟨2729373, by rfl⟩ : syracuseStep 7278329 = 5458747) B5458747
theorem B5459831 : Blo 1512953 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B5107643 : Blo 1512953 5107643 := bstep (se 1 (by rfl) ⟨3830732, by rfl⟩ : syracuseStep 5107643 = 7661465) B7661465
theorem B7278599 : Blo 1512953 7278599 := bstep (se 1 (by rfl) ⟨5458949, by rfl⟩ : syracuseStep 7278599 = 10917899) B10917899
theorem B5746859 : Blo 1512953 5746859 := bstep (se 1 (by rfl) ⟨4310144, by rfl⟩ : syracuseStep 5746859 = 8620289) B8620289
theorem B6558241 : Blo 1512953 6558241 := bstep (se 2 (by rfl) ⟨2459340, by rfl⟩ : syracuseStep 6558241 = 4918681) B4918681
theorem B3404411 : Blo 1512953 3404411 := bstep (se 1 (by rfl) ⟨2553308, by rfl⟩ : syracuseStep 3404411 = 5106617) B5106617
theorem B3232379 : Blo 1512953 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B17470163 : Blo 1512953 17470163 := bstep (se 1 (by rfl) ⟨13102622, by rfl⟩ : syracuseStep 17470163 = 26205245) B26205245
theorem B3404537 : Blo 1512953 3404537 := bstep (se 2 (by rfl) ⟨1276701, by rfl⟩ : syracuseStep 3404537 = 2553403) B2553403
theorem B17240849 : Blo 1512953 17240849 := bstep (se 2 (by rfl) ⟨6465318, by rfl⟩ : syracuseStep 17240849 = 12930637) B12930637
theorem B20730775 : Blo 1512953 20730775 := bstep (se 1 (by rfl) ⟨15548081, by rfl⟩ : syracuseStep 20730775 = 31096163) B31096163
theorem B3404807 : Blo 1512953 3404807 := bstep (se 1 (by rfl) ⟨2553605, by rfl⟩ : syracuseStep 3404807 = 5107211) B5107211
theorem B3404879 : Blo 1512953 3404879 := bstep (se 1 (by rfl) ⟨2553659, by rfl⟩ : syracuseStep 3404879 = 5107319) B5107319
theorem B11490497 : Blo 1512953 11490497 := bstep (se 2 (by rfl) ⟨4308936, by rfl⟩ : syracuseStep 11490497 = 8617873) B8617873
theorem B5748029 : Blo 1512953 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B6141271 : Blo 1512953 6141271 := bstep (se 1 (by rfl) ⟨4605953, by rfl⟩ : syracuseStep 6141271 = 9211907) B9211907
theorem B8181157 : Blo 1512953 8181157 := bstep (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) B1533967
theorem B2553275 : Blo 1512953 2553275 := bstep (se 1 (by rfl) ⟨1914956, by rfl⟩ : syracuseStep 2553275 = 3829913) B3829913
theorem B3405275 : Blo 1512953 3405275 := bstep (se 1 (by rfl) ⟨2553956, by rfl⟩ : syracuseStep 3405275 = 5107913) B5107913
theorem B3831259 : Blo 1512953 3831259 := bstep (se 1 (by rfl) ⟨2873444, by rfl⟩ : syracuseStep 3831259 = 5746889) B5746889
theorem B1512999 : Blo 1512953 1512999 := bstep (se 1 (by rfl) ⟨1134749, by rfl⟩ : syracuseStep 1512999 = 2269499) B2269499
theorem B2553383 : Blo 1512953 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B8181287 : Blo 1512953 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B7665191 : Blo 1512953 7665191 := bstep (se 1 (by rfl) ⟨5748893, by rfl⟩ : syracuseStep 7665191 = 11497787) B11497787
theorem B1513039 : Blo 1512953 1513039 := bstep (se 1 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 1513039 = 2269559) B2269559
theorem B1513055 : Blo 1512953 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B4601441 : Blo 1512953 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B1513083 : Blo 1512953 1513083 := bstep (se 1 (by rfl) ⟨1134812, by rfl⟩ : syracuseStep 1513083 = 2269625) B2269625
theorem B5109371 : Blo 1512953 5109371 := bstep (se 1 (by rfl) ⟨3832028, by rfl⟩ : syracuseStep 5109371 = 7664057) B7664057
theorem B5748347 : Blo 1512953 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B6469267 : Blo 1512953 6469267 := bstep (se 1 (by rfl) ⟨4851950, by rfl⟩ : syracuseStep 6469267 = 9703901) B9703901
theorem B1513135 : Blo 1512953 1513135 := bstep (se 1 (by rfl) ⟨1134851, by rfl⟩ : syracuseStep 1513135 = 2269703) B2269703
theorem B1513159 : Blo 1512953 1513159 := bstep (se 1 (by rfl) ⟨1134869, by rfl⟩ : syracuseStep 1513159 = 2269739) B2269739
theorem B1513179 : Blo 1512953 1513179 := bstep (se 1 (by rfl) ⟨1134884, by rfl⟩ : syracuseStep 1513179 = 2269769) B2269769
theorem B11499245 : Blo 1512953 11499245 := bstep (se 3 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 11499245 = 4312217) B4312217
theorem B5109533 : Blo 1512953 5109533 := bstep (se 3 (by rfl) ⟨958037, by rfl⟩ : syracuseStep 5109533 = 1916075) B1916075
theorem B1513255 : Blo 1512953 1513255 := bstep (se 1 (by rfl) ⟨1134941, by rfl⟩ : syracuseStep 1513255 = 2269883) B2269883
theorem B2553673 : Blo 1512953 2553673 := bstep (se 2 (by rfl) ⟨957627, by rfl⟩ : syracuseStep 2553673 = 1915255) B1915255
theorem B1513295 : Blo 1512953 1513295 := bstep (se 1 (by rfl) ⟨1134971, by rfl⟩ : syracuseStep 1513295 = 2269943) B2269943
theorem B1513311 : Blo 1512953 1513311 := bstep (se 1 (by rfl) ⟨1134983, by rfl⟩ : syracuseStep 1513311 = 2269967) B2269967
theorem B2553707 : Blo 1512953 2553707 := bstep (se 1 (by rfl) ⟨1915280, by rfl⟩ : syracuseStep 2553707 = 3830561) B3830561
theorem B1513339 : Blo 1512953 1513339 := bstep (se 1 (by rfl) ⟨1135004, by rfl⟩ : syracuseStep 1513339 = 2270009) B2270009
theorem B1513391 : Blo 1512953 1513391 := bstep (se 1 (by rfl) ⟨1135043, by rfl⟩ : syracuseStep 1513391 = 2270087) B2270087
theorem B3405743 : Blo 1512953 3405743 := bstep (se 1 (by rfl) ⟨2554307, by rfl⟩ : syracuseStep 3405743 = 5108615) B5108615
theorem B3233719 : Blo 1512953 3233719 := bstep (se 1 (by rfl) ⟨2425289, by rfl⟩ : syracuseStep 3233719 = 4850579) B4850579
theorem B1513415 : Blo 1512953 1513415 := bstep (se 1 (by rfl) ⟨1135061, by rfl⟩ : syracuseStep 1513415 = 2270123) B2270123
theorem B1513435 : Blo 1512953 1513435 := bstep (se 1 (by rfl) ⟨1135076, by rfl⟩ : syracuseStep 1513435 = 2270153) B2270153
theorem B1513511 : Blo 1512953 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B12941369 : Blo 1512953 12941369 := bstep (se 2 (by rfl) ⟨4853013, by rfl⟩ : syracuseStep 12941369 = 9706027) B9706027
theorem B1513551 : Blo 1512953 1513551 := bstep (se 1 (by rfl) ⟨1135163, by rfl⟩ : syracuseStep 1513551 = 2270327) B2270327
theorem B3831887 : Blo 1512953 3831887 := bstep (se 1 (by rfl) ⟨2873915, by rfl⟩ : syracuseStep 3831887 = 5747831) B5747831
theorem B1513567 : Blo 1512953 1513567 := bstep (se 1 (by rfl) ⟨1135175, by rfl⟩ : syracuseStep 1513567 = 2270351) B2270351
theorem B1513595 : Blo 1512953 1513595 := bstep (se 1 (by rfl) ⟨1135196, by rfl⟩ : syracuseStep 1513595 = 2270393) B2270393
theorem B3405995 : Blo 1512953 3405995 := bstep (se 1 (by rfl) ⟨2554496, by rfl⟩ : syracuseStep 3405995 = 5108993) B5108993
theorem B1513647 : Blo 1512953 1513647 := bstep (se 1 (by rfl) ⟨1135235, by rfl⟩ : syracuseStep 1513647 = 2270471) B2270471
theorem B1513671 : Blo 1512953 1513671 := bstep (se 1 (by rfl) ⟨1135253, by rfl⟩ : syracuseStep 1513671 = 2270507) B2270507
theorem B1513691 : Blo 1512953 1513691 := bstep (se 1 (by rfl) ⟨1135268, by rfl⟩ : syracuseStep 1513691 = 2270537) B2270537
theorem B2554105 : Blo 1512953 2554105 := bstep (se 2 (by rfl) ⟨957789, by rfl⟩ : syracuseStep 2554105 = 1915579) B1915579
theorem B9328907 : Blo 1512953 9328907 := bstep (se 1 (by rfl) ⟨6996680, by rfl⟩ : syracuseStep 9328907 = 13993361) B13993361
theorem B1513767 : Blo 1512953 1513767 := bstep (se 1 (by rfl) ⟨1135325, by rfl⟩ : syracuseStep 1513767 = 2270651) B2270651
theorem B1513807 : Blo 1512953 1513807 := bstep (se 1 (by rfl) ⟨1135355, by rfl⟩ : syracuseStep 1513807 = 2270711) B2270711
theorem B1513823 : Blo 1512953 1513823 := bstep (se 1 (by rfl) ⟨1135367, by rfl⟩ : syracuseStep 1513823 = 2270735) B2270735
theorem B1513851 : Blo 1512953 1513851 := bstep (se 1 (by rfl) ⟨1135388, by rfl⟩ : syracuseStep 1513851 = 2270777) B2270777
theorem B1513903 : Blo 1512953 1513903 := bstep (se 1 (by rfl) ⟨1135427, by rfl⟩ : syracuseStep 1513903 = 2270855) B2270855
theorem B1513927 : Blo 1512953 1513927 := bstep (se 1 (by rfl) ⟨1135445, by rfl⟩ : syracuseStep 1513927 = 2270891) B2270891
theorem B1702363 : Blo 1512953 1702363 := bstep (se 1 (by rfl) ⟨1276772, by rfl⟩ : syracuseStep 1702363 = 2553545) B2553545
theorem B1513947 : Blo 1512953 1513947 := bstep (se 1 (by rfl) ⟨1135460, by rfl⟩ : syracuseStep 1513947 = 2270921) B2270921
theorem B5110235 : Blo 1512953 5110235 := bstep (se 1 (by rfl) ⟨3832676, by rfl⟩ : syracuseStep 5110235 = 7665353) B7665353
theorem B2554375 : Blo 1512953 2554375 := bstep (se 1 (by rfl) ⟨1915781, by rfl⟩ : syracuseStep 2554375 = 3831563) B3831563
theorem B12270113 : Blo 1512953 12270113 := bstep (se 2 (by rfl) ⟨4601292, by rfl⟩ : syracuseStep 12270113 = 9202585) B9202585
theorem B1514023 : Blo 1512953 1514023 := bstep (se 1 (by rfl) ⟨1135517, by rfl⟩ : syracuseStep 1514023 = 2271035) B2271035
theorem B1514063 : Blo 1512953 1514063 := bstep (se 1 (by rfl) ⟨1135547, by rfl⟩ : syracuseStep 1514063 = 2271095) B2271095
theorem B1514079 : Blo 1512953 1514079 := bstep (se 1 (by rfl) ⟨1135559, by rfl⟩ : syracuseStep 1514079 = 2271119) B2271119
theorem B1514107 : Blo 1512953 1514107 := bstep (se 1 (by rfl) ⟨1135580, by rfl⟩ : syracuseStep 1514107 = 2271161) B2271161
theorem B1514159 : Blo 1512953 1514159 := bstep (se 1 (by rfl) ⟨1135619, by rfl⟩ : syracuseStep 1514159 = 2271239) B2271239
theorem B11500217 : Blo 1512953 11500217 := bstep (se 2 (by rfl) ⟨4312581, by rfl⟩ : syracuseStep 11500217 = 8625163) B8625163
theorem B5176007 : Blo 1512953 5176007 := bstep (se 1 (by rfl) ⟨3882005, by rfl⟩ : syracuseStep 5176007 = 7764011) B7764011
theorem B3406535 : Blo 1512953 3406535 := bstep (se 1 (by rfl) ⟨2554901, by rfl⟩ : syracuseStep 3406535 = 5109803) B5109803
theorem B1514183 : Blo 1512953 1514183 := bstep (se 1 (by rfl) ⟨1135637, by rfl⟩ : syracuseStep 1514183 = 2271275) B2271275
theorem B3832535 : Blo 1512953 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B1514203 : Blo 1512953 1514203 := bstep (se 1 (by rfl) ⟨1135652, by rfl⟩ : syracuseStep 1514203 = 2271305) B2271305
theorem B1514279 : Blo 1512953 1514279 := bstep (se 1 (by rfl) ⟨1135709, by rfl⟩ : syracuseStep 1514279 = 2271419) B2271419
theorem B1514319 : Blo 1512953 1514319 := bstep (se 1 (by rfl) ⟨1135739, by rfl⟩ : syracuseStep 1514319 = 2271479) B2271479
theorem B1514335 : Blo 1512953 1514335 := bstep (se 1 (by rfl) ⟨1135751, by rfl⟩ : syracuseStep 1514335 = 2271503) B2271503
theorem B1514363 : Blo 1512953 1514363 := bstep (se 1 (by rfl) ⟨1135772, by rfl⟩ : syracuseStep 1514363 = 2271545) B2271545
theorem B9706385 : Blo 1512953 9706385 := bstep (se 2 (by rfl) ⟨3639894, by rfl⟩ : syracuseStep 9706385 = 7279789) B7279789
theorem B1702831 : Blo 1512953 1702831 := bstep (se 1 (by rfl) ⟨1277123, by rfl⟩ : syracuseStep 1702831 = 2554247) B2554247
theorem B1514415 : Blo 1512953 1514415 := bstep (se 1 (by rfl) ⟨1135811, by rfl⟩ : syracuseStep 1514415 = 2271623) B2271623
theorem B2554807 : Blo 1512953 2554807 := bstep (se 1 (by rfl) ⟨1916105, by rfl⟩ : syracuseStep 2554807 = 3832211) B3832211
theorem B2874295 : Blo 1512953 2874295 := bstep (se 1 (by rfl) ⟨2155721, by rfl⟩ : syracuseStep 2874295 = 4311443) B4311443
theorem B1514439 : Blo 1512953 1514439 := bstep (se 1 (by rfl) ⟨1135829, by rfl⟩ : syracuseStep 1514439 = 2271659) B2271659
theorem B1514459 : Blo 1512953 1514459 := bstep (se 1 (by rfl) ⟨1135844, by rfl⟩ : syracuseStep 1514459 = 2271689) B2271689
theorem B5749775 : Blo 1512953 5749775 := bstep (se 1 (by rfl) ⟨4312331, by rfl⟩ : syracuseStep 5749775 = 8624663) B8624663
theorem B1514535 : Blo 1512953 1514535 := bstep (se 1 (by rfl) ⟨1135901, by rfl⟩ : syracuseStep 1514535 = 2271803) B2271803
theorem B3636281 : Blo 1512953 3636281 := bstep (se 2 (by rfl) ⟨1363605, by rfl⟩ : syracuseStep 3636281 = 2727211) B2727211
theorem B1514575 : Blo 1512953 1514575 := bstep (se 1 (by rfl) ⟨1135931, by rfl⟩ : syracuseStep 1514575 = 2271863) B2271863
theorem B1514591 : Blo 1512953 1514591 := bstep (se 1 (by rfl) ⟨1135943, by rfl⟩ : syracuseStep 1514591 = 2271887) B2271887
theorem B2555003 : Blo 1512953 2555003 := bstep (se 1 (by rfl) ⟨1916252, by rfl⟩ : syracuseStep 2555003 = 3832505) B3832505
theorem B1514619 : Blo 1512953 1514619 := bstep (se 1 (by rfl) ⟨1135964, by rfl⟩ : syracuseStep 1514619 = 2271929) B2271929
theorem B5110937 : Blo 1512953 5110937 := bstep (se 2 (by rfl) ⟨1916601, by rfl⟩ : syracuseStep 5110937 = 3833203) B3833203
theorem B1514671 : Blo 1512953 1514671 := bstep (se 1 (by rfl) ⟨1136003, by rfl⟩ : syracuseStep 1514671 = 2272007) B2272007
theorem B11066561 : Blo 1512953 11066561 := bstep (se 2 (by rfl) ⟨4149960, by rfl⟩ : syracuseStep 11066561 = 8299921) B8299921
theorem B1514695 : Blo 1512953 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B1514715 : Blo 1512953 1514715 := bstep (se 1 (by rfl) ⟨1136036, by rfl⟩ : syracuseStep 1514715 = 2272073) B2272073
theorem B14196005 : Blo 1512953 14196005 := bstep (se 4 (by rfl) ⟨1330875, by rfl⟩ : syracuseStep 14196005 = 2661751) B2661751
theorem B1514791 : Blo 1512953 1514791 := bstep (se 1 (by rfl) ⟨1136093, by rfl⟩ : syracuseStep 1514791 = 2272187) B2272187
theorem B1514831 : Blo 1512953 1514831 := bstep (se 1 (by rfl) ⟨1136123, by rfl⟩ : syracuseStep 1514831 = 2272247) B2272247
theorem B1703263 : Blo 1512953 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B1514847 : Blo 1512953 1514847 := bstep (se 1 (by rfl) ⟨1136135, by rfl⟩ : syracuseStep 1514847 = 2272271) B2272271
theorem B1514875 : Blo 1512953 1514875 := bstep (se 1 (by rfl) ⟨1136156, by rfl⟩ : syracuseStep 1514875 = 2272313) B2272313
theorem B7273871 : Blo 1512953 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B10911149 : Blo 1512953 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B2424239 : Blo 1512953 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B1514927 : Blo 1512953 1514927 := bstep (se 1 (by rfl) ⟨1136195, by rfl⟩ : syracuseStep 1514927 = 2272391) B2272391
theorem B1514951 : Blo 1512953 1514951 := bstep (se 1 (by rfl) ⟨1136213, by rfl⟩ : syracuseStep 1514951 = 2272427) B2272427
theorem B2555401 : Blo 1512953 2555401 := bstep (se 2 (by rfl) ⟨958275, by rfl⟩ : syracuseStep 2555401 = 1916551) B1916551
theorem B1916455 : Blo 1512953 1916455 := bstep (se 1 (by rfl) ⟨1437341, by rfl⟩ : syracuseStep 1916455 = 2874683) B2874683
theorem B3407399 : Blo 1512953 3407399 := bstep (se 1 (by rfl) ⟨2555549, by rfl⟩ : syracuseStep 3407399 = 5111099) B5111099
theorem B41410115 : Blo 1512953 41410115 := bstep (se 1 (by rfl) ⟨31057586, by rfl⟩ : syracuseStep 41410115 = 62115173) B62115173
theorem B7667297 : Blo 1512953 7667297 := bstep (se 2 (by rfl) ⟨2875236, by rfl⟩ : syracuseStep 7667297 = 5750473) B5750473
theorem B11501189 : Blo 1512953 11501189 := bstep (se 4 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 11501189 = 2156473) B2156473
theorem B2555563 : Blo 1512953 2555563 := bstep (se 1 (by rfl) ⟨1916672, by rfl⟩ : syracuseStep 2555563 = 3833345) B3833345
theorem B1703623 : Blo 1512953 1703623 := bstep (se 1 (by rfl) ⟨1277717, by rfl⟩ : syracuseStep 1703623 = 2555435) B2555435
theorem B66371309 : Blo 1512953 66371309 := bstep (se 3 (by rfl) ⟨12444620, by rfl⟩ : syracuseStep 66371309 = 24889241) B24889241
theorem B7765753 : Blo 1512953 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B2424649 : Blo 1512953 2424649 := bstep (se 2 (by rfl) ⟨909243, by rfl⟩ : syracuseStep 2424649 = 1818487) B1818487
theorem B7659359 : Blo 1512953 7659359 := bstep (se 1 (by rfl) ⟨5744519, by rfl⟩ : syracuseStep 7659359 = 11489039) B11489039
theorem B9207647 : Blo 1512953 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B1916779 : Blo 1512953 1916779 := bstep (se 1 (by rfl) ⟨1437584, by rfl⟩ : syracuseStep 1916779 = 2875169) B2875169
theorem B3407723 : Blo 1512953 3407723 := bstep (se 1 (by rfl) ⟨2555792, by rfl⟩ : syracuseStep 3407723 = 5111585) B5111585
theorem B3407777 : Blo 1512953 3407777 := bstep (se 2 (by rfl) ⟨1277916, by rfl⟩ : syracuseStep 3407777 = 2555833) B2555833
theorem B2555867 : Blo 1512953 2555867 := bstep (se 1 (by rfl) ⟨1916900, by rfl⟩ : syracuseStep 2555867 = 3833801) B3833801
theorem B7659521 : Blo 1512953 7659521 := bstep (se 2 (by rfl) ⟨2872320, by rfl⟩ : syracuseStep 7659521 = 5744641) B5744641
theorem B6553705 : Blo 1512953 6553705 := bstep (se 2 (by rfl) ⟨2457639, by rfl⟩ : syracuseStep 6553705 = 4915279) B4915279
theorem B3408083 : Blo 1512953 3408083 := bstep (se 1 (by rfl) ⟨2556062, by rfl⟩ : syracuseStep 3408083 = 5112125) B5112125
theorem B3408137 : Blo 1512953 3408137 := bstep (se 2 (by rfl) ⟨1278051, by rfl⟩ : syracuseStep 3408137 = 2556103) B2556103
theorem B28385597 : Blo 1512953 28385597 := bstep (se 3 (by rfl) ⟨5322299, by rfl⟩ : syracuseStep 28385597 = 10644599) B10644599
theorem B2269607 : Blo 1512953 2269607 := bstep (se 1 (by rfl) ⟨1702205, by rfl⟩ : syracuseStep 2269607 = 3404411) B3404411
theorem B2154919 : Blo 1512953 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B3834287 : Blo 1512953 3834287 := bstep (se 1 (by rfl) ⟨2875715, by rfl⟩ : syracuseStep 3834287 = 5751431) B5751431
theorem B14541281 : Blo 1512953 14541281 := bstep (se 2 (by rfl) ⟨5452980, by rfl⟩ : syracuseStep 14541281 = 10905961) B10905961
theorem B3834337 : Blo 1512953 3834337 := bstep (se 2 (by rfl) ⟨1437876, by rfl⟩ : syracuseStep 3834337 = 2875753) B2875753
theorem B3408353 : Blo 1512953 3408353 := bstep (se 2 (by rfl) ⟨1278132, by rfl⟩ : syracuseStep 3408353 = 2556265) B2556265
theorem B2269691 : Blo 1512953 2269691 := bstep (se 1 (by rfl) ⟨1702268, by rfl⟩ : syracuseStep 2269691 = 3404537) B3404537
theorem B11493899 : Blo 1512953 11493899 := bstep (se 1 (by rfl) ⟨8620424, by rfl⟩ : syracuseStep 11493899 = 17240849) B17240849
theorem B6554209 : Blo 1512953 6554209 := bstep (se 2 (by rfl) ⟨2457828, by rfl⟩ : syracuseStep 6554209 = 4915657) B4915657
theorem B2269817 : Blo 1512953 2269817 := bstep (se 2 (by rfl) ⟨851181, by rfl⟩ : syracuseStep 2269817 = 1702363) B1702363
theorem B2269871 : Blo 1512953 2269871 := bstep (se 1 (by rfl) ⟨1702403, by rfl⟩ : syracuseStep 2269871 = 3404807) B3404807
theorem B5112503 : Blo 1512953 5112503 := bstep (se 1 (by rfl) ⟨3834377, by rfl⟩ : syracuseStep 5112503 = 7668755) B7668755
theorem B2269919 : Blo 1512953 2269919 := bstep (se 1 (by rfl) ⟨1702439, by rfl⟩ : syracuseStep 2269919 = 3404879) B3404879
theorem B25854713 : Blo 1512953 25854713 := bstep (se 2 (by rfl) ⟨9695517, by rfl⟩ : syracuseStep 25854713 = 19391035) B19391035
theorem B7660331 : Blo 1512953 7660331 := bstep (se 1 (by rfl) ⟨5745248, by rfl⟩ : syracuseStep 7660331 = 11490497) B11490497
theorem B10355651 : Blo 1512953 10355651 := bstep (se 1 (by rfl) ⟨7766738, by rfl⟩ : syracuseStep 10355651 = 15533477) B15533477
theorem B2270183 : Blo 1512953 2270183 := bstep (se 1 (by rfl) ⟨1702637, by rfl⟩ : syracuseStep 2270183 = 3405275) B3405275
theorem B3736567 : Blo 1512953 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B6906977 : Blo 1512953 6906977 := bstep (se 2 (by rfl) ⟨2590116, by rfl⟩ : syracuseStep 6906977 = 5180233) B5180233
theorem B4850887 : Blo 1512953 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B27641033 : Blo 1512953 27641033 := bstep (se 2 (by rfl) ⟨10365387, by rfl⟩ : syracuseStep 27641033 = 20730775) B20730775
theorem B2270441 : Blo 1512953 2270441 := bstep (se 2 (by rfl) ⟨851415, by rfl⟩ : syracuseStep 2270441 = 1702831) B1702831
theorem B13288691 : Blo 1512953 13288691 := bstep (se 1 (by rfl) ⟨9966518, by rfl⟩ : syracuseStep 13288691 = 19933037) B19933037
theorem B2270495 : Blo 1512953 2270495 := bstep (se 1 (by rfl) ⟨1702871, by rfl⟩ : syracuseStep 2270495 = 3405743) B3405743
theorem B7669079 : Blo 1512953 7669079 := bstep (se 1 (by rfl) ⟨5751809, by rfl⟩ : syracuseStep 7669079 = 11503619) B11503619
theorem B8627579 : Blo 1512953 8627579 := bstep (se 1 (by rfl) ⟨6470684, by rfl⟩ : syracuseStep 8627579 = 12941369) B12941369
theorem B2270663 : Blo 1512953 2270663 := bstep (se 1 (by rfl) ⟨1702997, by rfl⟩ : syracuseStep 2270663 = 3405995) B3405995
theorem B6219271 : Blo 1512953 6219271 := bstep (se 1 (by rfl) ⟨4664453, by rfl⟩ : syracuseStep 6219271 = 9328907) B9328907
theorem B2271017 : Blo 1512953 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B3450671 : Blo 1512953 3450671 := bstep (se 1 (by rfl) ⟨2588003, by rfl⟩ : syracuseStep 3450671 = 5176007) B5176007
theorem B2271023 : Blo 1512953 2271023 := bstep (se 1 (by rfl) ⟨1703267, by rfl⟩ : syracuseStep 2271023 = 3406535) B3406535
theorem B8619857 : Blo 1512953 8619857 := bstep (se 2 (by rfl) ⟨3232446, by rfl⟩ : syracuseStep 8619857 = 6464893) B6464893
theorem B17483791 : Blo 1512953 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B9464003 : Blo 1512953 9464003 := bstep (se 1 (by rfl) ⟨7098002, by rfl⟩ : syracuseStep 9464003 = 14196005) B14196005
theorem B2271497 : Blo 1512953 2271497 := bstep (se 2 (by rfl) ⟨851811, by rfl⟩ : syracuseStep 2271497 = 1703623) B1703623
theorem B1616159 : Blo 1512953 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B9701669 : Blo 1512953 9701669 := bstep (se 4 (by rfl) ⟨909531, by rfl⟩ : syracuseStep 9701669 = 1819063) B1819063
theorem B2271599 : Blo 1512953 2271599 := bstep (se 1 (by rfl) ⟨1703699, by rfl⟩ : syracuseStep 2271599 = 3407399) B3407399
theorem B44247539 : Blo 1512953 44247539 := bstep (se 1 (by rfl) ⟨33185654, by rfl⟩ : syracuseStep 44247539 = 66371309) B66371309
theorem B4852219 : Blo 1512953 4852219 := bstep (se 1 (by rfl) ⟨3639164, by rfl⟩ : syracuseStep 4852219 = 7278329) B7278329
theorem B5106239 : Blo 1512953 5106239 := bstep (se 1 (by rfl) ⟨3829679, by rfl⟩ : syracuseStep 5106239 = 7659359) B7659359
theorem B6138431 : Blo 1512953 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B2271815 : Blo 1512953 2271815 := bstep (se 1 (by rfl) ⟨1703861, by rfl⟩ : syracuseStep 2271815 = 3407723) B3407723
theorem B4311625 : Blo 1512953 4311625 := bstep (se 2 (by rfl) ⟨1616859, by rfl⟩ : syracuseStep 4311625 = 3233719) B3233719
theorem B3639887 : Blo 1512953 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B2271851 : Blo 1512953 2271851 := bstep (se 1 (by rfl) ⟨1703888, by rfl⟩ : syracuseStep 2271851 = 3407777) B3407777
theorem B4852399 : Blo 1512953 4852399 := bstep (se 1 (by rfl) ⟨3639299, by rfl⟩ : syracuseStep 4852399 = 7278599) B7278599
theorem B7662275 : Blo 1512953 7662275 := bstep (se 1 (by rfl) ⟨5746706, by rfl⟩ : syracuseStep 7662275 = 11493413) B11493413
theorem B2272079 : Blo 1512953 2272079 := bstep (se 1 (by rfl) ⟨1704059, by rfl⟩ : syracuseStep 2272079 = 3408119) B3408119
theorem B8744321 : Blo 1512953 8744321 := bstep (se 2 (by rfl) ⟨3279120, by rfl⟩ : syracuseStep 8744321 = 6558241) B6558241
theorem B3452321 : Blo 1512953 3452321 := bstep (se 2 (by rfl) ⟨1294620, by rfl⟩ : syracuseStep 3452321 = 2589241) B2589241
theorem B6909371 : Blo 1512953 6909371 := bstep (se 1 (by rfl) ⟨5182028, by rfl⟩ : syracuseStep 6909371 = 10364057) B10364057
theorem B6909383 : Blo 1512953 6909383 := bstep (se 1 (by rfl) ⟨5182037, by rfl⟩ : syracuseStep 6909383 = 10364075) B10364075
theorem B6557345 : Blo 1512953 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B3067627 : Blo 1512953 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B3452651 : Blo 1512953 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B5110127 : Blo 1512953 5110127 := bstep (se 1 (by rfl) ⟨3832595, by rfl⟩ : syracuseStep 5110127 = 7665191) B7665191
theorem B8180075 : Blo 1512953 8180075 := bstep (se 1 (by rfl) ⟨6135056, by rfl⟩ : syracuseStep 8180075 = 12270113) B12270113
theorem B5108075 : Blo 1512953 5108075 := bstep (se 1 (by rfl) ⟨3831056, by rfl⟩ : syracuseStep 5108075 = 7662113) B7662113
theorem B8188361 : Blo 1512953 8188361 := bstep (se 2 (by rfl) ⟨3070635, by rfl⟩ : syracuseStep 8188361 = 6141271) B6141271
theorem B8188379 : Blo 1512953 8188379 := bstep (se 1 (by rfl) ⟨6141284, by rfl⟩ : syracuseStep 8188379 = 12282569) B12282569
theorem B3830267 : Blo 1512953 3830267 := bstep (se 1 (by rfl) ⟨2872700, by rfl⟩ : syracuseStep 3830267 = 5745401) B5745401
theorem B10908209 : Blo 1512953 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B5108345 : Blo 1512953 5108345 := bstep (se 2 (by rfl) ⟨1915629, by rfl⟩ : syracuseStep 5108345 = 3831259) B3831259
theorem B29094551 : Blo 1512953 29094551 := bstep (se 1 (by rfl) ⟨21820913, by rfl⟩ : syracuseStep 29094551 = 43641827) B43641827
theorem B17478389 : Blo 1512953 17478389 := bstep (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) B1638599
theorem B7377707 : Blo 1512953 7377707 := bstep (se 1 (by rfl) ⟨5533280, by rfl⟩ : syracuseStep 7377707 = 11066561) B11066561
theorem B3404699 : Blo 1512953 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B6468599 : Blo 1512953 6468599 := bstep (se 1 (by rfl) ⟨4851449, by rfl⟩ : syracuseStep 6468599 = 9702899) B9702899
theorem B3404897 : Blo 1512953 3404897 := bstep (se 2 (by rfl) ⟨1276836, by rfl⟩ : syracuseStep 3404897 = 2553673) B2553673
theorem B3232865 : Blo 1512953 3232865 := bstep (se 2 (by rfl) ⟨1212324, by rfl⟩ : syracuseStep 3232865 = 2424649) B2424649
theorem B3405095 : Blo 1512953 3405095 := bstep (se 1 (by rfl) ⟨2553821, by rfl⟩ : syracuseStep 3405095 = 5107643) B5107643
theorem B1725787 : Blo 1512953 1725787 := bstep (se 1 (by rfl) ⟨1294340, by rfl⟩ : syracuseStep 1725787 = 2588681) B2588681
theorem B19404157 : Blo 1512953 19404157 := bstep (se 3 (by rfl) ⟨3638279, by rfl⟩ : syracuseStep 19404157 = 7276559) B7276559
theorem B3831239 : Blo 1512953 3831239 := bstep (se 1 (by rfl) ⟨2873429, by rfl⟩ : syracuseStep 3831239 = 5746859) B5746859
theorem B1512955 : Blo 1512953 1512955 := bstep (se 1 (by rfl) ⟨1134716, by rfl⟩ : syracuseStep 1512955 = 2269433) B2269433
theorem B1513023 : Blo 1512953 1513023 := bstep (se 1 (by rfl) ⟨1134767, by rfl⟩ : syracuseStep 1513023 = 2269535) B2269535
theorem B1513031 : Blo 1512953 1513031 := bstep (se 1 (by rfl) ⟨1134773, by rfl⟩ : syracuseStep 1513031 = 2269547) B2269547
theorem B3405473 : Blo 1512953 3405473 := bstep (se 2 (by rfl) ⟨1277052, by rfl⟩ : syracuseStep 3405473 = 2554105) B2554105
theorem B1513183 : Blo 1512953 1513183 := bstep (se 1 (by rfl) ⟨1134887, by rfl⟩ : syracuseStep 1513183 = 2269775) B2269775
theorem B1513263 : Blo 1512953 1513263 := bstep (se 1 (by rfl) ⟨1134947, by rfl⟩ : syracuseStep 1513263 = 2269895) B2269895
theorem B11646775 : Blo 1512953 11646775 := bstep (se 1 (by rfl) ⟨8735081, by rfl⟩ : syracuseStep 11646775 = 17470163) B17470163
theorem B1513371 : Blo 1512953 1513371 := bstep (se 1 (by rfl) ⟨1135028, by rfl⟩ : syracuseStep 1513371 = 2270057) B2270057
theorem B1513423 : Blo 1512953 1513423 := bstep (se 1 (by rfl) ⟨1135067, by rfl⟩ : syracuseStep 1513423 = 2270135) B2270135
theorem B1513447 : Blo 1512953 1513447 := bstep (se 1 (by rfl) ⟨1135085, by rfl⟩ : syracuseStep 1513447 = 2270171) B2270171
theorem B3405833 : Blo 1512953 3405833 := bstep (se 2 (by rfl) ⟨1277187, by rfl⟩ : syracuseStep 3405833 = 2554375) B2554375
theorem B3832019 : Blo 1512953 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B5749001 : Blo 1512953 5749001 := bstep (se 2 (by rfl) ⟨2155875, by rfl⟩ : syracuseStep 5749001 = 4311751) B4311751
theorem B2185481 : Blo 1512953 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1513759 : Blo 1512953 1513759 := bstep (se 1 (by rfl) ⟨1135319, by rfl⟩ : syracuseStep 1513759 = 2270639) B2270639
theorem B1702183 : Blo 1512953 1702183 := bstep (se 1 (by rfl) ⟨1276637, by rfl⟩ : syracuseStep 1702183 = 2553275) B2553275
theorem B13810009 : Blo 1512953 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B1513819 : Blo 1512953 1513819 := bstep (se 1 (by rfl) ⟨1135364, by rfl⟩ : syracuseStep 1513819 = 2270729) B2270729
theorem B1702255 : Blo 1512953 1702255 := bstep (se 1 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 1702255 = 2553383) B2553383
theorem B5454191 : Blo 1512953 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B2873711 : Blo 1512953 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B1513839 : Blo 1512953 1513839 := bstep (se 1 (by rfl) ⟨1135379, by rfl⟩ : syracuseStep 1513839 = 2270759) B2270759
theorem B3406247 : Blo 1512953 3406247 := bstep (se 1 (by rfl) ⟨2554685, by rfl⟩ : syracuseStep 3406247 = 5109371) B5109371
theorem B1513895 : Blo 1512953 1513895 := bstep (se 1 (by rfl) ⟨1135421, by rfl⟩ : syracuseStep 1513895 = 2270843) B2270843
theorem B3832231 : Blo 1512953 3832231 := bstep (se 1 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 3832231 = 5748347) B5748347
theorem B24558005 : Blo 1512953 24558005 := bstep (se 5 (by rfl) ⟨1151156, by rfl⟩ : syracuseStep 24558005 = 2302313) B2302313
theorem B7666163 : Blo 1512953 7666163 := bstep (se 1 (by rfl) ⟨5749622, by rfl⟩ : syracuseStep 7666163 = 11499245) B11499245
theorem B1513979 : Blo 1512953 1513979 := bstep (se 1 (by rfl) ⟨1135484, by rfl⟩ : syracuseStep 1513979 = 2270969) B2270969
theorem B3406355 : Blo 1512953 3406355 := bstep (se 1 (by rfl) ⟨2554766, by rfl⟩ : syracuseStep 3406355 = 5109533) B5109533
theorem B1514047 : Blo 1512953 1514047 := bstep (se 1 (by rfl) ⟨1135535, by rfl⟩ : syracuseStep 1514047 = 2271071) B2271071
theorem B1702471 : Blo 1512953 1702471 := bstep (se 1 (by rfl) ⟨1276853, by rfl⟩ : syracuseStep 1702471 = 2553707) B2553707
theorem B1514055 : Blo 1512953 1514055 := bstep (se 1 (by rfl) ⟨1135541, by rfl⟩ : syracuseStep 1514055 = 2271083) B2271083
theorem B3406409 : Blo 1512953 3406409 := bstep (se 2 (by rfl) ⟨1277403, by rfl⟩ : syracuseStep 3406409 = 2554807) B2554807
theorem B3832393 : Blo 1512953 3832393 := bstep (se 2 (by rfl) ⟨1437147, by rfl⟩ : syracuseStep 3832393 = 2874295) B2874295
theorem B2554591 : Blo 1512953 2554591 := bstep (se 1 (by rfl) ⟨1915943, by rfl⟩ : syracuseStep 2554591 = 3831887) B3831887
theorem B1514207 : Blo 1512953 1514207 := bstep (se 1 (by rfl) ⟨1135655, by rfl⟩ : syracuseStep 1514207 = 2271311) B2271311
theorem B1514287 : Blo 1512953 1514287 := bstep (se 1 (by rfl) ⟨1135715, by rfl⟩ : syracuseStep 1514287 = 2271431) B2271431
theorem B1514395 : Blo 1512953 1514395 := bstep (se 1 (by rfl) ⟨1135796, by rfl⟩ : syracuseStep 1514395 = 2271593) B2271593
theorem B1514447 : Blo 1512953 1514447 := bstep (se 1 (by rfl) ⟨1135835, by rfl⟩ : syracuseStep 1514447 = 2271671) B2271671
theorem B3406823 : Blo 1512953 3406823 := bstep (se 1 (by rfl) ⟨2555117, by rfl⟩ : syracuseStep 3406823 = 5110235) B5110235
theorem B1514471 : Blo 1512953 1514471 := bstep (se 1 (by rfl) ⟨1135853, by rfl⟩ : syracuseStep 1514471 = 2271707) B2271707
theorem B7666811 : Blo 1512953 7666811 := bstep (se 1 (by rfl) ⟨5750108, by rfl⟩ : syracuseStep 7666811 = 11500217) B11500217
theorem B2555023 : Blo 1512953 2555023 := bstep (se 1 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 2555023 = 3832535) B3832535
theorem B6470923 : Blo 1512953 6470923 := bstep (se 1 (by rfl) ⟨4853192, by rfl⟩ : syracuseStep 6470923 = 9706385) B9706385
theorem B1514783 : Blo 1512953 1514783 := bstep (se 1 (by rfl) ⟨1136087, by rfl⟩ : syracuseStep 1514783 = 2272175) B2272175
theorem B1514843 : Blo 1512953 1514843 := bstep (se 1 (by rfl) ⟨1136132, by rfl⟩ : syracuseStep 1514843 = 2272265) B2272265
theorem B3833183 : Blo 1512953 3833183 := bstep (se 1 (by rfl) ⟨2874887, by rfl⟩ : syracuseStep 3833183 = 5749775) B5749775
theorem B3407201 : Blo 1512953 3407201 := bstep (se 2 (by rfl) ⟨1277700, by rfl⟩ : syracuseStep 3407201 = 2555401) B2555401
theorem B1514863 : Blo 1512953 1514863 := bstep (se 1 (by rfl) ⟨1136147, by rfl⟩ : syracuseStep 1514863 = 2272295) B2272295
theorem B2424187 : Blo 1512953 2424187 := bstep (se 1 (by rfl) ⟨1818140, by rfl⟩ : syracuseStep 2424187 = 3636281) B3636281
theorem B2555273 : Blo 1512953 2555273 := bstep (se 2 (by rfl) ⟨958227, by rfl⟩ : syracuseStep 2555273 = 1916455) B1916455
theorem B14556581 : Blo 1512953 14556581 := bstep (se 4 (by rfl) ⟨1364679, by rfl⟩ : syracuseStep 14556581 = 2729359) B2729359
theorem B1703335 : Blo 1512953 1703335 := bstep (se 1 (by rfl) ⟨1277501, by rfl⟩ : syracuseStep 1703335 = 2555003) B2555003
theorem B1514919 : Blo 1512953 1514919 := bstep (se 1 (by rfl) ⟨1136189, by rfl⟩ : syracuseStep 1514919 = 2272379) B2272379
theorem B3407291 : Blo 1512953 3407291 := bstep (se 1 (by rfl) ⟨2555468, by rfl⟩ : syracuseStep 3407291 = 5110937) B5110937
theorem B7003579 : Blo 1512953 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B38788631 : Blo 1512953 38788631 := bstep (se 1 (by rfl) ⟨29091473, by rfl⟩ : syracuseStep 38788631 = 58182947) B58182947
theorem B8625689 : Blo 1512953 8625689 := bstep (se 2 (by rfl) ⟨3234633, by rfl⟩ : syracuseStep 8625689 = 6469267) B6469267
theorem B3407417 : Blo 1512953 3407417 := bstep (se 2 (by rfl) ⟨1277781, by rfl⟩ : syracuseStep 3407417 = 2555563) B2555563
theorem B4849247 : Blo 1512953 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B7274099 : Blo 1512953 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B10354337 : Blo 1512953 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B27606743 : Blo 1512953 27606743 := bstep (se 1 (by rfl) ⟨20705057, by rfl⟩ : syracuseStep 27606743 = 41410115) B41410115
theorem B2875115 : Blo 1512953 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B5111531 : Blo 1512953 5111531 := bstep (se 1 (by rfl) ⟨3833648, by rfl⟩ : syracuseStep 5111531 = 7667297) B7667297
theorem B7667459 : Blo 1512953 7667459 := bstep (se 1 (by rfl) ⟨5750594, by rfl⟩ : syracuseStep 7667459 = 11501189) B11501189
theorem B2555705 : Blo 1512953 2555705 := bstep (se 2 (by rfl) ⟨958389, by rfl⟩ : syracuseStep 2555705 = 1916779) B1916779
theorem B1703911 : Blo 1512953 1703911 := bstep (se 1 (by rfl) ⟨1277933, by rfl⟩ : syracuseStep 1703911 = 2555867) B2555867
theorem B33169445 : Blo 1512953 33169445 := bstep (se 4 (by rfl) ⟨3109635, by rfl⟩ : syracuseStep 33169445 = 6219271) B6219271
theorem B2556191 : Blo 1512953 2556191 := bstep (se 1 (by rfl) ⟨1917143, by rfl⟩ : syracuseStep 2556191 = 3834287) B3834287
theorem B2269577 : Blo 1512953 2269577 := bstep (se 2 (by rfl) ⟨851091, by rfl⟩ : syracuseStep 2269577 = 1702183) B1702183
theorem B3408335 : Blo 1512953 3408335 := bstep (se 1 (by rfl) ⟨2556251, by rfl⟩ : syracuseStep 3408335 = 5112503) B5112503
theorem B2269673 : Blo 1512953 2269673 := bstep (se 2 (by rfl) ⟨851127, by rfl⟩ : syracuseStep 2269673 = 1702255) B1702255
theorem B17236475 : Blo 1512953 17236475 := bstep (se 1 (by rfl) ⟨12927356, by rfl⟩ : syracuseStep 17236475 = 25854713) B25854713
theorem B2269799 : Blo 1512953 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B5112449 : Blo 1512953 5112449 := bstep (se 2 (by rfl) ⟨1917168, by rfl⟩ : syracuseStep 5112449 = 3834337) B3834337
theorem B2269931 : Blo 1512953 2269931 := bstep (se 1 (by rfl) ⟨1702448, by rfl⟩ : syracuseStep 2269931 = 3404897) B3404897
theorem B2155243 : Blo 1512953 2155243 := bstep (se 1 (by rfl) ⟨1616432, by rfl⟩ : syracuseStep 2155243 = 3232865) B3232865
theorem B4604651 : Blo 1512953 4604651 := bstep (se 1 (by rfl) ⟨3453488, by rfl⟩ : syracuseStep 4604651 = 6906977) B6906977
theorem B4309757 : Blo 1512953 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B2269961 : Blo 1512953 2269961 := bstep (se 2 (by rfl) ⟨851235, by rfl⟩ : syracuseStep 2269961 = 1702471) B1702471
theorem B75694925 : Blo 1512953 75694925 := bstep (se 3 (by rfl) ⟨14192798, by rfl⟩ : syracuseStep 75694925 = 28385597) B28385597
theorem B2270063 : Blo 1512953 2270063 := bstep (se 1 (by rfl) ⟨1702547, by rfl⟩ : syracuseStep 2270063 = 3405095) B3405095
theorem B5112719 : Blo 1512953 5112719 := bstep (se 1 (by rfl) ⟨3834539, by rfl⟩ : syracuseStep 5112719 = 7669079) B7669079
theorem B5751719 : Blo 1512953 5751719 := bstep (se 1 (by rfl) ⟨4313789, by rfl⟩ : syracuseStep 5751719 = 8627579) B8627579
theorem B2270315 : Blo 1512953 2270315 := bstep (se 1 (by rfl) ⟨1702736, by rfl⟩ : syracuseStep 2270315 = 3405473) B3405473
theorem B2270555 : Blo 1512953 2270555 := bstep (se 1 (by rfl) ⟨1702916, by rfl⟩ : syracuseStep 2270555 = 3405833) B3405833
theorem B6309335 : Blo 1512953 6309335 := bstep (se 1 (by rfl) ⟨4732001, by rfl⟩ : syracuseStep 6309335 = 9464003) B9464003
theorem B2270831 : Blo 1512953 2270831 := bstep (se 1 (by rfl) ⟨1703123, by rfl⟩ : syracuseStep 2270831 = 3406247) B3406247
theorem B2270903 : Blo 1512953 2270903 := bstep (se 1 (by rfl) ⟨1703177, by rfl⟩ : syracuseStep 2270903 = 3406355) B3406355
theorem B8627897 : Blo 1512953 8627897 := bstep (se 2 (by rfl) ⟨3235461, by rfl⟩ : syracuseStep 8627897 = 6470923) B6470923
theorem B2270939 : Blo 1512953 2270939 := bstep (se 1 (by rfl) ⟨1703204, by rfl⟩ : syracuseStep 2270939 = 3406409) B3406409
theorem B2426591 : Blo 1512953 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B25872209 : Blo 1512953 25872209 := bstep (se 2 (by rfl) ⟨9702078, by rfl⟩ : syracuseStep 25872209 = 19404157) B19404157
theorem B2271113 : Blo 1512953 2271113 := bstep (se 2 (by rfl) ⟨851667, by rfl⟩ : syracuseStep 2271113 = 1703335) B1703335
theorem B12928997 : Blo 1512953 12928997 := bstep (se 4 (by rfl) ⟨1212093, by rfl⟩ : syracuseStep 12928997 = 2424187) B2424187
theorem B2271215 : Blo 1512953 2271215 := bstep (se 1 (by rfl) ⟨1703411, by rfl⟩ : syracuseStep 2271215 = 3406823) B3406823
theorem B2271467 : Blo 1512953 2271467 := bstep (se 1 (by rfl) ⟨1703600, by rfl⟩ : syracuseStep 2271467 = 3407201) B3407201
theorem B2271527 : Blo 1512953 2271527 := bstep (se 1 (by rfl) ⟨1703645, by rfl⟩ : syracuseStep 2271527 = 3407291) B3407291
theorem B4606247 : Blo 1512953 4606247 := bstep (se 1 (by rfl) ⟨3454685, by rfl⟩ : syracuseStep 4606247 = 6909371) B6909371
theorem B4606255 : Blo 1512953 4606255 := bstep (se 1 (by rfl) ⟨3454691, by rfl⟩ : syracuseStep 4606255 = 6909383) B6909383
theorem B4090169 : Blo 1512953 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B2271611 : Blo 1512953 2271611 := bstep (se 1 (by rfl) ⟨1703708, by rfl⟩ : syracuseStep 2271611 = 3407417) B3407417
theorem B2271881 : Blo 1512953 2271881 := bstep (se 2 (by rfl) ⟨851955, by rfl⟩ : syracuseStep 2271881 = 1703911) B1703911
theorem B5106347 : Blo 1512953 5106347 := bstep (se 1 (by rfl) ⟨3829760, by rfl⟩ : syracuseStep 5106347 = 7659521) B7659521
theorem B2272055 : Blo 1512953 2272055 := bstep (se 1 (by rfl) ⟨1704041, by rfl⟩ : syracuseStep 2272055 = 3408083) B3408083
theorem B2272091 : Blo 1512953 2272091 := bstep (se 1 (by rfl) ⟨1704068, by rfl⟩ : syracuseStep 2272091 = 3408137) B3408137
theorem B5458907 : Blo 1512953 5458907 := bstep (se 1 (by rfl) ⟨4094180, by rfl⟩ : syracuseStep 5458907 = 8188361) B8188361
theorem B5458919 : Blo 1512953 5458919 := bstep (se 1 (by rfl) ⟨4094189, by rfl⟩ : syracuseStep 5458919 = 8188379) B8188379
theorem B9694187 : Blo 1512953 9694187 := bstep (se 1 (by rfl) ⟨7270640, by rfl⟩ : syracuseStep 9694187 = 14541281) B14541281
theorem B2272235 : Blo 1512953 2272235 := bstep (se 1 (by rfl) ⟨1704176, by rfl⟩ : syracuseStep 2272235 = 3408353) B3408353
theorem B7662599 : Blo 1512953 7662599 := bstep (se 1 (by rfl) ⟨5746949, by rfl⟩ : syracuseStep 7662599 = 11493899) B11493899
theorem B5106887 : Blo 1512953 5106887 := bstep (se 1 (by rfl) ⟨3830165, by rfl⟩ : syracuseStep 5106887 = 7660331) B7660331
theorem B5827949 : Blo 1512953 5827949 := bstep (se 3 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 5827949 = 2185481) B2185481
theorem B18427355 : Blo 1512953 18427355 := bstep (se 1 (by rfl) ⟨13820516, by rfl⟩ : syracuseStep 18427355 = 27641033) B27641033
theorem B8859127 : Blo 1512953 8859127 := bstep (se 1 (by rfl) ⟨6644345, by rfl⟩ : syracuseStep 8859127 = 13288691) B13288691
theorem B23318189 : Blo 1512953 23318189 := bstep (se 3 (by rfl) ⟨4372160, by rfl⟩ : syracuseStep 23318189 = 8744321) B8744321
theorem B5746571 : Blo 1512953 5746571 := bstep (se 1 (by rfl) ⟨4309928, by rfl⟩ : syracuseStep 5746571 = 8619857) B8619857
theorem B6467779 : Blo 1512953 6467779 := bstep (se 1 (by rfl) ⟨4850834, by rfl⟩ : syracuseStep 6467779 = 9701669) B9701669
theorem B6467849 : Blo 1512953 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B16372003 : Blo 1512953 16372003 := bstep (se 1 (by rfl) ⟨12279002, by rfl⟩ : syracuseStep 16372003 = 24558005) B24558005
theorem B3404159 : Blo 1512953 3404159 := bstep (se 1 (by rfl) ⟨2553119, by rfl⟩ : syracuseStep 3404159 = 5106239) B5106239
theorem B4092287 : Blo 1512953 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B5108183 : Blo 1512953 5108183 := bstep (se 1 (by rfl) ⟨3831137, by rfl⟩ : syracuseStep 5108183 = 7662275) B7662275
theorem B46609037 : Blo 1512953 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B19673885 : Blo 1512953 19673885 := bstep (se 3 (by rfl) ⟨3688853, by rfl⟩ : syracuseStep 19673885 = 7377707) B7377707
theorem B9704387 : Blo 1512953 9704387 := bstep (se 1 (by rfl) ⟨7278290, by rfl⟩ : syracuseStep 9704387 = 14556581) B14556581
theorem B25859087 : Blo 1512953 25859087 := bstep (se 1 (by rfl) ⟨19394315, by rfl⟩ : syracuseStep 25859087 = 38788631) B38788631
theorem B3232831 : Blo 1512953 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B15529033 : Blo 1512953 15529033 := bstep (se 2 (by rfl) ⟨5823387, by rfl⟩ : syracuseStep 15529033 = 11646775) B11646775
theorem B6902891 : Blo 1512953 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B4371563 : Blo 1512953 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B18404495 : Blo 1512953 18404495 := bstep (se 1 (by rfl) ⟨13803371, by rfl⟩ : syracuseStep 18404495 = 27606743) B27606743
theorem B19928357 : Blo 1512953 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B17249597 : Blo 1512953 17249597 := bstep (se 3 (by rfl) ⟨3234299, by rfl⟩ : syracuseStep 17249597 = 6468599) B6468599
theorem B23311721 : Blo 1512953 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B8738273 : Blo 1512953 8738273 := bstep (se 2 (by rfl) ⟨3276852, by rfl⟩ : syracuseStep 8738273 = 6553705) B6553705
theorem B3405383 : Blo 1512953 3405383 := bstep (se 1 (by rfl) ⟨2554037, by rfl⟩ : syracuseStep 3405383 = 5108075) B5108075
theorem B1513071 : Blo 1512953 1513071 := bstep (se 1 (by rfl) ⟨1134803, by rfl⟩ : syracuseStep 1513071 = 2269607) B2269607
theorem B1513127 : Blo 1512953 1513127 := bstep (se 1 (by rfl) ⟨1134845, by rfl⟩ : syracuseStep 1513127 = 2269691) B2269691
theorem B2553511 : Blo 1512953 2553511 := bstep (se 1 (by rfl) ⟨1915133, by rfl⟩ : syracuseStep 2553511 = 3830267) B3830267
theorem B1513211 : Blo 1512953 1513211 := bstep (se 1 (by rfl) ⟨1134908, by rfl⟩ : syracuseStep 1513211 = 2269817) B2269817
theorem B3405563 : Blo 1512953 3405563 := bstep (se 1 (by rfl) ⟨2554172, by rfl⟩ : syracuseStep 3405563 = 5108345) B5108345
theorem B19396367 : Blo 1512953 19396367 := bstep (se 1 (by rfl) ⟨14547275, by rfl⟩ : syracuseStep 19396367 = 29094551) B29094551
theorem B1513247 : Blo 1512953 1513247 := bstep (se 1 (by rfl) ⟨1134935, by rfl⟩ : syracuseStep 1513247 = 2269871) B2269871
theorem B18413345 : Blo 1512953 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B1513279 : Blo 1512953 1513279 := bstep (se 1 (by rfl) ⟨1134959, by rfl⟩ : syracuseStep 1513279 = 2269919) B2269919
theorem B2873225 : Blo 1512953 2873225 := bstep (se 2 (by rfl) ⟨1077459, by rfl⟩ : syracuseStep 2873225 = 2154919) B2154919
theorem B5109641 : Blo 1512953 5109641 := bstep (se 2 (by rfl) ⟨1916115, by rfl⟩ : syracuseStep 5109641 = 3832231) B3832231
theorem B6903767 : Blo 1512953 6903767 := bstep (se 1 (by rfl) ⟨5177825, by rfl⟩ : syracuseStep 6903767 = 10355651) B10355651
theorem B1513455 : Blo 1512953 1513455 := bstep (se 1 (by rfl) ⟨1135091, by rfl⟩ : syracuseStep 1513455 = 2270183) B2270183
theorem B6469625 : Blo 1512953 6469625 := bstep (se 2 (by rfl) ⟨2426109, by rfl⟩ : syracuseStep 6469625 = 4852219) B4852219
theorem B5109857 : Blo 1512953 5109857 := bstep (se 2 (by rfl) ⟨1916196, by rfl⟩ : syracuseStep 5109857 = 3832393) B3832393
theorem B5748833 : Blo 1512953 5748833 := bstep (se 2 (by rfl) ⟨2155812, by rfl⟩ : syracuseStep 5748833 = 4311625) B4311625
theorem B8738945 : Blo 1512953 8738945 := bstep (se 2 (by rfl) ⟨3277104, by rfl⟩ : syracuseStep 8738945 = 6554209) B6554209
theorem B1513627 : Blo 1512953 1513627 := bstep (se 1 (by rfl) ⟨1135220, by rfl⟩ : syracuseStep 1513627 = 2270441) B2270441
theorem B1513663 : Blo 1512953 1513663 := bstep (se 1 (by rfl) ⟨1135247, by rfl⟩ : syracuseStep 1513663 = 2270495) B2270495
theorem B6469865 : Blo 1512953 6469865 := bstep (se 2 (by rfl) ⟨2426199, by rfl⟩ : syracuseStep 6469865 = 4852399) B4852399
theorem B21813533 : Blo 1512953 21813533 := bstep (se 3 (by rfl) ⟨4090037, by rfl⟩ : syracuseStep 21813533 = 8180075) B8180075
theorem B3406121 : Blo 1512953 3406121 := bstep (se 2 (by rfl) ⟨1277295, by rfl⟩ : syracuseStep 3406121 = 2554591) B2554591
theorem B2554159 : Blo 1512953 2554159 := bstep (se 1 (by rfl) ⟨1915619, by rfl⟩ : syracuseStep 2554159 = 3831239) B3831239
theorem B1513775 : Blo 1512953 1513775 := bstep (se 1 (by rfl) ⟨1135331, by rfl⟩ : syracuseStep 1513775 = 2270663) B2270663
theorem B1514011 : Blo 1512953 1514011 := bstep (se 1 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 1514011 = 2271017) B2271017
theorem B2300447 : Blo 1512953 2300447 := bstep (se 1 (by rfl) ⟨1725335, by rfl⟩ : syracuseStep 2300447 = 3450671) B3450671
theorem B1514015 : Blo 1512953 1514015 := bstep (se 1 (by rfl) ⟨1135511, by rfl⟩ : syracuseStep 1514015 = 2271023) B2271023
theorem B29088557 : Blo 1512953 29088557 := bstep (se 3 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 29088557 = 10908209) B10908209
theorem B2554679 : Blo 1512953 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B3832667 : Blo 1512953 3832667 := bstep (se 1 (by rfl) ⟨2874500, by rfl⟩ : syracuseStep 3832667 = 5749001) B5749001
theorem B1514331 : Blo 1512953 1514331 := bstep (se 1 (by rfl) ⟨1135748, by rfl⟩ : syracuseStep 1514331 = 2271497) B2271497
theorem B3406697 : Blo 1512953 3406697 := bstep (se 2 (by rfl) ⟨1277511, by rfl⟩ : syracuseStep 3406697 = 2555023) B2555023
theorem B3636127 : Blo 1512953 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1915807 : Blo 1512953 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B3406751 : Blo 1512953 3406751 := bstep (se 1 (by rfl) ⟨2555063, by rfl⟩ : syracuseStep 3406751 = 5110127) B5110127
theorem B1514399 : Blo 1512953 1514399 := bstep (se 1 (by rfl) ⟨1135799, by rfl⟩ : syracuseStep 1514399 = 2271599) B2271599
theorem B29498359 : Blo 1512953 29498359 := bstep (se 1 (by rfl) ⟨22123769, by rfl⟩ : syracuseStep 29498359 = 44247539) B44247539
theorem B5110775 : Blo 1512953 5110775 := bstep (se 1 (by rfl) ⟨3833081, by rfl⟩ : syracuseStep 5110775 = 7666163) B7666163
theorem B1514543 : Blo 1512953 1514543 := bstep (se 1 (by rfl) ⟨1135907, by rfl⟩ : syracuseStep 1514543 = 2271815) B2271815
theorem B1514567 : Blo 1512953 1514567 := bstep (se 1 (by rfl) ⟨1135925, by rfl⟩ : syracuseStep 1514567 = 2271851) B2271851
theorem B2301049 : Blo 1512953 2301049 := bstep (se 2 (by rfl) ⟨862893, by rfl⟩ : syracuseStep 2301049 = 1725787) B1725787
theorem B1514719 : Blo 1512953 1514719 := bstep (se 1 (by rfl) ⟨1136039, by rfl⟩ : syracuseStep 1514719 = 2272079) B2272079
theorem B9338105 : Blo 1512953 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B7666973 : Blo 1512953 7666973 := bstep (se 3 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 7666973 = 2875115) B2875115
theorem B5111207 : Blo 1512953 5111207 := bstep (se 1 (by rfl) ⟨3833405, by rfl⟩ : syracuseStep 5111207 = 7666811) B7666811
theorem B2555455 : Blo 1512953 2555455 := bstep (se 1 (by rfl) ⟨1916591, by rfl⟩ : syracuseStep 2555455 = 3833183) B3833183
theorem B1703515 : Blo 1512953 1703515 := bstep (se 1 (by rfl) ⟨1277636, by rfl⟩ : syracuseStep 1703515 = 2555273) B2555273
theorem B2301547 : Blo 1512953 2301547 := bstep (se 1 (by rfl) ⟨1726160, by rfl⟩ : syracuseStep 2301547 = 3452321) B3452321
theorem B5750459 : Blo 1512953 5750459 := bstep (se 1 (by rfl) ⟨4312844, by rfl⟩ : syracuseStep 5750459 = 8625689) B8625689
theorem B4849399 : Blo 1512953 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B2301767 : Blo 1512953 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B3407687 : Blo 1512953 3407687 := bstep (se 1 (by rfl) ⟨2555765, by rfl⟩ : syracuseStep 3407687 = 5111531) B5111531
theorem B5111639 : Blo 1512953 5111639 := bstep (se 1 (by rfl) ⟨3833729, by rfl⟩ : syracuseStep 5111639 = 7667459) B7667459
theorem B1703803 : Blo 1512953 1703803 := bstep (se 1 (by rfl) ⟨1277852, by rfl⟩ : syracuseStep 1703803 = 2555705) B2555705
theorem B1704127 : Blo 1512953 1704127 := bstep (se 1 (by rfl) ⟨1278095, by rfl⟩ : syracuseStep 1704127 = 2556191) B2556191
theorem B2269439 : Blo 1512953 2269439 := bstep (se 1 (by rfl) ⟨1702079, by rfl⟩ : syracuseStep 2269439 = 3404159) B3404159
theorem B3408299 : Blo 1512953 3408299 := bstep (se 1 (by rfl) ⟨2556224, by rfl⟩ : syracuseStep 3408299 = 5112449) B5112449
theorem B31072691 : Blo 1512953 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B50463283 : Blo 1512953 50463283 := bstep (se 1 (by rfl) ⟨37847462, by rfl⟩ : syracuseStep 50463283 = 75694925) B75694925
theorem B3408479 : Blo 1512953 3408479 := bstep (se 1 (by rfl) ⟨2556359, by rfl⟩ : syracuseStep 3408479 = 5112719) B5112719
theorem B3834479 : Blo 1512953 3834479 := bstep (se 1 (by rfl) ⟨2875859, by rfl⟩ : syracuseStep 3834479 = 5751719) B5751719
theorem B15541147 : Blo 1512953 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B5825515 : Blo 1512953 5825515 := bstep (se 1 (by rfl) ⟨4369136, by rfl⟩ : syracuseStep 5825515 = 8738273) B8738273
theorem B10912765 : Blo 1512953 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B2270255 : Blo 1512953 2270255 := bstep (se 1 (by rfl) ⟨1702691, by rfl⟩ : syracuseStep 2270255 = 3405383) B3405383
theorem B5751931 : Blo 1512953 5751931 := bstep (se 1 (by rfl) ⟨4313948, by rfl⟩ : syracuseStep 5751931 = 8627897) B8627897
theorem B2270375 : Blo 1512953 2270375 := bstep (se 1 (by rfl) ⟨1702781, by rfl⟩ : syracuseStep 2270375 = 3405563) B3405563
theorem B25863461 : Blo 1512953 25863461 := bstep (se 4 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 25863461 = 4849399) B4849399
theorem B8619331 : Blo 1512953 8619331 := bstep (se 1 (by rfl) ⟨6464498, by rfl⟩ : syracuseStep 8619331 = 12928997) B12928997
theorem B39331145 : Blo 1512953 39331145 := bstep (se 2 (by rfl) ⟨14749179, by rfl⟩ : syracuseStep 39331145 = 29498359) B29498359
theorem B4310441 : Blo 1512953 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B5825963 : Blo 1512953 5825963 := bstep (se 1 (by rfl) ⟨4369472, by rfl⟩ : syracuseStep 5825963 = 8738945) B8738945
theorem B14542355 : Blo 1512953 14542355 := bstep (se 1 (by rfl) ⟨10906766, by rfl⟩ : syracuseStep 14542355 = 21813533) B21813533
theorem B2270747 : Blo 1512953 2270747 := bstep (se 1 (by rfl) ⟨1703060, by rfl⟩ : syracuseStep 2270747 = 3406121) B3406121
theorem B19392371 : Blo 1512953 19392371 := bstep (se 1 (by rfl) ⟨14544278, by rfl⟩ : syracuseStep 19392371 = 29088557) B29088557
theorem B2271131 : Blo 1512953 2271131 := bstep (se 1 (by rfl) ⟨1703348, by rfl⟩ : syracuseStep 2271131 = 3406697) B3406697
theorem B2271167 : Blo 1512953 2271167 := bstep (se 1 (by rfl) ⟨1703375, by rfl⟩ : syracuseStep 2271167 = 3406751) B3406751
theorem B3639271 : Blo 1512953 3639271 := bstep (se 1 (by rfl) ⟨2729453, by rfl⟩ : syracuseStep 3639271 = 5458907) B5458907
theorem B52463693 : Blo 1512953 52463693 := bstep (se 3 (by rfl) ⟨9836942, by rfl⟩ : syracuseStep 52463693 = 19673885) B19673885
theorem B2271353 : Blo 1512953 2271353 := bstep (se 2 (by rfl) ⟨851757, by rfl⟩ : syracuseStep 2271353 = 1703515) B1703515
theorem B3885299 : Blo 1512953 3885299 := bstep (se 1 (by rfl) ⟨2913974, by rfl⟩ : syracuseStep 3885299 = 5827949) B5827949
theorem B2271737 : Blo 1512953 2271737 := bstep (se 2 (by rfl) ⟨851901, by rfl⟩ : syracuseStep 2271737 = 1703803) B1703803
theorem B1534511 : Blo 1512953 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B2271791 : Blo 1512953 2271791 := bstep (se 1 (by rfl) ⟨1703843, by rfl⟩ : syracuseStep 2271791 = 3407687) B3407687
theorem B22112963 : Blo 1512953 22112963 := bstep (se 1 (by rfl) ⟨16584722, by rfl⟩ : syracuseStep 22112963 = 33169445) B33169445
theorem B4311899 : Blo 1512953 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B2272223 : Blo 1512953 2272223 := bstep (se 1 (by rfl) ⟨1704167, by rfl⟩ : syracuseStep 2272223 = 3408335) B3408335
theorem B17239391 : Blo 1512953 17239391 := bstep (se 1 (by rfl) ⟨12929543, by rfl⟩ : syracuseStep 17239391 = 25859087) B25859087
theorem B1617727 : Blo 1512953 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B12930911 : Blo 1512953 12930911 := bstep (se 1 (by rfl) ⟨9698183, by rfl⟩ : syracuseStep 12930911 = 19396367) B19396367
theorem B12275563 : Blo 1512953 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B17248139 : Blo 1512953 17248139 := bstep (se 1 (by rfl) ⟨12936104, by rfl⟩ : syracuseStep 17248139 = 25872209) B25872209
theorem B4313083 : Blo 1512953 4313083 := bstep (se 1 (by rfl) ⟨3234812, by rfl⟩ : syracuseStep 4313083 = 6469625) B6469625
theorem B20705377 : Blo 1512953 20705377 := bstep (se 2 (by rfl) ⟨7764516, by rfl⟩ : syracuseStep 20705377 = 15529033) B15529033
theorem B4313243 : Blo 1512953 4313243 := bstep (se 1 (by rfl) ⟨3234932, by rfl⟩ : syracuseStep 4313243 = 6469865) B6469865
theorem B3068065 : Blo 1512953 3068065 := bstep (se 2 (by rfl) ⟨1150524, by rfl⟩ : syracuseStep 3068065 = 2301049) B2301049
theorem B3404231 : Blo 1512953 3404231 := bstep (se 1 (by rfl) ⟨2553173, by rfl⟩ : syracuseStep 3404231 = 5106347) B5106347
theorem B5108399 : Blo 1512953 5108399 := bstep (se 1 (by rfl) ⟨3831299, by rfl⟩ : syracuseStep 5108399 = 7662599) B7662599
theorem B3404591 : Blo 1512953 3404591 := bstep (se 1 (by rfl) ⟨2553443, by rfl⟩ : syracuseStep 3404591 = 5106887) B5106887
theorem B3068729 : Blo 1512953 3068729 := bstep (se 2 (by rfl) ⟨1150773, by rfl⟩ : syracuseStep 3068729 = 2301547) B2301547
theorem B3404681 : Blo 1512953 3404681 := bstep (se 2 (by rfl) ⟨1276755, by rfl⟩ : syracuseStep 3404681 = 2553511) B2553511
theorem B12284903 : Blo 1512953 12284903 := bstep (se 1 (by rfl) ⟨9213677, by rfl⟩ : syracuseStep 12284903 = 18427355) B18427355
theorem B15545459 : Blo 1512953 15545459 := bstep (se 1 (by rfl) ⟨11659094, by rfl⟩ : syracuseStep 15545459 = 23318189) B23318189
theorem B3831047 : Blo 1512953 3831047 := bstep (se 1 (by rfl) ⟨2873285, by rfl⟩ : syracuseStep 3831047 = 5746571) B5746571
theorem B1513051 : Blo 1512953 1513051 := bstep (se 1 (by rfl) ⟨1134788, by rfl⟩ : syracuseStep 1513051 = 2269577) B2269577
theorem B8623705 : Blo 1512953 8623705 := bstep (se 2 (by rfl) ⟨3233889, by rfl⟩ : syracuseStep 8623705 = 6467779) B6467779
theorem B3405455 : Blo 1512953 3405455 := bstep (se 1 (by rfl) ⟨2554091, by rfl⟩ : syracuseStep 3405455 = 5108183) B5108183
theorem B1513115 : Blo 1512953 1513115 := bstep (se 1 (by rfl) ⟨1134836, by rfl⟩ : syracuseStep 1513115 = 2269673) B2269673
theorem B11490983 : Blo 1512953 11490983 := bstep (se 1 (by rfl) ⟨8618237, by rfl⟩ : syracuseStep 11490983 = 17236475) B17236475
theorem B21829337 : Blo 1512953 21829337 := bstep (se 2 (by rfl) ⟨8186001, by rfl⟩ : syracuseStep 21829337 = 16372003) B16372003
theorem B3405545 : Blo 1512953 3405545 := bstep (se 2 (by rfl) ⟨1277079, by rfl⟩ : syracuseStep 3405545 = 2554159) B2554159
theorem B1513199 : Blo 1512953 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B6141673 : Blo 1512953 6141673 := bstep (se 2 (by rfl) ⟨2303127, by rfl⟩ : syracuseStep 6141673 = 4606255) B4606255
theorem B1513287 : Blo 1512953 1513287 := bstep (se 1 (by rfl) ⟨1134965, by rfl⟩ : syracuseStep 1513287 = 2269931) B2269931
theorem B3069767 : Blo 1512953 3069767 := bstep (se 1 (by rfl) ⟨2302325, by rfl⟩ : syracuseStep 3069767 = 4604651) B4604651
theorem B2873171 : Blo 1512953 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1513307 : Blo 1512953 1513307 := bstep (se 1 (by rfl) ⟨1134980, by rfl⟩ : syracuseStep 1513307 = 2269961) B2269961
theorem B1513375 : Blo 1512953 1513375 := bstep (se 1 (by rfl) ⟨1135031, by rfl⟩ : syracuseStep 1513375 = 2270063) B2270063
theorem B6469591 : Blo 1512953 6469591 := bstep (se 1 (by rfl) ⟨4852193, by rfl⟩ : syracuseStep 6469591 = 9704387) B9704387
theorem B4601927 : Blo 1512953 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B1513543 : Blo 1512953 1513543 := bstep (se 1 (by rfl) ⟨1135157, by rfl⟩ : syracuseStep 1513543 = 2270315) B2270315
theorem B2914375 : Blo 1512953 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B12269663 : Blo 1512953 12269663 := bstep (se 1 (by rfl) ⟨9202247, by rfl⟩ : syracuseStep 12269663 = 18404495) B18404495
theorem B13285571 : Blo 1512953 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B11499731 : Blo 1512953 11499731 := bstep (se 1 (by rfl) ⟨8624798, by rfl⟩ : syracuseStep 11499731 = 17249597) B17249597
theorem B1513703 : Blo 1512953 1513703 := bstep (se 1 (by rfl) ⟨1135277, by rfl⟩ : syracuseStep 1513703 = 2270555) B2270555
theorem B2873657 : Blo 1512953 2873657 := bstep (se 2 (by rfl) ⟨1077621, by rfl⟩ : syracuseStep 2873657 = 2155243) B2155243
theorem B1513887 : Blo 1512953 1513887 := bstep (se 1 (by rfl) ⟨1135415, by rfl⟩ : syracuseStep 1513887 = 2270831) B2270831
theorem B1513935 : Blo 1512953 1513935 := bstep (se 1 (by rfl) ⟨1135451, by rfl⟩ : syracuseStep 1513935 = 2270903) B2270903
theorem B1513959 : Blo 1512953 1513959 := bstep (se 1 (by rfl) ⟨1135469, by rfl⟩ : syracuseStep 1513959 = 2270939) B2270939
theorem B4848169 : Blo 1512953 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B2554409 : Blo 1512953 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B16824893 : Blo 1512953 16824893 := bstep (se 3 (by rfl) ⟨3154667, by rfl⟩ : syracuseStep 16824893 = 6309335) B6309335
theorem B1915483 : Blo 1512953 1915483 := bstep (se 1 (by rfl) ⟨1436612, by rfl⟩ : syracuseStep 1915483 = 2873225) B2873225
theorem B3406427 : Blo 1512953 3406427 := bstep (se 1 (by rfl) ⟨2554820, by rfl⟩ : syracuseStep 3406427 = 5109641) B5109641
theorem B1514075 : Blo 1512953 1514075 := bstep (se 1 (by rfl) ⟨1135556, by rfl⟩ : syracuseStep 1514075 = 2271113) B2271113
theorem B4602511 : Blo 1512953 4602511 := bstep (se 1 (by rfl) ⟨3451883, by rfl⟩ : syracuseStep 4602511 = 6903767) B6903767
theorem B1514143 : Blo 1512953 1514143 := bstep (se 1 (by rfl) ⟨1135607, by rfl⟩ : syracuseStep 1514143 = 2271215) B2271215
theorem B3406571 : Blo 1512953 3406571 := bstep (se 1 (by rfl) ⟨2554928, by rfl⟩ : syracuseStep 3406571 = 5109857) B5109857
theorem B3832555 : Blo 1512953 3832555 := bstep (se 1 (by rfl) ⟨2874416, by rfl⟩ : syracuseStep 3832555 = 5748833) B5748833
theorem B6134525 : Blo 1512953 6134525 := bstep (se 3 (by rfl) ⟨1150223, by rfl⟩ : syracuseStep 6134525 = 2300447) B2300447
theorem B1514311 : Blo 1512953 1514311 := bstep (se 1 (by rfl) ⟨1135733, by rfl⟩ : syracuseStep 1514311 = 2271467) B2271467
theorem B1514351 : Blo 1512953 1514351 := bstep (se 1 (by rfl) ⟨1135763, by rfl⟩ : syracuseStep 1514351 = 2271527) B2271527
theorem B3070831 : Blo 1512953 3070831 := bstep (se 1 (by rfl) ⟨2303123, by rfl⟩ : syracuseStep 3070831 = 4606247) B4606247
theorem B2726779 : Blo 1512953 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B1514407 : Blo 1512953 1514407 := bstep (se 1 (by rfl) ⟨1135805, by rfl⟩ : syracuseStep 1514407 = 2271611) B2271611
theorem B1514587 : Blo 1512953 1514587 := bstep (se 1 (by rfl) ⟨1135940, by rfl⟩ : syracuseStep 1514587 = 2271881) B2271881
theorem B1703119 : Blo 1512953 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B1514703 : Blo 1512953 1514703 := bstep (se 1 (by rfl) ⟨1136027, by rfl⟩ : syracuseStep 1514703 = 2272055) B2272055
theorem B2555111 : Blo 1512953 2555111 := bstep (se 1 (by rfl) ⟨1916333, by rfl⟩ : syracuseStep 2555111 = 3832667) B3832667
theorem B1514727 : Blo 1512953 1514727 := bstep (se 1 (by rfl) ⟨1136045, by rfl⟩ : syracuseStep 1514727 = 2272091) B2272091
theorem B6462791 : Blo 1512953 6462791 := bstep (se 1 (by rfl) ⟨4847093, by rfl⟩ : syracuseStep 6462791 = 9694187) B9694187
theorem B11812169 : Blo 1512953 11812169 := bstep (se 2 (by rfl) ⟨4429563, by rfl⟩ : syracuseStep 11812169 = 8859127) B8859127
theorem B1514823 : Blo 1512953 1514823 := bstep (se 1 (by rfl) ⟨1136117, by rfl⟩ : syracuseStep 1514823 = 2272235) B2272235
theorem B3407183 : Blo 1512953 3407183 := bstep (se 1 (by rfl) ⟨2555387, by rfl⟩ : syracuseStep 3407183 = 5110775) B5110775
theorem B3407273 : Blo 1512953 3407273 := bstep (se 2 (by rfl) ⟨1277727, by rfl⟩ : syracuseStep 3407273 = 2555455) B2555455
theorem B6225403 : Blo 1512953 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B5111315 : Blo 1512953 5111315 := bstep (se 1 (by rfl) ⟨3833486, by rfl⟩ : syracuseStep 5111315 = 7666973) B7666973
theorem B3407471 : Blo 1512953 3407471 := bstep (se 1 (by rfl) ⟨2555603, by rfl⟩ : syracuseStep 3407471 = 5111207) B5111207
theorem B3833639 : Blo 1512953 3833639 := bstep (se 1 (by rfl) ⟨2875229, by rfl⟩ : syracuseStep 3833639 = 5750459) B5750459
theorem B3407759 : Blo 1512953 3407759 := bstep (se 1 (by rfl) ⟨2555819, by rfl⟩ : syracuseStep 3407759 = 5111639) B5111639
theorem B14557117 : Blo 1512953 14557117 := bstep (se 3 (by rfl) ⟨2729459, by rfl⟩ : syracuseStep 14557117 = 5458919) B5458919
theorem B2875495 : Blo 1512953 2875495 := bstep (se 1 (by rfl) ⟨2156621, by rfl⟩ : syracuseStep 2875495 = 4313243) B4313243
theorem B27607169 : Blo 1512953 27607169 := bstep (se 2 (by rfl) ⟨10352688, by rfl⟩ : syracuseStep 27607169 = 20705377) B20705377
theorem B2269487 : Blo 1512953 2269487 := bstep (se 1 (by rfl) ⟨1702115, by rfl⟩ : syracuseStep 2269487 = 3404231) B3404231
theorem B2556319 : Blo 1512953 2556319 := bstep (se 1 (by rfl) ⟨1917239, by rfl⟩ : syracuseStep 2556319 = 3834479) B3834479
theorem B2269727 : Blo 1512953 2269727 := bstep (se 1 (by rfl) ⟨1702295, by rfl⟩ : syracuseStep 2269727 = 3404591) B3404591
theorem B2269787 : Blo 1512953 2269787 := bstep (se 1 (by rfl) ⟨1702340, by rfl⟩ : syracuseStep 2269787 = 3404681) B3404681
theorem B6464225 : Blo 1512953 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B10363639 : Blo 1512953 10363639 := bstep (se 1 (by rfl) ⟨7772729, by rfl⟩ : syracuseStep 10363639 = 15545459) B15545459
theorem B6136681 : Blo 1512953 6136681 := bstep (se 2 (by rfl) ⟨2301255, by rfl⟩ : syracuseStep 6136681 = 4602511) B4602511
theorem B2270303 : Blo 1512953 2270303 := bstep (se 1 (by rfl) ⟨1702727, by rfl⟩ : syracuseStep 2270303 = 3405455) B3405455
theorem B7660655 : Blo 1512953 7660655 := bstep (se 1 (by rfl) ⟨5745491, by rfl⟩ : syracuseStep 7660655 = 11490983) B11490983
theorem B2270363 : Blo 1512953 2270363 := bstep (se 1 (by rfl) ⟨1702772, by rfl⟩ : syracuseStep 2270363 = 3405545) B3405545
theorem B12928247 : Blo 1512953 12928247 := bstep (se 1 (by rfl) ⟨9696185, by rfl⟩ : syracuseStep 12928247 = 19392371) B19392371
theorem B7767353 : Blo 1512953 7767353 := bstep (se 2 (by rfl) ⟨2912757, by rfl⟩ : syracuseStep 7767353 = 5825515) B5825515
theorem B14550353 : Blo 1512953 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B2590199 : Blo 1512953 2590199 := bstep (se 1 (by rfl) ⟨1942649, by rfl⟩ : syracuseStep 2590199 = 3885299) B3885299
theorem B7669241 : Blo 1512953 7669241 := bstep (se 2 (by rfl) ⟨2875965, by rfl⟩ : syracuseStep 7669241 = 5751931) B5751931
theorem B2270825 : Blo 1512953 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B2270951 : Blo 1512953 2270951 := bstep (se 1 (by rfl) ⟨1703213, by rfl⟩ : syracuseStep 2270951 = 3406427) B3406427
theorem B2271047 : Blo 1512953 2271047 := bstep (se 1 (by rfl) ⟨1703285, by rfl⟩ : syracuseStep 2271047 = 3406571) B3406571
theorem B4089683 : Blo 1512953 4089683 := bstep (se 1 (by rfl) ⟨3067262, by rfl⟩ : syracuseStep 4089683 = 6134525) B6134525
theorem B8300537 : Blo 1512953 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B7874779 : Blo 1512953 7874779 := bstep (se 1 (by rfl) ⟨5906084, by rfl⟩ : syracuseStep 7874779 = 11812169) B11812169
theorem B7661789 : Blo 1512953 7661789 := bstep (se 3 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 7661789 = 2873171) B2873171
theorem B2271455 : Blo 1512953 2271455 := bstep (se 1 (by rfl) ⟨1703591, by rfl⟩ : syracuseStep 2271455 = 3407183) B3407183
theorem B2271515 : Blo 1512953 2271515 := bstep (se 1 (by rfl) ⟨1703636, by rfl⟩ : syracuseStep 2271515 = 3407273) B3407273
theorem B2271647 : Blo 1512953 2271647 := bstep (se 1 (by rfl) ⟨1703735, by rfl⟩ : syracuseStep 2271647 = 3407471) B3407471
theorem B2156969 : Blo 1512953 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B8620607 : Blo 1512953 8620607 := bstep (se 1 (by rfl) ⟨6465455, by rfl⟩ : syracuseStep 8620607 = 12930911) B12930911
theorem B19409489 : Blo 1512953 19409489 := bstep (se 2 (by rfl) ⟨7278558, by rfl⟩ : syracuseStep 19409489 = 14557117) B14557117
theorem B2271839 : Blo 1512953 2271839 := bstep (se 1 (by rfl) ⟨1703879, by rfl⟩ : syracuseStep 2271839 = 3407759) B3407759
theorem B4852361 : Blo 1512953 4852361 := bstep (se 2 (by rfl) ⟨1819635, by rfl⟩ : syracuseStep 4852361 = 3639271) B3639271
theorem B3885833 : Blo 1512953 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B4090753 : Blo 1512953 4090753 := bstep (se 2 (by rfl) ⟨1534032, by rfl⟩ : syracuseStep 4090753 = 3068065) B3068065
theorem B2272169 : Blo 1512953 2272169 := bstep (se 2 (by rfl) ⟨852063, by rfl⟩ : syracuseStep 2272169 = 1704127) B1704127
theorem B2272199 : Blo 1512953 2272199 := bstep (se 1 (by rfl) ⟨1704149, by rfl⟩ : syracuseStep 2272199 = 3408299) B3408299
theorem B2272319 : Blo 1512953 2272319 := bstep (se 1 (by rfl) ⟨1704239, by rfl⟩ : syracuseStep 2272319 = 3408479) B3408479
theorem B67284377 : Blo 1512953 67284377 := bstep (se 2 (by rfl) ⟨25231641, by rfl⟩ : syracuseStep 67284377 = 50463283) B50463283
theorem B7663085 : Blo 1512953 7663085 := bstep (se 3 (by rfl) ⟨1436828, by rfl⟩ : syracuseStep 7663085 = 2873657) B2873657
theorem B9694903 : Blo 1512953 9694903 := bstep (se 1 (by rfl) ⟨7271177, by rfl⟩ : syracuseStep 9694903 = 14542355) B14542355
theorem B15535901 : Blo 1512953 15535901 := bstep (se 3 (by rfl) ⟨2912981, by rfl⟩ : syracuseStep 15535901 = 5825963) B5825963
theorem B14552891 : Blo 1512953 14552891 := bstep (se 1 (by rfl) ⟨10914668, by rfl⟩ : syracuseStep 14552891 = 21829337) B21829337
theorem B20721529 : Blo 1512953 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B32755589 : Blo 1512953 32755589 := bstep (se 4 (by rfl) ⟨3070836, by rfl⟩ : syracuseStep 32755589 = 6141673) B6141673
theorem B3067951 : Blo 1512953 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B34975795 : Blo 1512953 34975795 := bstep (se 1 (by rfl) ⟨26231846, by rfl⟩ : syracuseStep 34975795 = 52463693) B52463693
theorem B8179775 : Blo 1512953 8179775 := bstep (se 1 (by rfl) ⟨6134831, by rfl⟩ : syracuseStep 8179775 = 12269663) B12269663
theorem B4092029 : Blo 1512953 4092029 := bstep (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) B1534511
theorem B14741975 : Blo 1512953 14741975 := bstep (se 1 (by rfl) ⟨11056481, by rfl⟩ : syracuseStep 14741975 = 22112963) B22112963
theorem B11498273 : Blo 1512953 11498273 := bstep (se 2 (by rfl) ⟨4311852, by rfl⟩ : syracuseStep 11498273 = 8623705) B8623705
theorem B11498759 : Blo 1512953 11498759 := bstep (se 1 (by rfl) ⟨8624069, by rfl⟩ : syracuseStep 11498759 = 17248139) B17248139
theorem B1512959 : Blo 1512953 1512959 := bstep (se 1 (by rfl) ⟨1134719, by rfl⟩ : syracuseStep 1512959 = 2269439) B2269439
theorem B3405599 : Blo 1512953 3405599 := bstep (se 1 (by rfl) ⟨2554199, by rfl⟩ : syracuseStep 3405599 = 5108399) B5108399
theorem B2045819 : Blo 1512953 2045819 := bstep (se 1 (by rfl) ⟨1534364, by rfl⟩ : syracuseStep 2045819 = 3068729) B3068729
theorem B1513503 : Blo 1512953 1513503 := bstep (se 1 (by rfl) ⟨1135127, by rfl⟩ : syracuseStep 1513503 = 2270255) B2270255
theorem B1513583 : Blo 1512953 1513583 := bstep (se 1 (by rfl) ⟨1135187, by rfl⟩ : syracuseStep 1513583 = 2270375) B2270375
theorem B2553977 : Blo 1512953 2553977 := bstep (se 2 (by rfl) ⟨957741, by rfl⟩ : syracuseStep 2553977 = 1915483) B1915483
theorem B2554031 : Blo 1512953 2554031 := bstep (se 1 (by rfl) ⟨1915523, by rfl⟩ : syracuseStep 2554031 = 3831047) B3831047
theorem B17242307 : Blo 1512953 17242307 := bstep (se 1 (by rfl) ⟨12931730, by rfl⟩ : syracuseStep 17242307 = 25863461) B25863461
theorem B26220763 : Blo 1512953 26220763 := bstep (se 1 (by rfl) ⟨19665572, by rfl⟩ : syracuseStep 26220763 = 39331145) B39331145
theorem B2873627 : Blo 1512953 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B5110073 : Blo 1512953 5110073 := bstep (se 2 (by rfl) ⟨1916277, by rfl⟩ : syracuseStep 5110073 = 3832555) B3832555
theorem B1513831 : Blo 1512953 1513831 := bstep (se 1 (by rfl) ⟨1135373, by rfl⟩ : syracuseStep 1513831 = 2270747) B2270747
theorem B82860509 : Blo 1512953 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B4094441 : Blo 1512953 4094441 := bstep (se 2 (by rfl) ⟨1535415, by rfl⟩ : syracuseStep 4094441 = 3070831) B3070831
theorem B3635705 : Blo 1512953 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B2046511 : Blo 1512953 2046511 := bstep (se 1 (by rfl) ⟨1534883, by rfl⟩ : syracuseStep 2046511 = 3069767) B3069767
theorem B1514087 : Blo 1512953 1514087 := bstep (se 1 (by rfl) ⟨1135565, by rfl⟩ : syracuseStep 1514087 = 2271131) B2271131
theorem B1514111 : Blo 1512953 1514111 := bstep (se 1 (by rfl) ⟨1135583, by rfl⟩ : syracuseStep 1514111 = 2271167) B2271167
theorem B1514235 : Blo 1512953 1514235 := bstep (se 1 (by rfl) ⟨1135676, by rfl⟩ : syracuseStep 1514235 = 2271353) B2271353
theorem B7666487 : Blo 1512953 7666487 := bstep (se 1 (by rfl) ⟨5749865, by rfl⟩ : syracuseStep 7666487 = 11499731) B11499731
theorem B44866381 : Blo 1512953 44866381 := bstep (se 3 (by rfl) ⟨8412446, by rfl⟩ : syracuseStep 44866381 = 16824893) B16824893
theorem B1514491 : Blo 1512953 1514491 := bstep (se 1 (by rfl) ⟨1135868, by rfl⟩ : syracuseStep 1514491 = 2271737) B2271737
theorem B1702939 : Blo 1512953 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B1514527 : Blo 1512953 1514527 := bstep (se 1 (by rfl) ⟨1135895, by rfl⟩ : syracuseStep 1514527 = 2271791) B2271791
theorem B11492441 : Blo 1512953 11492441 := bstep (se 2 (by rfl) ⟨4309665, by rfl⟩ : syracuseStep 11492441 = 8619331) B8619331
theorem B2874599 : Blo 1512953 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B1514815 : Blo 1512953 1514815 := bstep (se 1 (by rfl) ⟨1136111, by rfl⟩ : syracuseStep 1514815 = 2272223) B2272223
theorem B141712757 : Blo 1512953 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B5750777 : Blo 1512953 5750777 := bstep (se 2 (by rfl) ⟨2156541, by rfl⟩ : syracuseStep 5750777 = 4313083) B4313083
theorem B1703407 : Blo 1512953 1703407 := bstep (se 1 (by rfl) ⟨1277555, by rfl⟩ : syracuseStep 1703407 = 2555111) B2555111
theorem B4308527 : Blo 1512953 4308527 := bstep (se 1 (by rfl) ⟨3231395, by rfl⟩ : syracuseStep 4308527 = 6462791) B6462791
theorem B11492927 : Blo 1512953 11492927 := bstep (se 1 (by rfl) ⟨8619695, by rfl⟩ : syracuseStep 11492927 = 17239391) B17239391
theorem B3407543 : Blo 1512953 3407543 := bstep (se 1 (by rfl) ⟨2555657, by rfl⟩ : syracuseStep 3407543 = 5111315) B5111315
theorem B16367417 : Blo 1512953 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B2555759 : Blo 1512953 2555759 := bstep (se 1 (by rfl) ⟨1916819, by rfl⟩ : syracuseStep 2555759 = 3833639) B3833639
theorem B32759741 : Blo 1512953 32759741 := bstep (se 3 (by rfl) ⟨6142451, by rfl⟩ : syracuseStep 32759741 = 12284903) B12284903
theorem B8626121 : Blo 1512953 8626121 := bstep (se 2 (by rfl) ⟨3234795, by rfl⟩ : syracuseStep 8626121 = 6469591) B6469591
theorem B2728019 : Blo 1512953 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B3833993 : Blo 1512953 3833993 := bstep (se 2 (by rfl) ⟨1437747, by rfl⟩ : syracuseStep 3833993 = 2875495) B2875495
theorem B3408425 : Blo 1512953 3408425 := bstep (se 2 (by rfl) ⟨1278159, by rfl⟩ : syracuseStep 3408425 = 2556319) B2556319
theorem B8618831 : Blo 1512953 8618831 := bstep (se 1 (by rfl) ⟨6464123, by rfl⟩ : syracuseStep 8618831 = 12928247) B12928247
theorem B9700235 : Blo 1512953 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B5112827 : Blo 1512953 5112827 := bstep (se 1 (by rfl) ⟨3834620, by rfl⟩ : syracuseStep 5112827 = 7669241) B7669241
theorem B5751917 : Blo 1512953 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B2270399 : Blo 1512953 2270399 := bstep (se 1 (by rfl) ⟨1702799, by rfl⟩ : syracuseStep 2270399 = 3405599) B3405599
theorem B2270585 : Blo 1512953 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B11494871 : Blo 1512953 11494871 := bstep (se 1 (by rfl) ⟨8621153, by rfl⟩ : syracuseStep 11494871 = 17242307) B17242307
theorem B55240339 : Blo 1512953 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B2729627 : Blo 1512953 2729627 := bstep (se 1 (by rfl) ⟨2047220, by rfl⟩ : syracuseStep 2729627 = 4094441) B4094441
theorem B2590555 : Blo 1512953 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B17237933 : Blo 1512953 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B2271209 : Blo 1512953 2271209 := bstep (se 2 (by rfl) ⟨851703, by rfl⟩ : syracuseStep 2271209 = 1703407) B1703407
theorem B7661627 : Blo 1512953 7661627 := bstep (se 1 (by rfl) ⟨5746220, by rfl⟩ : syracuseStep 7661627 = 11492441) B11492441
theorem B7661951 : Blo 1512953 7661951 := bstep (se 1 (by rfl) ⟨5746463, by rfl⟩ : syracuseStep 7661951 = 11492927) B11492927
theorem B2271695 : Blo 1512953 2271695 := bstep (se 1 (by rfl) ⟨1703771, by rfl⟩ : syracuseStep 2271695 = 3407543) B3407543
theorem B10357267 : Blo 1512953 10357267 := bstep (se 1 (by rfl) ⟨7767950, by rfl⟩ : syracuseStep 10357267 = 15535901) B15535901
theorem B9701927 : Blo 1512953 9701927 := bstep (se 1 (by rfl) ⟨7276445, by rfl⟩ : syracuseStep 9701927 = 14552891) B14552891
theorem B4090601 : Blo 1512953 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B10914725 : Blo 1512953 10914725 := bstep (se 4 (by rfl) ⟨1023255, by rfl⟩ : syracuseStep 10914725 = 2046511) B2046511
theorem B5107103 : Blo 1512953 5107103 := bstep (se 1 (by rfl) ⟨3830327, by rfl⟩ : syracuseStep 5107103 = 7660655) B7660655
theorem B20712941 : Blo 1512953 20712941 := bstep (se 3 (by rfl) ⟨3883676, by rfl⟩ : syracuseStep 20712941 = 7767353) B7767353
theorem B59821841 : Blo 1512953 59821841 := bstep (se 2 (by rfl) ⟨22433190, by rfl⟩ : syracuseStep 59821841 = 44866381) B44866381
theorem B9695213 : Blo 1512953 9695213 := bstep (se 3 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 9695213 = 3635705) B3635705
theorem B5533691 : Blo 1512953 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B5107859 : Blo 1512953 5107859 := bstep (se 1 (by rfl) ⟨3830894, by rfl⟩ : syracuseStep 5107859 = 7661789) B7661789
theorem B5747071 : Blo 1512953 5747071 := bstep (se 1 (by rfl) ⟨4310303, by rfl⟩ : syracuseStep 5747071 = 8620607) B8620607
theorem B12939659 : Blo 1512953 12939659 := bstep (se 1 (by rfl) ⟨9704744, by rfl⟩ : syracuseStep 12939659 = 19409489) B19409489
theorem B94475171 : Blo 1512953 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B44856251 : Blo 1512953 44856251 := bstep (se 1 (by rfl) ⟨33642188, by rfl⟩ : syracuseStep 44856251 = 67284377) B67284377
theorem B3833851 : Blo 1512953 3833851 := bstep (se 1 (by rfl) ⟨2875388, by rfl⟩ : syracuseStep 3833851 = 5750777) B5750777
theorem B5108723 : Blo 1512953 5108723 := bstep (se 1 (by rfl) ⟨3831542, by rfl⟩ : syracuseStep 5108723 = 7663085) B7663085
theorem B2872351 : Blo 1512953 2872351 := bstep (se 1 (by rfl) ⟨2154263, by rfl⟩ : syracuseStep 2872351 = 4308527) B4308527
theorem B27628705 : Blo 1512953 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B21837059 : Blo 1512953 21837059 := bstep (se 1 (by rfl) ⟨16377794, by rfl⟩ : syracuseStep 21837059 = 32755589) B32755589
theorem B5453183 : Blo 1512953 5453183 := bstep (se 1 (by rfl) ⟨4089887, by rfl⟩ : syracuseStep 5453183 = 8179775) B8179775
theorem B46634393 : Blo 1512953 46634393 := bstep (se 2 (by rfl) ⟨17487897, by rfl⟩ : syracuseStep 46634393 = 34975795) B34975795
theorem B18404779 : Blo 1512953 18404779 := bstep (se 1 (by rfl) ⟨13803584, by rfl⟩ : syracuseStep 18404779 = 27607169) B27607169
theorem B1512991 : Blo 1512953 1512991 := bstep (se 1 (by rfl) ⟨1134743, by rfl⟩ : syracuseStep 1512991 = 2269487) B2269487
theorem B10499705 : Blo 1512953 10499705 := bstep (se 2 (by rfl) ⟨3937389, by rfl⟩ : syracuseStep 10499705 = 7874779) B7874779
theorem B34961017 : Blo 1512953 34961017 := bstep (se 2 (by rfl) ⟨13110381, by rfl⟩ : syracuseStep 34961017 = 26220763) B26220763
theorem B9827983 : Blo 1512953 9827983 := bstep (se 1 (by rfl) ⟨7370987, by rfl⟩ : syracuseStep 9827983 = 14741975) B14741975
theorem B1513151 : Blo 1512953 1513151 := bstep (se 1 (by rfl) ⟨1134863, by rfl⟩ : syracuseStep 1513151 = 2269727) B2269727
theorem B1513191 : Blo 1512953 1513191 := bstep (se 1 (by rfl) ⟨1134893, by rfl⟩ : syracuseStep 1513191 = 2269787) B2269787
theorem B7665515 : Blo 1512953 7665515 := bstep (se 1 (by rfl) ⟨5749136, by rfl⟩ : syracuseStep 7665515 = 11498273) B11498273
theorem B1513535 : Blo 1512953 1513535 := bstep (se 1 (by rfl) ⟨1135151, by rfl⟩ : syracuseStep 1513535 = 2270303) B2270303
theorem B1513575 : Blo 1512953 1513575 := bstep (se 1 (by rfl) ⟨1135181, by rfl⟩ : syracuseStep 1513575 = 2270363) B2270363
theorem B7665839 : Blo 1512953 7665839 := bstep (se 1 (by rfl) ⟨5749379, by rfl⟩ : syracuseStep 7665839 = 11498759) B11498759
theorem B13818185 : Blo 1512953 13818185 := bstep (se 2 (by rfl) ⟨5181819, by rfl⟩ : syracuseStep 13818185 = 10363639) B10363639
theorem B1726799 : Blo 1512953 1726799 := bstep (se 1 (by rfl) ⟨1295099, by rfl⟩ : syracuseStep 1726799 = 2590199) B2590199
theorem B1513883 : Blo 1512953 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B8182241 : Blo 1512953 8182241 := bstep (se 2 (by rfl) ⟨3068340, by rfl⟩ : syracuseStep 8182241 = 6136681) B6136681
theorem B1513967 : Blo 1512953 1513967 := bstep (se 1 (by rfl) ⟨1135475, by rfl⟩ : syracuseStep 1513967 = 2270951) B2270951
theorem B5454337 : Blo 1512953 5454337 := bstep (se 2 (by rfl) ⟨2045376, by rfl⟩ : syracuseStep 5454337 = 4090753) B4090753
theorem B1514031 : Blo 1512953 1514031 := bstep (se 1 (by rfl) ⟨1135523, by rfl⟩ : syracuseStep 1514031 = 2271047) B2271047
theorem B2726455 : Blo 1512953 2726455 := bstep (se 1 (by rfl) ⟨2044841, by rfl⟩ : syracuseStep 2726455 = 4089683) B4089683
theorem B1702651 : Blo 1512953 1702651 := bstep (se 1 (by rfl) ⟨1276988, by rfl⟩ : syracuseStep 1702651 = 2553977) B2553977
theorem B1702687 : Blo 1512953 1702687 := bstep (se 1 (by rfl) ⟨1277015, by rfl⟩ : syracuseStep 1702687 = 2554031) B2554031
theorem B1514303 : Blo 1512953 1514303 := bstep (se 1 (by rfl) ⟨1135727, by rfl⟩ : syracuseStep 1514303 = 2271455) B2271455
theorem B1915751 : Blo 1512953 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B1514343 : Blo 1512953 1514343 := bstep (se 1 (by rfl) ⟨1135757, by rfl⟩ : syracuseStep 1514343 = 2271515) B2271515
theorem B3406715 : Blo 1512953 3406715 := bstep (se 1 (by rfl) ⟨2555036, by rfl⟩ : syracuseStep 3406715 = 5110073) B5110073
theorem B1514431 : Blo 1512953 1514431 := bstep (se 1 (by rfl) ⟨1135823, by rfl⟩ : syracuseStep 1514431 = 2271647) B2271647
theorem B1514559 : Blo 1512953 1514559 := bstep (se 1 (by rfl) ⟨1135919, by rfl⟩ : syracuseStep 1514559 = 2271839) B2271839
theorem B3234907 : Blo 1512953 3234907 := bstep (se 1 (by rfl) ⟨2426180, by rfl⟩ : syracuseStep 3234907 = 4852361) B4852361
theorem B5110991 : Blo 1512953 5110991 := bstep (se 1 (by rfl) ⟨3833243, by rfl⟩ : syracuseStep 5110991 = 7666487) B7666487
theorem B1514779 : Blo 1512953 1514779 := bstep (se 1 (by rfl) ⟨1136084, by rfl⟩ : syracuseStep 1514779 = 2272169) B2272169
theorem B1514799 : Blo 1512953 1514799 := bstep (se 1 (by rfl) ⟨1136099, by rfl⟩ : syracuseStep 1514799 = 2272199) B2272199
theorem B1514879 : Blo 1512953 1514879 := bstep (se 1 (by rfl) ⟨1136159, by rfl⟩ : syracuseStep 1514879 = 2272319) B2272319
theorem B1916399 : Blo 1512953 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B12926537 : Blo 1512953 12926537 := bstep (se 2 (by rfl) ⟨4847451, by rfl⟩ : syracuseStep 12926537 = 9694903) B9694903
theorem B5455517 : Blo 1512953 5455517 := bstep (se 3 (by rfl) ⟨1022909, by rfl⟩ : syracuseStep 5455517 = 2045819) B2045819
theorem B10911611 : Blo 1512953 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B1703839 : Blo 1512953 1703839 := bstep (se 1 (by rfl) ⟨1277879, by rfl⟩ : syracuseStep 1703839 = 2555759) B2555759
theorem B21839827 : Blo 1512953 21839827 := bstep (se 1 (by rfl) ⟨16379870, by rfl⟩ : syracuseStep 21839827 = 32759741) B32759741
theorem B5750747 : Blo 1512953 5750747 := bstep (se 1 (by rfl) ⟨4313060, by rfl⟩ : syracuseStep 5750747 = 8626121) B8626121
theorem B1818679 : Blo 1512953 1818679 := bstep (se 1 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 1818679 = 2728019) B2728019
theorem B2555995 : Blo 1512953 2555995 := bstep (se 1 (by rfl) ⟨1916996, by rfl⟩ : syracuseStep 2555995 = 3833993) B3833993
theorem B8626439 : Blo 1512953 8626439 := bstep (se 1 (by rfl) ⟨6469829, by rfl⟩ : syracuseStep 8626439 = 12939659) B12939659
theorem B3408551 : Blo 1512953 3408551 := bstep (se 1 (by rfl) ⟨2556413, by rfl⟩ : syracuseStep 3408551 = 5112827) B5112827
theorem B3834611 : Blo 1512953 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B14558039 : Blo 1512953 14558039 := bstep (se 1 (by rfl) ⟨10918529, by rfl⟩ : syracuseStep 14558039 = 21837059) B21837059
theorem B4604797 : Blo 1512953 4604797 := bstep (se 3 (by rfl) ⟨863399, by rfl⟩ : syracuseStep 4604797 = 1726799) B1726799
theorem B31089595 : Blo 1512953 31089595 := bstep (se 1 (by rfl) ⟨23317196, by rfl⟩ : syracuseStep 31089595 = 46634393) B46634393
theorem B2270201 : Blo 1512953 2270201 := bstep (se 2 (by rfl) ⟨851325, by rfl⟩ : syracuseStep 2270201 = 1702651) B1702651
theorem B2270249 : Blo 1512953 2270249 := bstep (se 2 (by rfl) ⟨851343, by rfl⟩ : syracuseStep 2270249 = 1702687) B1702687
theorem B1819751 : Blo 1512953 1819751 := bstep (se 1 (by rfl) ⟨1364813, by rfl⟩ : syracuseStep 1819751 = 2729627) B2729627
theorem B2271143 : Blo 1512953 2271143 := bstep (se 1 (by rfl) ⟨1703357, by rfl⟩ : syracuseStep 2271143 = 3406715) B3406715
theorem B7276483 : Blo 1512953 7276483 := bstep (se 1 (by rfl) ⟨5457362, by rfl⟩ : syracuseStep 7276483 = 10914725) B10914725
theorem B46614689 : Blo 1512953 46614689 := bstep (se 2 (by rfl) ⟨17480508, by rfl⟩ : syracuseStep 46614689 = 34961017) B34961017
theorem B39881227 : Blo 1512953 39881227 := bstep (se 1 (by rfl) ⟨29910920, by rfl⟩ : syracuseStep 39881227 = 59821841) B59821841
theorem B2271785 : Blo 1512953 2271785 := bstep (se 2 (by rfl) ⟨851919, by rfl⟩ : syracuseStep 2271785 = 1703839) B1703839
theorem B14756509 : Blo 1512953 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B2272283 : Blo 1512953 2272283 := bstep (se 1 (by rfl) ⟨1704212, by rfl⟩ : syracuseStep 2272283 = 3408425) B3408425
theorem B7662761 : Blo 1512953 7662761 := bstep (se 2 (by rfl) ⟨2873535, by rfl⟩ : syracuseStep 7662761 = 5747071) B5747071
theorem B5745887 : Blo 1512953 5745887 := bstep (se 1 (by rfl) ⟨4309415, by rfl⟩ : syracuseStep 5745887 = 8618831) B8618831
theorem B6466823 : Blo 1512953 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B29904167 : Blo 1512953 29904167 := bstep (se 1 (by rfl) ⟨22428125, by rfl⟩ : syracuseStep 29904167 = 44856251) B44856251
theorem B7663247 : Blo 1512953 7663247 := bstep (se 1 (by rfl) ⟨5747435, by rfl⟩ : syracuseStep 7663247 = 11494871) B11494871
theorem B6999803 : Blo 1512953 6999803 := bstep (se 1 (by rfl) ⟨5249852, by rfl⟩ : syracuseStep 6999803 = 10499705) B10499705
theorem B5111801 : Blo 1512953 5111801 := bstep (se 2 (by rfl) ⟨1916925, by rfl⟩ : syracuseStep 5111801 = 3833851) B3833851
theorem B5107751 : Blo 1512953 5107751 := bstep (se 1 (by rfl) ⟨3830813, by rfl⟩ : syracuseStep 5107751 = 7661627) B7661627
theorem B3829801 : Blo 1512953 3829801 := bstep (se 2 (by rfl) ⟨1436175, by rfl⟩ : syracuseStep 3829801 = 2872351) B2872351
theorem B4313209 : Blo 1512953 4313209 := bstep (se 2 (by rfl) ⟨1617453, by rfl⟩ : syracuseStep 4313209 = 3234907) B3234907
theorem B9212123 : Blo 1512953 9212123 := bstep (se 1 (by rfl) ⟨6909092, by rfl⟩ : syracuseStep 9212123 = 13818185) B13818185
theorem B5107967 : Blo 1512953 5107967 := bstep (se 1 (by rfl) ⟨3830975, by rfl⟩ : syracuseStep 5107967 = 7661951) B7661951
theorem B6467951 : Blo 1512953 6467951 := bstep (se 1 (by rfl) ⟨4850963, by rfl⟩ : syracuseStep 6467951 = 9701927) B9701927
theorem B24539705 : Blo 1512953 24539705 := bstep (se 2 (by rfl) ⟨9202389, by rfl⟩ : syracuseStep 24539705 = 18404779) B18404779
theorem B10908269 : Blo 1512953 10908269 := bstep (se 3 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 10908269 = 4090601) B4090601
theorem B13103977 : Blo 1512953 13103977 := bstep (se 2 (by rfl) ⟨4913991, by rfl⟩ : syracuseStep 13103977 = 9827983) B9827983
theorem B5108669 : Blo 1512953 5108669 := bstep (se 3 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 5108669 = 1915751) B1915751
theorem B3404735 : Blo 1512953 3404735 := bstep (se 1 (by rfl) ⟨2553551, by rfl⟩ : syracuseStep 3404735 = 5107103) B5107103
theorem B13808627 : Blo 1512953 13808627 := bstep (se 1 (by rfl) ⟨10356470, by rfl⟩ : syracuseStep 13808627 = 20712941) B20712941
theorem B251933789 : Blo 1512953 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B3454073 : Blo 1512953 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B29119769 : Blo 1512953 29119769 := bstep (se 2 (by rfl) ⟨10919913, by rfl⟩ : syracuseStep 29119769 = 21839827) B21839827
theorem B3405239 : Blo 1512953 3405239 := bstep (se 1 (by rfl) ⟨2553929, by rfl⟩ : syracuseStep 3405239 = 5107859) B5107859
theorem B3405815 : Blo 1512953 3405815 := bstep (se 1 (by rfl) ⟨2554361, by rfl⟩ : syracuseStep 3405815 = 5108723) B5108723
theorem B7272449 : Blo 1512953 7272449 := bstep (se 2 (by rfl) ⟨2727168, by rfl⟩ : syracuseStep 7272449 = 5454337) B5454337
theorem B13809689 : Blo 1512953 13809689 := bstep (se 2 (by rfl) ⟨5178633, by rfl⟩ : syracuseStep 13809689 = 10357267) B10357267
theorem B3635273 : Blo 1512953 3635273 := bstep (se 2 (by rfl) ⟨1363227, by rfl⟩ : syracuseStep 3635273 = 2726455) B2726455
theorem B1513599 : Blo 1512953 1513599 := bstep (se 1 (by rfl) ⟨1135199, by rfl⟩ : syracuseStep 1513599 = 2270399) B2270399
theorem B1513723 : Blo 1512953 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B3635455 : Blo 1512953 3635455 := bstep (se 1 (by rfl) ⟨2726591, by rfl⟩ : syracuseStep 3635455 = 5453183) B5453183
theorem B5110343 : Blo 1512953 5110343 := bstep (se 1 (by rfl) ⟨3832757, by rfl⟩ : syracuseStep 5110343 = 7665515) B7665515
theorem B11491955 : Blo 1512953 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B5110397 : Blo 1512953 5110397 := bstep (se 3 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 5110397 = 1916399) B1916399
theorem B1514139 : Blo 1512953 1514139 := bstep (se 1 (by rfl) ⟨1135604, by rfl⟩ : syracuseStep 1514139 = 2271209) B2271209
theorem B5110559 : Blo 1512953 5110559 := bstep (se 1 (by rfl) ⟨3832919, by rfl⟩ : syracuseStep 5110559 = 7665839) B7665839
theorem B36838273 : Blo 1512953 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B1514463 : Blo 1512953 1514463 := bstep (se 1 (by rfl) ⟨1135847, by rfl⟩ : syracuseStep 1514463 = 2271695) B2271695
theorem B5454827 : Blo 1512953 5454827 := bstep (se 1 (by rfl) ⟨4091120, by rfl⟩ : syracuseStep 5454827 = 8182241) B8182241
theorem B14548045 : Blo 1512953 14548045 := bstep (se 3 (by rfl) ⟨2727758, by rfl⟩ : syracuseStep 14548045 = 5455517) B5455517
theorem B3407327 : Blo 1512953 3407327 := bstep (se 1 (by rfl) ⟨2555495, by rfl⟩ : syracuseStep 3407327 = 5110991) B5110991
theorem B73653785 : Blo 1512953 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B8617691 : Blo 1512953 8617691 := bstep (se 1 (by rfl) ⟨6463268, by rfl⟩ : syracuseStep 8617691 = 12926537) B12926537
theorem B7274407 : Blo 1512953 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B3833831 : Blo 1512953 3833831 := bstep (se 1 (by rfl) ⟨2875373, by rfl⟩ : syracuseStep 3833831 = 5750747) B5750747
theorem B6463475 : Blo 1512953 6463475 := bstep (se 1 (by rfl) ⟨4847606, by rfl⟩ : syracuseStep 6463475 = 9695213) B9695213
theorem B2424905 : Blo 1512953 2424905 := bstep (se 2 (by rfl) ⟨909339, by rfl⟩ : syracuseStep 2424905 = 1818679) B1818679
theorem B3407993 : Blo 1512953 3407993 := bstep (se 2 (by rfl) ⟨1277997, by rfl⟩ : syracuseStep 3407993 = 2555995) B2555995
theorem B5750945 : Blo 1512953 5750945 := bstep (se 2 (by rfl) ⟨2156604, by rfl⟩ : syracuseStep 5750945 = 4313209) B4313209
theorem B5750959 : Blo 1512953 5750959 := bstep (se 1 (by rfl) ⟨4313219, by rfl⟩ : syracuseStep 5750959 = 8626439) B8626439
theorem B16359803 : Blo 1512953 16359803 := bstep (se 1 (by rfl) ⟨12269852, by rfl⟩ : syracuseStep 16359803 = 24539705) B24539705
theorem B2556407 : Blo 1512953 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B2269823 : Blo 1512953 2269823 := bstep (se 1 (by rfl) ⟨1702367, by rfl⟩ : syracuseStep 2269823 = 3404735) B3404735
theorem B53174969 : Blo 1512953 53174969 := bstep (se 2 (by rfl) ⟨19940613, by rfl⟩ : syracuseStep 53174969 = 39881227) B39881227
theorem B2302715 : Blo 1512953 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B2270159 : Blo 1512953 2270159 := bstep (se 1 (by rfl) ⟨1702619, by rfl⟩ : syracuseStep 2270159 = 3405239) B3405239
theorem B41452793 : Blo 1512953 41452793 := bstep (se 2 (by rfl) ⟨15544797, by rfl⟩ : syracuseStep 41452793 = 31089595) B31089595
theorem B2270543 : Blo 1512953 2270543 := bstep (se 1 (by rfl) ⟨1702907, by rfl⟩ : syracuseStep 2270543 = 3405815) B3405815
theorem B7661303 : Blo 1512953 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B4311215 : Blo 1512953 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B2271551 : Blo 1512953 2271551 := bstep (se 1 (by rfl) ⟨1703663, by rfl⟩ : syracuseStep 2271551 = 3407327) B3407327
theorem B5745127 : Blo 1512953 5745127 := bstep (se 1 (by rfl) ⟨4308845, by rfl⟩ : syracuseStep 5745127 = 8617691) B8617691
theorem B9701977 : Blo 1512953 9701977 := bstep (se 2 (by rfl) ⟨3638241, by rfl⟩ : syracuseStep 9701977 = 7276483) B7276483
theorem B5106401 : Blo 1512953 5106401 := bstep (se 2 (by rfl) ⟨1914900, by rfl⟩ : syracuseStep 5106401 = 3829801) B3829801
theorem B4311967 : Blo 1512953 4311967 := bstep (se 1 (by rfl) ⟨3233975, by rfl⟩ : syracuseStep 4311967 = 6467951) B6467951
theorem B4852669 : Blo 1512953 4852669 := bstep (se 3 (by rfl) ⟨909875, by rfl⟩ : syracuseStep 4852669 = 1819751) B1819751
theorem B2272367 : Blo 1512953 2272367 := bstep (se 1 (by rfl) ⟨1704275, by rfl⟩ : syracuseStep 2272367 = 3408551) B3408551
theorem B167955859 : Blo 1512953 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B79744445 : Blo 1512953 79744445 := bstep (se 3 (by rfl) ⟨14952083, by rfl⟩ : syracuseStep 79744445 = 29904167) B29904167
theorem B6139729 : Blo 1512953 6139729 := bstep (se 2 (by rfl) ⟨2302398, by rfl⟩ : syracuseStep 6139729 = 4604797) B4604797
theorem B31076459 : Blo 1512953 31076459 := bstep (se 1 (by rfl) ⟨23307344, by rfl⟩ : syracuseStep 31076459 = 46614689) B46614689
theorem B5108507 : Blo 1512953 5108507 := bstep (se 1 (by rfl) ⟨3831380, by rfl⟩ : syracuseStep 5108507 = 7662761) B7662761
theorem B3830591 : Blo 1512953 3830591 := bstep (se 1 (by rfl) ⟨2872943, by rfl⟩ : syracuseStep 3830591 = 5745887) B5745887
theorem B5108831 : Blo 1512953 5108831 := bstep (se 1 (by rfl) ⟨3831623, by rfl⟩ : syracuseStep 5108831 = 7663247) B7663247
theorem B4666535 : Blo 1512953 4666535 := bstep (se 1 (by rfl) ⟨3499901, by rfl⟩ : syracuseStep 4666535 = 6999803) B6999803
theorem B3405167 : Blo 1512953 3405167 := bstep (se 1 (by rfl) ⟨2553875, by rfl⟩ : syracuseStep 3405167 = 5107751) B5107751
theorem B6141415 : Blo 1512953 6141415 := bstep (se 1 (by rfl) ⟨4606061, by rfl⟩ : syracuseStep 6141415 = 9212123) B9212123
theorem B3405311 : Blo 1512953 3405311 := bstep (se 1 (by rfl) ⟨2553983, by rfl⟩ : syracuseStep 3405311 = 5107967) B5107967
theorem B4847273 : Blo 1512953 4847273 := bstep (se 2 (by rfl) ⟨1817727, by rfl⟩ : syracuseStep 4847273 = 3635455) B3635455
theorem B7272179 : Blo 1512953 7272179 := bstep (se 1 (by rfl) ⟨5454134, by rfl⟩ : syracuseStep 7272179 = 10908269) B10908269
theorem B9705359 : Blo 1512953 9705359 := bstep (se 1 (by rfl) ⟨7279019, by rfl⟩ : syracuseStep 9705359 = 14558039) B14558039
theorem B3405779 : Blo 1512953 3405779 := bstep (se 1 (by rfl) ⟨2554334, by rfl⟩ : syracuseStep 3405779 = 5108669) B5108669
theorem B9205751 : Blo 1512953 9205751 := bstep (se 1 (by rfl) ⟨6904313, by rfl⟩ : syracuseStep 9205751 = 13808627) B13808627
theorem B1513467 : Blo 1512953 1513467 := bstep (se 1 (by rfl) ⟨1135100, by rfl⟩ : syracuseStep 1513467 = 2270201) B2270201
theorem B1513499 : Blo 1512953 1513499 := bstep (se 1 (by rfl) ⟨1135124, by rfl⟩ : syracuseStep 1513499 = 2270249) B2270249
theorem B19413179 : Blo 1512953 19413179 := bstep (se 1 (by rfl) ⟨14559884, by rfl⟩ : syracuseStep 19413179 = 29119769) B29119769
theorem B19675345 : Blo 1512953 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B17471969 : Blo 1512953 17471969 := bstep (se 2 (by rfl) ⟨6551988, by rfl⟩ : syracuseStep 17471969 = 13103977) B13103977
theorem B49117697 : Blo 1512953 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B1514095 : Blo 1512953 1514095 := bstep (se 1 (by rfl) ⟨1135571, by rfl⟩ : syracuseStep 1514095 = 2271143) B2271143
theorem B4848299 : Blo 1512953 4848299 := bstep (se 1 (by rfl) ⟨3636224, by rfl⟩ : syracuseStep 4848299 = 7272449) B7272449
theorem B9206459 : Blo 1512953 9206459 := bstep (se 1 (by rfl) ⟨6904844, by rfl⟩ : syracuseStep 9206459 = 13809689) B13809689
theorem B2423515 : Blo 1512953 2423515 := bstep (se 1 (by rfl) ⟨1817636, by rfl⟩ : syracuseStep 2423515 = 3635273) B3635273
theorem B19397393 : Blo 1512953 19397393 := bstep (se 2 (by rfl) ⟨7274022, by rfl⟩ : syracuseStep 19397393 = 14548045) B14548045
theorem B1514523 : Blo 1512953 1514523 := bstep (se 1 (by rfl) ⟨1135892, by rfl⟩ : syracuseStep 1514523 = 2271785) B2271785
theorem B3406895 : Blo 1512953 3406895 := bstep (se 1 (by rfl) ⟨2555171, by rfl⟩ : syracuseStep 3406895 = 5110343) B5110343
theorem B3406931 : Blo 1512953 3406931 := bstep (se 1 (by rfl) ⟨2555198, by rfl⟩ : syracuseStep 3406931 = 5110397) B5110397
theorem B3407039 : Blo 1512953 3407039 := bstep (se 1 (by rfl) ⟨2555279, by rfl⟩ : syracuseStep 3407039 = 5110559) B5110559
theorem B3636551 : Blo 1512953 3636551 := bstep (se 1 (by rfl) ⟨2727413, by rfl⟩ : syracuseStep 3636551 = 5454827) B5454827
theorem B1514855 : Blo 1512953 1514855 := bstep (se 1 (by rfl) ⟨1136141, by rfl⟩ : syracuseStep 1514855 = 2272283) B2272283
theorem B49102523 : Blo 1512953 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B9699209 : Blo 1512953 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B2555887 : Blo 1512953 2555887 := bstep (se 1 (by rfl) ⟨1916915, by rfl⟩ : syracuseStep 2555887 = 3833831) B3833831
theorem B4308983 : Blo 1512953 4308983 := bstep (se 1 (by rfl) ⟨3231737, by rfl⟩ : syracuseStep 4308983 = 6463475) B6463475
theorem B3407867 : Blo 1512953 3407867 := bstep (se 1 (by rfl) ⟨2555900, by rfl⟩ : syracuseStep 3407867 = 5111801) B5111801
theorem B20717639 : Blo 1512953 20717639 := bstep (se 1 (by rfl) ⟨15538229, by rfl⟩ : syracuseStep 20717639 = 31076459) B31076459
theorem B3833963 : Blo 1512953 3833963 := bstep (se 1 (by rfl) ⟨2875472, by rfl⟩ : syracuseStep 3833963 = 5750945) B5750945
theorem B7667945 : Blo 1512953 7667945 := bstep (se 2 (by rfl) ⟨2875479, by rfl⟩ : syracuseStep 7667945 = 5750959) B5750959
theorem B1704271 : Blo 1512953 1704271 := bstep (se 1 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 1704271 = 2556407) B2556407
theorem B7660169 : Blo 1512953 7660169 := bstep (se 2 (by rfl) ⟨2872563, by rfl⟩ : syracuseStep 7660169 = 5745127) B5745127
theorem B12935969 : Blo 1512953 12935969 := bstep (se 2 (by rfl) ⟨4850988, by rfl⟩ : syracuseStep 12935969 = 9701977) B9701977
theorem B2270111 : Blo 1512953 2270111 := bstep (se 1 (by rfl) ⟨1702583, by rfl⟩ : syracuseStep 2270111 = 3405167) B3405167
theorem B2270207 : Blo 1512953 2270207 := bstep (se 1 (by rfl) ⟨1702655, by rfl⟩ : syracuseStep 2270207 = 3405311) B3405311
theorem B2270519 : Blo 1512953 2270519 := bstep (se 1 (by rfl) ⟨1702889, by rfl⟩ : syracuseStep 2270519 = 3405779) B3405779
theorem B6137167 : Blo 1512953 6137167 := bstep (se 1 (by rfl) ⟨4602875, by rfl⟩ : syracuseStep 6137167 = 9205751) B9205751
theorem B32745131 : Blo 1512953 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B49776373 : Blo 1512953 49776373 := bstep (se 5 (by rfl) ⟨2333267, by rfl⟩ : syracuseStep 49776373 = 4666535) B4666535
theorem B6137639 : Blo 1512953 6137639 := bstep (se 1 (by rfl) ⟨4603229, by rfl⟩ : syracuseStep 6137639 = 9206459) B9206459
theorem B2271263 : Blo 1512953 2271263 := bstep (se 1 (by rfl) ⟨1703447, by rfl⟩ : syracuseStep 2271263 = 3406895) B3406895
theorem B2271287 : Blo 1512953 2271287 := bstep (se 1 (by rfl) ⟨1703465, by rfl⟩ : syracuseStep 2271287 = 3406931) B3406931
theorem B2271359 : Blo 1512953 2271359 := bstep (se 1 (by rfl) ⟨1703519, by rfl⟩ : syracuseStep 2271359 = 3407039) B3407039
theorem B25880957 : Blo 1512953 25880957 := bstep (se 3 (by rfl) ⟨4852679, by rfl⟩ : syracuseStep 25880957 = 9705359) B9705359
theorem B8186305 : Blo 1512953 8186305 := bstep (se 2 (by rfl) ⟨3069864, by rfl⟩ : syracuseStep 8186305 = 6139729) B6139729
theorem B6466139 : Blo 1512953 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B2271911 : Blo 1512953 2271911 := bstep (se 1 (by rfl) ⟨1703933, by rfl⟩ : syracuseStep 2271911 = 3407867) B3407867
theorem B1616603 : Blo 1512953 1616603 := bstep (se 1 (by rfl) ⟨1212452, by rfl⟩ : syracuseStep 1616603 = 2424905) B2424905
theorem B2271995 : Blo 1512953 2271995 := bstep (se 1 (by rfl) ⟨1703996, by rfl⟩ : syracuseStep 2271995 = 3407993) B3407993
theorem B10906535 : Blo 1512953 10906535 := bstep (se 1 (by rfl) ⟨8179901, by rfl⟩ : syracuseStep 10906535 = 16359803) B16359803
theorem B26233793 : Blo 1512953 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B35449979 : Blo 1512953 35449979 := bstep (se 1 (by rfl) ⟨26587484, by rfl⟩ : syracuseStep 35449979 = 53174969) B53174969
theorem B27635195 : Blo 1512953 27635195 := bstep (se 1 (by rfl) ⟨20726396, by rfl⟩ : syracuseStep 27635195 = 41452793) B41452793
theorem B3231353 : Blo 1512953 3231353 := bstep (se 2 (by rfl) ⟨1211757, by rfl⟩ : syracuseStep 3231353 = 2423515) B2423515
theorem B3231515 : Blo 1512953 3231515 := bstep (se 1 (by rfl) ⟨2423636, by rfl⟩ : syracuseStep 3231515 = 4847273) B4847273
theorem B5107535 : Blo 1512953 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B3232199 : Blo 1512953 3232199 := bstep (se 1 (by rfl) ⟨2424149, by rfl⟩ : syracuseStep 3232199 = 4848299) B4848299
theorem B3404267 : Blo 1512953 3404267 := bstep (se 1 (by rfl) ⟨2553200, by rfl⟩ : syracuseStep 3404267 = 5106401) B5106401
theorem B12931595 : Blo 1512953 12931595 := bstep (se 1 (by rfl) ⟨9698696, by rfl⟩ : syracuseStep 12931595 = 19397393) B19397393
theorem B223941145 : Blo 1512953 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B8188553 : Blo 1512953 8188553 := bstep (se 2 (by rfl) ⟨3070707, by rfl⟩ : syracuseStep 8188553 = 6141415) B6141415
theorem B6140573 : Blo 1512953 6140573 := bstep (se 3 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 6140573 = 2302715) B2302715
theorem B53162963 : Blo 1512953 53162963 := bstep (se 1 (by rfl) ⟨39872222, by rfl⟩ : syracuseStep 53162963 = 79744445) B79744445
theorem B2872655 : Blo 1512953 2872655 := bstep (se 1 (by rfl) ⟨2154491, by rfl⟩ : syracuseStep 2872655 = 4308983) B4308983
theorem B1513215 : Blo 1512953 1513215 := bstep (se 1 (by rfl) ⟨1134911, by rfl⟩ : syracuseStep 1513215 = 2269823) B2269823
theorem B3405671 : Blo 1512953 3405671 := bstep (se 1 (by rfl) ⟨2554253, by rfl⟩ : syracuseStep 3405671 = 5108507) B5108507
theorem B2553727 : Blo 1512953 2553727 := bstep (se 1 (by rfl) ⟨1915295, by rfl⟩ : syracuseStep 2553727 = 3830591) B3830591
theorem B1513439 : Blo 1512953 1513439 := bstep (se 1 (by rfl) ⟨1135079, by rfl⟩ : syracuseStep 1513439 = 2270159) B2270159
theorem B3405887 : Blo 1512953 3405887 := bstep (se 1 (by rfl) ⟨2554415, by rfl⟩ : syracuseStep 3405887 = 5108831) B5108831
theorem B1513695 : Blo 1512953 1513695 := bstep (se 1 (by rfl) ⟨1135271, by rfl⟩ : syracuseStep 1513695 = 2270543) B2270543
theorem B4848119 : Blo 1512953 4848119 := bstep (se 1 (by rfl) ⟨3636089, by rfl⟩ : syracuseStep 4848119 = 7272179) B7272179
theorem B5749289 : Blo 1512953 5749289 := bstep (se 2 (by rfl) ⟨2155983, by rfl⟩ : syracuseStep 5749289 = 4311967) B4311967
theorem B6470225 : Blo 1512953 6470225 := bstep (se 2 (by rfl) ⟨2426334, by rfl⟩ : syracuseStep 6470225 = 4852669) B4852669
theorem B2874143 : Blo 1512953 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B12942119 : Blo 1512953 12942119 := bstep (se 1 (by rfl) ⟨9706589, by rfl⟩ : syracuseStep 12942119 = 19413179) B19413179
theorem B1514367 : Blo 1512953 1514367 := bstep (se 1 (by rfl) ⟨1135775, by rfl⟩ : syracuseStep 1514367 = 2271551) B2271551
theorem B11647979 : Blo 1512953 11647979 := bstep (se 1 (by rfl) ⟨8735984, by rfl⟩ : syracuseStep 11647979 = 17471969) B17471969
theorem B1514911 : Blo 1512953 1514911 := bstep (se 1 (by rfl) ⟨1136183, by rfl⟩ : syracuseStep 1514911 = 2272367) B2272367
theorem B2424367 : Blo 1512953 2424367 := bstep (se 1 (by rfl) ⟨1818275, by rfl⟩ : syracuseStep 2424367 = 3636551) B3636551
theorem B32735015 : Blo 1512953 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B3407849 : Blo 1512953 3407849 := bstep (se 2 (by rfl) ⟨1277943, by rfl⟩ : syracuseStep 3407849 = 2555887) B2555887
theorem B13811759 : Blo 1512953 13811759 := bstep (se 1 (by rfl) ⟨10358819, by rfl⟩ : syracuseStep 13811759 = 20717639) B20717639
theorem B2555975 : Blo 1512953 2555975 := bstep (se 1 (by rfl) ⟨1916981, by rfl⟩ : syracuseStep 2555975 = 3833963) B3833963
theorem B5111963 : Blo 1512953 5111963 := bstep (se 1 (by rfl) ⟨3833972, by rfl⟩ : syracuseStep 5111963 = 7667945) B7667945
theorem B2154799 : Blo 1512953 2154799 := bstep (se 1 (by rfl) ⟨1616099, by rfl⟩ : syracuseStep 2154799 = 3232199) B3232199
theorem B2269511 : Blo 1512953 2269511 := bstep (se 1 (by rfl) ⟨1702133, by rfl⟩ : syracuseStep 2269511 = 3404267) B3404267
theorem B2270447 : Blo 1512953 2270447 := bstep (se 1 (by rfl) ⟨1702835, by rfl⟩ : syracuseStep 2270447 = 3405671) B3405671
theorem B2270591 : Blo 1512953 2270591 := bstep (se 1 (by rfl) ⟨1702943, by rfl⟩ : syracuseStep 2270591 = 3405887) B3405887
theorem B17253971 : Blo 1512953 17253971 := bstep (se 1 (by rfl) ⟨12940478, by rfl⟩ : syracuseStep 17253971 = 25880957) B25880957
theorem B4310759 : Blo 1512953 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B8628079 : Blo 1512953 8628079 := bstep (se 1 (by rfl) ⟨6471059, by rfl⟩ : syracuseStep 8628079 = 12942119) B12942119
theorem B29084093 : Blo 1512953 29084093 := bstep (se 3 (by rfl) ⟨5453267, by rfl⟩ : syracuseStep 29084093 = 10906535) B10906535
theorem B2271899 : Blo 1512953 2271899 := bstep (se 1 (by rfl) ⟨1703924, by rfl⟩ : syracuseStep 2271899 = 3407849) B3407849
theorem B8621063 : Blo 1512953 8621063 := bstep (se 1 (by rfl) ⟨6465797, by rfl⟩ : syracuseStep 8621063 = 12931595) B12931595
theorem B5106779 : Blo 1512953 5106779 := bstep (se 1 (by rfl) ⟨3830084, by rfl⟩ : syracuseStep 5106779 = 7660169) B7660169
theorem B5459035 : Blo 1512953 5459035 := bstep (se 1 (by rfl) ⟨4094276, by rfl⟩ : syracuseStep 5459035 = 8188553) B8188553
theorem B2272361 : Blo 1512953 2272361 := bstep (se 2 (by rfl) ⟨852135, by rfl⟩ : syracuseStep 2272361 = 1704271) B1704271
theorem B10915073 : Blo 1512953 10915073 := bstep (se 2 (by rfl) ⟨4093152, by rfl⟩ : syracuseStep 10915073 = 8186305) B8186305
theorem B35441975 : Blo 1512953 35441975 := bstep (se 1 (by rfl) ⟨26581481, by rfl⟩ : syracuseStep 35441975 = 53162963) B53162963
theorem B4091759 : Blo 1512953 4091759 := bstep (se 1 (by rfl) ⟨3068819, by rfl⟩ : syracuseStep 4091759 = 6137639) B6137639
theorem B3232079 : Blo 1512953 3232079 := bstep (se 1 (by rfl) ⟨2424059, by rfl⟩ : syracuseStep 3232079 = 4848119) B4848119
theorem B4313483 : Blo 1512953 4313483 := bstep (se 1 (by rfl) ⟨3235112, by rfl⟩ : syracuseStep 4313483 = 6470225) B6470225
theorem B3232489 : Blo 1512953 3232489 := bstep (se 2 (by rfl) ⟨1212183, by rfl⟩ : syracuseStep 3232489 = 2424367) B2424367
theorem B7664381 : Blo 1512953 7664381 := bstep (se 3 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 7664381 = 2874143) B2874143
theorem B66368497 : Blo 1512953 66368497 := bstep (se 2 (by rfl) ⟨24888186, by rfl⟩ : syracuseStep 66368497 = 49776373) B49776373
theorem B3404969 : Blo 1512953 3404969 := bstep (se 2 (by rfl) ⟨1276863, by rfl⟩ : syracuseStep 3404969 = 2553727) B2553727
theorem B3405023 : Blo 1512953 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B94533277 : Blo 1512953 94533277 := bstep (se 3 (by rfl) ⟨17724989, by rfl⟩ : syracuseStep 94533277 = 35449979) B35449979
theorem B4093715 : Blo 1512953 4093715 := bstep (se 1 (by rfl) ⟨3070286, by rfl⟩ : syracuseStep 4093715 = 6140573) B6140573
theorem B8623979 : Blo 1512953 8623979 := bstep (se 1 (by rfl) ⟨6467984, by rfl⟩ : syracuseStep 8623979 = 12935969) B12935969
theorem B1513407 : Blo 1512953 1513407 := bstep (se 1 (by rfl) ⟨1135055, by rfl⟩ : syracuseStep 1513407 = 2270111) B2270111
theorem B1513471 : Blo 1512953 1513471 := bstep (se 1 (by rfl) ⟨1135103, by rfl⟩ : syracuseStep 1513471 = 2270207) B2270207
theorem B298588193 : Blo 1512953 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B1513679 : Blo 1512953 1513679 := bstep (se 1 (by rfl) ⟨1135259, by rfl⟩ : syracuseStep 1513679 = 2270519) B2270519
theorem B1915103 : Blo 1512953 1915103 := bstep (se 1 (by rfl) ⟨1436327, by rfl⟩ : syracuseStep 1915103 = 2872655) B2872655
theorem B21830087 : Blo 1512953 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B1514175 : Blo 1512953 1514175 := bstep (se 1 (by rfl) ⟨1135631, by rfl⟩ : syracuseStep 1514175 = 2271263) B2271263
theorem B1514191 : Blo 1512953 1514191 := bstep (se 1 (by rfl) ⟨1135643, by rfl⟩ : syracuseStep 1514191 = 2271287) B2271287
theorem B1514239 : Blo 1512953 1514239 := bstep (se 1 (by rfl) ⟨1135679, by rfl⟩ : syracuseStep 1514239 = 2271359) B2271359
theorem B8616941 : Blo 1512953 8616941 := bstep (se 3 (by rfl) ⟨1615676, by rfl⟩ : syracuseStep 8616941 = 3231353) B3231353
theorem B3832859 : Blo 1512953 3832859 := bstep (se 1 (by rfl) ⟨2874644, by rfl⟩ : syracuseStep 3832859 = 5749289) B5749289
theorem B8182889 : Blo 1512953 8182889 := bstep (se 2 (by rfl) ⟨3068583, by rfl⟩ : syracuseStep 8182889 = 6137167) B6137167
theorem B1514607 : Blo 1512953 1514607 := bstep (se 1 (by rfl) ⟨1135955, by rfl⟩ : syracuseStep 1514607 = 2271911) B2271911
theorem B1514663 : Blo 1512953 1514663 := bstep (se 1 (by rfl) ⟨1135997, by rfl⟩ : syracuseStep 1514663 = 2271995) B2271995
theorem B17489195 : Blo 1512953 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B7765319 : Blo 1512953 7765319 := bstep (se 1 (by rfl) ⟨5823989, by rfl⟩ : syracuseStep 7765319 = 11647979) B11647979
theorem B8617373 : Blo 1512953 8617373 := bstep (se 3 (by rfl) ⟨1615757, by rfl⟩ : syracuseStep 8617373 = 3231515) B3231515
theorem B17243765 : Blo 1512953 17243765 := bstep (se 5 (by rfl) ⟨808301, by rfl⟩ : syracuseStep 17243765 = 1616603) B1616603
theorem B18423463 : Blo 1512953 18423463 := bstep (se 1 (by rfl) ⟨13817597, by rfl⟩ : syracuseStep 18423463 = 27635195) B27635195
theorem B21823343 : Blo 1512953 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B9207839 : Blo 1512953 9207839 := bstep (se 1 (by rfl) ⟨6905879, by rfl⟩ : syracuseStep 9207839 = 13811759) B13811759
theorem B1703983 : Blo 1512953 1703983 := bstep (se 1 (by rfl) ⟨1277987, by rfl⟩ : syracuseStep 1703983 = 2555975) B2555975
theorem B3407975 : Blo 1512953 3407975 := bstep (se 1 (by rfl) ⟨2555981, by rfl⟩ : syracuseStep 3407975 = 5111963) B5111963
theorem B2154719 : Blo 1512953 2154719 := bstep (se 1 (by rfl) ⟨1616039, by rfl⟩ : syracuseStep 2154719 = 3232079) B3232079
theorem B2875655 : Blo 1512953 2875655 := bstep (se 1 (by rfl) ⟨2156741, by rfl⟩ : syracuseStep 2875655 = 4313483) B4313483
theorem B2269979 : Blo 1512953 2269979 := bstep (se 1 (by rfl) ⟨1702484, by rfl⟩ : syracuseStep 2269979 = 3404969) B3404969
theorem B2270015 : Blo 1512953 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B4309985 : Blo 1512953 4309985 := bstep (se 2 (by rfl) ⟨1616244, by rfl⟩ : syracuseStep 4309985 = 3232489) B3232489
theorem B11502647 : Blo 1512953 11502647 := bstep (se 1 (by rfl) ⟨8626985, by rfl⟩ : syracuseStep 11502647 = 17253971) B17253971
theorem B2729143 : Blo 1512953 2729143 := bstep (se 1 (by rfl) ⟨2046857, by rfl⟩ : syracuseStep 2729143 = 4093715) B4093715
theorem B88491329 : Blo 1512953 88491329 := bstep (se 2 (by rfl) ⟨33184248, by rfl⟩ : syracuseStep 88491329 = 66368497) B66368497
theorem B199058795 : Blo 1512953 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B11495357 : Blo 1512953 11495357 := bstep (se 3 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 11495357 = 4310759) B4310759
theorem B5744627 : Blo 1512953 5744627 := bstep (se 1 (by rfl) ⟨4308470, by rfl⟩ : syracuseStep 5744627 = 8616941) B8616941
theorem B7276715 : Blo 1512953 7276715 := bstep (se 1 (by rfl) ⟨5457536, by rfl⟩ : syracuseStep 7276715 = 10915073) B10915073
theorem B11659463 : Blo 1512953 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B23627983 : Blo 1512953 23627983 := bstep (se 1 (by rfl) ⟨17720987, by rfl⟩ : syracuseStep 23627983 = 35441975) B35441975
theorem B126044369 : Blo 1512953 126044369 := bstep (se 2 (by rfl) ⟨47266638, by rfl⟩ : syracuseStep 126044369 = 94533277) B94533277
theorem B5744915 : Blo 1512953 5744915 := bstep (se 1 (by rfl) ⟨4308686, by rfl⟩ : syracuseStep 5744915 = 8617373) B8617373
theorem B11495843 : Blo 1512953 11495843 := bstep (se 1 (by rfl) ⟨8621882, by rfl⟩ : syracuseStep 11495843 = 17243765) B17243765
theorem B11504105 : Blo 1512953 11504105 := bstep (se 2 (by rfl) ⟨4314039, by rfl⟩ : syracuseStep 11504105 = 8628079) B8628079
theorem B5106941 : Blo 1512953 5106941 := bstep (se 3 (by rfl) ⟨957551, by rfl⟩ : syracuseStep 5106941 = 1915103) B1915103
theorem B7278713 : Blo 1512953 7278713 := bstep (se 2 (by rfl) ⟨2729517, by rfl⟩ : syracuseStep 7278713 = 5459035) B5459035
theorem B14553391 : Blo 1512953 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B5747375 : Blo 1512953 5747375 := bstep (se 1 (by rfl) ⟨4310531, by rfl⟩ : syracuseStep 5747375 = 8621063) B8621063
theorem B3404519 : Blo 1512953 3404519 := bstep (se 1 (by rfl) ⟨2553389, by rfl⟩ : syracuseStep 3404519 = 5106779) B5106779
theorem B24564617 : Blo 1512953 24564617 := bstep (se 2 (by rfl) ⟨9211731, by rfl⟩ : syracuseStep 24564617 = 18423463) B18423463
theorem B1513007 : Blo 1512953 1513007 := bstep (se 1 (by rfl) ⟨1134755, by rfl⟩ : syracuseStep 1513007 = 2269511) B2269511
theorem B2873065 : Blo 1512953 2873065 := bstep (se 2 (by rfl) ⟨1077399, by rfl⟩ : syracuseStep 2873065 = 2154799) B2154799
theorem B5109587 : Blo 1512953 5109587 := bstep (se 1 (by rfl) ⟨3832190, by rfl⟩ : syracuseStep 5109587 = 7664381) B7664381
theorem B1513631 : Blo 1512953 1513631 := bstep (se 1 (by rfl) ⟨1135223, by rfl⟩ : syracuseStep 1513631 = 2270447) B2270447
theorem B1513727 : Blo 1512953 1513727 := bstep (se 1 (by rfl) ⟨1135295, by rfl⟩ : syracuseStep 1513727 = 2270591) B2270591
theorem B5749319 : Blo 1512953 5749319 := bstep (se 1 (by rfl) ⟨4311989, by rfl⟩ : syracuseStep 5749319 = 8623979) B8623979
theorem B19389395 : Blo 1512953 19389395 := bstep (se 1 (by rfl) ⟨14542046, by rfl⟩ : syracuseStep 19389395 = 29084093) B29084093
theorem B1514599 : Blo 1512953 1514599 := bstep (se 1 (by rfl) ⟨1135949, by rfl⟩ : syracuseStep 1514599 = 2271899) B2271899
theorem B2555239 : Blo 1512953 2555239 := bstep (se 1 (by rfl) ⟨1916429, by rfl⟩ : syracuseStep 2555239 = 3832859) B3832859
theorem B5455259 : Blo 1512953 5455259 := bstep (se 1 (by rfl) ⟨4091444, by rfl⟩ : syracuseStep 5455259 = 8182889) B8182889
theorem B1514907 : Blo 1512953 1514907 := bstep (se 1 (by rfl) ⟨1136180, by rfl⟩ : syracuseStep 1514907 = 2272361) B2272361
theorem B5176879 : Blo 1512953 5176879 := bstep (se 1 (by rfl) ⟨3882659, by rfl⟩ : syracuseStep 5176879 = 7765319) B7765319
theorem B2727839 : Blo 1512953 2727839 := bstep (se 1 (by rfl) ⟨2045879, by rfl⟩ : syracuseStep 2727839 = 4091759) B4091759
theorem B14548895 : Blo 1512953 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B1917103 : Blo 1512953 1917103 := bstep (se 1 (by rfl) ⟨1437827, by rfl⟩ : syracuseStep 1917103 = 2875655) B2875655
theorem B2269679 : Blo 1512953 2269679 := bstep (se 1 (by rfl) ⟨1702259, by rfl⟩ : syracuseStep 2269679 = 3404519) B3404519
theorem B16376411 : Blo 1512953 16376411 := bstep (se 1 (by rfl) ⟨12282308, by rfl⟩ : syracuseStep 16376411 = 24564617) B24564617
theorem B7668431 : Blo 1512953 7668431 := bstep (se 1 (by rfl) ⟨5751323, by rfl⟩ : syracuseStep 7668431 = 11502647) B11502647
theorem B4851143 : Blo 1512953 4851143 := bstep (se 1 (by rfl) ⟨3638357, by rfl⟩ : syracuseStep 4851143 = 7276715) B7276715
theorem B3638857 : Blo 1512953 3638857 := bstep (se 2 (by rfl) ⟨1364571, by rfl⟩ : syracuseStep 3638857 = 2729143) B2729143
theorem B7669403 : Blo 1512953 7669403 := bstep (se 1 (by rfl) ⟨5752052, by rfl⟩ : syracuseStep 7669403 = 11504105) B11504105
theorem B6138559 : Blo 1512953 6138559 := bstep (se 1 (by rfl) ⟨4603919, by rfl⟩ : syracuseStep 6138559 = 9207839) B9207839
theorem B2271977 : Blo 1512953 2271977 := bstep (se 2 (by rfl) ⟨851991, by rfl⟩ : syracuseStep 2271977 = 1703983) B1703983
theorem B2271983 : Blo 1512953 2271983 := bstep (se 1 (by rfl) ⟨1703987, by rfl⟩ : syracuseStep 2271983 = 3407975) B3407975
theorem B4852475 : Blo 1512953 4852475 := bstep (se 1 (by rfl) ⟨3639356, by rfl⟩ : syracuseStep 4852475 = 7278713) B7278713
theorem B27610021 : Blo 1512953 27610021 := bstep (se 4 (by rfl) ⟨2588439, by rfl⟩ : syracuseStep 27610021 = 5176879) B5176879
theorem B5745917 : Blo 1512953 5745917 := bstep (se 3 (by rfl) ⟨1077359, by rfl⟩ : syracuseStep 5745917 = 2154719) B2154719
theorem B58994219 : Blo 1512953 58994219 := bstep (se 1 (by rfl) ⟨44245664, by rfl⟩ : syracuseStep 58994219 = 88491329) B88491329
theorem B132705863 : Blo 1512953 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B7663571 : Blo 1512953 7663571 := bstep (se 1 (by rfl) ⟨5747678, by rfl⟩ : syracuseStep 7663571 = 11495357) B11495357
theorem B3829751 : Blo 1512953 3829751 := bstep (se 1 (by rfl) ⟨2872313, by rfl⟩ : syracuseStep 3829751 = 5744627) B5744627
theorem B84029579 : Blo 1512953 84029579 := bstep (se 1 (by rfl) ⟨63022184, by rfl⟩ : syracuseStep 84029579 = 126044369) B126044369
theorem B3829943 : Blo 1512953 3829943 := bstep (se 1 (by rfl) ⟨2872457, by rfl⟩ : syracuseStep 3829943 = 5744915) B5744915
theorem B7663895 : Blo 1512953 7663895 := bstep (se 1 (by rfl) ⟨5747921, by rfl⟩ : syracuseStep 7663895 = 11495843) B11495843
theorem B3404627 : Blo 1512953 3404627 := bstep (se 1 (by rfl) ⟨2553470, by rfl⟩ : syracuseStep 3404627 = 5106941) B5106941
theorem B3830753 : Blo 1512953 3830753 := bstep (se 2 (by rfl) ⟨1436532, by rfl⟩ : syracuseStep 3830753 = 2873065) B2873065
theorem B31503977 : Blo 1512953 31503977 := bstep (se 2 (by rfl) ⟨11813991, by rfl⟩ : syracuseStep 31503977 = 23627983) B23627983
theorem B19404521 : Blo 1512953 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B3831583 : Blo 1512953 3831583 := bstep (se 1 (by rfl) ⟨2873687, by rfl⟩ : syracuseStep 3831583 = 5747375) B5747375
theorem B1513319 : Blo 1512953 1513319 := bstep (se 1 (by rfl) ⟨1134989, by rfl⟩ : syracuseStep 1513319 = 2269979) B2269979
theorem B1513343 : Blo 1512953 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B2873323 : Blo 1512953 2873323 := bstep (se 1 (by rfl) ⟨2154992, by rfl⟩ : syracuseStep 2873323 = 4309985) B4309985
theorem B3406391 : Blo 1512953 3406391 := bstep (se 1 (by rfl) ⟨2554793, by rfl⟩ : syracuseStep 3406391 = 5109587) B5109587
theorem B7772975 : Blo 1512953 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B3832879 : Blo 1512953 3832879 := bstep (se 1 (by rfl) ⟨2874659, by rfl⟩ : syracuseStep 3832879 = 5749319) B5749319
theorem B3406985 : Blo 1512953 3406985 := bstep (se 2 (by rfl) ⟨1277619, by rfl⟩ : syracuseStep 3406985 = 2555239) B2555239
theorem B12926263 : Blo 1512953 12926263 := bstep (se 1 (by rfl) ⟨9694697, by rfl⟩ : syracuseStep 12926263 = 19389395) B19389395
theorem B3636839 : Blo 1512953 3636839 := bstep (se 1 (by rfl) ⟨2727629, by rfl⟩ : syracuseStep 3636839 = 5455259) B5455259
theorem B1818559 : Blo 1512953 1818559 := bstep (se 1 (by rfl) ⟨1363919, by rfl⟩ : syracuseStep 1818559 = 2727839) B2727839
theorem B9699263 : Blo 1512953 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B2556137 : Blo 1512953 2556137 := bstep (se 2 (by rfl) ⟨958551, by rfl⟩ : syracuseStep 2556137 = 1917103) B1917103
theorem B5112287 : Blo 1512953 5112287 := bstep (se 1 (by rfl) ⟨3834215, by rfl⟩ : syracuseStep 5112287 = 7668431) B7668431
theorem B2269751 : Blo 1512953 2269751 := bstep (se 1 (by rfl) ⟨1702313, by rfl⟩ : syracuseStep 2269751 = 3404627) B3404627
theorem B8184745 : Blo 1512953 8184745 := bstep (se 2 (by rfl) ⟨3069279, by rfl⟩ : syracuseStep 8184745 = 6138559) B6138559
theorem B5112935 : Blo 1512953 5112935 := bstep (se 1 (by rfl) ⟨3834701, by rfl⟩ : syracuseStep 5112935 = 7669403) B7669403
theorem B12936347 : Blo 1512953 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B2270927 : Blo 1512953 2270927 := bstep (se 1 (by rfl) ⟨1703195, by rfl⟩ : syracuseStep 2270927 = 3406391) B3406391
theorem B2271323 : Blo 1512953 2271323 := bstep (se 1 (by rfl) ⟨1703492, by rfl⟩ : syracuseStep 2271323 = 3406985) B3406985
theorem B4851809 : Blo 1512953 4851809 := bstep (se 2 (by rfl) ⟨1819428, by rfl⟩ : syracuseStep 4851809 = 3638857) B3638857
theorem B6466175 : Blo 1512953 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B56019719 : Blo 1512953 56019719 := bstep (se 1 (by rfl) ⟨42014789, by rfl⟩ : syracuseStep 56019719 = 84029579) B84029579
theorem B5181983 : Blo 1512953 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B3830611 : Blo 1512953 3830611 := bstep (se 1 (by rfl) ⟨2872958, by rfl⟩ : syracuseStep 3830611 = 5745917) B5745917
theorem B5108777 : Blo 1512953 5108777 := bstep (se 2 (by rfl) ⟨1915791, by rfl⟩ : syracuseStep 5108777 = 3831583) B3831583
theorem B88470575 : Blo 1512953 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B5109047 : Blo 1512953 5109047 := bstep (se 1 (by rfl) ⟨3831785, by rfl⟩ : syracuseStep 5109047 = 7663571) B7663571
theorem B3831097 : Blo 1512953 3831097 := bstep (se 2 (by rfl) ⟨1436661, by rfl⟩ : syracuseStep 3831097 = 2873323) B2873323
theorem B2553167 : Blo 1512953 2553167 := bstep (se 1 (by rfl) ⟨1914875, by rfl⟩ : syracuseStep 2553167 = 3829751) B3829751
theorem B2553295 : Blo 1512953 2553295 := bstep (se 1 (by rfl) ⟨1914971, by rfl⟩ : syracuseStep 2553295 = 3829943) B3829943
theorem B5109263 : Blo 1512953 5109263 := bstep (se 1 (by rfl) ⟨3831947, by rfl⟩ : syracuseStep 5109263 = 7663895) B7663895
theorem B1513119 : Blo 1512953 1513119 := bstep (se 1 (by rfl) ⟨1134839, by rfl⟩ : syracuseStep 1513119 = 2269679) B2269679
theorem B10917607 : Blo 1512953 10917607 := bstep (se 1 (by rfl) ⟨8188205, by rfl⟩ : syracuseStep 10917607 = 16376411) B16376411
theorem B2553835 : Blo 1512953 2553835 := bstep (se 1 (by rfl) ⟨1915376, by rfl⟩ : syracuseStep 2553835 = 3830753) B3830753
theorem B3234095 : Blo 1512953 3234095 := bstep (se 1 (by rfl) ⟨2425571, by rfl⟩ : syracuseStep 3234095 = 4851143) B4851143
theorem B21002651 : Blo 1512953 21002651 := bstep (se 1 (by rfl) ⟨15751988, by rfl⟩ : syracuseStep 21002651 = 31503977) B31503977
theorem B36813361 : Blo 1512953 36813361 := bstep (se 2 (by rfl) ⟨13805010, by rfl⟩ : syracuseStep 36813361 = 27610021) B27610021
theorem B5110505 : Blo 1512953 5110505 := bstep (se 2 (by rfl) ⟨1916439, by rfl⟩ : syracuseStep 5110505 = 3832879) B3832879
theorem B9698237 : Blo 1512953 9698237 := bstep (se 3 (by rfl) ⟨1818419, by rfl⟩ : syracuseStep 9698237 = 3636839) B3636839
theorem B17235017 : Blo 1512953 17235017 := bstep (se 2 (by rfl) ⟨6463131, by rfl⟩ : syracuseStep 17235017 = 12926263) B12926263
theorem B1514651 : Blo 1512953 1514651 := bstep (se 1 (by rfl) ⟨1135988, by rfl⟩ : syracuseStep 1514651 = 2271977) B2271977
theorem B1514655 : Blo 1512953 1514655 := bstep (se 1 (by rfl) ⟨1135991, by rfl⟩ : syracuseStep 1514655 = 2271983) B2271983
theorem B3234983 : Blo 1512953 3234983 := bstep (se 1 (by rfl) ⟨2426237, by rfl⟩ : syracuseStep 3234983 = 4852475) B4852475
theorem B39329479 : Blo 1512953 39329479 := bstep (se 1 (by rfl) ⟨29497109, by rfl⟩ : syracuseStep 39329479 = 58994219) B58994219
theorem B2424745 : Blo 1512953 2424745 := bstep (se 2 (by rfl) ⟨909279, by rfl⟩ : syracuseStep 2424745 = 1818559) B1818559
theorem B1704091 : Blo 1512953 1704091 := bstep (se 1 (by rfl) ⟨1278068, by rfl⟩ : syracuseStep 1704091 = 2556137) B2556137
theorem B3408191 : Blo 1512953 3408191 := bstep (se 1 (by rfl) ⟨2556143, by rfl⟩ : syracuseStep 3408191 = 5112287) B5112287
theorem B8626621 : Blo 1512953 8626621 := bstep (se 3 (by rfl) ⟨1617491, by rfl⟩ : syracuseStep 8626621 = 3234983) B3234983
theorem B3408623 : Blo 1512953 3408623 := bstep (se 1 (by rfl) ⟨2556467, by rfl⟩ : syracuseStep 3408623 = 5112935) B5112935
theorem B209757221 : Blo 1512953 209757221 := bstep (se 4 (by rfl) ⟨19664739, by rfl⟩ : syracuseStep 209757221 = 39329479) B39329479
theorem B2156063 : Blo 1512953 2156063 := bstep (se 1 (by rfl) ⟨1617047, by rfl⟩ : syracuseStep 2156063 = 3234095) B3234095
theorem B14001767 : Blo 1512953 14001767 := bstep (se 1 (by rfl) ⟨10501325, by rfl⟩ : syracuseStep 14001767 = 21002651) B21002651
theorem B4310783 : Blo 1512953 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B6465491 : Blo 1512953 6465491 := bstep (se 1 (by rfl) ⟨4849118, by rfl⟩ : syracuseStep 6465491 = 9698237) B9698237
theorem B5107481 : Blo 1512953 5107481 := bstep (se 2 (by rfl) ⟨1915305, by rfl⟩ : syracuseStep 5107481 = 3830611) B3830611
theorem B5108129 : Blo 1512953 5108129 := bstep (se 2 (by rfl) ⟨1915548, by rfl⟩ : syracuseStep 5108129 = 3831097) B3831097
theorem B3404393 : Blo 1512953 3404393 := bstep (se 2 (by rfl) ⟨1276647, by rfl⟩ : syracuseStep 3404393 = 2553295) B2553295
theorem B149385917 : Blo 1512953 149385917 := bstep (se 3 (by rfl) ⟨28009859, by rfl⟩ : syracuseStep 149385917 = 56019719) B56019719
theorem B11490011 : Blo 1512953 11490011 := bstep (se 1 (by rfl) ⟨8617508, by rfl⟩ : syracuseStep 11490011 = 17235017) B17235017
theorem B12931973 : Blo 1512953 12931973 := bstep (se 4 (by rfl) ⟨1212372, by rfl⟩ : syracuseStep 12931973 = 2424745) B2424745
theorem B43651973 : Blo 1512953 43651973 := bstep (se 4 (by rfl) ⟨4092372, by rfl⟩ : syracuseStep 43651973 = 8184745) B8184745
theorem B3405113 : Blo 1512953 3405113 := bstep (se 2 (by rfl) ⟨1276917, by rfl⟩ : syracuseStep 3405113 = 2553835) B2553835
theorem B3454655 : Blo 1512953 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B1513167 : Blo 1512953 1513167 := bstep (se 1 (by rfl) ⟨1134875, by rfl⟩ : syracuseStep 1513167 = 2269751) B2269751
theorem B3405851 : Blo 1512953 3405851 := bstep (se 1 (by rfl) ⟨2554388, by rfl⟩ : syracuseStep 3405851 = 5108777) B5108777
theorem B58980383 : Blo 1512953 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B49084481 : Blo 1512953 49084481 := bstep (se 2 (by rfl) ⟨18406680, by rfl⟩ : syracuseStep 49084481 = 36813361) B36813361
theorem B8624231 : Blo 1512953 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B3406031 : Blo 1512953 3406031 := bstep (se 1 (by rfl) ⟨2554523, by rfl⟩ : syracuseStep 3406031 = 5109047) B5109047
theorem B1702111 : Blo 1512953 1702111 := bstep (se 1 (by rfl) ⟨1276583, by rfl⟩ : syracuseStep 1702111 = 2553167) B2553167
theorem B3406175 : Blo 1512953 3406175 := bstep (se 1 (by rfl) ⟨2554631, by rfl⟩ : syracuseStep 3406175 = 5109263) B5109263
theorem B1513951 : Blo 1512953 1513951 := bstep (se 1 (by rfl) ⟨1135463, by rfl⟩ : syracuseStep 1513951 = 2270927) B2270927
theorem B1514215 : Blo 1512953 1514215 := bstep (se 1 (by rfl) ⟨1135661, by rfl⟩ : syracuseStep 1514215 = 2271323) B2271323
theorem B3234539 : Blo 1512953 3234539 := bstep (se 1 (by rfl) ⟨2425904, by rfl⟩ : syracuseStep 3234539 = 4851809) B4851809
theorem B3407003 : Blo 1512953 3407003 := bstep (se 1 (by rfl) ⟨2555252, by rfl⟩ : syracuseStep 3407003 = 5110505) B5110505
theorem B14556809 : Blo 1512953 14556809 := bstep (se 2 (by rfl) ⟨5458803, by rfl⟩ : syracuseStep 14556809 = 10917607) B10917607
theorem B2269481 : Blo 1512953 2269481 := bstep (se 2 (by rfl) ⟨851055, by rfl⟩ : syracuseStep 2269481 = 1702111) B1702111
theorem B2269595 : Blo 1512953 2269595 := bstep (se 1 (by rfl) ⟨1702196, by rfl⟩ : syracuseStep 2269595 = 3404393) B3404393
theorem B7660007 : Blo 1512953 7660007 := bstep (se 1 (by rfl) ⟨5745005, by rfl⟩ : syracuseStep 7660007 = 11490011) B11490011
theorem B11502161 : Blo 1512953 11502161 := bstep (se 2 (by rfl) ⟨4313310, by rfl⟩ : syracuseStep 11502161 = 8626621) B8626621
theorem B139838147 : Blo 1512953 139838147 := bstep (se 1 (by rfl) ⟨104878610, by rfl⟩ : syracuseStep 139838147 = 209757221) B209757221
theorem B2270075 : Blo 1512953 2270075 := bstep (se 1 (by rfl) ⟨1702556, by rfl⟩ : syracuseStep 2270075 = 3405113) B3405113
theorem B4310327 : Blo 1512953 4310327 := bstep (se 1 (by rfl) ⟨3232745, by rfl⟩ : syracuseStep 4310327 = 6465491) B6465491
theorem B2270567 : Blo 1512953 2270567 := bstep (se 1 (by rfl) ⟨1702925, by rfl⟩ : syracuseStep 2270567 = 3405851) B3405851
theorem B2270687 : Blo 1512953 2270687 := bstep (se 1 (by rfl) ⟨1703015, by rfl⟩ : syracuseStep 2270687 = 3406031) B3406031
theorem B2270783 : Blo 1512953 2270783 := bstep (se 1 (by rfl) ⟨1703087, by rfl⟩ : syracuseStep 2270783 = 3406175) B3406175
theorem B398362445 : Blo 1512953 398362445 := bstep (se 3 (by rfl) ⟨74692958, by rfl⟩ : syracuseStep 398362445 = 149385917) B149385917
theorem B36849653 : Blo 1512953 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B2271335 : Blo 1512953 2271335 := bstep (se 1 (by rfl) ⟨1703501, by rfl⟩ : syracuseStep 2271335 = 3407003) B3407003
theorem B2272121 : Blo 1512953 2272121 := bstep (se 2 (by rfl) ⟨852045, by rfl⟩ : syracuseStep 2272121 = 1704091) B1704091
theorem B2272127 : Blo 1512953 2272127 := bstep (se 1 (by rfl) ⟨1704095, by rfl⟩ : syracuseStep 2272127 = 3408191) B3408191
theorem B2272415 : Blo 1512953 2272415 := bstep (se 1 (by rfl) ⟨1704311, by rfl⟩ : syracuseStep 2272415 = 3408623) B3408623
theorem B8621315 : Blo 1512953 8621315 := bstep (se 1 (by rfl) ⟨6465986, by rfl⟩ : syracuseStep 8621315 = 12931973) B12931973
theorem B29101315 : Blo 1512953 29101315 := bstep (se 1 (by rfl) ⟨21825986, by rfl⟩ : syracuseStep 29101315 = 43651973) B43651973
theorem B9334511 : Blo 1512953 9334511 := bstep (se 1 (by rfl) ⟨7000883, by rfl⟩ : syracuseStep 9334511 = 14001767) B14001767
theorem B32722987 : Blo 1512953 32722987 := bstep (se 1 (by rfl) ⟨24542240, by rfl⟩ : syracuseStep 32722987 = 49084481) B49084481
theorem B9704539 : Blo 1512953 9704539 := bstep (se 1 (by rfl) ⟨7278404, by rfl⟩ : syracuseStep 9704539 = 14556809) B14556809
theorem B3404987 : Blo 1512953 3404987 := bstep (se 1 (by rfl) ⟨2553740, by rfl⟩ : syracuseStep 3404987 = 5107481) B5107481
theorem B3405419 : Blo 1512953 3405419 := bstep (se 1 (by rfl) ⟨2554064, by rfl⟩ : syracuseStep 3405419 = 5108129) B5108129
theorem B2873855 : Blo 1512953 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B39320255 : Blo 1512953 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B5749487 : Blo 1512953 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B5749501 : Blo 1512953 5749501 := bstep (se 3 (by rfl) ⟨1078031, by rfl⟩ : syracuseStep 5749501 = 2156063) B2156063
theorem B8625437 : Blo 1512953 8625437 := bstep (se 3 (by rfl) ⟨1617269, by rfl⟩ : syracuseStep 8625437 = 3234539) B3234539
theorem B43630649 : Blo 1512953 43630649 := bstep (se 2 (by rfl) ⟨16361493, by rfl⟩ : syracuseStep 43630649 = 32722987) B32722987
theorem B7668107 : Blo 1512953 7668107 := bstep (se 1 (by rfl) ⟨5751080, by rfl⟩ : syracuseStep 7668107 = 11502161) B11502161
theorem B93225431 : Blo 1512953 93225431 := bstep (se 1 (by rfl) ⟨69919073, by rfl⟩ : syracuseStep 93225431 = 139838147) B139838147
theorem B2269991 : Blo 1512953 2269991 := bstep (se 1 (by rfl) ⟨1702493, by rfl⟩ : syracuseStep 2269991 = 3404987) B3404987
theorem B2270279 : Blo 1512953 2270279 := bstep (se 1 (by rfl) ⟨1702709, by rfl⟩ : syracuseStep 2270279 = 3405419) B3405419
theorem B5106671 : Blo 1512953 5106671 := bstep (se 1 (by rfl) ⟨3830003, by rfl⟩ : syracuseStep 5106671 = 7660007) B7660007
theorem B12939385 : Blo 1512953 12939385 := bstep (se 2 (by rfl) ⟨4852269, by rfl⟩ : syracuseStep 12939385 = 9704539) B9704539
theorem B38801753 : Blo 1512953 38801753 := bstep (se 2 (by rfl) ⟨14550657, by rfl⟩ : syracuseStep 38801753 = 29101315) B29101315
theorem B5747543 : Blo 1512953 5747543 := bstep (se 1 (by rfl) ⟨4310657, by rfl⟩ : syracuseStep 5747543 = 8621315) B8621315
theorem B6223007 : Blo 1512953 6223007 := bstep (se 1 (by rfl) ⟨4667255, by rfl⟩ : syracuseStep 6223007 = 9334511) B9334511
theorem B1512987 : Blo 1512953 1512987 := bstep (se 1 (by rfl) ⟨1134740, by rfl⟩ : syracuseStep 1512987 = 2269481) B2269481
theorem B1513063 : Blo 1512953 1513063 := bstep (se 1 (by rfl) ⟨1134797, by rfl⟩ : syracuseStep 1513063 = 2269595) B2269595
theorem B1513383 : Blo 1512953 1513383 := bstep (se 1 (by rfl) ⟨1135037, by rfl⟩ : syracuseStep 1513383 = 2270075) B2270075
theorem B2873551 : Blo 1512953 2873551 := bstep (se 1 (by rfl) ⟨2155163, by rfl⟩ : syracuseStep 2873551 = 4310327) B4310327
theorem B1513711 : Blo 1512953 1513711 := bstep (se 1 (by rfl) ⟨1135283, by rfl⟩ : syracuseStep 1513711 = 2270567) B2270567
theorem B1513791 : Blo 1512953 1513791 := bstep (se 1 (by rfl) ⟨1135343, by rfl⟩ : syracuseStep 1513791 = 2270687) B2270687
theorem B7666001 : Blo 1512953 7666001 := bstep (se 2 (by rfl) ⟨2874750, by rfl⟩ : syracuseStep 7666001 = 5749501) B5749501
theorem B1513855 : Blo 1512953 1513855 := bstep (se 1 (by rfl) ⟨1135391, by rfl⟩ : syracuseStep 1513855 = 2270783) B2270783
theorem B265574963 : Blo 1512953 265574963 := bstep (se 1 (by rfl) ⟨199181222, by rfl⟩ : syracuseStep 265574963 = 398362445) B398362445
theorem B24566435 : Blo 1512953 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B1514223 : Blo 1512953 1514223 := bstep (se 1 (by rfl) ⟨1135667, by rfl⟩ : syracuseStep 1514223 = 2271335) B2271335
theorem B1915903 : Blo 1512953 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B26213503 : Blo 1512953 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B3832991 : Blo 1512953 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B1514747 : Blo 1512953 1514747 := bstep (se 1 (by rfl) ⟨1136060, by rfl⟩ : syracuseStep 1514747 = 2272121) B2272121
theorem B1514751 : Blo 1512953 1514751 := bstep (se 1 (by rfl) ⟨1136063, by rfl⟩ : syracuseStep 1514751 = 2272127) B2272127
theorem B1514943 : Blo 1512953 1514943 := bstep (se 1 (by rfl) ⟨1136207, by rfl⟩ : syracuseStep 1514943 = 2272415) B2272415
theorem B5750291 : Blo 1512953 5750291 := bstep (se 1 (by rfl) ⟨4312718, by rfl⟩ : syracuseStep 5750291 = 8625437) B8625437
theorem B17252513 : Blo 1512953 17252513 := bstep (se 2 (by rfl) ⟨6469692, by rfl⟩ : syracuseStep 17252513 = 12939385) B12939385
theorem B5112071 : Blo 1512953 5112071 := bstep (se 1 (by rfl) ⟨3834053, by rfl⟩ : syracuseStep 5112071 = 7668107) B7668107
theorem B16377623 : Blo 1512953 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B4148671 : Blo 1512953 4148671 := bstep (se 1 (by rfl) ⟨3111503, by rfl⟩ : syracuseStep 4148671 = 6223007) B6223007
theorem B34951337 : Blo 1512953 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B177049975 : Blo 1512953 177049975 := bstep (se 1 (by rfl) ⟨132787481, by rfl⟩ : syracuseStep 177049975 = 265574963) B265574963
theorem B3404447 : Blo 1512953 3404447 := bstep (se 1 (by rfl) ⟨2553335, by rfl⟩ : syracuseStep 3404447 = 5106671) B5106671
theorem B29087099 : Blo 1512953 29087099 := bstep (se 1 (by rfl) ⟨21815324, by rfl⟩ : syracuseStep 29087099 = 43630649) B43630649
theorem B25867835 : Blo 1512953 25867835 := bstep (se 1 (by rfl) ⟨19400876, by rfl⟩ : syracuseStep 25867835 = 38801753) B38801753
theorem B3831401 : Blo 1512953 3831401 := bstep (se 2 (by rfl) ⟨1436775, by rfl⟩ : syracuseStep 3831401 = 2873551) B2873551
theorem B62150287 : Blo 1512953 62150287 := bstep (se 1 (by rfl) ⟨46612715, by rfl⟩ : syracuseStep 62150287 = 93225431) B93225431
theorem B1513327 : Blo 1512953 1513327 := bstep (se 1 (by rfl) ⟨1134995, by rfl⟩ : syracuseStep 1513327 = 2269991) B2269991
theorem B3831695 : Blo 1512953 3831695 := bstep (se 1 (by rfl) ⟨2873771, by rfl⟩ : syracuseStep 3831695 = 5747543) B5747543
theorem B1513519 : Blo 1512953 1513519 := bstep (se 1 (by rfl) ⟨1135139, by rfl⟩ : syracuseStep 1513519 = 2270279) B2270279
theorem B2554537 : Blo 1512953 2554537 := bstep (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) B1915903
theorem B5110667 : Blo 1512953 5110667 := bstep (se 1 (by rfl) ⟨3833000, by rfl⟩ : syracuseStep 5110667 = 7666001) B7666001
theorem B2555327 : Blo 1512953 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B3833527 : Blo 1512953 3833527 := bstep (se 1 (by rfl) ⟨2875145, by rfl⟩ : syracuseStep 3833527 = 5750291) B5750291
theorem B11501675 : Blo 1512953 11501675 := bstep (se 1 (by rfl) ⟨8626256, by rfl⟩ : syracuseStep 11501675 = 17252513) B17252513
theorem B3408047 : Blo 1512953 3408047 := bstep (se 1 (by rfl) ⟨2556035, by rfl⟩ : syracuseStep 3408047 = 5112071) B5112071
theorem B2269631 : Blo 1512953 2269631 := bstep (se 1 (by rfl) ⟨1702223, by rfl⟩ : syracuseStep 2269631 = 3404447) B3404447
theorem B19391399 : Blo 1512953 19391399 := bstep (se 1 (by rfl) ⟨14543549, by rfl⟩ : syracuseStep 19391399 = 29087099) B29087099
theorem B17245223 : Blo 1512953 17245223 := bstep (se 1 (by rfl) ⟨12933917, by rfl⟩ : syracuseStep 17245223 = 25867835) B25867835
theorem B5531561 : Blo 1512953 5531561 := bstep (se 2 (by rfl) ⟨2074335, by rfl⟩ : syracuseStep 5531561 = 4148671) B4148671
theorem B23300891 : Blo 1512953 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B82867049 : Blo 1512953 82867049 := bstep (se 2 (by rfl) ⟨31075143, by rfl⟩ : syracuseStep 82867049 = 62150287) B62150287
theorem B236066633 : Blo 1512953 236066633 := bstep (se 2 (by rfl) ⟨88524987, by rfl⟩ : syracuseStep 236066633 = 177049975) B177049975
theorem B3406049 : Blo 1512953 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B2554267 : Blo 1512953 2554267 := bstep (se 1 (by rfl) ⟨1915700, by rfl⟩ : syracuseStep 2554267 = 3831401) B3831401
theorem B10918415 : Blo 1512953 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B2554463 : Blo 1512953 2554463 := bstep (se 1 (by rfl) ⟨1915847, by rfl⟩ : syracuseStep 2554463 = 3831695) B3831695
theorem B3407111 : Blo 1512953 3407111 := bstep (se 1 (by rfl) ⟨2555333, by rfl⟩ : syracuseStep 3407111 = 5110667) B5110667
theorem B5111369 : Blo 1512953 5111369 := bstep (se 2 (by rfl) ⟨1916763, by rfl⟩ : syracuseStep 5111369 = 3833527) B3833527
theorem B1703551 : Blo 1512953 1703551 := bstep (se 1 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 1703551 = 2555327) B2555327
theorem B7667783 : Blo 1512953 7667783 := bstep (se 1 (by rfl) ⟨5750837, by rfl⟩ : syracuseStep 7667783 = 11501675) B11501675
theorem B12927599 : Blo 1512953 12927599 := bstep (se 1 (by rfl) ⟨9695699, by rfl⟩ : syracuseStep 12927599 = 19391399) B19391399
theorem B157377755 : Blo 1512953 157377755 := bstep (se 1 (by rfl) ⟨118033316, by rfl⟩ : syracuseStep 157377755 = 236066633) B236066633
theorem B3687707 : Blo 1512953 3687707 := bstep (se 1 (by rfl) ⟨2765780, by rfl⟩ : syracuseStep 3687707 = 5531561) B5531561
theorem B29115773 : Blo 1512953 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B2270699 : Blo 1512953 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B15533927 : Blo 1512953 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B2271401 : Blo 1512953 2271401 := bstep (se 2 (by rfl) ⟨851775, by rfl⟩ : syracuseStep 2271401 = 1703551) B1703551
theorem B2271407 : Blo 1512953 2271407 := bstep (se 1 (by rfl) ⟨1703555, by rfl⟩ : syracuseStep 2271407 = 3407111) B3407111
theorem B2272031 : Blo 1512953 2272031 := bstep (se 1 (by rfl) ⟨1704023, by rfl⟩ : syracuseStep 2272031 = 3408047) B3408047
theorem B11496815 : Blo 1512953 11496815 := bstep (se 1 (by rfl) ⟨8622611, by rfl⟩ : syracuseStep 11496815 = 17245223) B17245223
theorem B1513087 : Blo 1512953 1513087 := bstep (se 1 (by rfl) ⟨1134815, by rfl⟩ : syracuseStep 1513087 = 2269631) B2269631
theorem B3405689 : Blo 1512953 3405689 := bstep (se 2 (by rfl) ⟨1277133, by rfl⟩ : syracuseStep 3405689 = 2554267) B2554267
theorem B55244699 : Blo 1512953 55244699 := bstep (se 1 (by rfl) ⟨41433524, by rfl⟩ : syracuseStep 55244699 = 82867049) B82867049
theorem B1702975 : Blo 1512953 1702975 := bstep (se 1 (by rfl) ⟨1277231, by rfl⟩ : syracuseStep 1702975 = 2554463) B2554463
theorem B3407579 : Blo 1512953 3407579 := bstep (se 1 (by rfl) ⟨2555684, by rfl⟩ : syracuseStep 3407579 = 5111369) B5111369
theorem B5111855 : Blo 1512953 5111855 := bstep (se 1 (by rfl) ⟨3833891, by rfl⟩ : syracuseStep 5111855 = 7667783) B7667783
theorem B8618399 : Blo 1512953 8618399 := bstep (se 1 (by rfl) ⟨6463799, by rfl⟩ : syracuseStep 8618399 = 12927599) B12927599
theorem B10355951 : Blo 1512953 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B2270459 : Blo 1512953 2270459 := bstep (se 1 (by rfl) ⟨1702844, by rfl⟩ : syracuseStep 2270459 = 3405689) B3405689
theorem B2270633 : Blo 1512953 2270633 := bstep (se 2 (by rfl) ⟨851487, by rfl⟩ : syracuseStep 2270633 = 1702975) B1702975
theorem B2271719 : Blo 1512953 2271719 := bstep (se 1 (by rfl) ⟨1703789, by rfl⟩ : syracuseStep 2271719 = 3407579) B3407579
theorem B9833885 : Blo 1512953 9833885 := bstep (se 3 (by rfl) ⟨1843853, by rfl⟩ : syracuseStep 9833885 = 3687707) B3687707
theorem B104918503 : Blo 1512953 104918503 := bstep (se 1 (by rfl) ⟨78688877, by rfl⟩ : syracuseStep 104918503 = 157377755) B157377755
theorem B19410515 : Blo 1512953 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B7664543 : Blo 1512953 7664543 := bstep (se 1 (by rfl) ⟨5748407, by rfl⟩ : syracuseStep 7664543 = 11496815) B11496815
theorem B1513799 : Blo 1512953 1513799 := bstep (se 1 (by rfl) ⟨1135349, by rfl⟩ : syracuseStep 1513799 = 2270699) B2270699
theorem B36829799 : Blo 1512953 36829799 := bstep (se 1 (by rfl) ⟨27622349, by rfl⟩ : syracuseStep 36829799 = 55244699) B55244699
theorem B1514267 : Blo 1512953 1514267 := bstep (se 1 (by rfl) ⟨1135700, by rfl⟩ : syracuseStep 1514267 = 2271401) B2271401
theorem B1514271 : Blo 1512953 1514271 := bstep (se 1 (by rfl) ⟨1135703, by rfl⟩ : syracuseStep 1514271 = 2271407) B2271407
theorem B1514687 : Blo 1512953 1514687 := bstep (se 1 (by rfl) ⟨1136015, by rfl⟩ : syracuseStep 1514687 = 2272031) B2272031
theorem B3407903 : Blo 1512953 3407903 := bstep (se 1 (by rfl) ⟨2555927, by rfl⟩ : syracuseStep 3407903 = 5111855) B5111855
theorem B24553199 : Blo 1512953 24553199 := bstep (se 1 (by rfl) ⟨18414899, by rfl⟩ : syracuseStep 24553199 = 36829799) B36829799
theorem B6555923 : Blo 1512953 6555923 := bstep (se 1 (by rfl) ⟨4916942, by rfl⟩ : syracuseStep 6555923 = 9833885) B9833885
theorem B5745599 : Blo 1512953 5745599 := bstep (se 1 (by rfl) ⟨4309199, by rfl⟩ : syracuseStep 5745599 = 8618399) B8618399
theorem B139891337 : Blo 1512953 139891337 := bstep (se 2 (by rfl) ⟨52459251, by rfl⟩ : syracuseStep 139891337 = 104918503) B104918503
theorem B12940343 : Blo 1512953 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B5109695 : Blo 1512953 5109695 := bstep (se 1 (by rfl) ⟨3832271, by rfl⟩ : syracuseStep 5109695 = 7664543) B7664543
theorem B6903967 : Blo 1512953 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B1513639 : Blo 1512953 1513639 := bstep (se 1 (by rfl) ⟨1135229, by rfl⟩ : syracuseStep 1513639 = 2270459) B2270459
theorem B1513755 : Blo 1512953 1513755 := bstep (se 1 (by rfl) ⟨1135316, by rfl⟩ : syracuseStep 1513755 = 2270633) B2270633
theorem B1514479 : Blo 1512953 1514479 := bstep (se 1 (by rfl) ⟨1135859, by rfl⟩ : syracuseStep 1514479 = 2271719) B2271719
theorem B8626895 : Blo 1512953 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B16368799 : Blo 1512953 16368799 := bstep (se 1 (by rfl) ⟨12276599, by rfl⟩ : syracuseStep 16368799 = 24553199) B24553199
theorem B2271935 : Blo 1512953 2271935 := bstep (se 1 (by rfl) ⟨1703951, by rfl⟩ : syracuseStep 2271935 = 3407903) B3407903
theorem B93260891 : Blo 1512953 93260891 := bstep (se 1 (by rfl) ⟨69945668, by rfl⟩ : syracuseStep 93260891 = 139891337) B139891337
theorem B4370615 : Blo 1512953 4370615 := bstep (se 1 (by rfl) ⟨3277961, by rfl⟩ : syracuseStep 4370615 = 6555923) B6555923
theorem B3830399 : Blo 1512953 3830399 := bstep (se 1 (by rfl) ⟨2872799, by rfl⟩ : syracuseStep 3830399 = 5745599) B5745599
theorem B9205289 : Blo 1512953 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B3406463 : Blo 1512953 3406463 := bstep (se 1 (by rfl) ⟨2554847, by rfl⟩ : syracuseStep 3406463 = 5109695) B5109695
theorem B5751263 : Blo 1512953 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B6136859 : Blo 1512953 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B21825065 : Blo 1512953 21825065 := bstep (se 2 (by rfl) ⟨8184399, by rfl⟩ : syracuseStep 21825065 = 16368799) B16368799
theorem B2270975 : Blo 1512953 2270975 := bstep (se 1 (by rfl) ⟨1703231, by rfl⟩ : syracuseStep 2270975 = 3406463) B3406463
theorem B62173927 : Blo 1512953 62173927 := bstep (se 1 (by rfl) ⟨46630445, by rfl⟩ : syracuseStep 62173927 = 93260891) B93260891
theorem B2913743 : Blo 1512953 2913743 := bstep (se 1 (by rfl) ⟨2185307, by rfl⟩ : syracuseStep 2913743 = 4370615) B4370615
theorem B2553599 : Blo 1512953 2553599 := bstep (se 1 (by rfl) ⟨1915199, by rfl⟩ : syracuseStep 2553599 = 3830399) B3830399
theorem B1514623 : Blo 1512953 1514623 := bstep (se 1 (by rfl) ⟨1135967, by rfl⟩ : syracuseStep 1514623 = 2271935) B2271935
theorem B3834175 : Blo 1512953 3834175 := bstep (se 1 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 3834175 = 5751263) B5751263
theorem B14550043 : Blo 1512953 14550043 := bstep (se 1 (by rfl) ⟨10912532, by rfl⟩ : syracuseStep 14550043 = 21825065) B21825065
theorem B4091239 : Blo 1512953 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B82898569 : Blo 1512953 82898569 := bstep (se 2 (by rfl) ⟨31086963, by rfl⟩ : syracuseStep 82898569 = 62173927) B62173927
theorem B7769981 : Blo 1512953 7769981 := bstep (se 3 (by rfl) ⟨1456871, by rfl⟩ : syracuseStep 7769981 = 2913743) B2913743
theorem B1702399 : Blo 1512953 1702399 := bstep (se 1 (by rfl) ⟨1276799, by rfl⟩ : syracuseStep 1702399 = 2553599) B2553599
theorem B1513983 : Blo 1512953 1513983 := bstep (se 1 (by rfl) ⟨1135487, by rfl⟩ : syracuseStep 1513983 = 2270975) B2270975
theorem B5112233 : Blo 1512953 5112233 := bstep (se 2 (by rfl) ⟨1917087, by rfl⟩ : syracuseStep 5112233 = 3834175) B3834175
theorem B2269865 : Blo 1512953 2269865 := bstep (se 2 (by rfl) ⟨851199, by rfl⟩ : syracuseStep 2269865 = 1702399) B1702399
theorem B19400057 : Blo 1512953 19400057 := bstep (se 2 (by rfl) ⟨7275021, by rfl⟩ : syracuseStep 19400057 = 14550043) B14550043
theorem B5179987 : Blo 1512953 5179987 := bstep (se 1 (by rfl) ⟨3884990, by rfl⟩ : syracuseStep 5179987 = 7769981) B7769981
theorem B21819941 : Blo 1512953 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B110531425 : Blo 1512953 110531425 := bstep (se 2 (by rfl) ⟨41449284, by rfl⟩ : syracuseStep 110531425 = 82898569) B82898569
theorem B3408155 : Blo 1512953 3408155 := bstep (se 1 (by rfl) ⟨2556116, by rfl⟩ : syracuseStep 3408155 = 5112233) B5112233
theorem B6906649 : Blo 1512953 6906649 := bstep (se 2 (by rfl) ⟨2589993, by rfl⟩ : syracuseStep 6906649 = 5179987) B5179987
theorem B147375233 : Blo 1512953 147375233 := bstep (se 2 (by rfl) ⟨55265712, by rfl⟩ : syracuseStep 147375233 = 110531425) B110531425
theorem B14546627 : Blo 1512953 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B1513243 : Blo 1512953 1513243 := bstep (se 1 (by rfl) ⟨1134932, by rfl⟩ : syracuseStep 1513243 = 2269865) B2269865
theorem B12933371 : Blo 1512953 12933371 := bstep (se 1 (by rfl) ⟨9700028, by rfl⟩ : syracuseStep 12933371 = 19400057) B19400057
theorem B9208865 : Blo 1512953 9208865 := bstep (se 2 (by rfl) ⟨3453324, by rfl⟩ : syracuseStep 9208865 = 6906649) B6906649
theorem B2272103 : Blo 1512953 2272103 := bstep (se 1 (by rfl) ⟨1704077, by rfl⟩ : syracuseStep 2272103 = 3408155) B3408155
theorem B98250155 : Blo 1512953 98250155 := bstep (se 1 (by rfl) ⟨73687616, by rfl⟩ : syracuseStep 98250155 = 147375233) B147375233
theorem B8622247 : Blo 1512953 8622247 := bstep (se 1 (by rfl) ⟨6466685, by rfl⟩ : syracuseStep 8622247 = 12933371) B12933371
theorem B9697751 : Blo 1512953 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B6465167 : Blo 1512953 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B11496329 : Blo 1512953 11496329 := bstep (se 2 (by rfl) ⟨4311123, by rfl⟩ : syracuseStep 11496329 = 8622247) B8622247
theorem B6139243 : Blo 1512953 6139243 := bstep (se 1 (by rfl) ⟨4604432, by rfl⟩ : syracuseStep 6139243 = 9208865) B9208865
theorem B65500103 : Blo 1512953 65500103 := bstep (se 1 (by rfl) ⟨49125077, by rfl⟩ : syracuseStep 65500103 = 98250155) B98250155
theorem B1514735 : Blo 1512953 1514735 := bstep (se 1 (by rfl) ⟨1136051, by rfl⟩ : syracuseStep 1514735 = 2272103) B2272103
theorem B4310111 : Blo 1512953 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B8185657 : Blo 1512953 8185657 := bstep (se 2 (by rfl) ⟨3069621, by rfl⟩ : syracuseStep 8185657 = 6139243) B6139243
theorem B43666735 : Blo 1512953 43666735 := bstep (se 1 (by rfl) ⟨32750051, by rfl⟩ : syracuseStep 43666735 = 65500103) B65500103
theorem B7664219 : Blo 1512953 7664219 := bstep (se 1 (by rfl) ⟨5748164, by rfl⟩ : syracuseStep 7664219 = 11496329) B11496329
theorem B58222313 : Blo 1512953 58222313 := bstep (se 2 (by rfl) ⟨21833367, by rfl⟩ : syracuseStep 58222313 = 43666735) B43666735
theorem B10914209 : Blo 1512953 10914209 := bstep (se 2 (by rfl) ⟨4092828, by rfl⟩ : syracuseStep 10914209 = 8185657) B8185657
theorem B5109479 : Blo 1512953 5109479 := bstep (se 1 (by rfl) ⟨3832109, by rfl⟩ : syracuseStep 5109479 = 7664219) B7664219
theorem B2873407 : Blo 1512953 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B38814875 : Blo 1512953 38814875 := bstep (se 1 (by rfl) ⟨29111156, by rfl⟩ : syracuseStep 38814875 = 58222313) B58222313
theorem B7276139 : Blo 1512953 7276139 := bstep (se 1 (by rfl) ⟨5457104, by rfl⟩ : syracuseStep 7276139 = 10914209) B10914209
theorem B3831209 : Blo 1512953 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B3406319 : Blo 1512953 3406319 := bstep (se 1 (by rfl) ⟨2554739, by rfl⟩ : syracuseStep 3406319 = 5109479) B5109479
theorem B4850759 : Blo 1512953 4850759 := bstep (se 1 (by rfl) ⟨3638069, by rfl⟩ : syracuseStep 4850759 = 7276139) B7276139
theorem B2270879 : Blo 1512953 2270879 := bstep (se 1 (by rfl) ⟨1703159, by rfl⟩ : syracuseStep 2270879 = 3406319) B3406319
theorem B25876583 : Blo 1512953 25876583 := bstep (se 1 (by rfl) ⟨19407437, by rfl⟩ : syracuseStep 25876583 = 38814875) B38814875
theorem B2554139 : Blo 1512953 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B3233839 : Blo 1512953 3233839 := bstep (se 1 (by rfl) ⟨2425379, by rfl⟩ : syracuseStep 3233839 = 4850759) B4850759
theorem B1513919 : Blo 1512953 1513919 := bstep (se 1 (by rfl) ⟨1135439, by rfl⟩ : syracuseStep 1513919 = 2270879) B2270879
theorem B17251055 : Blo 1512953 17251055 := bstep (se 1 (by rfl) ⟨12938291, by rfl⟩ : syracuseStep 17251055 = 25876583) B25876583
theorem B1702759 : Blo 1512953 1702759 := bstep (se 1 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 1702759 = 2554139) B2554139
theorem B2270345 : Blo 1512953 2270345 := bstep (se 2 (by rfl) ⟨851379, by rfl⟩ : syracuseStep 2270345 = 1702759) B1702759
theorem B4311785 : Blo 1512953 4311785 := bstep (se 2 (by rfl) ⟨1616919, by rfl⟩ : syracuseStep 4311785 = 3233839) B3233839
theorem B11500703 : Blo 1512953 11500703 := bstep (se 1 (by rfl) ⟨8625527, by rfl⟩ : syracuseStep 11500703 = 17251055) B17251055
theorem B1513563 : Blo 1512953 1513563 := bstep (se 1 (by rfl) ⟨1135172, by rfl⟩ : syracuseStep 1513563 = 2270345) B2270345
theorem B2874523 : Blo 1512953 2874523 := bstep (se 1 (by rfl) ⟨2155892, by rfl⟩ : syracuseStep 2874523 = 4311785) B4311785
theorem B7667135 : Blo 1512953 7667135 := bstep (se 1 (by rfl) ⟨5750351, by rfl⟩ : syracuseStep 7667135 = 11500703) B11500703
theorem B3832697 : Blo 1512953 3832697 := bstep (se 2 (by rfl) ⟨1437261, by rfl⟩ : syracuseStep 3832697 = 2874523) B2874523
theorem B5111423 : Blo 1512953 5111423 := bstep (se 1 (by rfl) ⟨3833567, by rfl⟩ : syracuseStep 5111423 = 7667135) B7667135
theorem B2555131 : Blo 1512953 2555131 := bstep (se 1 (by rfl) ⟨1916348, by rfl⟩ : syracuseStep 2555131 = 3832697) B3832697
theorem B3407615 : Blo 1512953 3407615 := bstep (se 1 (by rfl) ⟨2555711, by rfl⟩ : syracuseStep 3407615 = 5111423) B5111423
theorem B2271743 : Blo 1512953 2271743 := bstep (se 1 (by rfl) ⟨1703807, by rfl⟩ : syracuseStep 2271743 = 3407615) B3407615
theorem B3406841 : Blo 1512953 3406841 := bstep (se 2 (by rfl) ⟨1277565, by rfl⟩ : syracuseStep 3406841 = 2555131) B2555131
theorem B2271227 : Blo 1512953 2271227 := bstep (se 1 (by rfl) ⟨1703420, by rfl⟩ : syracuseStep 2271227 = 3406841) B3406841
theorem B1514495 : Blo 1512953 1514495 := bstep (se 1 (by rfl) ⟨1135871, by rfl⟩ : syracuseStep 1514495 = 2271743) B2271743
theorem B1514151 : Blo 1512953 1514151 := bstep (se 1 (by rfl) ⟨1135613, by rfl⟩ : syracuseStep 1514151 = 2271227) B2271227

theorem C0 (j : ℕ) (h1 : 378238 ≤ j) (h2 : j ≤ 378737) : Blo 1512953 (4 * j + 3) := by
  interval_cases j
  · exact B1512955
  · exact B1512959
  · exact B1512963
  · exact B1512967
  · exact B1512971
  · exact B1512975
  · exact B1512979
  · exact B1512983
  · exact B1512987
  · exact B1512991
  · exact B1512995
  · exact B1512999
  · exact B1513003
  · exact B1513007
  · exact B1513011
  · exact B1513015
  · exact B1513019
  · exact B1513023
  · exact B1513027
  · exact B1513031
  · exact B1513035
  · exact B1513039
  · exact B1513043
  · exact B1513047
  · exact B1513051
  · exact B1513055
  · exact B1513059
  · exact B1513063
  · exact B1513067
  · exact B1513071
  · exact B1513075
  · exact B1513079
  · exact B1513083
  · exact B1513087
  · exact B1513091
  · exact B1513095
  · exact B1513099
  · exact B1513103
  · exact B1513107
  · exact B1513111
  · exact B1513115
  · exact B1513119
  · exact B1513123
  · exact B1513127
  · exact B1513131
  · exact B1513135
  · exact B1513139
  · exact B1513143
  · exact B1513147
  · exact B1513151
  · exact B1513155
  · exact B1513159
  · exact B1513163
  · exact B1513167
  · exact B1513171
  · exact B1513175
  · exact B1513179
  · exact B1513183
  · exact B1513187
  · exact B1513191
  · exact B1513195
  · exact B1513199
  · exact B1513203
  · exact B1513207
  · exact B1513211
  · exact B1513215
  · exact B1513219
  · exact B1513223
  · exact B1513227
  · exact B1513231
  · exact B1513235
  · exact B1513239
  · exact B1513243
  · exact B1513247
  · exact B1513251
  · exact B1513255
  · exact B1513259
  · exact B1513263
  · exact B1513267
  · exact B1513271
  · exact B1513275
  · exact B1513279
  · exact B1513283
  · exact B1513287
  · exact B1513291
  · exact B1513295
  · exact B1513299
  · exact B1513303
  · exact B1513307
  · exact B1513311
  · exact B1513315
  · exact B1513319
  · exact B1513323
  · exact B1513327
  · exact B1513331
  · exact B1513335
  · exact B1513339
  · exact B1513343
  · exact B1513347
  · exact B1513351
  · exact B1513355
  · exact B1513359
  · exact B1513363
  · exact B1513367
  · exact B1513371
  · exact B1513375
  · exact B1513379
  · exact B1513383
  · exact B1513387
  · exact B1513391
  · exact B1513395
  · exact B1513399
  · exact B1513403
  · exact B1513407
  · exact B1513411
  · exact B1513415
  · exact B1513419
  · exact B1513423
  · exact B1513427
  · exact B1513431
  · exact B1513435
  · exact B1513439
  · exact B1513443
  · exact B1513447
  · exact B1513451
  · exact B1513455
  · exact B1513459
  · exact B1513463
  · exact B1513467
  · exact B1513471
  · exact B1513475
  · exact B1513479
  · exact B1513483
  · exact B1513487
  · exact B1513491
  · exact B1513495
  · exact B1513499
  · exact B1513503
  · exact B1513507
  · exact B1513511
  · exact B1513515
  · exact B1513519
  · exact B1513523
  · exact B1513527
  · exact B1513531
  · exact B1513535
  · exact B1513539
  · exact B1513543
  · exact B1513547
  · exact B1513551
  · exact B1513555
  · exact B1513559
  · exact B1513563
  · exact B1513567
  · exact B1513571
  · exact B1513575
  · exact B1513579
  · exact B1513583
  · exact B1513587
  · exact B1513591
  · exact B1513595
  · exact B1513599
  · exact B1513603
  · exact B1513607
  · exact B1513611
  · exact B1513615
  · exact B1513619
  · exact B1513623
  · exact B1513627
  · exact B1513631
  · exact B1513635
  · exact B1513639
  · exact B1513643
  · exact B1513647
  · exact B1513651
  · exact B1513655
  · exact B1513659
  · exact B1513663
  · exact B1513667
  · exact B1513671
  · exact B1513675
  · exact B1513679
  · exact B1513683
  · exact B1513687
  · exact B1513691
  · exact B1513695
  · exact B1513699
  · exact B1513703
  · exact B1513707
  · exact B1513711
  · exact B1513715
  · exact B1513719
  · exact B1513723
  · exact B1513727
  · exact B1513731
  · exact B1513735
  · exact B1513739
  · exact B1513743
  · exact B1513747
  · exact B1513751
  · exact B1513755
  · exact B1513759
  · exact B1513763
  · exact B1513767
  · exact B1513771
  · exact B1513775
  · exact B1513779
  · exact B1513783
  · exact B1513787
  · exact B1513791
  · exact B1513795
  · exact B1513799
  · exact B1513803
  · exact B1513807
  · exact B1513811
  · exact B1513815
  · exact B1513819
  · exact B1513823
  · exact B1513827
  · exact B1513831
  · exact B1513835
  · exact B1513839
  · exact B1513843
  · exact B1513847
  · exact B1513851
  · exact B1513855
  · exact B1513859
  · exact B1513863
  · exact B1513867
  · exact B1513871
  · exact B1513875
  · exact B1513879
  · exact B1513883
  · exact B1513887
  · exact B1513891
  · exact B1513895
  · exact B1513899
  · exact B1513903
  · exact B1513907
  · exact B1513911
  · exact B1513915
  · exact B1513919
  · exact B1513923
  · exact B1513927
  · exact B1513931
  · exact B1513935
  · exact B1513939
  · exact B1513943
  · exact B1513947
  · exact B1513951
  · exact B1513955
  · exact B1513959
  · exact B1513963
  · exact B1513967
  · exact B1513971
  · exact B1513975
  · exact B1513979
  · exact B1513983
  · exact B1513987
  · exact B1513991
  · exact B1513995
  · exact B1513999
  · exact B1514003
  · exact B1514007
  · exact B1514011
  · exact B1514015
  · exact B1514019
  · exact B1514023
  · exact B1514027
  · exact B1514031
  · exact B1514035
  · exact B1514039
  · exact B1514043
  · exact B1514047
  · exact B1514051
  · exact B1514055
  · exact B1514059
  · exact B1514063
  · exact B1514067
  · exact B1514071
  · exact B1514075
  · exact B1514079
  · exact B1514083
  · exact B1514087
  · exact B1514091
  · exact B1514095
  · exact B1514099
  · exact B1514103
  · exact B1514107
  · exact B1514111
  · exact B1514115
  · exact B1514119
  · exact B1514123
  · exact B1514127
  · exact B1514131
  · exact B1514135
  · exact B1514139
  · exact B1514143
  · exact B1514147
  · exact B1514151
  · exact B1514155
  · exact B1514159
  · exact B1514163
  · exact B1514167
  · exact B1514171
  · exact B1514175
  · exact B1514179
  · exact B1514183
  · exact B1514187
  · exact B1514191
  · exact B1514195
  · exact B1514199
  · exact B1514203
  · exact B1514207
  · exact B1514211
  · exact B1514215
  · exact B1514219
  · exact B1514223
  · exact B1514227
  · exact B1514231
  · exact B1514235
  · exact B1514239
  · exact B1514243
  · exact B1514247
  · exact B1514251
  · exact B1514255
  · exact B1514259
  · exact B1514263
  · exact B1514267
  · exact B1514271
  · exact B1514275
  · exact B1514279
  · exact B1514283
  · exact B1514287
  · exact B1514291
  · exact B1514295
  · exact B1514299
  · exact B1514303
  · exact B1514307
  · exact B1514311
  · exact B1514315
  · exact B1514319
  · exact B1514323
  · exact B1514327
  · exact B1514331
  · exact B1514335
  · exact B1514339
  · exact B1514343
  · exact B1514347
  · exact B1514351
  · exact B1514355
  · exact B1514359
  · exact B1514363
  · exact B1514367
  · exact B1514371
  · exact B1514375
  · exact B1514379
  · exact B1514383
  · exact B1514387
  · exact B1514391
  · exact B1514395
  · exact B1514399
  · exact B1514403
  · exact B1514407
  · exact B1514411
  · exact B1514415
  · exact B1514419
  · exact B1514423
  · exact B1514427
  · exact B1514431
  · exact B1514435
  · exact B1514439
  · exact B1514443
  · exact B1514447
  · exact B1514451
  · exact B1514455
  · exact B1514459
  · exact B1514463
  · exact B1514467
  · exact B1514471
  · exact B1514475
  · exact B1514479
  · exact B1514483
  · exact B1514487
  · exact B1514491
  · exact B1514495
  · exact B1514499
  · exact B1514503
  · exact B1514507
  · exact B1514511
  · exact B1514515
  · exact B1514519
  · exact B1514523
  · exact B1514527
  · exact B1514531
  · exact B1514535
  · exact B1514539
  · exact B1514543
  · exact B1514547
  · exact B1514551
  · exact B1514555
  · exact B1514559
  · exact B1514563
  · exact B1514567
  · exact B1514571
  · exact B1514575
  · exact B1514579
  · exact B1514583
  · exact B1514587
  · exact B1514591
  · exact B1514595
  · exact B1514599
  · exact B1514603
  · exact B1514607
  · exact B1514611
  · exact B1514615
  · exact B1514619
  · exact B1514623
  · exact B1514627
  · exact B1514631
  · exact B1514635
  · exact B1514639
  · exact B1514643
  · exact B1514647
  · exact B1514651
  · exact B1514655
  · exact B1514659
  · exact B1514663
  · exact B1514667
  · exact B1514671
  · exact B1514675
  · exact B1514679
  · exact B1514683
  · exact B1514687
  · exact B1514691
  · exact B1514695
  · exact B1514699
  · exact B1514703
  · exact B1514707
  · exact B1514711
  · exact B1514715
  · exact B1514719
  · exact B1514723
  · exact B1514727
  · exact B1514731
  · exact B1514735
  · exact B1514739
  · exact B1514743
  · exact B1514747
  · exact B1514751
  · exact B1514755
  · exact B1514759
  · exact B1514763
  · exact B1514767
  · exact B1514771
  · exact B1514775
  · exact B1514779
  · exact B1514783
  · exact B1514787
  · exact B1514791
  · exact B1514795
  · exact B1514799
  · exact B1514803
  · exact B1514807
  · exact B1514811
  · exact B1514815
  · exact B1514819
  · exact B1514823
  · exact B1514827
  · exact B1514831
  · exact B1514835
  · exact B1514839
  · exact B1514843
  · exact B1514847
  · exact B1514851
  · exact B1514855
  · exact B1514859
  · exact B1514863
  · exact B1514867
  · exact B1514871
  · exact B1514875
  · exact B1514879
  · exact B1514883
  · exact B1514887
  · exact B1514891
  · exact B1514895
  · exact B1514899
  · exact B1514903
  · exact B1514907
  · exact B1514911
  · exact B1514915
  · exact B1514919
  · exact B1514923
  · exact B1514927
  · exact B1514931
  · exact B1514935
  · exact B1514939
  · exact B1514943
  · exact B1514947
  · exact B1514951

theorem solution (m : ℕ) (hlo : 1512953 ≤ m) (hhi : m ≤ 1514953) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 378238 ≤ j := by omega
    have hj2 : j ≤ 378737 := by omega
    have hb : Blo 1512953 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
