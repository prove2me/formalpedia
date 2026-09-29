-- Prove2me | solution 1 for syracuse_descends_range_1198416_1200416
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:43.838626+00:00
-- url     : https://prove2.me/submissions/90d2af48-5fc6-4862-91ae-3db55050fe4d

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


theorem B2277389 : Blo 1198416 2277389 := bbase (se 3 (by rfl) ⟨427010, by rfl⟩ : syracuseStep 2277389 = 854021) (by norm_num)
theorem B2883637 : Blo 1198416 2883637 := bbase (se 5 (by rfl) ⟨135170, by rfl⟩ : syracuseStep 2883637 = 270341) (by norm_num)
theorem B2023501 : Blo 1198416 2023501 := bbase (se 3 (by rfl) ⟨379406, by rfl⟩ : syracuseStep 2023501 = 758813) (by norm_num)
theorem B1622101 : Blo 1198416 1622101 := bbase (se 8 (by rfl) ⟨9504, by rfl⟩ : syracuseStep 1622101 = 19009) (by norm_num)
theorem B2162837 : Blo 1198416 2162837 := bbase (se 6 (by rfl) ⟨50691, by rfl⟩ : syracuseStep 2162837 = 101383) (by norm_num)
theorem B2277533 : Blo 1198416 2277533 := bbase (se 3 (by rfl) ⟨427037, by rfl⟩ : syracuseStep 2277533 = 854075) (by norm_num)
theorem B2023589 : Blo 1198416 2023589 := bbase (se 4 (by rfl) ⟨189711, by rfl⟩ : syracuseStep 2023589 = 379423) (by norm_num)
theorem B4047029 : Blo 1198416 4047029 := bbase (se 5 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 4047029 = 379409) (by norm_num)
theorem B8642837 : Blo 1198416 8642837 := bbase (se 6 (by rfl) ⟨202566, by rfl⟩ : syracuseStep 8642837 = 405133) (by norm_num)
theorem B2023717 : Blo 1198416 2023717 := bbase (se 4 (by rfl) ⟨189723, by rfl⟩ : syracuseStep 2023717 = 379447) (by norm_num)
theorem B3416357 : Blo 1198416 3416357 := bbase (se 4 (by rfl) ⟨320283, by rfl⟩ : syracuseStep 3416357 = 640567) (by norm_num)
theorem B2736437 : Blo 1198416 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B2023805 : Blo 1198416 2023805 := bbase (se 3 (by rfl) ⟨379463, by rfl⟩ : syracuseStep 2023805 = 758927) (by norm_num)
theorem B2277821 : Blo 1198416 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B2884061 : Blo 1198416 2884061 := bbase (se 3 (by rfl) ⟨540761, by rfl⟩ : syracuseStep 2884061 = 1081523) (by norm_num)
theorem B2023933 : Blo 1198416 2023933 := bbase (se 3 (by rfl) ⟨379487, by rfl⟩ : syracuseStep 2023933 = 758975) (by norm_num)
theorem B2433581 : Blo 1198416 2433581 := bbase (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) (by norm_num)
theorem B9110069 : Blo 1198416 9110069 := bbase (se 5 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 9110069 = 854069) (by norm_num)
theorem B2024021 : Blo 1198416 2024021 := bbase (se 8 (by rfl) ⟨11859, by rfl⟩ : syracuseStep 2024021 = 23719) (by norm_num)
theorem B2277973 : Blo 1198416 2277973 := bbase (se 8 (by rfl) ⟨13347, by rfl⟩ : syracuseStep 2277973 = 26695) (by norm_num)
theorem B4047461 : Blo 1198416 4047461 := bbase (se 4 (by rfl) ⟨379449, by rfl⟩ : syracuseStep 4047461 = 758899) (by norm_num)
theorem B6070949 : Blo 1198416 6070949 := bbase (se 4 (by rfl) ⟨569151, by rfl⟩ : syracuseStep 6070949 = 1138303) (by norm_num)
theorem B1368785 : Blo 1198416 1368785 := bbase (se 2 (by rfl) ⟨513294, by rfl⟩ : syracuseStep 1368785 = 1026589) (by norm_num)
theorem B2024149 : Blo 1198416 2024149 := bbase (se 7 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 2024149 = 47441) (by norm_num)
theorem B4326149 : Blo 1198416 4326149 := bbase (se 4 (by rfl) ⟨405576, by rfl⟩ : syracuseStep 4326149 = 811153) (by norm_num)
theorem B1368857 : Blo 1198416 1368857 := bbase (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) (by norm_num)
theorem B2024237 : Blo 1198416 2024237 := bbase (se 3 (by rfl) ⟨379544, by rfl⟩ : syracuseStep 2024237 = 759089) (by norm_num)
theorem B2278277 : Blo 1198416 2278277 := bbase (se 4 (by rfl) ⟨213588, by rfl⟩ : syracuseStep 2278277 = 427177) (by norm_num)
theorem B2024365 : Blo 1198416 2024365 := bbase (se 3 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 2024365 = 759137) (by norm_num)
theorem B3417029 : Blo 1198416 3417029 := bbase (se 4 (by rfl) ⟨320346, by rfl⟩ : syracuseStep 3417029 = 640693) (by norm_num)
theorem B9102293 : Blo 1198416 9102293 := bbase (se 7 (by rfl) ⟨106667, by rfl⟩ : syracuseStep 9102293 = 213335) (by norm_num)
theorem B11535317 : Blo 1198416 11535317 := bbase (se 7 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 11535317 = 270359) (by norm_num)
theorem B4105205 : Blo 1198416 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B2024453 : Blo 1198416 2024453 := bbase (se 4 (by rfl) ⟨189792, by rfl⟩ : syracuseStep 2024453 = 379585) (by norm_num)
theorem B4047893 : Blo 1198416 4047893 := bbase (se 6 (by rfl) ⟨94872, by rfl⟩ : syracuseStep 4047893 = 189745) (by norm_num)
theorem B9724981 : Blo 1198416 9724981 := bbase (se 5 (by rfl) ⟨455858, by rfl⟩ : syracuseStep 9724981 = 911717) (by norm_num)
theorem B10937429 : Blo 1198416 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B8651893 : Blo 1198416 8651893 := bbase (se 5 (by rfl) ⟨405557, by rfl⟩ : syracuseStep 8651893 = 811115) (by norm_num)
theorem B2024581 : Blo 1198416 2024581 := bbase (se 4 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 2024581 = 379609) (by norm_num)
theorem B2221229 : Blo 1198416 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B2024669 : Blo 1198416 2024669 := bbase (se 3 (by rfl) ⟨379625, by rfl⟩ : syracuseStep 2024669 = 759251) (by norm_num)
theorem B3646709 : Blo 1198416 3646709 := bbase (se 5 (by rfl) ⟨170939, by rfl⟩ : syracuseStep 3646709 = 341879) (by norm_num)
theorem B1516801 : Blo 1198416 1516801 := bbase (se 2 (by rfl) ⟨568800, by rfl⟩ : syracuseStep 1516801 = 1137601) (by norm_num)
theorem B2696453 : Blo 1198416 2696453 := bbase (se 4 (by rfl) ⟨252792, by rfl⟩ : syracuseStep 2696453 = 505585) (by norm_num)
theorem B2696525 : Blo 1198416 2696525 := bbase (se 3 (by rfl) ⟨505598, by rfl⟩ : syracuseStep 2696525 = 1011197) (by norm_num)
theorem B2024797 : Blo 1198416 2024797 := bbase (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) (by norm_num)
theorem B1516897 : Blo 1198416 1516897 := bbase (se 2 (by rfl) ⟨568836, by rfl⟩ : syracuseStep 1516897 = 1137673) (by norm_num)
theorem B3417461 : Blo 1198416 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B2696597 : Blo 1198416 2696597 := bbase (se 6 (by rfl) ⟨63201, by rfl⟩ : syracuseStep 2696597 = 126403) (by norm_num)
theorem B2024885 : Blo 1198416 2024885 := bbase (se 5 (by rfl) ⟨94916, by rfl⟩ : syracuseStep 2024885 = 189833) (by norm_num)
theorem B4048325 : Blo 1198416 4048325 := bbase (se 4 (by rfl) ⟨379530, by rfl⟩ : syracuseStep 4048325 = 759061) (by norm_num)
theorem B2696669 : Blo 1198416 2696669 := bbase (se 3 (by rfl) ⟨505625, by rfl⟩ : syracuseStep 2696669 = 1011251) (by norm_num)
theorem B1517069 : Blo 1198416 1517069 := bbase (se 3 (by rfl) ⟨284450, by rfl⟩ : syracuseStep 1517069 = 568901) (by norm_num)
theorem B2696741 : Blo 1198416 2696741 := bbase (se 4 (by rfl) ⟨252819, by rfl⟩ : syracuseStep 2696741 = 505639) (by norm_num)
theorem B2025013 : Blo 1198416 2025013 := bbase (se 5 (by rfl) ⟨94922, by rfl⟩ : syracuseStep 2025013 = 189845) (by norm_num)
theorem B1459777 : Blo 1198416 1459777 := bbase (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) (by norm_num)
theorem B1517125 : Blo 1198416 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1386053 : Blo 1198416 1386053 := bbase (se 4 (by rfl) ⟨129942, by rfl⟩ : syracuseStep 1386053 = 259885) (by norm_num)
theorem B4556357 : Blo 1198416 4556357 := bbase (se 4 (by rfl) ⟨427158, by rfl⟩ : syracuseStep 4556357 = 854317) (by norm_num)
theorem B12977749 : Blo 1198416 12977749 := bbase (se 8 (by rfl) ⟨76041, by rfl⟩ : syracuseStep 12977749 = 152083) (by norm_num)
theorem B2696813 : Blo 1198416 2696813 := bbase (se 3 (by rfl) ⟨505652, by rfl⟩ : syracuseStep 2696813 = 1011305) (by norm_num)
theorem B2025101 : Blo 1198416 2025101 := bbase (se 3 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 2025101 = 759413) (by norm_num)
theorem B5760661 : Blo 1198416 5760661 := bbase (se 6 (by rfl) ⟨135015, by rfl⟩ : syracuseStep 5760661 = 270031) (by norm_num)
theorem B1517221 : Blo 1198416 1517221 := bbase (se 4 (by rfl) ⟨142239, by rfl⟩ : syracuseStep 1517221 = 284479) (by norm_num)
theorem B2696885 : Blo 1198416 2696885 := bbase (se 5 (by rfl) ⟨126416, by rfl⟩ : syracuseStep 2696885 = 252833) (by norm_num)
theorem B24610517 : Blo 1198416 24610517 := bbase (se 7 (by rfl) ⟨288404, by rfl⟩ : syracuseStep 24610517 = 576809) (by norm_num)
theorem B2696957 : Blo 1198416 2696957 := bbase (se 3 (by rfl) ⟨505679, by rfl⟩ : syracuseStep 2696957 = 1011359) (by norm_num)
theorem B3892997 : Blo 1198416 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B2025229 : Blo 1198416 2025229 := bbase (se 3 (by rfl) ⟨379730, by rfl⟩ : syracuseStep 2025229 = 759461) (by norm_num)
theorem B2107181 : Blo 1198416 2107181 := bbase (se 3 (by rfl) ⟨395096, by rfl⟩ : syracuseStep 2107181 = 790193) (by norm_num)
theorem B1279805 : Blo 1198416 1279805 := bbase (se 3 (by rfl) ⟨239963, by rfl⟩ : syracuseStep 1279805 = 479927) (by norm_num)
theorem B2697029 : Blo 1198416 2697029 := bbase (se 4 (by rfl) ⟨252846, by rfl⟩ : syracuseStep 2697029 = 505693) (by norm_num)
theorem B1517393 : Blo 1198416 1517393 := bbase (se 2 (by rfl) ⟨569022, by rfl⟩ : syracuseStep 1517393 = 1138045) (by norm_num)
theorem B4556645 : Blo 1198416 4556645 := bbase (se 4 (by rfl) ⟨427185, by rfl⟩ : syracuseStep 4556645 = 854371) (by norm_num)
theorem B2025317 : Blo 1198416 2025317 := bbase (se 4 (by rfl) ⟨189873, by rfl⟩ : syracuseStep 2025317 = 379747) (by norm_num)
theorem B4048757 : Blo 1198416 4048757 := bbase (se 5 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 4048757 = 379571) (by norm_num)
theorem B1517449 : Blo 1198416 1517449 := bbase (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) (by norm_num)
theorem B2697101 : Blo 1198416 2697101 := bbase (se 3 (by rfl) ⟨505706, by rfl⟩ : syracuseStep 2697101 = 1011413) (by norm_num)
theorem B6072245 : Blo 1198416 6072245 := bbase (se 5 (by rfl) ⟨284636, by rfl⟩ : syracuseStep 6072245 = 569273) (by norm_num)
theorem B2697173 : Blo 1198416 2697173 := bbase (se 7 (by rfl) ⟨31607, by rfl⟩ : syracuseStep 2697173 = 63215) (by norm_num)
theorem B2025445 : Blo 1198416 2025445 := bbase (se 4 (by rfl) ⟨189885, by rfl⟩ : syracuseStep 2025445 = 379771) (by norm_num)
theorem B1517545 : Blo 1198416 1517545 := bbase (se 2 (by rfl) ⟨569079, by rfl⟩ : syracuseStep 1517545 = 1138159) (by norm_num)
theorem B2697245 : Blo 1198416 2697245 := bbase (se 3 (by rfl) ⟨505733, by rfl⟩ : syracuseStep 2697245 = 1011467) (by norm_num)
theorem B1280053 : Blo 1198416 1280053 := bbase (se 5 (by rfl) ⟨60002, by rfl⟩ : syracuseStep 1280053 = 120005) (by norm_num)
theorem B2025533 : Blo 1198416 2025533 := bbase (se 3 (by rfl) ⟨379787, by rfl⟩ : syracuseStep 2025533 = 759575) (by norm_num)
theorem B2697317 : Blo 1198416 2697317 := bbase (se 4 (by rfl) ⟨252873, by rfl⟩ : syracuseStep 2697317 = 505747) (by norm_num)
theorem B3418213 : Blo 1198416 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B1517717 : Blo 1198416 1517717 := bbase (se 6 (by rfl) ⟨35571, by rfl⟩ : syracuseStep 1517717 = 71143) (by norm_num)
theorem B2697389 : Blo 1198416 2697389 := bbase (se 3 (by rfl) ⟨505760, by rfl⟩ : syracuseStep 2697389 = 1011521) (by norm_num)
theorem B2025661 : Blo 1198416 2025661 := bbase (se 3 (by rfl) ⟨379811, by rfl⟩ : syracuseStep 2025661 = 759623) (by norm_num)
theorem B1517773 : Blo 1198416 1517773 := bbase (se 3 (by rfl) ⟨284582, by rfl⟩ : syracuseStep 1517773 = 569165) (by norm_num)
theorem B2697461 : Blo 1198416 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B4049189 : Blo 1198416 4049189 := bbase (se 4 (by rfl) ⟨379611, by rfl⟩ : syracuseStep 4049189 = 759223) (by norm_num)
theorem B1517869 : Blo 1198416 1517869 := bbase (se 3 (by rfl) ⟨284600, by rfl⟩ : syracuseStep 1517869 = 569201) (by norm_num)
theorem B2697533 : Blo 1198416 2697533 := bbase (se 3 (by rfl) ⟨505787, by rfl⟩ : syracuseStep 2697533 = 1011575) (by norm_num)
theorem B4319573 : Blo 1198416 4319573 := bbase (se 10 (by rfl) ⟨6327, by rfl⟩ : syracuseStep 4319573 = 12655) (by norm_num)
theorem B2697605 : Blo 1198416 2697605 := bbase (se 4 (by rfl) ⟨252900, by rfl⟩ : syracuseStep 2697605 = 505801) (by norm_num)
theorem B2697677 : Blo 1198416 2697677 := bbase (se 3 (by rfl) ⟨505814, by rfl⟩ : syracuseStep 2697677 = 1011629) (by norm_num)
theorem B1214929 : Blo 1198416 1214929 := bbase (se 2 (by rfl) ⟨455598, by rfl⟩ : syracuseStep 1214929 = 911197) (by norm_num)
theorem B6482389 : Blo 1198416 6482389 := bbase (se 7 (by rfl) ⟨75965, by rfl⟩ : syracuseStep 6482389 = 151931) (by norm_num)
theorem B1518041 : Blo 1198416 1518041 := bbase (se 2 (by rfl) ⟨569265, by rfl⟩ : syracuseStep 1518041 = 1138531) (by norm_num)
theorem B1280485 : Blo 1198416 1280485 := bbase (se 4 (by rfl) ⟨120045, by rfl⟩ : syracuseStep 1280485 = 240091) (by norm_num)
theorem B1518097 : Blo 1198416 1518097 := bbase (se 2 (by rfl) ⟨569286, by rfl⟩ : syracuseStep 1518097 = 1138573) (by norm_num)
theorem B6826517 : Blo 1198416 6826517 := bbase (se 6 (by rfl) ⟨159996, by rfl⟩ : syracuseStep 6826517 = 319993) (by norm_num)
theorem B15362581 : Blo 1198416 15362581 := bbase (se 6 (by rfl) ⟨360060, by rfl⟩ : syracuseStep 15362581 = 720121) (by norm_num)
theorem B2697749 : Blo 1198416 2697749 := bbase (se 6 (by rfl) ⟨63228, by rfl⟩ : syracuseStep 2697749 = 126457) (by norm_num)
theorem B3648037 : Blo 1198416 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B1280557 : Blo 1198416 1280557 := bbase (se 3 (by rfl) ⟨240104, by rfl⟩ : syracuseStep 1280557 = 480209) (by norm_num)
theorem B2697821 : Blo 1198416 2697821 := bbase (se 3 (by rfl) ⟨505841, by rfl⟩ : syracuseStep 2697821 = 1011683) (by norm_num)
theorem B1518193 : Blo 1198416 1518193 := bbase (se 2 (by rfl) ⟨569322, by rfl⟩ : syracuseStep 1518193 = 1138645) (by norm_num)
theorem B3033733 : Blo 1198416 3033733 := bbase (se 4 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 3033733 = 568825) (by norm_num)
theorem B2697893 : Blo 1198416 2697893 := bbase (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) (by norm_num)
theorem B4049621 : Blo 1198416 4049621 := bbase (se 7 (by rfl) ⟨47456, by rfl⟩ : syracuseStep 4049621 = 94913) (by norm_num)
theorem B3844837 : Blo 1198416 3844837 := bbase (se 4 (by rfl) ⟨360453, by rfl⟩ : syracuseStep 3844837 = 720907) (by norm_num)
theorem B2697965 : Blo 1198416 2697965 := bbase (se 3 (by rfl) ⟨505868, by rfl⟩ : syracuseStep 2697965 = 1011737) (by norm_num)
theorem B3033845 : Blo 1198416 3033845 := bbase (se 5 (by rfl) ⟨142211, by rfl⟩ : syracuseStep 3033845 = 284423) (by norm_num)
theorem B1518365 : Blo 1198416 1518365 := bbase (se 3 (by rfl) ⟨284693, by rfl⟩ : syracuseStep 1518365 = 569387) (by norm_num)
theorem B3844901 : Blo 1198416 3844901 := bbase (se 4 (by rfl) ⟨360459, by rfl⟩ : syracuseStep 3844901 = 720919) (by norm_num)
theorem B2698037 : Blo 1198416 2698037 := bbase (se 5 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 2698037 = 252941) (by norm_num)
theorem B1518421 : Blo 1198416 1518421 := bbase (se 9 (by rfl) ⟨4448, by rfl⟩ : syracuseStep 1518421 = 8897) (by norm_num)
theorem B1919837 : Blo 1198416 1919837 := bbase (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) (by norm_num)
theorem B2698109 : Blo 1198416 2698109 := bbase (se 3 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 2698109 = 1011791) (by norm_num)
theorem B4860805 : Blo 1198416 4860805 := bbase (se 4 (by rfl) ⟨455700, by rfl⟩ : syracuseStep 4860805 = 911401) (by norm_num)
theorem B1280929 : Blo 1198416 1280929 := bbase (se 2 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 1280929 = 960697) (by norm_num)
theorem B3034037 : Blo 1198416 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B1518517 : Blo 1198416 1518517 := bbase (se 5 (by rfl) ⟨71180, by rfl⟩ : syracuseStep 1518517 = 142361) (by norm_num)
theorem B2698181 : Blo 1198416 2698181 := bbase (se 4 (by rfl) ⟨252954, by rfl⟩ : syracuseStep 2698181 = 505909) (by norm_num)
theorem B1297405 : Blo 1198416 1297405 := bbase (se 3 (by rfl) ⟨243263, by rfl⟩ : syracuseStep 1297405 = 486527) (by norm_num)
theorem B3075077 : Blo 1198416 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B4557829 : Blo 1198416 4557829 := bbase (se 4 (by rfl) ⟨427296, by rfl⟩ : syracuseStep 4557829 = 854593) (by norm_num)
theorem B2698253 : Blo 1198416 2698253 := bbase (se 3 (by rfl) ⟨505922, by rfl⟩ : syracuseStep 2698253 = 1011845) (by norm_num)
theorem B3460117 : Blo 1198416 3460117 := bbase (se 6 (by rfl) ⟨81096, by rfl⟩ : syracuseStep 3460117 = 162193) (by norm_num)
theorem B3894293 : Blo 1198416 3894293 := bbase (se 6 (by rfl) ⟨91272, by rfl⟩ : syracuseStep 3894293 = 182545) (by norm_num)
theorem B1920061 : Blo 1198416 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B1707085 : Blo 1198416 1707085 := bbase (se 3 (by rfl) ⟨320078, by rfl⟩ : syracuseStep 1707085 = 640157) (by norm_num)
theorem B2698325 : Blo 1198416 2698325 := bbase (se 8 (by rfl) ⟨15810, by rfl⟩ : syracuseStep 2698325 = 31621) (by norm_num)
theorem B1518689 : Blo 1198416 1518689 := bbase (se 2 (by rfl) ⟨569508, by rfl⟩ : syracuseStep 1518689 = 1139017) (by norm_num)
theorem B4050053 : Blo 1198416 4050053 := bbase (se 4 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 4050053 = 759385) (by norm_num)
theorem B1518745 : Blo 1198416 1518745 := bbase (se 2 (by rfl) ⟨569529, by rfl⟩ : syracuseStep 1518745 = 1139059) (by norm_num)
theorem B2698397 : Blo 1198416 2698397 := bbase (se 3 (by rfl) ⟨505949, by rfl⟩ : syracuseStep 2698397 = 1011899) (by norm_num)
theorem B6073541 : Blo 1198416 6073541 := bbase (se 4 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 6073541 = 1138789) (by norm_num)
theorem B2698469 : Blo 1198416 2698469 := bbase (se 4 (by rfl) ⟨252981, by rfl⟩ : syracuseStep 2698469 = 505963) (by norm_num)
theorem B1518841 : Blo 1198416 1518841 := bbase (se 2 (by rfl) ⟨569565, by rfl⟩ : syracuseStep 1518841 = 1139131) (by norm_num)
theorem B3034381 : Blo 1198416 3034381 := bbase (se 3 (by rfl) ⟨568946, by rfl⟩ : syracuseStep 3034381 = 1137893) (by norm_num)
theorem B1281305 : Blo 1198416 1281305 := bbase (se 2 (by rfl) ⟨480489, by rfl⟩ : syracuseStep 1281305 = 960979) (by norm_num)
theorem B2698541 : Blo 1198416 2698541 := bbase (se 3 (by rfl) ⟨505976, by rfl⟩ : syracuseStep 2698541 = 1011953) (by norm_num)
theorem B1215829 : Blo 1198416 1215829 := bbase (se 11 (by rfl) ⟨890, by rfl⟩ : syracuseStep 1215829 = 1781) (by norm_num)
theorem B1281377 : Blo 1198416 1281377 := bbase (se 2 (by rfl) ⟨480516, by rfl⟩ : syracuseStep 1281377 = 961033) (by norm_num)
theorem B2698613 : Blo 1198416 2698613 := bbase (se 5 (by rfl) ⟨126497, by rfl⟩ : syracuseStep 2698613 = 252995) (by norm_num)
theorem B3034493 : Blo 1198416 3034493 := bbase (se 3 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 3034493 = 1137935) (by norm_num)
theorem B1707421 : Blo 1198416 1707421 := bbase (se 3 (by rfl) ⟨320141, by rfl⟩ : syracuseStep 1707421 = 640283) (by norm_num)
theorem B1519013 : Blo 1198416 1519013 := bbase (se 4 (by rfl) ⟨142407, by rfl⟩ : syracuseStep 1519013 = 284815) (by norm_num)
theorem B2698685 : Blo 1198416 2698685 := bbase (se 3 (by rfl) ⟨506003, by rfl⟩ : syracuseStep 2698685 = 1012007) (by norm_num)
theorem B1519069 : Blo 1198416 1519069 := bbase (se 3 (by rfl) ⟨284825, by rfl⟩ : syracuseStep 1519069 = 569651) (by norm_num)
theorem B11095541 : Blo 1198416 11095541 := bbase (se 5 (by rfl) ⟨520103, by rfl⟩ : syracuseStep 11095541 = 1040207) (by norm_num)
theorem B1797629 : Blo 1198416 1797629 := bbase (se 3 (by rfl) ⟨337055, by rfl⟩ : syracuseStep 1797629 = 674111) (by norm_num)
theorem B2698757 : Blo 1198416 2698757 := bbase (se 4 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 2698757 = 506017) (by norm_num)
theorem B1797653 : Blo 1198416 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B1281565 : Blo 1198416 1281565 := bbase (se 3 (by rfl) ⟨240293, by rfl⟩ : syracuseStep 1281565 = 480587) (by norm_num)
theorem B1797677 : Blo 1198416 1797677 := bbase (se 3 (by rfl) ⟨337064, by rfl⟩ : syracuseStep 1797677 = 674129) (by norm_num)
theorem B4050485 : Blo 1198416 4050485 := bbase (se 5 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 4050485 = 379733) (by norm_num)
theorem B3034685 : Blo 1198416 3034685 := bbase (se 3 (by rfl) ⟨569003, by rfl⟩ : syracuseStep 3034685 = 1138007) (by norm_num)
theorem B1519165 : Blo 1198416 1519165 := bbase (se 3 (by rfl) ⟨284843, by rfl⟩ : syracuseStep 1519165 = 569687) (by norm_num)
theorem B1797701 : Blo 1198416 1797701 := bbase (se 4 (by rfl) ⟨168534, by rfl⟩ : syracuseStep 1797701 = 337069) (by norm_num)
theorem B2698829 : Blo 1198416 2698829 := bbase (se 3 (by rfl) ⟨506030, by rfl⟩ : syracuseStep 2698829 = 1012061) (by norm_num)
theorem B1797725 : Blo 1198416 1797725 := bbase (se 3 (by rfl) ⟨337073, by rfl⟩ : syracuseStep 1797725 = 674147) (by norm_num)
theorem B1797749 : Blo 1198416 1797749 := bbase (se 5 (by rfl) ⟨84269, by rfl⟩ : syracuseStep 1797749 = 168539) (by norm_num)
theorem B1707637 : Blo 1198416 1707637 := bbase (se 5 (by rfl) ⟨80045, by rfl⟩ : syracuseStep 1707637 = 160091) (by norm_num)
theorem B1797773 : Blo 1198416 1797773 := bbase (se 3 (by rfl) ⟨337082, by rfl⟩ : syracuseStep 1797773 = 674165) (by norm_num)
theorem B2698901 : Blo 1198416 2698901 := bbase (se 6 (by rfl) ⟨63255, by rfl⟩ : syracuseStep 2698901 = 126511) (by norm_num)
theorem B1797797 : Blo 1198416 1797797 := bbase (se 4 (by rfl) ⟨168543, by rfl⟩ : syracuseStep 1797797 = 337087) (by norm_num)
theorem B1797821 : Blo 1198416 1797821 := bbase (se 3 (by rfl) ⟨337091, by rfl⟩ : syracuseStep 1797821 = 674183) (by norm_num)
theorem B4550357 : Blo 1198416 4550357 := bbase (se 7 (by rfl) ⟨53324, by rfl⟩ : syracuseStep 4550357 = 106649) (by norm_num)
theorem B1797845 : Blo 1198416 1797845 := bbase (se 7 (by rfl) ⟨21068, by rfl⟩ : syracuseStep 1797845 = 42137) (by norm_num)
theorem B1281749 : Blo 1198416 1281749 := bbase (se 7 (by rfl) ⟨15020, by rfl⟩ : syracuseStep 1281749 = 30041) (by norm_num)
theorem B2698973 : Blo 1198416 2698973 := bbase (se 3 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 2698973 = 1012115) (by norm_num)
theorem B1797869 : Blo 1198416 1797869 := bbase (se 3 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 1797869 = 674201) (by norm_num)
theorem B1797893 : Blo 1198416 1797893 := bbase (se 4 (by rfl) ⟨168552, by rfl⟩ : syracuseStep 1797893 = 337105) (by norm_num)
theorem B1797917 : Blo 1198416 1797917 := bbase (se 3 (by rfl) ⟨337109, by rfl⟩ : syracuseStep 1797917 = 674219) (by norm_num)
theorem B2699045 : Blo 1198416 2699045 := bbase (se 4 (by rfl) ⟨253035, by rfl⟩ : syracuseStep 2699045 = 506071) (by norm_num)
theorem B1797941 : Blo 1198416 1797941 := bbase (se 5 (by rfl) ⟨84278, by rfl⟩ : syracuseStep 1797941 = 168557) (by norm_num)
theorem B1232705 : Blo 1198416 1232705 := bbase (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) (by norm_num)
theorem B1797965 : Blo 1198416 1797965 := bbase (se 3 (by rfl) ⟨337118, by rfl⟩ : syracuseStep 1797965 = 674237) (by norm_num)
theorem B1797989 : Blo 1198416 1797989 := bbase (se 4 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 1797989 = 337123) (by norm_num)
theorem B2191213 : Blo 1198416 2191213 := bbase (se 3 (by rfl) ⟨410852, by rfl⟩ : syracuseStep 2191213 = 821705) (by norm_num)
theorem B2699117 : Blo 1198416 2699117 := bbase (se 3 (by rfl) ⟨506084, by rfl⟩ : syracuseStep 2699117 = 1012169) (by norm_num)
theorem B1798013 : Blo 1198416 1798013 := bbase (se 3 (by rfl) ⟨337127, by rfl⟩ : syracuseStep 1798013 = 674255) (by norm_num)
theorem B1822589 : Blo 1198416 1822589 := bbase (se 3 (by rfl) ⟨341735, by rfl⟩ : syracuseStep 1822589 = 683471) (by norm_num)
theorem B1798037 : Blo 1198416 1798037 := bbase (se 6 (by rfl) ⟨42141, by rfl⟩ : syracuseStep 1798037 = 84283) (by norm_num)
theorem B3035029 : Blo 1198416 3035029 := bbase (se 6 (by rfl) ⟨71133, by rfl⟩ : syracuseStep 3035029 = 142267) (by norm_num)
theorem B1216405 : Blo 1198416 1216405 := bbase (se 6 (by rfl) ⟨28509, by rfl⟩ : syracuseStep 1216405 = 57019) (by norm_num)
theorem B5124005 : Blo 1198416 5124005 := bbase (se 4 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 5124005 = 960751) (by norm_num)
theorem B3698597 : Blo 1198416 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B1798061 : Blo 1198416 1798061 := bbase (se 3 (by rfl) ⟨337136, by rfl⟩ : syracuseStep 1798061 = 674273) (by norm_num)
theorem B2699189 : Blo 1198416 2699189 := bbase (se 5 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 2699189 = 253049) (by norm_num)
theorem B1798085 : Blo 1198416 1798085 := bbase (se 4 (by rfl) ⟨168570, by rfl⟩ : syracuseStep 1798085 = 337141) (by norm_num)
theorem B2191301 : Blo 1198416 2191301 := bbase (se 4 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 2191301 = 410869) (by norm_num)
theorem B1798109 : Blo 1198416 1798109 := bbase (se 3 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 1798109 = 674291) (by norm_num)
theorem B4050917 : Blo 1198416 4050917 := bbase (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) (by norm_num)
theorem B1708013 : Blo 1198416 1708013 := bbase (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) (by norm_num)
theorem B1798133 : Blo 1198416 1798133 := bbase (se 5 (by rfl) ⟨84287, by rfl⟩ : syracuseStep 1798133 = 168575) (by norm_num)
theorem B2699261 : Blo 1198416 2699261 := bbase (se 3 (by rfl) ⟨506111, by rfl⟩ : syracuseStep 2699261 = 1012223) (by norm_num)
theorem B3035141 : Blo 1198416 3035141 := bbase (se 4 (by rfl) ⟨284544, by rfl⟩ : syracuseStep 3035141 = 569089) (by norm_num)
theorem B1798157 : Blo 1198416 1798157 := bbase (se 3 (by rfl) ⟨337154, by rfl⟩ : syracuseStep 1798157 = 674309) (by norm_num)
theorem B1798181 : Blo 1198416 1798181 := bbase (se 4 (by rfl) ⟨168579, by rfl⟩ : syracuseStep 1798181 = 337159) (by norm_num)
theorem B1798205 : Blo 1198416 1798205 := bbase (se 3 (by rfl) ⟨337163, by rfl⟩ : syracuseStep 1798205 = 674327) (by norm_num)
theorem B2699333 : Blo 1198416 2699333 := bbase (se 4 (by rfl) ⟨253062, by rfl⟩ : syracuseStep 2699333 = 506125) (by norm_num)
theorem B1798229 : Blo 1198416 1798229 := bbase (se 8 (by rfl) ⟨10536, by rfl⟩ : syracuseStep 1798229 = 21073) (by norm_num)
theorem B1798253 : Blo 1198416 1798253 := bbase (se 3 (by rfl) ⟨337172, by rfl⟩ : syracuseStep 1798253 = 674345) (by norm_num)
theorem B1798277 : Blo 1198416 1798277 := bbase (se 4 (by rfl) ⟨168588, by rfl⟩ : syracuseStep 1798277 = 337177) (by norm_num)
theorem B2699405 : Blo 1198416 2699405 := bbase (se 3 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 2699405 = 1012277) (by norm_num)
theorem B1798301 : Blo 1198416 1798301 := bbase (se 3 (by rfl) ⟨337181, by rfl⟩ : syracuseStep 1798301 = 674363) (by norm_num)
theorem B1798325 : Blo 1198416 1798325 := bbase (se 5 (by rfl) ⟨84296, by rfl⟩ : syracuseStep 1798325 = 168593) (by norm_num)
theorem B3035333 : Blo 1198416 3035333 := bbase (se 4 (by rfl) ⟨284562, by rfl⟩ : syracuseStep 3035333 = 569125) (by norm_num)
theorem B1798349 : Blo 1198416 1798349 := bbase (se 3 (by rfl) ⟨337190, by rfl⟩ : syracuseStep 1798349 = 674381) (by norm_num)
theorem B2699477 : Blo 1198416 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B1405153 : Blo 1198416 1405153 := bbase (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) (by norm_num)
theorem B1798373 : Blo 1198416 1798373 := bbase (se 4 (by rfl) ⟨168597, by rfl⟩ : syracuseStep 1798373 = 337195) (by norm_num)
theorem B1798397 : Blo 1198416 1798397 := bbase (se 3 (by rfl) ⟨337199, by rfl⟩ : syracuseStep 1798397 = 674399) (by norm_num)
theorem B1798421 : Blo 1198416 1798421 := bbase (se 6 (by rfl) ⟨42150, by rfl⟩ : syracuseStep 1798421 = 84301) (by norm_num)
theorem B2699549 : Blo 1198416 2699549 := bbase (se 3 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 2699549 = 1012331) (by norm_num)
theorem B1798445 : Blo 1198416 1798445 := bbase (se 3 (by rfl) ⟨337208, by rfl⟩ : syracuseStep 1798445 = 674417) (by norm_num)
theorem B2879813 : Blo 1198416 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B1798469 : Blo 1198416 1798469 := bbase (se 4 (by rfl) ⟨168606, by rfl⟩ : syracuseStep 1798469 = 337213) (by norm_num)
theorem B5763413 : Blo 1198416 5763413 := bbase (se 10 (by rfl) ⟨8442, by rfl⟩ : syracuseStep 5763413 = 16885) (by norm_num)
theorem B1798493 : Blo 1198416 1798493 := bbase (se 3 (by rfl) ⟨337217, by rfl⟩ : syracuseStep 1798493 = 674435) (by norm_num)
theorem B2699621 : Blo 1198416 2699621 := bbase (se 4 (by rfl) ⟨253089, by rfl⟩ : syracuseStep 2699621 = 506179) (by norm_num)
theorem B1798517 : Blo 1198416 1798517 := bbase (se 5 (by rfl) ⟨84305, by rfl⟩ : syracuseStep 1798517 = 168611) (by norm_num)
theorem B1798541 : Blo 1198416 1798541 := bbase (se 3 (by rfl) ⟨337226, by rfl⟩ : syracuseStep 1798541 = 674453) (by norm_num)
theorem B4051349 : Blo 1198416 4051349 := bbase (se 6 (by rfl) ⟨94953, by rfl⟩ : syracuseStep 4051349 = 189907) (by norm_num)
theorem B1798565 : Blo 1198416 1798565 := bbase (se 4 (by rfl) ⟨168615, by rfl⟩ : syracuseStep 1798565 = 337231) (by norm_num)
theorem B2699693 : Blo 1198416 2699693 := bbase (se 3 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 2699693 = 1012385) (by norm_num)
theorem B1798589 : Blo 1198416 1798589 := bbase (se 3 (by rfl) ⟨337235, by rfl⟩ : syracuseStep 1798589 = 674471) (by norm_num)
theorem B1921477 : Blo 1198416 1921477 := bbase (se 4 (by rfl) ⟨180138, by rfl⟩ : syracuseStep 1921477 = 360277) (by norm_num)
theorem B1798613 : Blo 1198416 1798613 := bbase (se 7 (by rfl) ⟨21077, by rfl⟩ : syracuseStep 1798613 = 42155) (by norm_num)
theorem B6074837 : Blo 1198416 6074837 := bbase (se 7 (by rfl) ⟨71189, by rfl⟩ : syracuseStep 6074837 = 142379) (by norm_num)
theorem B4321765 : Blo 1198416 4321765 := bbase (se 4 (by rfl) ⟨405165, by rfl⟩ : syracuseStep 4321765 = 810331) (by norm_num)
theorem B1798637 : Blo 1198416 1798637 := bbase (se 3 (by rfl) ⟨337244, by rfl⟩ : syracuseStep 1798637 = 674489) (by norm_num)
theorem B2699765 : Blo 1198416 2699765 := bbase (se 5 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 2699765 = 253103) (by norm_num)
theorem B1798661 : Blo 1198416 1798661 := bbase (se 4 (by rfl) ⟨168624, by rfl⟩ : syracuseStep 1798661 = 337249) (by norm_num)
theorem B1798685 : Blo 1198416 1798685 := bbase (se 3 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 1798685 = 674507) (by norm_num)
theorem B3035677 : Blo 1198416 3035677 := bbase (se 3 (by rfl) ⟨569189, by rfl⟩ : syracuseStep 3035677 = 1138379) (by norm_num)
theorem B1798709 : Blo 1198416 1798709 := bbase (se 5 (by rfl) ⟨84314, by rfl⟩ : syracuseStep 1798709 = 168629) (by norm_num)
theorem B2699837 : Blo 1198416 2699837 := bbase (se 3 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 2699837 = 1012439) (by norm_num)
theorem B1798733 : Blo 1198416 1798733 := bbase (se 3 (by rfl) ⟨337262, by rfl⟩ : syracuseStep 1798733 = 674525) (by norm_num)
theorem B1798757 : Blo 1198416 1798757 := bbase (se 4 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 1798757 = 337267) (by norm_num)
theorem B6156901 : Blo 1198416 6156901 := bbase (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) (by norm_num)
theorem B1798781 : Blo 1198416 1798781 := bbase (se 3 (by rfl) ⟨337271, by rfl⟩ : syracuseStep 1798781 = 674543) (by norm_num)
theorem B2699909 : Blo 1198416 2699909 := bbase (se 4 (by rfl) ⟨253116, by rfl⟩ : syracuseStep 2699909 = 506233) (by norm_num)
theorem B3035789 : Blo 1198416 3035789 := bbase (se 3 (by rfl) ⟨569210, by rfl⟩ : syracuseStep 3035789 = 1138421) (by norm_num)
theorem B1798805 : Blo 1198416 1798805 := bbase (se 6 (by rfl) ⟨42159, by rfl⟩ : syracuseStep 1798805 = 84319) (by norm_num)
theorem B1348249 : Blo 1198416 1348249 := bbase (se 2 (by rfl) ⟨505593, by rfl⟩ : syracuseStep 1348249 = 1011187) (by norm_num)
theorem B1798829 : Blo 1198416 1798829 := bbase (se 3 (by rfl) ⟨337280, by rfl⟩ : syracuseStep 1798829 = 674561) (by norm_num)
theorem B6828725 : Blo 1198416 6828725 := bbase (se 5 (by rfl) ⟨320096, by rfl⟩ : syracuseStep 6828725 = 640193) (by norm_num)
theorem B1348285 : Blo 1198416 1348285 := bbase (se 3 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 1348285 = 505607) (by norm_num)
theorem B1798853 : Blo 1198416 1798853 := bbase (se 4 (by rfl) ⟨168642, by rfl⟩ : syracuseStep 1798853 = 337285) (by norm_num)
theorem B1921733 : Blo 1198416 1921733 := bbase (se 4 (by rfl) ⟨180162, by rfl⟩ : syracuseStep 1921733 = 360325) (by norm_num)
theorem B2699981 : Blo 1198416 2699981 := bbase (se 3 (by rfl) ⟨506246, by rfl⟩ : syracuseStep 2699981 = 1012493) (by norm_num)
theorem B1798877 : Blo 1198416 1798877 := bbase (se 3 (by rfl) ⟨337289, by rfl⟩ : syracuseStep 1798877 = 674579) (by norm_num)
theorem B1348321 : Blo 1198416 1348321 := bbase (se 2 (by rfl) ⟨505620, by rfl⟩ : syracuseStep 1348321 = 1011241) (by norm_num)
theorem B2880245 : Blo 1198416 2880245 := bbase (se 5 (by rfl) ⟨135011, by rfl⟩ : syracuseStep 2880245 = 270023) (by norm_num)
theorem B1798901 : Blo 1198416 1798901 := bbase (se 5 (by rfl) ⟨84323, by rfl⟩ : syracuseStep 1798901 = 168647) (by norm_num)
theorem B1348357 : Blo 1198416 1348357 := bbase (se 4 (by rfl) ⟨126408, by rfl⟩ : syracuseStep 1348357 = 252817) (by norm_num)
theorem B1798925 : Blo 1198416 1798925 := bbase (se 3 (by rfl) ⟨337298, by rfl⟩ : syracuseStep 1798925 = 674597) (by norm_num)
theorem B2700053 : Blo 1198416 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B1798949 : Blo 1198416 1798949 := bbase (se 4 (by rfl) ⟨168651, by rfl⟩ : syracuseStep 1798949 = 337303) (by norm_num)
theorem B1348393 : Blo 1198416 1348393 := bbase (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) (by norm_num)
theorem B1798973 : Blo 1198416 1798973 := bbase (se 3 (by rfl) ⟨337307, by rfl⟩ : syracuseStep 1798973 = 674615) (by norm_num)
theorem B1348429 : Blo 1198416 1348429 := bbase (se 3 (by rfl) ⟨252830, by rfl⟩ : syracuseStep 1348429 = 505661) (by norm_num)
theorem B3035981 : Blo 1198416 3035981 := bbase (se 3 (by rfl) ⟨569246, by rfl⟩ : syracuseStep 3035981 = 1138493) (by norm_num)
theorem B1798997 : Blo 1198416 1798997 := bbase (se 9 (by rfl) ⟨5270, by rfl⟩ : syracuseStep 1798997 = 10541) (by norm_num)
theorem B2700125 : Blo 1198416 2700125 := bbase (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) (by norm_num)
theorem B1799021 : Blo 1198416 1799021 := bbase (se 3 (by rfl) ⟨337316, by rfl⟩ : syracuseStep 1799021 = 674633) (by norm_num)
theorem B1348465 : Blo 1198416 1348465 := bbase (se 2 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 1348465 = 1011349) (by norm_num)
theorem B6067061 : Blo 1198416 6067061 := bbase (se 5 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 6067061 = 568787) (by norm_num)
theorem B1799045 : Blo 1198416 1799045 := bbase (se 4 (by rfl) ⟨168660, by rfl⟩ : syracuseStep 1799045 = 337321) (by norm_num)
theorem B1921925 : Blo 1198416 1921925 := bbase (se 4 (by rfl) ⟨180180, by rfl⟩ : syracuseStep 1921925 = 360361) (by norm_num)
theorem B2560909 : Blo 1198416 2560909 := bbase (se 3 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 2560909 = 960341) (by norm_num)
theorem B1823629 : Blo 1198416 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B1299341 : Blo 1198416 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B1348501 : Blo 1198416 1348501 := bbase (se 6 (by rfl) ⟨31605, by rfl⟩ : syracuseStep 1348501 = 63211) (by norm_num)
theorem B1799069 : Blo 1198416 1799069 := bbase (se 3 (by rfl) ⟨337325, by rfl⟩ : syracuseStep 1799069 = 674651) (by norm_num)
theorem B2700197 : Blo 1198416 2700197 := bbase (se 4 (by rfl) ⟨253143, by rfl⟩ : syracuseStep 2700197 = 506287) (by norm_num)
theorem B10941365 : Blo 1198416 10941365 := bbase (se 5 (by rfl) ⟨512876, by rfl⟩ : syracuseStep 10941365 = 1025753) (by norm_num)
theorem B1799093 : Blo 1198416 1799093 := bbase (se 5 (by rfl) ⟨84332, by rfl⟩ : syracuseStep 1799093 = 168665) (by norm_num)
theorem B1348537 : Blo 1198416 1348537 := bbase (se 2 (by rfl) ⟨505701, by rfl⟩ : syracuseStep 1348537 = 1011403) (by norm_num)
theorem B1799117 : Blo 1198416 1799117 := bbase (se 3 (by rfl) ⟨337334, by rfl⟩ : syracuseStep 1799117 = 674669) (by norm_num)
theorem B1348573 : Blo 1198416 1348573 := bbase (se 3 (by rfl) ⟨252857, by rfl⟩ : syracuseStep 1348573 = 505715) (by norm_num)
theorem B1799141 : Blo 1198416 1799141 := bbase (se 4 (by rfl) ⟨168669, by rfl⟩ : syracuseStep 1799141 = 337339) (by norm_num)
theorem B2700269 : Blo 1198416 2700269 := bbase (se 3 (by rfl) ⟨506300, by rfl⟩ : syracuseStep 2700269 = 1012601) (by norm_num)
theorem B1799165 : Blo 1198416 1799165 := bbase (se 3 (by rfl) ⟨337343, by rfl⟩ : syracuseStep 1799165 = 674687) (by norm_num)
theorem B1348609 : Blo 1198416 1348609 := bbase (se 2 (by rfl) ⟨505728, by rfl⟩ : syracuseStep 1348609 = 1011457) (by norm_num)
theorem B1799189 : Blo 1198416 1799189 := bbase (se 6 (by rfl) ⟨42168, by rfl⟩ : syracuseStep 1799189 = 84337) (by norm_num)
theorem B1348645 : Blo 1198416 1348645 := bbase (se 4 (by rfl) ⟨126435, by rfl⟩ : syracuseStep 1348645 = 252871) (by norm_num)
theorem B1799213 : Blo 1198416 1799213 := bbase (se 3 (by rfl) ⟨337352, by rfl⟩ : syracuseStep 1799213 = 674705) (by norm_num)
theorem B2700341 : Blo 1198416 2700341 := bbase (se 5 (by rfl) ⟨126578, by rfl⟩ : syracuseStep 2700341 = 253157) (by norm_num)
theorem B1799237 : Blo 1198416 1799237 := bbase (se 4 (by rfl) ⟨168678, by rfl⟩ : syracuseStep 1799237 = 337357) (by norm_num)
theorem B1348681 : Blo 1198416 1348681 := bbase (se 2 (by rfl) ⟨505755, by rfl⟩ : syracuseStep 1348681 = 1011511) (by norm_num)
theorem B6157397 : Blo 1198416 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1799261 : Blo 1198416 1799261 := bbase (se 3 (by rfl) ⟨337361, by rfl⟩ : syracuseStep 1799261 = 674723) (by norm_num)
theorem B1348717 : Blo 1198416 1348717 := bbase (se 3 (by rfl) ⟨252884, by rfl⟩ : syracuseStep 1348717 = 505769) (by norm_num)
theorem B1799285 : Blo 1198416 1799285 := bbase (se 5 (by rfl) ⟨84341, by rfl⟩ : syracuseStep 1799285 = 168683) (by norm_num)
theorem B4502645 : Blo 1198416 4502645 := bbase (se 5 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 4502645 = 422123) (by norm_num)
theorem B2700413 : Blo 1198416 2700413 := bbase (se 3 (by rfl) ⟨506327, by rfl⟩ : syracuseStep 2700413 = 1012655) (by norm_num)
theorem B1799309 : Blo 1198416 1799309 := bbase (se 3 (by rfl) ⟨337370, by rfl⟩ : syracuseStep 1799309 = 674741) (by norm_num)
theorem B1348753 : Blo 1198416 1348753 := bbase (se 2 (by rfl) ⟨505782, by rfl⟩ : syracuseStep 1348753 = 1011565) (by norm_num)
theorem B3036325 : Blo 1198416 3036325 := bbase (se 4 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 3036325 = 569311) (by norm_num)
theorem B1799333 : Blo 1198416 1799333 := bbase (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) (by norm_num)
theorem B1348789 : Blo 1198416 1348789 := bbase (se 5 (by rfl) ⟨63224, by rfl⟩ : syracuseStep 1348789 = 126449) (by norm_num)
theorem B1799357 : Blo 1198416 1799357 := bbase (se 3 (by rfl) ⟨337379, by rfl⟩ : syracuseStep 1799357 = 674759) (by norm_num)
theorem B2700485 : Blo 1198416 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B1799381 : Blo 1198416 1799381 := bbase (se 7 (by rfl) ⟨21086, by rfl⟩ : syracuseStep 1799381 = 42173) (by norm_num)
theorem B1348825 : Blo 1198416 1348825 := bbase (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) (by norm_num)
theorem B1799405 : Blo 1198416 1799405 := bbase (se 3 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 1799405 = 674777) (by norm_num)
theorem B1348861 : Blo 1198416 1348861 := bbase (se 3 (by rfl) ⟨252911, by rfl⟩ : syracuseStep 1348861 = 505823) (by norm_num)
theorem B1799429 : Blo 1198416 1799429 := bbase (se 4 (by rfl) ⟨168696, by rfl⟩ : syracuseStep 1799429 = 337393) (by norm_num)
theorem B2700557 : Blo 1198416 2700557 := bbase (se 3 (by rfl) ⟨506354, by rfl⟩ : syracuseStep 2700557 = 1012709) (by norm_num)
theorem B3413269 : Blo 1198416 3413269 := bbase (se 6 (by rfl) ⟨79998, by rfl⟩ : syracuseStep 3413269 = 159997) (by norm_num)
theorem B3036437 : Blo 1198416 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B1799453 : Blo 1198416 1799453 := bbase (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) (by norm_num)
theorem B1348897 : Blo 1198416 1348897 := bbase (se 2 (by rfl) ⟨505836, by rfl⟩ : syracuseStep 1348897 = 1011673) (by norm_num)
theorem B1799477 : Blo 1198416 1799477 := bbase (se 5 (by rfl) ⟨84350, by rfl⟩ : syracuseStep 1799477 = 168701) (by norm_num)
theorem B1348933 : Blo 1198416 1348933 := bbase (se 4 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 1348933 = 252925) (by norm_num)
theorem B1799501 : Blo 1198416 1799501 := bbase (se 3 (by rfl) ⟨337406, by rfl⟩ : syracuseStep 1799501 = 674813) (by norm_num)
theorem B2700629 : Blo 1198416 2700629 := bbase (se 13 (by rfl) ⟨494, by rfl⟩ : syracuseStep 2700629 = 989) (by norm_num)
theorem B1799525 : Blo 1198416 1799525 := bbase (se 4 (by rfl) ⟨168705, by rfl⟩ : syracuseStep 1799525 = 337411) (by norm_num)
theorem B1348969 : Blo 1198416 1348969 := bbase (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) (by norm_num)
theorem B1799549 : Blo 1198416 1799549 := bbase (se 3 (by rfl) ⟨337415, by rfl⟩ : syracuseStep 1799549 = 674831) (by norm_num)
theorem B1349005 : Blo 1198416 1349005 := bbase (se 3 (by rfl) ⟨252938, by rfl⟩ : syracuseStep 1349005 = 505877) (by norm_num)
theorem B1799573 : Blo 1198416 1799573 := bbase (se 6 (by rfl) ⟨42177, by rfl⟩ : syracuseStep 1799573 = 84355) (by norm_num)
theorem B2700701 : Blo 1198416 2700701 := bbase (se 3 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 2700701 = 1012763) (by norm_num)
theorem B1799597 : Blo 1198416 1799597 := bbase (se 3 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 1799597 = 674849) (by norm_num)
theorem B1349041 : Blo 1198416 1349041 := bbase (se 2 (by rfl) ⟨505890, by rfl⟩ : syracuseStep 1349041 = 1011781) (by norm_num)
theorem B8648117 : Blo 1198416 8648117 := bbase (se 5 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 8648117 = 810761) (by norm_num)
theorem B10253749 : Blo 1198416 10253749 := bbase (se 5 (by rfl) ⟨480644, by rfl⟩ : syracuseStep 10253749 = 961289) (by norm_num)
theorem B1799621 : Blo 1198416 1799621 := bbase (se 4 (by rfl) ⟨168714, by rfl⟩ : syracuseStep 1799621 = 337429) (by norm_num)
theorem B1349077 : Blo 1198416 1349077 := bbase (se 7 (by rfl) ⟨15809, by rfl⟩ : syracuseStep 1349077 = 31619) (by norm_num)
theorem B3036629 : Blo 1198416 3036629 := bbase (se 7 (by rfl) ⟨35585, by rfl⟩ : syracuseStep 3036629 = 71171) (by norm_num)
theorem B1799645 : Blo 1198416 1799645 := bbase (se 3 (by rfl) ⟨337433, by rfl⟩ : syracuseStep 1799645 = 674867) (by norm_num)
theorem B2700773 : Blo 1198416 2700773 := bbase (se 4 (by rfl) ⟨253197, by rfl⟩ : syracuseStep 2700773 = 506395) (by norm_num)
theorem B1799669 : Blo 1198416 1799669 := bbase (se 5 (by rfl) ⟨84359, by rfl⟩ : syracuseStep 1799669 = 168719) (by norm_num)
theorem B1349113 : Blo 1198416 1349113 := bbase (se 2 (by rfl) ⟨505917, by rfl⟩ : syracuseStep 1349113 = 1011835) (by norm_num)
theorem B1799693 : Blo 1198416 1799693 := bbase (se 3 (by rfl) ⟨337442, by rfl⟩ : syracuseStep 1799693 = 674885) (by norm_num)
theorem B1349149 : Blo 1198416 1349149 := bbase (se 3 (by rfl) ⟨252965, by rfl⟩ : syracuseStep 1349149 = 505931) (by norm_num)
theorem B1799717 : Blo 1198416 1799717 := bbase (se 4 (by rfl) ⟨168723, by rfl⟩ : syracuseStep 1799717 = 337447) (by norm_num)
theorem B2700845 : Blo 1198416 2700845 := bbase (se 3 (by rfl) ⟨506408, by rfl⟩ : syracuseStep 2700845 = 1012817) (by norm_num)
theorem B1799741 : Blo 1198416 1799741 := bbase (se 3 (by rfl) ⟨337451, by rfl⟩ : syracuseStep 1799741 = 674903) (by norm_num)
theorem B1349185 : Blo 1198416 1349185 := bbase (se 2 (by rfl) ⟨505944, by rfl⟩ : syracuseStep 1349185 = 1011889) (by norm_num)
theorem B3241541 : Blo 1198416 3241541 := bbase (se 4 (by rfl) ⟨303894, by rfl⟩ : syracuseStep 3241541 = 607789) (by norm_num)
theorem B1799765 : Blo 1198416 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B2430557 : Blo 1198416 2430557 := bbase (se 3 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 2430557 = 911459) (by norm_num)
theorem B1349221 : Blo 1198416 1349221 := bbase (se 4 (by rfl) ⟨126489, by rfl⟩ : syracuseStep 1349221 = 252979) (by norm_num)
theorem B1799789 : Blo 1198416 1799789 := bbase (se 3 (by rfl) ⟨337460, by rfl⟩ : syracuseStep 1799789 = 674921) (by norm_num)
theorem B2700917 : Blo 1198416 2700917 := bbase (se 5 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 2700917 = 253211) (by norm_num)
theorem B1799813 : Blo 1198416 1799813 := bbase (se 4 (by rfl) ⟨168732, by rfl⟩ : syracuseStep 1799813 = 337465) (by norm_num)
theorem B1349257 : Blo 1198416 1349257 := bbase (se 2 (by rfl) ⟨505971, by rfl⟩ : syracuseStep 1349257 = 1011943) (by norm_num)
theorem B5125781 : Blo 1198416 5125781 := bbase (se 6 (by rfl) ⟨120135, by rfl⟩ : syracuseStep 5125781 = 240271) (by norm_num)
theorem B1799837 : Blo 1198416 1799837 := bbase (se 3 (by rfl) ⟨337469, by rfl⟩ : syracuseStep 1799837 = 674939) (by norm_num)
theorem B1349293 : Blo 1198416 1349293 := bbase (se 3 (by rfl) ⟨252992, by rfl⟩ : syracuseStep 1349293 = 505985) (by norm_num)
theorem B1799861 : Blo 1198416 1799861 := bbase (se 5 (by rfl) ⟨84368, by rfl⟩ : syracuseStep 1799861 = 168737) (by norm_num)
theorem B1799885 : Blo 1198416 1799885 := bbase (se 3 (by rfl) ⟨337478, by rfl⟩ : syracuseStep 1799885 = 674957) (by norm_num)
theorem B1349329 : Blo 1198416 1349329 := bbase (se 2 (by rfl) ⟨505998, by rfl⟩ : syracuseStep 1349329 = 1011997) (by norm_num)
theorem B1799909 : Blo 1198416 1799909 := bbase (se 4 (by rfl) ⟨168741, by rfl⟩ : syracuseStep 1799909 = 337483) (by norm_num)
theorem B6076133 : Blo 1198416 6076133 := bbase (se 4 (by rfl) ⟨569637, by rfl⟩ : syracuseStep 6076133 = 1139275) (by norm_num)
theorem B1349365 : Blo 1198416 1349365 := bbase (se 5 (by rfl) ⟨63251, by rfl⟩ : syracuseStep 1349365 = 126503) (by norm_num)
theorem B1799933 : Blo 1198416 1799933 := bbase (se 3 (by rfl) ⟨337487, by rfl⟩ : syracuseStep 1799933 = 674975) (by norm_num)
theorem B2561797 : Blo 1198416 2561797 := bbase (se 4 (by rfl) ⟨240168, by rfl⟩ : syracuseStep 2561797 = 480337) (by norm_num)
theorem B4552469 : Blo 1198416 4552469 := bbase (se 6 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 4552469 = 213397) (by norm_num)
theorem B1799957 : Blo 1198416 1799957 := bbase (se 6 (by rfl) ⟨42186, by rfl⟩ : syracuseStep 1799957 = 84373) (by norm_num)
theorem B1349401 : Blo 1198416 1349401 := bbase (se 2 (by rfl) ⟨506025, by rfl⟩ : syracuseStep 1349401 = 1012051) (by norm_num)
theorem B3036973 : Blo 1198416 3036973 := bbase (se 3 (by rfl) ⟨569432, by rfl⟩ : syracuseStep 3036973 = 1138865) (by norm_num)
theorem B1799981 : Blo 1198416 1799981 := bbase (se 3 (by rfl) ⟨337496, by rfl⟩ : syracuseStep 1799981 = 674993) (by norm_num)
theorem B1349437 : Blo 1198416 1349437 := bbase (se 3 (by rfl) ⟨253019, by rfl⟩ : syracuseStep 1349437 = 506039) (by norm_num)
theorem B2275141 : Blo 1198416 2275141 := bbase (se 4 (by rfl) ⟨213294, by rfl⟩ : syracuseStep 2275141 = 426589) (by norm_num)
theorem B1800005 : Blo 1198416 1800005 := bbase (se 4 (by rfl) ⟨168750, by rfl⟩ : syracuseStep 1800005 = 337501) (by norm_num)
theorem B1800029 : Blo 1198416 1800029 := bbase (se 3 (by rfl) ⟨337505, by rfl⟩ : syracuseStep 1800029 = 675011) (by norm_num)
theorem B1349473 : Blo 1198416 1349473 := bbase (se 2 (by rfl) ⟨506052, by rfl⟩ : syracuseStep 1349473 = 1012105) (by norm_num)
theorem B1800053 : Blo 1198416 1800053 := bbase (se 5 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 1800053 = 168755) (by norm_num)
theorem B1349509 : Blo 1198416 1349509 := bbase (se 4 (by rfl) ⟨126516, by rfl⟩ : syracuseStep 1349509 = 253033) (by norm_num)
theorem B1800077 : Blo 1198416 1800077 := bbase (se 3 (by rfl) ⟨337514, by rfl⟩ : syracuseStep 1800077 = 675029) (by norm_num)
theorem B3037085 : Blo 1198416 3037085 := bbase (se 3 (by rfl) ⟨569453, by rfl⟩ : syracuseStep 3037085 = 1138907) (by norm_num)
theorem B4437925 : Blo 1198416 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B1800101 : Blo 1198416 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B1349545 : Blo 1198416 1349545 := bbase (se 2 (by rfl) ⟨506079, by rfl⟩ : syracuseStep 1349545 = 1012159) (by norm_num)
theorem B1800125 : Blo 1198416 1800125 := bbase (se 3 (by rfl) ⟨337523, by rfl⟩ : syracuseStep 1800125 = 675047) (by norm_num)
theorem B1349581 : Blo 1198416 1349581 := bbase (se 3 (by rfl) ⟨253046, by rfl⟩ : syracuseStep 1349581 = 506093) (by norm_num)
theorem B2275285 : Blo 1198416 2275285 := bbase (se 7 (by rfl) ⟨26663, by rfl⟩ : syracuseStep 2275285 = 53327) (by norm_num)
theorem B1800149 : Blo 1198416 1800149 := bbase (se 7 (by rfl) ⟨21095, by rfl⟩ : syracuseStep 1800149 = 42191) (by norm_num)
theorem B1800173 : Blo 1198416 1800173 := bbase (se 3 (by rfl) ⟨337532, by rfl⟩ : syracuseStep 1800173 = 675065) (by norm_num)
theorem B1349617 : Blo 1198416 1349617 := bbase (se 2 (by rfl) ⟨506106, by rfl⟩ : syracuseStep 1349617 = 1012213) (by norm_num)
theorem B1800197 : Blo 1198416 1800197 := bbase (se 4 (by rfl) ⟨168768, by rfl⟩ : syracuseStep 1800197 = 337537) (by norm_num)
theorem B2308117 : Blo 1198416 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B1349653 : Blo 1198416 1349653 := bbase (se 6 (by rfl) ⟨31632, by rfl⟩ : syracuseStep 1349653 = 63265) (by norm_num)
theorem B1800221 : Blo 1198416 1800221 := bbase (se 3 (by rfl) ⟨337541, by rfl⟩ : syracuseStep 1800221 = 675083) (by norm_num)
theorem B2922533 : Blo 1198416 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B4552757 : Blo 1198416 4552757 := bbase (se 5 (by rfl) ⟨213410, by rfl⟩ : syracuseStep 4552757 = 426821) (by norm_num)
theorem B1800245 : Blo 1198416 1800245 := bbase (se 5 (by rfl) ⟨84386, by rfl⟩ : syracuseStep 1800245 = 168773) (by norm_num)
theorem B1349689 : Blo 1198416 1349689 := bbase (se 2 (by rfl) ⟨506133, by rfl⟩ : syracuseStep 1349689 = 1012267) (by norm_num)
theorem B4044869 : Blo 1198416 4044869 := bbase (se 4 (by rfl) ⟨379206, by rfl⟩ : syracuseStep 4044869 = 758413) (by norm_num)
theorem B2734157 : Blo 1198416 2734157 := bbase (se 3 (by rfl) ⟨512654, by rfl⟩ : syracuseStep 2734157 = 1025309) (by norm_num)
theorem B1800269 : Blo 1198416 1800269 := bbase (se 3 (by rfl) ⟨337550, by rfl⟩ : syracuseStep 1800269 = 675101) (by norm_num)
theorem B21878869 : Blo 1198416 21878869 := bbase (se 8 (by rfl) ⟨128196, by rfl⟩ : syracuseStep 21878869 = 256393) (by norm_num)
theorem B1349725 : Blo 1198416 1349725 := bbase (se 3 (by rfl) ⟨253073, by rfl⟩ : syracuseStep 1349725 = 506147) (by norm_num)
theorem B3037277 : Blo 1198416 3037277 := bbase (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) (by norm_num)
theorem B1800293 : Blo 1198416 1800293 := bbase (se 4 (by rfl) ⟨168777, by rfl⟩ : syracuseStep 1800293 = 337555) (by norm_num)
theorem B2275445 : Blo 1198416 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B1800317 : Blo 1198416 1800317 := bbase (se 3 (by rfl) ⟨337559, by rfl⟩ : syracuseStep 1800317 = 675119) (by norm_num)
theorem B1349761 : Blo 1198416 1349761 := bbase (se 2 (by rfl) ⟨506160, by rfl⟩ : syracuseStep 1349761 = 1012321) (by norm_num)
theorem B6068357 : Blo 1198416 6068357 := bbase (se 4 (by rfl) ⟨568908, by rfl⟩ : syracuseStep 6068357 = 1137817) (by norm_num)
theorem B1800341 : Blo 1198416 1800341 := bbase (se 6 (by rfl) ⟨42195, by rfl⟩ : syracuseStep 1800341 = 84391) (by norm_num)
theorem B1349797 : Blo 1198416 1349797 := bbase (se 4 (by rfl) ⟨126543, by rfl⟩ : syracuseStep 1349797 = 253087) (by norm_num)
theorem B1800365 : Blo 1198416 1800365 := bbase (se 3 (by rfl) ⟨337568, by rfl⟩ : syracuseStep 1800365 = 675137) (by norm_num)
theorem B1800389 : Blo 1198416 1800389 := bbase (se 4 (by rfl) ⟨168786, by rfl⟩ : syracuseStep 1800389 = 337573) (by norm_num)
theorem B1349833 : Blo 1198416 1349833 := bbase (se 2 (by rfl) ⟨506187, by rfl⟩ : syracuseStep 1349833 = 1012375) (by norm_num)
theorem B1800413 : Blo 1198416 1800413 := bbase (se 3 (by rfl) ⟨337577, by rfl⟩ : syracuseStep 1800413 = 675155) (by norm_num)
theorem B1349869 : Blo 1198416 1349869 := bbase (se 3 (by rfl) ⟨253100, by rfl⟩ : syracuseStep 1349869 = 506201) (by norm_num)
theorem B2562293 : Blo 1198416 2562293 := bbase (se 5 (by rfl) ⟨120107, by rfl⟩ : syracuseStep 2562293 = 240215) (by norm_num)
theorem B1800437 : Blo 1198416 1800437 := bbase (se 5 (by rfl) ⟨84395, by rfl⟩ : syracuseStep 1800437 = 168791) (by norm_num)
theorem B2275589 : Blo 1198416 2275589 := bbase (se 4 (by rfl) ⟨213336, by rfl⟩ : syracuseStep 2275589 = 426673) (by norm_num)
theorem B1800461 : Blo 1198416 1800461 := bbase (se 3 (by rfl) ⟨337586, by rfl⟩ : syracuseStep 1800461 = 675173) (by norm_num)
theorem B1349905 : Blo 1198416 1349905 := bbase (se 2 (by rfl) ⟨506214, by rfl⟩ : syracuseStep 1349905 = 1012429) (by norm_num)
theorem B1800485 : Blo 1198416 1800485 := bbase (se 4 (by rfl) ⟨168795, by rfl⟩ : syracuseStep 1800485 = 337591) (by norm_num)
theorem B1349941 : Blo 1198416 1349941 := bbase (se 5 (by rfl) ⟨63278, by rfl⟩ : syracuseStep 1349941 = 126557) (by norm_num)
theorem B1800509 : Blo 1198416 1800509 := bbase (se 3 (by rfl) ⟨337595, by rfl⟩ : syracuseStep 1800509 = 675191) (by norm_num)
theorem B41564501 : Blo 1198416 41564501 := bbase (se 10 (by rfl) ⟨60885, by rfl⟩ : syracuseStep 41564501 = 121771) (by norm_num)
theorem B1800533 : Blo 1198416 1800533 := bbase (se 10 (by rfl) ⟨2637, by rfl⟩ : syracuseStep 1800533 = 5275) (by norm_num)
theorem B1349977 : Blo 1198416 1349977 := bbase (se 2 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 1349977 = 1012483) (by norm_num)
theorem B1800557 : Blo 1198416 1800557 := bbase (se 3 (by rfl) ⟨337604, by rfl⟩ : syracuseStep 1800557 = 675209) (by norm_num)
theorem B1350013 : Blo 1198416 1350013 := bbase (se 3 (by rfl) ⟨253127, by rfl⟩ : syracuseStep 1350013 = 506255) (by norm_num)
theorem B2734469 : Blo 1198416 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B1800581 : Blo 1198416 1800581 := bbase (se 4 (by rfl) ⟨168804, by rfl⟩ : syracuseStep 1800581 = 337609) (by norm_num)
theorem B1440137 : Blo 1198416 1440137 := bbase (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) (by norm_num)
theorem B1948045 : Blo 1198416 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B1800605 : Blo 1198416 1800605 := bbase (se 3 (by rfl) ⟨337613, by rfl⟩ : syracuseStep 1800605 = 675227) (by norm_num)
theorem B1350049 : Blo 1198416 1350049 := bbase (se 2 (by rfl) ⟨506268, by rfl⟩ : syracuseStep 1350049 = 1012537) (by norm_num)
theorem B3037621 : Blo 1198416 3037621 := bbase (se 5 (by rfl) ⟨142388, by rfl⟩ : syracuseStep 3037621 = 284777) (by norm_num)
theorem B1440185 : Blo 1198416 1440185 := bbase (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) (by norm_num)
theorem B1350085 : Blo 1198416 1350085 := bbase (se 4 (by rfl) ⟨126570, by rfl⟩ : syracuseStep 1350085 = 253141) (by norm_num)
theorem B1350121 : Blo 1198416 1350121 := bbase (se 2 (by rfl) ⟨506295, by rfl⟩ : syracuseStep 1350121 = 1012591) (by norm_num)
theorem B4045301 : Blo 1198416 4045301 := bbase (se 5 (by rfl) ⟨189623, by rfl⟩ : syracuseStep 4045301 = 379247) (by norm_num)
theorem B1350157 : Blo 1198416 1350157 := bbase (se 3 (by rfl) ⟨253154, by rfl⟩ : syracuseStep 1350157 = 506309) (by norm_num)
theorem B1440281 : Blo 1198416 1440281 := bbase (se 2 (by rfl) ⟨540105, by rfl⟩ : syracuseStep 1440281 = 1080211) (by norm_num)
theorem B2275877 : Blo 1198416 2275877 := bbase (se 4 (by rfl) ⟨213363, by rfl⟩ : syracuseStep 2275877 = 426727) (by norm_num)
theorem B3037733 : Blo 1198416 3037733 := bbase (se 4 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 3037733 = 569575) (by norm_num)
theorem B1350193 : Blo 1198416 1350193 := bbase (se 2 (by rfl) ⟨506322, by rfl⟩ : syracuseStep 1350193 = 1012645) (by norm_num)
theorem B1350229 : Blo 1198416 1350229 := bbase (se 8 (by rfl) ⟨7911, by rfl⟩ : syracuseStep 1350229 = 15823) (by norm_num)
theorem B5126773 : Blo 1198416 5126773 := bbase (se 5 (by rfl) ⟨240317, by rfl⟩ : syracuseStep 5126773 = 480635) (by norm_num)
theorem B1350265 : Blo 1198416 1350265 := bbase (se 2 (by rfl) ⟨506349, by rfl⟩ : syracuseStep 1350265 = 1012699) (by norm_num)
theorem B1538713 : Blo 1198416 1538713 := bbase (se 2 (by rfl) ⟨577017, by rfl⟩ : syracuseStep 1538713 = 1154035) (by norm_num)
theorem B1350301 : Blo 1198416 1350301 := bbase (se 3 (by rfl) ⟨253181, by rfl⟩ : syracuseStep 1350301 = 506363) (by norm_num)
theorem B5765813 : Blo 1198416 5765813 := bbase (se 5 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 5765813 = 540545) (by norm_num)
theorem B2276029 : Blo 1198416 2276029 := bbase (se 3 (by rfl) ⟨426755, by rfl⟩ : syracuseStep 2276029 = 853511) (by norm_num)
theorem B1440445 : Blo 1198416 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B1350337 : Blo 1198416 1350337 := bbase (se 2 (by rfl) ⟨506376, by rfl⟩ : syracuseStep 1350337 = 1012753) (by norm_num)
theorem B3037925 : Blo 1198416 3037925 := bbase (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) (by norm_num)
theorem B1350373 : Blo 1198416 1350373 := bbase (se 4 (by rfl) ⟨126597, by rfl⟩ : syracuseStep 1350373 = 253195) (by norm_num)
theorem B3414773 : Blo 1198416 3414773 := bbase (se 5 (by rfl) ⟨160067, by rfl⟩ : syracuseStep 3414773 = 320135) (by norm_num)
theorem B1366777 : Blo 1198416 1366777 := bbase (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) (by norm_num)
theorem B1350409 : Blo 1198416 1350409 := bbase (se 2 (by rfl) ⟨506403, by rfl⟩ : syracuseStep 1350409 = 1012807) (by norm_num)
theorem B1350445 : Blo 1198416 1350445 := bbase (se 3 (by rfl) ⟨253208, by rfl⟩ : syracuseStep 1350445 = 506417) (by norm_num)
theorem B1440661 : Blo 1198416 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B4045733 : Blo 1198416 4045733 := bbase (se 4 (by rfl) ⟨379287, by rfl⟩ : syracuseStep 4045733 = 758575) (by norm_num)
theorem B1620901 : Blo 1198416 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B3079109 : Blo 1198416 3079109 := bbase (se 4 (by rfl) ⟨288666, by rfl⟩ : syracuseStep 3079109 = 577333) (by norm_num)
theorem B2276333 : Blo 1198416 2276333 := bbase (se 3 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 2276333 = 853625) (by norm_num)
theorem B2022421 : Blo 1198416 2022421 := bbase (se 6 (by rfl) ⟨47400, by rfl⟩ : syracuseStep 2022421 = 94801) (by norm_num)
theorem B1440829 : Blo 1198416 1440829 := bbase (se 3 (by rfl) ⟨270155, by rfl⟩ : syracuseStep 1440829 = 540311) (by norm_num)
theorem B3038269 : Blo 1198416 3038269 := bbase (se 3 (by rfl) ⟨569675, by rfl⟩ : syracuseStep 3038269 = 1139351) (by norm_num)
theorem B2563157 : Blo 1198416 2563157 := bbase (se 8 (by rfl) ⟨15018, by rfl⟩ : syracuseStep 2563157 = 30037) (by norm_num)
theorem B2022509 : Blo 1198416 2022509 := bbase (se 3 (by rfl) ⟨379220, by rfl⟩ : syracuseStep 2022509 = 758441) (by norm_num)
theorem B3038381 : Blo 1198416 3038381 := bbase (se 3 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 3038381 = 1139393) (by norm_num)
theorem B1621181 : Blo 1198416 1621181 := bbase (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) (by norm_num)
theorem B4553941 : Blo 1198416 4553941 := bbase (se 7 (by rfl) ⟨53366, by rfl⟩ : syracuseStep 4553941 = 106733) (by norm_num)
theorem B2563301 : Blo 1198416 2563301 := bbase (se 4 (by rfl) ⟨240309, by rfl⟩ : syracuseStep 2563301 = 480619) (by norm_num)
theorem B2022637 : Blo 1198416 2022637 := bbase (se 3 (by rfl) ⟨379244, by rfl⟩ : syracuseStep 2022637 = 758489) (by norm_num)
theorem B2022725 : Blo 1198416 2022725 := bbase (se 4 (by rfl) ⟨189630, by rfl⟩ : syracuseStep 2022725 = 379261) (by norm_num)
theorem B6479189 : Blo 1198416 6479189 := bbase (se 11 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 6479189 = 9491) (by norm_num)
theorem B4046165 : Blo 1198416 4046165 := bbase (se 11 (by rfl) ⟨2963, by rfl⟩ : syracuseStep 4046165 = 5927) (by norm_num)
theorem B2465149 : Blo 1198416 2465149 := bbase (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) (by norm_num)
theorem B6069653 : Blo 1198416 6069653 := bbase (se 6 (by rfl) ⟨142257, by rfl⟩ : syracuseStep 6069653 = 284515) (by norm_num)
theorem B2735525 : Blo 1198416 2735525 := bbase (se 4 (by rfl) ⟨256455, by rfl⟩ : syracuseStep 2735525 = 512911) (by norm_num)
theorem B2022853 : Blo 1198416 2022853 := bbase (se 4 (by rfl) ⟨189642, by rfl⟩ : syracuseStep 2022853 = 379285) (by norm_num)
theorem B4554245 : Blo 1198416 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B2022941 : Blo 1198416 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B1367617 : Blo 1198416 1367617 := bbase (se 2 (by rfl) ⟨512856, by rfl⟩ : syracuseStep 1367617 = 1025713) (by norm_num)
theorem B1441357 : Blo 1198416 1441357 := bbase (se 3 (by rfl) ⟨270254, by rfl⟩ : syracuseStep 1441357 = 540509) (by norm_num)
theorem B2252405 : Blo 1198416 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1367689 : Blo 1198416 1367689 := bbase (se 2 (by rfl) ⟨512883, by rfl⟩ : syracuseStep 1367689 = 1025767) (by norm_num)
theorem B2023069 : Blo 1198416 2023069 := bbase (se 3 (by rfl) ⟨379325, by rfl⟩ : syracuseStep 2023069 = 758651) (by norm_num)
theorem B2277085 : Blo 1198416 2277085 := bbase (se 3 (by rfl) ⟨426953, by rfl⟩ : syracuseStep 2277085 = 853907) (by norm_num)
theorem B2023157 : Blo 1198416 2023157 := bbase (se 5 (by rfl) ⟨94835, by rfl⟩ : syracuseStep 2023157 = 189671) (by norm_num)
theorem B4046597 : Blo 1198416 4046597 := bbase (se 4 (by rfl) ⟨379368, by rfl⟩ : syracuseStep 4046597 = 758737) (by norm_num)
theorem B2309917 : Blo 1198416 2309917 := bbase (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) (by norm_num)
theorem B3284837 : Blo 1198416 3284837 := bbase (se 4 (by rfl) ⟨307953, by rfl⟩ : syracuseStep 3284837 = 615907) (by norm_num)
theorem B2277229 : Blo 1198416 2277229 := bbase (se 3 (by rfl) ⟨426980, by rfl⟩ : syracuseStep 2277229 = 853961) (by norm_num)
theorem B2023285 : Blo 1198416 2023285 := bbase (se 5 (by rfl) ⟨94841, by rfl⟩ : syracuseStep 2023285 = 189683) (by norm_num)
theorem B1621885 : Blo 1198416 1621885 := bbase (se 3 (by rfl) ⟨304103, by rfl⟩ : syracuseStep 1621885 = 608207) (by norm_num)
theorem B2023373 : Blo 1198416 2023373 := bbase (se 3 (by rfl) ⟨379382, by rfl⟩ : syracuseStep 2023373 = 758765) (by norm_num)
theorem B3842005 : Blo 1198416 3842005 := bbase (se 7 (by rfl) ⟨45023, by rfl⟩ : syracuseStep 3842005 = 90047) (by norm_num)
theorem B5119973 : Blo 1198416 5119973 := bbase (se 4 (by rfl) ⟨479997, by rfl⟩ : syracuseStep 5119973 = 959995) (by norm_num)
theorem B2023427 : Blo 1198416 2023427 := bstep (se 1 (by rfl) ⟨1517570, by rfl⟩ : syracuseStep 2023427 = 3035141) B3035141
theorem B1441891 : Blo 1198416 1441891 := bstep (se 1 (by rfl) ⟨1081418, by rfl⟩ : syracuseStep 1441891 = 2162837) B2162837
theorem B29171825 : Blo 1198416 29171825 := bstep (se 2 (by rfl) ⟨10939434, by rfl⟩ : syracuseStep 29171825 = 21878869) B21878869
theorem B2162801 : Blo 1198416 2162801 := bstep (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) B1622101
theorem B2023555 : Blo 1198416 2023555 := bstep (se 1 (by rfl) ⟨1517666, by rfl⟩ : syracuseStep 2023555 = 3035333) B3035333
theorem B2277571 : Blo 1198416 2277571 := bstep (se 1 (by rfl) ⟨1708178, by rfl⟩ : syracuseStep 2277571 = 3416357) B3416357
theorem B3842275 : Blo 1198416 3842275 := bstep (se 1 (by rfl) ⟨2881706, by rfl⟩ : syracuseStep 3842275 = 5763413) B5763413
theorem B2023697 : Blo 1198416 2023697 := bstep (se 2 (by rfl) ⟨758886, by rfl⟩ : syracuseStep 2023697 = 1517773) B1517773
theorem B1622387 : Blo 1198416 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B4047245 : Blo 1198416 4047245 := bstep (se 3 (by rfl) ⟨758858, by rfl⟩ : syracuseStep 4047245 = 1517717) B1517717
theorem B2023825 : Blo 1198416 2023825 := bstep (se 2 (by rfl) ⟨758934, by rfl⟩ : syracuseStep 2023825 = 1517869) B1517869
theorem B2023859 : Blo 1198416 2023859 := bstep (se 1 (by rfl) ⟨1517894, by rfl⟩ : syracuseStep 2023859 = 3035789) B3035789
theorem B4047299 : Blo 1198416 4047299 := bstep (se 1 (by rfl) ⟨3035474, by rfl⟩ : syracuseStep 4047299 = 6070949) B6070949
theorem B5923277 : Blo 1198416 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B2884099 : Blo 1198416 2884099 := bstep (se 1 (by rfl) ⟨2163074, by rfl⟩ : syracuseStep 2884099 = 4326149) B4326149
theorem B2597393 : Blo 1198416 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B2023987 : Blo 1198416 2023987 := bstep (se 1 (by rfl) ⟨1517990, by rfl⟩ : syracuseStep 2023987 = 3035981) B3035981
theorem B8643185 : Blo 1198416 8643185 := bstep (se 2 (by rfl) ⟨3241194, by rfl⟩ : syracuseStep 8643185 = 6482389) B6482389
theorem B2278019 : Blo 1198416 2278019 := bstep (se 1 (by rfl) ⟨1708514, by rfl⟩ : syracuseStep 2278019 = 3417029) B3417029
theorem B6832781 : Blo 1198416 6832781 := bstep (se 3 (by rfl) ⟨1281146, by rfl⟩ : syracuseStep 6832781 = 2562293) B2562293
theorem B2736803 : Blo 1198416 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B2024129 : Blo 1198416 2024129 := bstep (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) B1518097
theorem B4047569 : Blo 1198416 4047569 := bstep (se 2 (by rfl) ⟨1517838, by rfl⟩ : syracuseStep 4047569 = 3035677) B3035677
theorem B7291619 : Blo 1198416 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B4104931 : Blo 1198416 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B3416813 : Blo 1198416 3416813 := bstep (se 3 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 3416813 = 1281305) B1281305
theorem B8209201 : Blo 1198416 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B2024257 : Blo 1198416 2024257 := bstep (se 2 (by rfl) ⟨759096, by rfl⟩ : syracuseStep 2024257 = 1518193) B1518193
theorem B2024291 : Blo 1198416 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B11518861 : Blo 1198416 11518861 := bstep (se 3 (by rfl) ⟨2159786, by rfl⟩ : syracuseStep 11518861 = 4319573) B4319573
theorem B2278307 : Blo 1198416 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B3417005 : Blo 1198416 3417005 := bstep (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) B1281377
theorem B2024419 : Blo 1198416 2024419 := bstep (se 1 (by rfl) ⟨1518314, by rfl⟩ : syracuseStep 2024419 = 3036629) B3036629
theorem B2024561 : Blo 1198416 2024561 := bstep (se 2 (by rfl) ⟨759210, by rfl⟩ : syracuseStep 2024561 = 1518421) B1518421
theorem B6481073 : Blo 1198416 6481073 := bstep (se 2 (by rfl) ⟨2430402, by rfl⟩ : syracuseStep 6481073 = 4860805) B4860805
theorem B4048109 : Blo 1198416 4048109 := bstep (se 3 (by rfl) ⟨759020, by rfl⟩ : syracuseStep 4048109 = 1518041) B1518041
theorem B2024689 : Blo 1198416 2024689 := bstep (se 2 (by rfl) ⟨759258, by rfl⟩ : syracuseStep 2024689 = 1518517) B1518517
theorem B2024723 : Blo 1198416 2024723 := bstep (se 1 (by rfl) ⟨1518542, by rfl⟩ : syracuseStep 2024723 = 3037085) B3037085
theorem B4048163 : Blo 1198416 4048163 := bstep (se 1 (by rfl) ⟨3036122, by rfl⟩ : syracuseStep 4048163 = 6072245) B6072245
theorem B1729873 : Blo 1198416 1729873 := bstep (se 2 (by rfl) ⟨648702, by rfl⟩ : syracuseStep 1729873 = 1297405) B1297405
theorem B2696561 : Blo 1198416 2696561 := bstep (se 2 (by rfl) ⟨1011210, by rfl⟩ : syracuseStep 2696561 = 2022421) B2022421
theorem B4613489 : Blo 1198416 4613489 := bstep (se 2 (by rfl) ⟨1730058, by rfl⟩ : syracuseStep 4613489 = 3460117) B3460117
theorem B2696579 : Blo 1198416 2696579 := bstep (se 1 (by rfl) ⟨2022434, by rfl⟩ : syracuseStep 2696579 = 4044869) B4044869
theorem B2024851 : Blo 1198416 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B1516963 : Blo 1198416 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B11535857 : Blo 1198416 11535857 := bstep (se 2 (by rfl) ⟨4325946, by rfl⟩ : syracuseStep 11535857 = 8651893) B8651893
theorem B1517059 : Blo 1198416 1517059 := bstep (se 1 (by rfl) ⟨1137794, by rfl⟩ : syracuseStep 1517059 = 2275589) B2275589
theorem B2024993 : Blo 1198416 2024993 := bstep (se 2 (by rfl) ⟨759372, by rfl⟩ : syracuseStep 2024993 = 1518745) B1518745
theorem B4048433 : Blo 1198416 4048433 := bstep (se 2 (by rfl) ⟨1518162, by rfl⟩ : syracuseStep 4048433 = 3036325) B3036325
theorem B6071921 : Blo 1198416 6071921 := bstep (se 2 (by rfl) ⟨2276970, by rfl⟩ : syracuseStep 6071921 = 4553941) B4553941
theorem B6006413 : Blo 1198416 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B2696849 : Blo 1198416 2696849 := bstep (se 2 (by rfl) ⟨1011318, by rfl⟩ : syracuseStep 2696849 = 2022637) B2022637
theorem B2025121 : Blo 1198416 2025121 := bstep (se 2 (by rfl) ⟨759420, by rfl⟩ : syracuseStep 2025121 = 1518841) B1518841
theorem B2696867 : Blo 1198416 2696867 := bstep (se 1 (by rfl) ⟨2022650, by rfl⟩ : syracuseStep 2696867 = 4045301) B4045301
theorem B2025155 : Blo 1198416 2025155 := bstep (se 1 (by rfl) ⟨1518866, by rfl⟩ : syracuseStep 2025155 = 3037733) B3037733
theorem B3843875 : Blo 1198416 3843875 := bstep (se 1 (by rfl) ⟨2882906, by rfl⟩ : syracuseStep 3843875 = 5765813) B5765813
theorem B2025283 : Blo 1198416 2025283 := bstep (se 1 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 2025283 = 3037925) B3037925
theorem B3286865 : Blo 1198416 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B3417997 : Blo 1198416 3417997 := bstep (se 3 (by rfl) ⟨640874, by rfl⟩ : syracuseStep 3417997 = 1281749) B1281749
theorem B1279891 : Blo 1198416 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B2697137 : Blo 1198416 2697137 := bstep (se 2 (by rfl) ⟨1011426, by rfl⟩ : syracuseStep 2697137 = 2022853) B2022853
theorem B2697155 : Blo 1198416 2697155 := bstep (se 1 (by rfl) ⟨2022866, by rfl⟩ : syracuseStep 2697155 = 4045733) B4045733
theorem B2025425 : Blo 1198416 2025425 := bstep (se 2 (by rfl) ⟨759534, by rfl⟩ : syracuseStep 2025425 = 1519069) B1519069
theorem B1517555 : Blo 1198416 1517555 := bstep (se 1 (by rfl) ⟨1138166, by rfl⟩ : syracuseStep 1517555 = 2276333) B2276333
theorem B2050051 : Blo 1198416 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B4048973 : Blo 1198416 4048973 := bstep (se 3 (by rfl) ⟨759182, by rfl⟩ : syracuseStep 4048973 = 1518365) B1518365
theorem B2025553 : Blo 1198416 2025553 := bstep (se 2 (by rfl) ⟨759582, by rfl⟩ : syracuseStep 2025553 = 1519165) B1519165
theorem B17303665 : Blo 1198416 17303665 := bstep (se 2 (by rfl) ⟨6488874, by rfl⟩ : syracuseStep 17303665 = 12977749) B12977749
theorem B2025587 : Blo 1198416 2025587 := bstep (se 1 (by rfl) ⟨1519190, by rfl⟩ : syracuseStep 2025587 = 3038381) B3038381
theorem B4049027 : Blo 1198416 4049027 := bstep (se 1 (by rfl) ⟨3036770, by rfl⟩ : syracuseStep 4049027 = 6073541) B6073541
theorem B3287213 : Blo 1198416 3287213 := bstep (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) B1232705
theorem B23668933 : Blo 1198416 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B2697425 : Blo 1198416 2697425 := bstep (se 2 (by rfl) ⟨1011534, by rfl⟩ : syracuseStep 2697425 = 2023069) B2023069
theorem B4319459 : Blo 1198416 4319459 := bstep (se 1 (by rfl) ⟨3239594, by rfl⟩ : syracuseStep 4319459 = 6479189) B6479189
theorem B2697443 : Blo 1198416 2697443 := bstep (se 1 (by rfl) ⟨2023082, by rfl⟩ : syracuseStep 2697443 = 4046165) B4046165
theorem B1198419 : Blo 1198416 1198419 := bstep (se 1 (by rfl) ⟨898814, by rfl⟩ : syracuseStep 1198419 = 1797629) B1797629
theorem B1198435 : Blo 1198416 1198435 := bstep (se 1 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 1198435 = 1797653) B1797653
theorem B1198451 : Blo 1198416 1198451 := bstep (se 1 (by rfl) ⟨898838, by rfl⟩ : syracuseStep 1198451 = 1797677) B1797677
theorem B1198467 : Blo 1198416 1198467 := bstep (se 1 (by rfl) ⟨898850, by rfl⟩ : syracuseStep 1198467 = 1797701) B1797701
theorem B4049297 : Blo 1198416 4049297 := bstep (se 2 (by rfl) ⟨1518486, by rfl⟩ : syracuseStep 4049297 = 3036973) B3036973
theorem B1198483 : Blo 1198416 1198483 := bstep (se 1 (by rfl) ⟨898862, by rfl⟩ : syracuseStep 1198483 = 1797725) B1797725
theorem B1198499 : Blo 1198416 1198499 := bstep (se 1 (by rfl) ⟨898874, by rfl⟩ : syracuseStep 1198499 = 1797749) B1797749
theorem B3033521 : Blo 1198416 3033521 := bstep (se 2 (by rfl) ⟨1137570, by rfl⟩ : syracuseStep 3033521 = 2275141) B2275141
theorem B1198515 : Blo 1198416 1198515 := bstep (se 1 (by rfl) ⟨898886, by rfl⟩ : syracuseStep 1198515 = 1797773) B1797773
theorem B1198531 : Blo 1198416 1198531 := bstep (se 1 (by rfl) ⟨898898, by rfl⟩ : syracuseStep 1198531 = 1797797) B1797797
theorem B1198547 : Blo 1198416 1198547 := bstep (se 1 (by rfl) ⟨898910, by rfl⟩ : syracuseStep 1198547 = 1797821) B1797821
theorem B3033571 : Blo 1198416 3033571 := bstep (se 1 (by rfl) ⟨2275178, by rfl⟩ : syracuseStep 3033571 = 4550357) B4550357
theorem B1198563 : Blo 1198416 1198563 := bstep (se 1 (by rfl) ⟨898922, by rfl⟩ : syracuseStep 1198563 = 1797845) B1797845
theorem B2697713 : Blo 1198416 2697713 := bstep (se 2 (by rfl) ⟨1011642, by rfl⟩ : syracuseStep 2697713 = 2023285) B2023285
theorem B1198579 : Blo 1198416 1198579 := bstep (se 1 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 1198579 = 1797869) B1797869
theorem B1198595 : Blo 1198416 1198595 := bstep (se 1 (by rfl) ⟨898946, by rfl⟩ : syracuseStep 1198595 = 1797893) B1797893
theorem B2697731 : Blo 1198416 2697731 := bstep (se 1 (by rfl) ⟨2023298, by rfl⟩ : syracuseStep 2697731 = 4046597) B4046597
theorem B1198611 : Blo 1198416 1198611 := bstep (se 1 (by rfl) ⟨898958, by rfl⟩ : syracuseStep 1198611 = 1797917) B1797917
theorem B1198627 : Blo 1198416 1198627 := bstep (se 1 (by rfl) ⟨898970, by rfl⟩ : syracuseStep 1198627 = 1797941) B1797941
theorem B1198643 : Blo 1198416 1198643 := bstep (se 1 (by rfl) ⟨898982, by rfl⟩ : syracuseStep 1198643 = 1797965) B1797965
theorem B1198659 : Blo 1198416 1198659 := bstep (se 1 (by rfl) ⟨898994, by rfl⟩ : syracuseStep 1198659 = 1797989) B1797989
theorem B2189891 : Blo 1198416 2189891 := bstep (se 1 (by rfl) ⟨1642418, by rfl⟩ : syracuseStep 2189891 = 3284837) B3284837
theorem B1198675 : Blo 1198416 1198675 := bstep (se 1 (by rfl) ⟨899006, by rfl⟩ : syracuseStep 1198675 = 1798013) B1798013
theorem B1215059 : Blo 1198416 1215059 := bstep (se 1 (by rfl) ⟨911294, by rfl⟩ : syracuseStep 1215059 = 1822589) B1822589
theorem B1198691 : Blo 1198416 1198691 := bstep (se 1 (by rfl) ⟨899018, by rfl⟩ : syracuseStep 1198691 = 1798037) B1798037
theorem B3033713 : Blo 1198416 3033713 := bstep (se 2 (by rfl) ⟨1137642, by rfl⟩ : syracuseStep 3033713 = 2275285) B2275285
theorem B5122673 : Blo 1198416 5122673 := bstep (se 2 (by rfl) ⟨1921002, by rfl⟩ : syracuseStep 5122673 = 3842005) B3842005
theorem B1198707 : Blo 1198416 1198707 := bstep (se 1 (by rfl) ⟨899030, by rfl⟩ : syracuseStep 1198707 = 1798061) B1798061
theorem B1198723 : Blo 1198416 1198723 := bstep (se 1 (by rfl) ⟨899042, by rfl⟩ : syracuseStep 1198723 = 1798085) B1798085
theorem B1460867 : Blo 1198416 1460867 := bstep (se 1 (by rfl) ⟨1095650, by rfl⟩ : syracuseStep 1460867 = 2191301) B2191301
theorem B1198739 : Blo 1198416 1198739 := bstep (se 1 (by rfl) ⟨899054, by rfl⟩ : syracuseStep 1198739 = 1798109) B1798109
theorem B1198755 : Blo 1198416 1198755 := bstep (se 1 (by rfl) ⟨899066, by rfl⟩ : syracuseStep 1198755 = 1798133) B1798133
theorem B1198771 : Blo 1198416 1198771 := bstep (se 1 (by rfl) ⟨899078, by rfl⟩ : syracuseStep 1198771 = 1798157) B1798157
theorem B1518259 : Blo 1198416 1518259 := bstep (se 1 (by rfl) ⟨1138694, by rfl⟩ : syracuseStep 1518259 = 2277389) B2277389
theorem B1198787 : Blo 1198416 1198787 := bstep (se 1 (by rfl) ⟨899090, by rfl⟩ : syracuseStep 1198787 = 1798181) B1798181
theorem B1198803 : Blo 1198416 1198803 := bstep (se 1 (by rfl) ⟨899102, by rfl⟩ : syracuseStep 1198803 = 1798205) B1798205
theorem B1198819 : Blo 1198416 1198819 := bstep (se 1 (by rfl) ⟨899114, by rfl⟩ : syracuseStep 1198819 = 1798229) B1798229
theorem B3844849 : Blo 1198416 3844849 := bstep (se 2 (by rfl) ⟨1441818, by rfl⟩ : syracuseStep 3844849 = 2883637) B2883637
theorem B1198835 : Blo 1198416 1198835 := bstep (se 1 (by rfl) ⟨899126, by rfl⟩ : syracuseStep 1198835 = 1798253) B1798253
theorem B1198851 : Blo 1198416 1198851 := bstep (se 1 (by rfl) ⟨899138, by rfl⟩ : syracuseStep 1198851 = 1798277) B1798277
theorem B2698001 : Blo 1198416 2698001 := bstep (se 2 (by rfl) ⟨1011750, by rfl⟩ : syracuseStep 2698001 = 2023501) B2023501
theorem B1198867 : Blo 1198416 1198867 := bstep (se 1 (by rfl) ⟨899150, by rfl⟩ : syracuseStep 1198867 = 1798301) B1798301
theorem B1518355 : Blo 1198416 1518355 := bstep (se 1 (by rfl) ⟨1138766, by rfl⟩ : syracuseStep 1518355 = 2277533) B2277533
theorem B1198883 : Blo 1198416 1198883 := bstep (se 1 (by rfl) ⟨899162, by rfl⟩ : syracuseStep 1198883 = 1798325) B1798325
theorem B2698019 : Blo 1198416 2698019 := bstep (se 1 (by rfl) ⟨2023514, by rfl⟩ : syracuseStep 2698019 = 4047029) B4047029
theorem B4557617 : Blo 1198416 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B1198899 : Blo 1198416 1198899 := bstep (se 1 (by rfl) ⟨899174, by rfl⟩ : syracuseStep 1198899 = 1798349) B1798349
theorem B1198915 : Blo 1198416 1198915 := bstep (se 1 (by rfl) ⟨899186, by rfl⟩ : syracuseStep 1198915 = 1798373) B1798373
theorem B6835013 : Blo 1198416 6835013 := bstep (se 4 (by rfl) ⟨640782, by rfl⟩ : syracuseStep 6835013 = 1281565) B1281565
theorem B1198931 : Blo 1198416 1198931 := bstep (se 1 (by rfl) ⟨899198, by rfl⟩ : syracuseStep 1198931 = 1798397) B1798397
theorem B1198947 : Blo 1198416 1198947 := bstep (se 1 (by rfl) ⟨899210, by rfl⟩ : syracuseStep 1198947 = 1798421) B1798421
theorem B5761891 : Blo 1198416 5761891 := bstep (se 1 (by rfl) ⟨4321418, by rfl⟩ : syracuseStep 5761891 = 8642837) B8642837
theorem B1198963 : Blo 1198416 1198963 := bstep (se 1 (by rfl) ⟨899222, by rfl⟩ : syracuseStep 1198963 = 1798445) B1798445
theorem B1919875 : Blo 1198416 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B1198979 : Blo 1198416 1198979 := bstep (se 1 (by rfl) ⟨899234, by rfl⟩ : syracuseStep 1198979 = 1798469) B1798469
theorem B1198995 : Blo 1198416 1198995 := bstep (se 1 (by rfl) ⟨899246, by rfl⟩ : syracuseStep 1198995 = 1798493) B1798493
theorem B1199011 : Blo 1198416 1199011 := bstep (se 1 (by rfl) ⟨899258, by rfl⟩ : syracuseStep 1199011 = 1798517) B1798517
theorem B4049837 : Blo 1198416 4049837 := bstep (se 3 (by rfl) ⟨759344, by rfl⟩ : syracuseStep 4049837 = 1518689) B1518689
theorem B1199027 : Blo 1198416 1199027 := bstep (se 1 (by rfl) ⟨899270, by rfl⟩ : syracuseStep 1199027 = 1798541) B1798541
theorem B1199043 : Blo 1198416 1199043 := bstep (se 1 (by rfl) ⟨899282, by rfl⟩ : syracuseStep 1199043 = 1798565) B1798565
theorem B6826949 : Blo 1198416 6826949 := bstep (se 4 (by rfl) ⟨640026, by rfl⟩ : syracuseStep 6826949 = 1280053) B1280053
theorem B1199059 : Blo 1198416 1199059 := bstep (se 1 (by rfl) ⟨899294, by rfl⟩ : syracuseStep 1199059 = 1798589) B1798589
theorem B1199075 : Blo 1198416 1199075 := bstep (se 1 (by rfl) ⟨899306, by rfl⟩ : syracuseStep 1199075 = 1798613) B1798613
theorem B4049891 : Blo 1198416 4049891 := bstep (se 1 (by rfl) ⟨3037418, by rfl⟩ : syracuseStep 4049891 = 6074837) B6074837
theorem B1199091 : Blo 1198416 1199091 := bstep (se 1 (by rfl) ⟨899318, by rfl⟩ : syracuseStep 1199091 = 1798637) B1798637
theorem B1199107 : Blo 1198416 1199107 := bstep (se 1 (by rfl) ⟨899330, by rfl⟩ : syracuseStep 1199107 = 1798661) B1798661
theorem B1199123 : Blo 1198416 1199123 := bstep (se 1 (by rfl) ⟨899342, by rfl⟩ : syracuseStep 1199123 = 1798685) B1798685
theorem B1199139 : Blo 1198416 1199139 := bstep (se 1 (by rfl) ⟨899354, by rfl⟩ : syracuseStep 1199139 = 1798709) B1798709
theorem B6073379 : Blo 1198416 6073379 := bstep (se 1 (by rfl) ⟨4555034, by rfl⟩ : syracuseStep 6073379 = 9110069) B9110069
theorem B2698289 : Blo 1198416 2698289 := bstep (se 2 (by rfl) ⟨1011858, by rfl⟩ : syracuseStep 2698289 = 2023717) B2023717
theorem B1199155 : Blo 1198416 1199155 := bstep (se 1 (by rfl) ⟨899366, by rfl⟩ : syracuseStep 1199155 = 1798733) B1798733
theorem B1199171 : Blo 1198416 1199171 := bstep (se 1 (by rfl) ⟨899378, by rfl⟩ : syracuseStep 1199171 = 1798757) B1798757
theorem B2698307 : Blo 1198416 2698307 := bstep (se 1 (by rfl) ⟨2023730, by rfl⟩ : syracuseStep 2698307 = 4047461) B4047461
theorem B7687237 : Blo 1198416 7687237 := bstep (se 4 (by rfl) ⟨720678, by rfl⟩ : syracuseStep 7687237 = 1441357) B1441357
theorem B1199187 : Blo 1198416 1199187 := bstep (se 1 (by rfl) ⟨899390, by rfl⟩ : syracuseStep 1199187 = 1798781) B1798781
theorem B1199203 : Blo 1198416 1199203 := bstep (se 1 (by rfl) ⟨899402, by rfl⟩ : syracuseStep 1199203 = 1798805) B1798805
theorem B1199219 : Blo 1198416 1199219 := bstep (se 1 (by rfl) ⟨899414, by rfl⟩ : syracuseStep 1199219 = 1798829) B1798829
theorem B1199235 : Blo 1198416 1199235 := bstep (se 1 (by rfl) ⟨899426, by rfl⟩ : syracuseStep 1199235 = 1798853) B1798853
theorem B1281155 : Blo 1198416 1281155 := bstep (se 1 (by rfl) ⟨960866, by rfl⟩ : syracuseStep 1281155 = 1921733) B1921733
theorem B1199251 : Blo 1198416 1199251 := bstep (se 1 (by rfl) ⟨899438, by rfl⟩ : syracuseStep 1199251 = 1798877) B1798877
theorem B1199267 : Blo 1198416 1199267 := bstep (se 1 (by rfl) ⟨899450, by rfl⟩ : syracuseStep 1199267 = 1798901) B1798901
theorem B1199283 : Blo 1198416 1199283 := bstep (se 1 (by rfl) ⟨899462, by rfl⟩ : syracuseStep 1199283 = 1798925) B1798925
theorem B1199299 : Blo 1198416 1199299 := bstep (se 1 (by rfl) ⟨899474, by rfl⟩ : syracuseStep 1199299 = 1798949) B1798949
theorem B1199315 : Blo 1198416 1199315 := bstep (se 1 (by rfl) ⟨899486, by rfl⟩ : syracuseStep 1199315 = 1798973) B1798973
theorem B1199331 : Blo 1198416 1199331 := bstep (se 1 (by rfl) ⟨899498, by rfl⟩ : syracuseStep 1199331 = 1798997) B1798997
theorem B4050161 : Blo 1198416 4050161 := bstep (se 2 (by rfl) ⟨1518810, by rfl⟩ : syracuseStep 4050161 = 3037621) B3037621
theorem B1199347 : Blo 1198416 1199347 := bstep (se 1 (by rfl) ⟨899510, by rfl⟩ : syracuseStep 1199347 = 1799021) B1799021
theorem B1199363 : Blo 1198416 1199363 := bstep (se 1 (by rfl) ⟨899522, by rfl⟩ : syracuseStep 1199363 = 1799045) B1799045
theorem B1518851 : Blo 1198416 1518851 := bstep (se 1 (by rfl) ⟨1139138, by rfl⟩ : syracuseStep 1518851 = 2278277) B2278277
theorem B1199379 : Blo 1198416 1199379 := bstep (se 1 (by rfl) ⟨899534, by rfl⟩ : syracuseStep 1199379 = 1799069) B1799069
theorem B1199395 : Blo 1198416 1199395 := bstep (se 1 (by rfl) ⟨899546, by rfl⟩ : syracuseStep 1199395 = 1799093) B1799093
theorem B1707313 : Blo 1198416 1707313 := bstep (se 2 (by rfl) ⟨640242, by rfl⟩ : syracuseStep 1707313 = 1280485) B1280485
theorem B5762353 : Blo 1198416 5762353 := bstep (se 2 (by rfl) ⟨2160882, by rfl⟩ : syracuseStep 5762353 = 4321765) B4321765
theorem B1199411 : Blo 1198416 1199411 := bstep (se 1 (by rfl) ⟨899558, by rfl⟩ : syracuseStep 1199411 = 1799117) B1799117
theorem B13651253 : Blo 1198416 13651253 := bstep (se 5 (by rfl) ⟨639902, by rfl⟩ : syracuseStep 13651253 = 1279805) B1279805
theorem B1199427 : Blo 1198416 1199427 := bstep (se 1 (by rfl) ⟨899570, by rfl⟩ : syracuseStep 1199427 = 1799141) B1799141
theorem B2698577 : Blo 1198416 2698577 := bstep (se 2 (by rfl) ⟨1011966, by rfl⟩ : syracuseStep 2698577 = 2023933) B2023933
theorem B1199443 : Blo 1198416 1199443 := bstep (se 1 (by rfl) ⟨899582, by rfl⟩ : syracuseStep 1199443 = 1799165) B1799165
theorem B2698595 : Blo 1198416 2698595 := bstep (se 1 (by rfl) ⟨2023946, by rfl⟩ : syracuseStep 2698595 = 4047893) B4047893
theorem B1199459 : Blo 1198416 1199459 := bstep (se 1 (by rfl) ⟨899594, by rfl⟩ : syracuseStep 1199459 = 1799189) B1799189
theorem B20483441 : Blo 1198416 20483441 := bstep (se 2 (by rfl) ⟨7681290, by rfl⟩ : syracuseStep 20483441 = 15362581) B15362581
theorem B1199475 : Blo 1198416 1199475 := bstep (se 1 (by rfl) ⟨899606, by rfl⟩ : syracuseStep 1199475 = 1799213) B1799213
theorem B1199491 : Blo 1198416 1199491 := bstep (se 1 (by rfl) ⟨899618, by rfl⟩ : syracuseStep 1199491 = 1799237) B1799237
theorem B1707409 : Blo 1198416 1707409 := bstep (se 2 (by rfl) ⟨640278, by rfl⟩ : syracuseStep 1707409 = 1280557) B1280557
theorem B1199507 : Blo 1198416 1199507 := bstep (se 1 (by rfl) ⟨899630, by rfl⟩ : syracuseStep 1199507 = 1799261) B1799261
theorem B1199523 : Blo 1198416 1199523 := bstep (se 1 (by rfl) ⟨899642, by rfl⟩ : syracuseStep 1199523 = 1799285) B1799285
theorem B3001763 : Blo 1198416 3001763 := bstep (se 1 (by rfl) ⟨2251322, by rfl⟩ : syracuseStep 3001763 = 4502645) B4502645
theorem B1199539 : Blo 1198416 1199539 := bstep (se 1 (by rfl) ⟨899654, by rfl⟩ : syracuseStep 1199539 = 1799309) B1799309
theorem B1199555 : Blo 1198416 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B1199571 : Blo 1198416 1199571 := bstep (se 1 (by rfl) ⟨899678, by rfl⟩ : syracuseStep 1199571 = 1799357) B1799357
theorem B1199587 : Blo 1198416 1199587 := bstep (se 1 (by rfl) ⟨899690, by rfl⟩ : syracuseStep 1199587 = 1799381) B1799381
theorem B6835697 : Blo 1198416 6835697 := bstep (se 2 (by rfl) ⟨2563386, by rfl⟩ : syracuseStep 6835697 = 5126773) B5126773
theorem B1199603 : Blo 1198416 1199603 := bstep (se 1 (by rfl) ⟨899702, by rfl⟩ : syracuseStep 1199603 = 1799405) B1799405
theorem B1797635 : Blo 1198416 1797635 := bstep (se 1 (by rfl) ⟨1348226, by rfl⟩ : syracuseStep 1797635 = 2696453) B2696453
theorem B1199619 : Blo 1198416 1199619 := bstep (se 1 (by rfl) ⟨899714, by rfl⟩ : syracuseStep 1199619 = 1799429) B1799429
theorem B1199635 : Blo 1198416 1199635 := bstep (se 1 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 1199635 = 1799453) B1799453
theorem B1797665 : Blo 1198416 1797665 := bstep (se 2 (by rfl) ⟨674124, by rfl⟩ : syracuseStep 1797665 = 1348249) B1348249
theorem B2051617 : Blo 1198416 2051617 := bstep (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) B1538713
theorem B1199651 : Blo 1198416 1199651 := bstep (se 1 (by rfl) ⟨899738, by rfl⟩ : syracuseStep 1199651 = 1799477) B1799477
theorem B1797683 : Blo 1198416 1797683 := bstep (se 1 (by rfl) ⟨1348262, by rfl⟩ : syracuseStep 1797683 = 2696525) B2696525
theorem B1199667 : Blo 1198416 1199667 := bstep (se 1 (by rfl) ⟨899750, by rfl⟩ : syracuseStep 1199667 = 1799501) B1799501
theorem B1199683 : Blo 1198416 1199683 := bstep (se 1 (by rfl) ⟨899762, by rfl⟩ : syracuseStep 1199683 = 1799525) B1799525
theorem B1797713 : Blo 1198416 1797713 := bstep (se 2 (by rfl) ⟨674142, by rfl⟩ : syracuseStep 1797713 = 1348285) B1348285
theorem B3034705 : Blo 1198416 3034705 := bstep (se 2 (by rfl) ⟨1138014, by rfl⟩ : syracuseStep 3034705 = 2276029) B2276029
theorem B1920593 : Blo 1198416 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1199699 : Blo 1198416 1199699 := bstep (se 1 (by rfl) ⟨899774, by rfl⟩ : syracuseStep 1199699 = 1799549) B1799549
theorem B1797731 : Blo 1198416 1797731 := bstep (se 1 (by rfl) ⟨1348298, by rfl⟩ : syracuseStep 1797731 = 2696597) B2696597
theorem B1199715 : Blo 1198416 1199715 := bstep (se 1 (by rfl) ⟨899786, by rfl⟩ : syracuseStep 1199715 = 1799573) B1799573
theorem B2698865 : Blo 1198416 2698865 := bstep (se 2 (by rfl) ⟨1012074, by rfl⟩ : syracuseStep 2698865 = 2024149) B2024149
theorem B1199731 : Blo 1198416 1199731 := bstep (se 1 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 1199731 = 1799597) B1799597
theorem B1797761 : Blo 1198416 1797761 := bstep (se 2 (by rfl) ⟨674160, by rfl⟩ : syracuseStep 1797761 = 1348321) B1348321
theorem B2698883 : Blo 1198416 2698883 := bstep (se 1 (by rfl) ⟨2024162, by rfl⟩ : syracuseStep 2698883 = 4048325) B4048325
theorem B1199747 : Blo 1198416 1199747 := bstep (se 1 (by rfl) ⟨899810, by rfl⟩ : syracuseStep 1199747 = 1799621) B1799621
theorem B1797779 : Blo 1198416 1797779 := bstep (se 1 (by rfl) ⟨1348334, by rfl⟩ : syracuseStep 1797779 = 2696669) B2696669
theorem B1199763 : Blo 1198416 1199763 := bstep (se 1 (by rfl) ⟨899822, by rfl⟩ : syracuseStep 1199763 = 1799645) B1799645
theorem B1199779 : Blo 1198416 1199779 := bstep (se 1 (by rfl) ⟨899834, by rfl⟩ : syracuseStep 1199779 = 1799669) B1799669
theorem B1797809 : Blo 1198416 1797809 := bstep (se 2 (by rfl) ⟨674178, by rfl⟩ : syracuseStep 1797809 = 1348357) B1348357
theorem B1199795 : Blo 1198416 1199795 := bstep (se 1 (by rfl) ⟨899846, by rfl⟩ : syracuseStep 1199795 = 1799693) B1799693
theorem B1797827 : Blo 1198416 1797827 := bstep (se 1 (by rfl) ⟨1348370, by rfl⟩ : syracuseStep 1797827 = 2696741) B2696741
theorem B1199811 : Blo 1198416 1199811 := bstep (se 1 (by rfl) ⟨899858, by rfl⟩ : syracuseStep 1199811 = 1799717) B1799717
theorem B1199827 : Blo 1198416 1199827 := bstep (se 1 (by rfl) ⟨899870, by rfl⟩ : syracuseStep 1199827 = 1799741) B1799741
theorem B1797857 : Blo 1198416 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B1199843 : Blo 1198416 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B1797875 : Blo 1198416 1797875 := bstep (se 1 (by rfl) ⟨1348406, by rfl⟩ : syracuseStep 1797875 = 2696813) B2696813
theorem B1199859 : Blo 1198416 1199859 := bstep (se 1 (by rfl) ⟨899894, by rfl⟩ : syracuseStep 1199859 = 1799789) B1799789
theorem B1199875 : Blo 1198416 1199875 := bstep (se 1 (by rfl) ⟨899906, by rfl⟩ : syracuseStep 1199875 = 1799813) B1799813
theorem B4050701 : Blo 1198416 4050701 := bstep (se 3 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 4050701 = 1519013) B1519013
theorem B1797905 : Blo 1198416 1797905 := bstep (se 2 (by rfl) ⟨674214, by rfl⟩ : syracuseStep 1797905 = 1348429) B1348429
theorem B1199891 : Blo 1198416 1199891 := bstep (se 1 (by rfl) ⟨899918, by rfl⟩ : syracuseStep 1199891 = 1799837) B1799837
theorem B1797923 : Blo 1198416 1797923 := bstep (se 1 (by rfl) ⟨1348442, by rfl⟩ : syracuseStep 1797923 = 2696885) B2696885
theorem B1199907 : Blo 1198416 1199907 := bstep (se 1 (by rfl) ⟨899930, by rfl⟩ : syracuseStep 1199907 = 1799861) B1799861
theorem B1199923 : Blo 1198416 1199923 := bstep (se 1 (by rfl) ⟨899942, by rfl⟩ : syracuseStep 1199923 = 1799885) B1799885
theorem B1797953 : Blo 1198416 1797953 := bstep (se 2 (by rfl) ⟨674232, by rfl⟩ : syracuseStep 1797953 = 1348465) B1348465
theorem B1199939 : Blo 1198416 1199939 := bstep (se 1 (by rfl) ⟨899954, by rfl⟩ : syracuseStep 1199939 = 1799909) B1799909
theorem B4050755 : Blo 1198416 4050755 := bstep (se 1 (by rfl) ⟨3038066, by rfl⟩ : syracuseStep 4050755 = 6076133) B6076133
theorem B6074189 : Blo 1198416 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B1797971 : Blo 1198416 1797971 := bstep (se 1 (by rfl) ⟨1348478, by rfl⟩ : syracuseStep 1797971 = 2696957) B2696957
theorem B1199955 : Blo 1198416 1199955 := bstep (se 1 (by rfl) ⟨899966, by rfl⟩ : syracuseStep 1199955 = 1799933) B1799933
theorem B3034979 : Blo 1198416 3034979 := bstep (se 1 (by rfl) ⟨2276234, by rfl⟩ : syracuseStep 3034979 = 4552469) B4552469
theorem B1199971 : Blo 1198416 1199971 := bstep (se 1 (by rfl) ⟨899978, by rfl⟩ : syracuseStep 1199971 = 1799957) B1799957
theorem B1798001 : Blo 1198416 1798001 := bstep (se 2 (by rfl) ⟨674250, by rfl⟩ : syracuseStep 1798001 = 1348501) B1348501
theorem B1920881 : Blo 1198416 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1404787 : Blo 1198416 1404787 := bstep (se 1 (by rfl) ⟨1053590, by rfl⟩ : syracuseStep 1404787 = 2107181) B2107181
theorem B1199987 : Blo 1198416 1199987 := bstep (se 1 (by rfl) ⟨899990, by rfl⟩ : syracuseStep 1199987 = 1799981) B1799981
theorem B1707905 : Blo 1198416 1707905 := bstep (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) B1280929
theorem B1798019 : Blo 1198416 1798019 := bstep (se 1 (by rfl) ⟨1348514, by rfl⟩ : syracuseStep 1798019 = 2697029) B2697029
theorem B1200003 : Blo 1198416 1200003 := bstep (se 1 (by rfl) ⟨900002, by rfl⟩ : syracuseStep 1200003 = 1800005) B1800005
theorem B2699153 : Blo 1198416 2699153 := bstep (se 2 (by rfl) ⟨1012182, by rfl⟩ : syracuseStep 2699153 = 2024365) B2024365
theorem B1200019 : Blo 1198416 1200019 := bstep (se 1 (by rfl) ⟨900014, by rfl⟩ : syracuseStep 1200019 = 1800029) B1800029
theorem B1798049 : Blo 1198416 1798049 := bstep (se 2 (by rfl) ⟨674268, by rfl⟩ : syracuseStep 1798049 = 1348537) B1348537
theorem B2699171 : Blo 1198416 2699171 := bstep (se 1 (by rfl) ⟨2024378, by rfl⟩ : syracuseStep 2699171 = 4048757) B4048757
theorem B1200035 : Blo 1198416 1200035 := bstep (se 1 (by rfl) ⟨900026, by rfl⟩ : syracuseStep 1200035 = 1800053) B1800053
theorem B1798067 : Blo 1198416 1798067 := bstep (se 1 (by rfl) ⟨1348550, by rfl⟩ : syracuseStep 1798067 = 2697101) B2697101
theorem B1200051 : Blo 1198416 1200051 := bstep (se 1 (by rfl) ⟨900038, by rfl⟩ : syracuseStep 1200051 = 1800077) B1800077
theorem B1200067 : Blo 1198416 1200067 := bstep (se 1 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 1200067 = 1800101) B1800101
theorem B1798097 : Blo 1198416 1798097 := bstep (se 2 (by rfl) ⟨674286, by rfl⟩ : syracuseStep 1798097 = 1348573) B1348573
theorem B1200083 : Blo 1198416 1200083 := bstep (se 1 (by rfl) ⟨900062, by rfl⟩ : syracuseStep 1200083 = 1800125) B1800125
theorem B1798115 : Blo 1198416 1798115 := bstep (se 1 (by rfl) ⟨1348586, by rfl⟩ : syracuseStep 1798115 = 2697173) B2697173
theorem B1200099 : Blo 1198416 1200099 := bstep (se 1 (by rfl) ⟨900074, by rfl⟩ : syracuseStep 1200099 = 1800149) B1800149
theorem B1200115 : Blo 1198416 1200115 := bstep (se 1 (by rfl) ⟨900086, by rfl⟩ : syracuseStep 1200115 = 1800173) B1800173
theorem B1798145 : Blo 1198416 1798145 := bstep (se 2 (by rfl) ⟨674304, by rfl⟩ : syracuseStep 1798145 = 1348609) B1348609
theorem B1200131 : Blo 1198416 1200131 := bstep (se 1 (by rfl) ⟨900098, by rfl⟩ : syracuseStep 1200131 = 1800197) B1800197
theorem B1798163 : Blo 1198416 1798163 := bstep (se 1 (by rfl) ⟨1348622, by rfl⟩ : syracuseStep 1798163 = 2697245) B2697245
theorem B1200147 : Blo 1198416 1200147 := bstep (se 1 (by rfl) ⟨900110, by rfl⟩ : syracuseStep 1200147 = 1800221) B1800221
theorem B3035171 : Blo 1198416 3035171 := bstep (se 1 (by rfl) ⟨2276378, by rfl⟩ : syracuseStep 3035171 = 4552757) B4552757
theorem B1200163 : Blo 1198416 1200163 := bstep (se 1 (by rfl) ⟨900122, by rfl⟩ : syracuseStep 1200163 = 1800245) B1800245
theorem B1798193 : Blo 1198416 1798193 := bstep (se 2 (by rfl) ⟨674322, by rfl⟩ : syracuseStep 1798193 = 1348645) B1348645
theorem B1822771 : Blo 1198416 1822771 := bstep (se 1 (by rfl) ⟨1367078, by rfl⟩ : syracuseStep 1822771 = 2734157) B2734157
theorem B1200179 : Blo 1198416 1200179 := bstep (se 1 (by rfl) ⟨900134, by rfl⟩ : syracuseStep 1200179 = 1800269) B1800269
theorem B1798211 : Blo 1198416 1798211 := bstep (se 1 (by rfl) ⟨1348658, by rfl⟩ : syracuseStep 1798211 = 2697317) B2697317
theorem B1200195 : Blo 1198416 1200195 := bstep (se 1 (by rfl) ⟨900146, by rfl⟩ : syracuseStep 1200195 = 1800293) B1800293
theorem B2560081 : Blo 1198416 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B1921105 : Blo 1198416 1921105 := bstep (se 2 (by rfl) ⟨720414, by rfl⟩ : syracuseStep 1921105 = 1440829) B1440829
theorem B1200211 : Blo 1198416 1200211 := bstep (se 1 (by rfl) ⟨900158, by rfl⟩ : syracuseStep 1200211 = 1800317) B1800317
theorem B4051025 : Blo 1198416 4051025 := bstep (se 2 (by rfl) ⟨1519134, by rfl⟩ : syracuseStep 4051025 = 3038269) B3038269
theorem B1798241 : Blo 1198416 1798241 := bstep (se 2 (by rfl) ⟨674340, by rfl⟩ : syracuseStep 1798241 = 1348681) B1348681
theorem B1200227 : Blo 1198416 1200227 := bstep (se 1 (by rfl) ⟨900170, by rfl⟩ : syracuseStep 1200227 = 1800341) B1800341
theorem B1798259 : Blo 1198416 1798259 := bstep (se 1 (by rfl) ⟨1348694, by rfl⟩ : syracuseStep 1798259 = 2697389) B2697389
theorem B1200243 : Blo 1198416 1200243 := bstep (se 1 (by rfl) ⟨900182, by rfl⟩ : syracuseStep 1200243 = 1800365) B1800365
theorem B1200259 : Blo 1198416 1200259 := bstep (se 1 (by rfl) ⟨900194, by rfl⟩ : syracuseStep 1200259 = 1800389) B1800389
theorem B1798289 : Blo 1198416 1798289 := bstep (se 2 (by rfl) ⟨674358, by rfl⟩ : syracuseStep 1798289 = 1348717) B1348717
theorem B1200275 : Blo 1198416 1200275 := bstep (se 1 (by rfl) ⟨900206, by rfl⟩ : syracuseStep 1200275 = 1800413) B1800413
theorem B1798307 : Blo 1198416 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B1200291 : Blo 1198416 1200291 := bstep (se 1 (by rfl) ⟨900218, by rfl⟩ : syracuseStep 1200291 = 1800437) B1800437
theorem B2699441 : Blo 1198416 2699441 := bstep (se 2 (by rfl) ⟨1012290, by rfl⟩ : syracuseStep 2699441 = 2024581) B2024581
theorem B1200307 : Blo 1198416 1200307 := bstep (se 1 (by rfl) ⟨900230, by rfl⟩ : syracuseStep 1200307 = 1800461) B1800461
theorem B1798337 : Blo 1198416 1798337 := bstep (se 2 (by rfl) ⟨674376, by rfl⟩ : syracuseStep 1798337 = 1348753) B1348753
theorem B2699459 : Blo 1198416 2699459 := bstep (se 1 (by rfl) ⟨2024594, by rfl⟩ : syracuseStep 2699459 = 4049189) B4049189
theorem B1200323 : Blo 1198416 1200323 := bstep (se 1 (by rfl) ⟨900242, by rfl⟩ : syracuseStep 1200323 = 1800485) B1800485
theorem B1798355 : Blo 1198416 1798355 := bstep (se 1 (by rfl) ⟨1348766, by rfl⟩ : syracuseStep 1798355 = 2697533) B2697533
theorem B1200339 : Blo 1198416 1200339 := bstep (se 1 (by rfl) ⟨900254, by rfl⟩ : syracuseStep 1200339 = 1800509) B1800509
theorem B27709667 : Blo 1198416 27709667 := bstep (se 1 (by rfl) ⟨20782250, by rfl⟩ : syracuseStep 27709667 = 41564501) B41564501
theorem B1200355 : Blo 1198416 1200355 := bstep (se 1 (by rfl) ⟨900266, by rfl⟩ : syracuseStep 1200355 = 1800533) B1800533
theorem B1798385 : Blo 1198416 1798385 := bstep (se 2 (by rfl) ⟨674394, by rfl⟩ : syracuseStep 1798385 = 1348789) B1348789
theorem B1200371 : Blo 1198416 1200371 := bstep (se 1 (by rfl) ⟨900278, by rfl⟩ : syracuseStep 1200371 = 1800557) B1800557
theorem B1798403 : Blo 1198416 1798403 := bstep (se 1 (by rfl) ⟨1348802, by rfl⟩ : syracuseStep 1798403 = 2697605) B2697605
theorem B1822979 : Blo 1198416 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B1200387 : Blo 1198416 1200387 := bstep (se 1 (by rfl) ⟨900290, by rfl⟩ : syracuseStep 1200387 = 1800581) B1800581
theorem B1200403 : Blo 1198416 1200403 := bstep (se 1 (by rfl) ⟨900302, by rfl⟩ : syracuseStep 1200403 = 1800605) B1800605
theorem B1798433 : Blo 1198416 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B1798451 : Blo 1198416 1798451 := bstep (se 1 (by rfl) ⟨1348838, by rfl⟩ : syracuseStep 1798451 = 2697677) B2697677
theorem B1798481 : Blo 1198416 1798481 := bstep (se 2 (by rfl) ⟨674430, by rfl⟩ : syracuseStep 1798481 = 1348861) B1348861
theorem B4551011 : Blo 1198416 4551011 := bstep (se 1 (by rfl) ⟨3413258, by rfl⟩ : syracuseStep 4551011 = 6826517) B6826517
theorem B1798499 : Blo 1198416 1798499 := bstep (se 1 (by rfl) ⟨1348874, by rfl⟩ : syracuseStep 1798499 = 2697749) B2697749
theorem B4551025 : Blo 1198416 4551025 := bstep (se 2 (by rfl) ⟨1706634, by rfl⟩ : syracuseStep 4551025 = 3413269) B3413269
theorem B1798529 : Blo 1198416 1798529 := bstep (se 2 (by rfl) ⟨674448, by rfl⟩ : syracuseStep 1798529 = 1348897) B1348897
theorem B13668749 : Blo 1198416 13668749 := bstep (se 3 (by rfl) ⟨2562890, by rfl⟩ : syracuseStep 13668749 = 5125781) B5125781
theorem B1798547 : Blo 1198416 1798547 := bstep (se 1 (by rfl) ⟨1348910, by rfl⟩ : syracuseStep 1798547 = 2697821) B2697821
theorem B1798577 : Blo 1198416 1798577 := bstep (se 2 (by rfl) ⟨674466, by rfl⟩ : syracuseStep 1798577 = 1348933) B1348933
theorem B1798595 : Blo 1198416 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B6484421 : Blo 1198416 6484421 := bstep (se 4 (by rfl) ⟨607914, by rfl⟩ : syracuseStep 6484421 = 1215829) B1215829
theorem B2699729 : Blo 1198416 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B1798625 : Blo 1198416 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B2699747 : Blo 1198416 2699747 := bstep (se 1 (by rfl) ⟨2024810, by rfl⟩ : syracuseStep 2699747 = 4049621) B4049621
theorem B1798643 : Blo 1198416 1798643 := bstep (se 1 (by rfl) ⟨1348982, by rfl⟩ : syracuseStep 1798643 = 2697965) B2697965
theorem B1798673 : Blo 1198416 1798673 := bstep (se 2 (by rfl) ⟨674502, by rfl⟩ : syracuseStep 1798673 = 1349005) B1349005
theorem B1798691 : Blo 1198416 1798691 := bstep (se 1 (by rfl) ⟨1349018, by rfl⟩ : syracuseStep 1798691 = 2698037) B2698037
theorem B3650093 : Blo 1198416 3650093 := bstep (se 3 (by rfl) ⟨684392, by rfl⟩ : syracuseStep 3650093 = 1368785) B1368785
theorem B1798721 : Blo 1198416 1798721 := bstep (se 2 (by rfl) ⟨674520, by rfl⟩ : syracuseStep 1798721 = 1349041) B1349041
theorem B1798739 : Blo 1198416 1798739 := bstep (se 1 (by rfl) ⟨1349054, by rfl⟩ : syracuseStep 1798739 = 2698109) B2698109
theorem B1798769 : Blo 1198416 1798769 := bstep (se 2 (by rfl) ⟨674538, by rfl⟩ : syracuseStep 1798769 = 1349077) B1349077
theorem B1798787 : Blo 1198416 1798787 := bstep (se 1 (by rfl) ⟨1349090, by rfl⟩ : syracuseStep 1798787 = 2698181) B2698181
theorem B2052739 : Blo 1198416 2052739 := bstep (se 1 (by rfl) ⟨1539554, by rfl⟩ : syracuseStep 2052739 = 3079109) B3079109
theorem B7680653 : Blo 1198416 7680653 := bstep (se 3 (by rfl) ⟨1440122, by rfl⟩ : syracuseStep 7680653 = 2880245) B2880245
theorem B1798817 : Blo 1198416 1798817 := bstep (se 2 (by rfl) ⟨674556, by rfl⟩ : syracuseStep 1798817 = 1349113) B1349113
theorem B1798835 : Blo 1198416 1798835 := bstep (se 1 (by rfl) ⟨1349126, by rfl⟩ : syracuseStep 1798835 = 2698253) B2698253
theorem B1798865 : Blo 1198416 1798865 := bstep (se 2 (by rfl) ⟨674574, by rfl⟩ : syracuseStep 1798865 = 1349149) B1349149
theorem B1798883 : Blo 1198416 1798883 := bstep (se 1 (by rfl) ⟨1349162, by rfl⟩ : syracuseStep 1798883 = 2698325) B2698325
theorem B1708771 : Blo 1198416 1708771 := bstep (se 1 (by rfl) ⟨1281578, by rfl⟩ : syracuseStep 1708771 = 2563157) B2563157
theorem B3650285 : Blo 1198416 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B2700017 : Blo 1198416 2700017 := bstep (se 2 (by rfl) ⟨1012506, by rfl⟩ : syracuseStep 2700017 = 2025013) B2025013
theorem B1348339 : Blo 1198416 1348339 := bstep (se 1 (by rfl) ⟨1011254, by rfl⟩ : syracuseStep 1348339 = 2022509) B2022509
theorem B1946369 : Blo 1198416 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B1798913 : Blo 1198416 1798913 := bstep (se 2 (by rfl) ⟨674592, by rfl⟩ : syracuseStep 1798913 = 1349185) B1349185
theorem B1823489 : Blo 1198416 1823489 := bstep (se 2 (by rfl) ⟨683808, by rfl⟩ : syracuseStep 1823489 = 1367617) B1367617
theorem B2700035 : Blo 1198416 2700035 := bstep (se 1 (by rfl) ⟨2025026, by rfl⟩ : syracuseStep 2700035 = 4050053) B4050053
theorem B1798931 : Blo 1198416 1798931 := bstep (se 1 (by rfl) ⟨1349198, by rfl⟩ : syracuseStep 1798931 = 2698397) B2698397
theorem B1798961 : Blo 1198416 1798961 := bstep (se 2 (by rfl) ⟨674610, by rfl⟩ : syracuseStep 1798961 = 1349221) B1349221
theorem B1798979 : Blo 1198416 1798979 := bstep (se 1 (by rfl) ⟨1349234, by rfl⟩ : syracuseStep 1798979 = 2698469) B2698469
theorem B1708867 : Blo 1198416 1708867 := bstep (se 1 (by rfl) ⟨1281650, by rfl⟩ : syracuseStep 1708867 = 2563301) B2563301
theorem B1799009 : Blo 1198416 1799009 := bstep (se 2 (by rfl) ⟨674628, by rfl⟩ : syracuseStep 1799009 = 1349257) B1349257
theorem B1823585 : Blo 1198416 1823585 := bstep (se 2 (by rfl) ⟨683844, by rfl⟩ : syracuseStep 1823585 = 1367689) B1367689
theorem B7680881 : Blo 1198416 7680881 := bstep (se 2 (by rfl) ⟨2880330, by rfl⟩ : syracuseStep 7680881 = 5760661) B5760661
theorem B1799027 : Blo 1198416 1799027 := bstep (se 1 (by rfl) ⟨1349270, by rfl⟩ : syracuseStep 1799027 = 2698541) B2698541
theorem B1348483 : Blo 1198416 1348483 := bstep (se 1 (by rfl) ⟨1011362, by rfl⟩ : syracuseStep 1348483 = 2022725) B2022725
theorem B1799057 : Blo 1198416 1799057 := bstep (se 2 (by rfl) ⟨674646, by rfl⟩ : syracuseStep 1799057 = 1349293) B1349293
theorem B1799075 : Blo 1198416 1799075 := bstep (se 1 (by rfl) ⟨1349306, by rfl⟩ : syracuseStep 1799075 = 2698613) B2698613
theorem B1799105 : Blo 1198416 1799105 := bstep (se 2 (by rfl) ⟨674664, by rfl⟩ : syracuseStep 1799105 = 1349329) B1349329
theorem B1823683 : Blo 1198416 1823683 := bstep (se 1 (by rfl) ⟨1367762, by rfl⟩ : syracuseStep 1823683 = 2735525) B2735525
theorem B3036113 : Blo 1198416 3036113 := bstep (se 2 (by rfl) ⟨1138542, by rfl⟩ : syracuseStep 3036113 = 2277085) B2277085
theorem B1799123 : Blo 1198416 1799123 := bstep (se 1 (by rfl) ⟨1349342, by rfl⟩ : syracuseStep 1799123 = 2698685) B2698685
theorem B1799153 : Blo 1198416 1799153 := bstep (se 2 (by rfl) ⟨674682, by rfl⟩ : syracuseStep 1799153 = 1349365) B1349365
theorem B1799171 : Blo 1198416 1799171 := bstep (se 1 (by rfl) ⟨1349378, by rfl⟩ : syracuseStep 1799171 = 2698757) B2698757
theorem B3036163 : Blo 1198416 3036163 := bstep (se 1 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 3036163 = 4554245) B4554245
theorem B5125133 : Blo 1198416 5125133 := bstep (se 3 (by rfl) ⟨960962, by rfl⟩ : syracuseStep 5125133 = 1921925) B1921925
theorem B2700305 : Blo 1198416 2700305 := bstep (se 2 (by rfl) ⟨1012614, by rfl⟩ : syracuseStep 2700305 = 2025229) B2025229
theorem B1348627 : Blo 1198416 1348627 := bstep (se 1 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 1348627 = 2022941) B2022941
theorem B1799201 : Blo 1198416 1799201 := bstep (se 2 (by rfl) ⟨674700, by rfl⟩ : syracuseStep 1799201 = 1349401) B1349401
theorem B2700323 : Blo 1198416 2700323 := bstep (se 1 (by rfl) ⟨2025242, by rfl⟩ : syracuseStep 2700323 = 4050485) B4050485
theorem B1799219 : Blo 1198416 1799219 := bstep (se 1 (by rfl) ⟨1349414, by rfl⟩ : syracuseStep 1799219 = 2698829) B2698829
theorem B1799249 : Blo 1198416 1799249 := bstep (se 2 (by rfl) ⟨674718, by rfl⟩ : syracuseStep 1799249 = 1349437) B1349437
theorem B1799267 : Blo 1198416 1799267 := bstep (se 1 (by rfl) ⟨1349450, by rfl⟩ : syracuseStep 1799267 = 2698901) B2698901
theorem B1799297 : Blo 1198416 1799297 := bstep (se 2 (by rfl) ⟨674736, by rfl⟩ : syracuseStep 1799297 = 1349473) B1349473
theorem B29176973 : Blo 1198416 29176973 := bstep (se 3 (by rfl) ⟨5470682, by rfl⟩ : syracuseStep 29176973 = 10941365) B10941365
theorem B3036305 : Blo 1198416 3036305 := bstep (se 2 (by rfl) ⟨1138614, by rfl⟩ : syracuseStep 3036305 = 2277229) B2277229
theorem B1799315 : Blo 1198416 1799315 := bstep (se 1 (by rfl) ⟨1349486, by rfl⟩ : syracuseStep 1799315 = 2698973) B2698973
theorem B2921617 : Blo 1198416 2921617 := bstep (se 2 (by rfl) ⟨1095606, by rfl⟩ : syracuseStep 2921617 = 2191213) B2191213
theorem B1348771 : Blo 1198416 1348771 := bstep (se 1 (by rfl) ⟨1011578, by rfl⟩ : syracuseStep 1348771 = 2023157) B2023157
theorem B1799345 : Blo 1198416 1799345 := bstep (se 2 (by rfl) ⟨674754, by rfl⟩ : syracuseStep 1799345 = 1349509) B1349509
theorem B1799363 : Blo 1198416 1799363 := bstep (se 1 (by rfl) ⟨1349522, by rfl⟩ : syracuseStep 1799363 = 2699045) B2699045
theorem B1799393 : Blo 1198416 1799393 := bstep (se 2 (by rfl) ⟨674772, by rfl⟩ : syracuseStep 1799393 = 1349545) B1349545
theorem B1799411 : Blo 1198416 1799411 := bstep (se 1 (by rfl) ⟨1349558, by rfl⟩ : syracuseStep 1799411 = 2699117) B2699117
theorem B1799441 : Blo 1198416 1799441 := bstep (se 2 (by rfl) ⟨674790, by rfl⟩ : syracuseStep 1799441 = 1349581) B1349581
theorem B1799459 : Blo 1198416 1799459 := bstep (se 1 (by rfl) ⟨1349594, by rfl⟩ : syracuseStep 1799459 = 2699189) B2699189
theorem B2700593 : Blo 1198416 2700593 := bstep (se 2 (by rfl) ⟨1012722, by rfl⟩ : syracuseStep 2700593 = 2025445) B2025445
theorem B1348915 : Blo 1198416 1348915 := bstep (se 1 (by rfl) ⟨1011686, by rfl⟩ : syracuseStep 1348915 = 2023373) B2023373
theorem B1799489 : Blo 1198416 1799489 := bstep (se 2 (by rfl) ⟨674808, by rfl⟩ : syracuseStep 1799489 = 1349617) B1349617
theorem B3413315 : Blo 1198416 3413315 := bstep (se 1 (by rfl) ⟨2559986, by rfl⟩ : syracuseStep 3413315 = 5119973) B5119973
theorem B2700611 : Blo 1198416 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B1799507 : Blo 1198416 1799507 := bstep (se 1 (by rfl) ⟨1349630, by rfl⟩ : syracuseStep 1799507 = 2699261) B2699261
theorem B3077489 : Blo 1198416 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B1799537 : Blo 1198416 1799537 := bstep (se 2 (by rfl) ⟨674826, by rfl⟩ : syracuseStep 1799537 = 1349653) B1349653
theorem B1799555 : Blo 1198416 1799555 := bstep (se 1 (by rfl) ⟨1349666, by rfl⟩ : syracuseStep 1799555 = 2699333) B2699333
theorem B1799585 : Blo 1198416 1799585 := bstep (se 2 (by rfl) ⟨674844, by rfl⟩ : syracuseStep 1799585 = 1349689) B1349689
theorem B1799603 : Blo 1198416 1799603 := bstep (se 1 (by rfl) ⟨1349702, by rfl⟩ : syracuseStep 1799603 = 2699405) B2699405
theorem B1349059 : Blo 1198416 1349059 := bstep (se 1 (by rfl) ⟨1011794, by rfl⟩ : syracuseStep 1349059 = 2023589) B2023589
theorem B1799633 : Blo 1198416 1799633 := bstep (se 2 (by rfl) ⟨674862, by rfl⟩ : syracuseStep 1799633 = 1349725) B1349725
theorem B1799651 : Blo 1198416 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B1799681 : Blo 1198416 1799681 := bstep (se 2 (by rfl) ⟨674880, by rfl⟩ : syracuseStep 1799681 = 1349761) B1349761
theorem B1799699 : Blo 1198416 1799699 := bstep (se 1 (by rfl) ⟨1349774, by rfl⟩ : syracuseStep 1799699 = 2699549) B2699549
theorem B1799729 : Blo 1198416 1799729 := bstep (se 2 (by rfl) ⟨674898, by rfl⟩ : syracuseStep 1799729 = 1349797) B1349797
theorem B1799747 : Blo 1198416 1799747 := bstep (se 1 (by rfl) ⟨1349810, by rfl⟩ : syracuseStep 1799747 = 2699621) B2699621
theorem B2700881 : Blo 1198416 2700881 := bstep (se 2 (by rfl) ⟨1012830, by rfl⟩ : syracuseStep 2700881 = 2025661) B2025661
theorem B1349203 : Blo 1198416 1349203 := bstep (se 1 (by rfl) ⟨1011902, by rfl⟩ : syracuseStep 1349203 = 2023805) B2023805
theorem B1799777 : Blo 1198416 1799777 := bstep (se 2 (by rfl) ⟨674916, by rfl⟩ : syracuseStep 1799777 = 1349833) B1349833
theorem B2700899 : Blo 1198416 2700899 := bstep (se 1 (by rfl) ⟨2025674, by rfl⟩ : syracuseStep 2700899 = 4051349) B4051349
theorem B1799795 : Blo 1198416 1799795 := bstep (se 1 (by rfl) ⟨1349846, by rfl⟩ : syracuseStep 1799795 = 2699693) B2699693
theorem B1799825 : Blo 1198416 1799825 := bstep (se 2 (by rfl) ⟨674934, by rfl⟩ : syracuseStep 1799825 = 1349869) B1349869
theorem B1922707 : Blo 1198416 1922707 := bstep (se 1 (by rfl) ⟨1442030, by rfl⟩ : syracuseStep 1922707 = 2884061) B2884061
theorem B1799843 : Blo 1198416 1799843 := bstep (se 1 (by rfl) ⟨1349882, by rfl⟩ : syracuseStep 1799843 = 2699765) B2699765
theorem B1799873 : Blo 1198416 1799873 := bstep (se 2 (by rfl) ⟨674952, by rfl⟩ : syracuseStep 1799873 = 1349905) B1349905
theorem B1799891 : Blo 1198416 1799891 := bstep (se 1 (by rfl) ⟨1349918, by rfl⟩ : syracuseStep 1799891 = 2699837) B2699837
theorem B1349347 : Blo 1198416 1349347 := bstep (se 1 (by rfl) ⟨1012010, by rfl⟩ : syracuseStep 1349347 = 2024021) B2024021
theorem B1799921 : Blo 1198416 1799921 := bstep (se 2 (by rfl) ⟨674970, by rfl⟩ : syracuseStep 1799921 = 1349941) B1349941
theorem B1799939 : Blo 1198416 1799939 := bstep (se 1 (by rfl) ⟨1349954, by rfl⟩ : syracuseStep 1799939 = 2699909) B2699909
theorem B1799969 : Blo 1198416 1799969 := bstep (se 2 (by rfl) ⟨674988, by rfl⟩ : syracuseStep 1799969 = 1349977) B1349977
theorem B4552483 : Blo 1198416 4552483 := bstep (se 1 (by rfl) ⟨3414362, by rfl⟩ : syracuseStep 4552483 = 6828725) B6828725
theorem B1799987 : Blo 1198416 1799987 := bstep (se 1 (by rfl) ⟨1349990, by rfl⟩ : syracuseStep 1799987 = 2699981) B2699981
theorem B4323149 : Blo 1198416 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B1800017 : Blo 1198416 1800017 := bstep (se 2 (by rfl) ⟨675006, by rfl⟩ : syracuseStep 1800017 = 1350013) B1350013
theorem B1800035 : Blo 1198416 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B1349491 : Blo 1198416 1349491 := bstep (se 1 (by rfl) ⟨1012118, by rfl⟩ : syracuseStep 1349491 = 2024237) B2024237
theorem B1800065 : Blo 1198416 1800065 := bstep (se 2 (by rfl) ⟨675024, by rfl⟩ : syracuseStep 1800065 = 1350049) B1350049
theorem B1800083 : Blo 1198416 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B4044707 : Blo 1198416 4044707 := bstep (se 1 (by rfl) ⟨3033530, by rfl⟩ : syracuseStep 4044707 = 6067061) B6067061
theorem B2561969 : Blo 1198416 2561969 := bstep (se 2 (by rfl) ⟨960738, by rfl⟩ : syracuseStep 2561969 = 1921477) B1921477
theorem B1800113 : Blo 1198416 1800113 := bstep (se 2 (by rfl) ⟨675042, by rfl⟩ : syracuseStep 1800113 = 1350085) B1350085
theorem B1800131 : Blo 1198416 1800131 := bstep (se 1 (by rfl) ⟨1350098, by rfl⟩ : syracuseStep 1800131 = 2700197) B2700197
theorem B1800161 : Blo 1198416 1800161 := bstep (se 2 (by rfl) ⟨675060, by rfl⟩ : syracuseStep 1800161 = 1350121) B1350121
theorem B6068195 : Blo 1198416 6068195 := bstep (se 1 (by rfl) ⟨4551146, by rfl⟩ : syracuseStep 6068195 = 9102293) B9102293
theorem B7690211 : Blo 1198416 7690211 := bstep (se 1 (by rfl) ⟨5767658, by rfl⟩ : syracuseStep 7690211 = 11535317) B11535317
theorem B1800179 : Blo 1198416 1800179 := bstep (se 1 (by rfl) ⟨1350134, by rfl⟩ : syracuseStep 1800179 = 2700269) B2700269
theorem B1349635 : Blo 1198416 1349635 := bstep (se 1 (by rfl) ⟨1012226, by rfl⟩ : syracuseStep 1349635 = 2024453) B2024453
theorem B1800209 : Blo 1198416 1800209 := bstep (se 2 (by rfl) ⟨675078, by rfl⟩ : syracuseStep 1800209 = 1350157) B1350157
theorem B1800227 : Blo 1198416 1800227 := bstep (se 1 (by rfl) ⟨1350170, by rfl⟩ : syracuseStep 1800227 = 2700341) B2700341
theorem B4864049 : Blo 1198416 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B14784565 : Blo 1198416 14784565 := bstep (se 5 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 14784565 = 1386053) B1386053
theorem B1800257 : Blo 1198416 1800257 := bstep (se 2 (by rfl) ⟨675096, by rfl⟩ : syracuseStep 1800257 = 1350193) B1350193
theorem B1800275 : Blo 1198416 1800275 := bstep (se 1 (by rfl) ⟨1350206, by rfl⟩ : syracuseStep 1800275 = 2700413) B2700413
theorem B3037297 : Blo 1198416 3037297 := bstep (se 2 (by rfl) ⟨1138986, by rfl⟩ : syracuseStep 3037297 = 2277973) B2277973
theorem B1800305 : Blo 1198416 1800305 := bstep (se 2 (by rfl) ⟨675114, by rfl⟩ : syracuseStep 1800305 = 1350229) B1350229
theorem B1800323 : Blo 1198416 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B7297165 : Blo 1198416 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B1349779 : Blo 1198416 1349779 := bstep (se 1 (by rfl) ⟨1012334, by rfl⟩ : syracuseStep 1349779 = 2024669) B2024669
theorem B1800353 : Blo 1198416 1800353 := bstep (se 2 (by rfl) ⟨675132, by rfl⟩ : syracuseStep 1800353 = 1350265) B1350265
theorem B2431139 : Blo 1198416 2431139 := bstep (se 1 (by rfl) ⟨1823354, by rfl⟩ : syracuseStep 2431139 = 3646709) B3646709
theorem B4044977 : Blo 1198416 4044977 := bstep (se 2 (by rfl) ⟨1516866, by rfl⟩ : syracuseStep 4044977 = 3033733) B3033733
theorem B1800371 : Blo 1198416 1800371 := bstep (se 1 (by rfl) ⟨1350278, by rfl⟩ : syracuseStep 1800371 = 2700557) B2700557
theorem B1800401 : Blo 1198416 1800401 := bstep (se 2 (by rfl) ⟨675150, by rfl⟩ : syracuseStep 1800401 = 1350301) B1350301
theorem B1800419 : Blo 1198416 1800419 := bstep (se 1 (by rfl) ⟨1350314, by rfl⟩ : syracuseStep 1800419 = 2700629) B2700629
theorem B1800449 : Blo 1198416 1800449 := bstep (se 2 (by rfl) ⟨675168, by rfl⟩ : syracuseStep 1800449 = 1350337) B1350337
theorem B1800467 : Blo 1198416 1800467 := bstep (se 1 (by rfl) ⟨1350350, by rfl⟩ : syracuseStep 1800467 = 2700701) B2700701
theorem B5765411 : Blo 1198416 5765411 := bstep (se 1 (by rfl) ⟨4324058, by rfl⟩ : syracuseStep 5765411 = 8648117) B8648117
theorem B1349923 : Blo 1198416 1349923 := bstep (se 1 (by rfl) ⟨1012442, by rfl⟩ : syracuseStep 1349923 = 2024885) B2024885
theorem B5126449 : Blo 1198416 5126449 := bstep (se 2 (by rfl) ⟨1922418, by rfl⟩ : syracuseStep 5126449 = 3844837) B3844837
theorem B1800497 : Blo 1198416 1800497 := bstep (se 2 (by rfl) ⟨675186, by rfl⟩ : syracuseStep 1800497 = 1350373) B1350373
theorem B1800515 : Blo 1198416 1800515 := bstep (se 1 (by rfl) ⟨1350386, by rfl⟩ : syracuseStep 1800515 = 2700773) B2700773
theorem B1800545 : Blo 1198416 1800545 := bstep (se 2 (by rfl) ⟨675204, by rfl⟩ : syracuseStep 1800545 = 1350409) B1350409
theorem B3840365 : Blo 1198416 3840365 := bstep (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) B1440137
theorem B1800563 : Blo 1198416 1800563 := bstep (se 1 (by rfl) ⟨1350422, by rfl⟩ : syracuseStep 1800563 = 2700845) B2700845
theorem B2161027 : Blo 1198416 2161027 := bstep (se 1 (by rfl) ⟨1620770, by rfl⟩ : syracuseStep 2161027 = 3241541) B3241541
theorem B3037571 : Blo 1198416 3037571 := bstep (se 1 (by rfl) ⟨2278178, by rfl⟩ : syracuseStep 3037571 = 4556357) B4556357
theorem B1800593 : Blo 1198416 1800593 := bstep (se 2 (by rfl) ⟨675222, by rfl⟩ : syracuseStep 1800593 = 1350445) B1350445
theorem B1620371 : Blo 1198416 1620371 := bstep (se 1 (by rfl) ⟨1215278, by rfl⟩ : syracuseStep 1620371 = 2430557) B2430557
theorem B1800611 : Blo 1198416 1800611 := bstep (se 1 (by rfl) ⟨1350458, by rfl⟩ : syracuseStep 1800611 = 2700917) B2700917
theorem B1350067 : Blo 1198416 1350067 := bstep (se 1 (by rfl) ⟨1012550, by rfl⟩ : syracuseStep 1350067 = 2025101) B2025101
theorem B16407011 : Blo 1198416 16407011 := bstep (se 1 (by rfl) ⟨12305258, by rfl⟩ : syracuseStep 16407011 = 24610517) B24610517
theorem B3840493 : Blo 1198416 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B2595331 : Blo 1198416 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B7494149 : Blo 1198416 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B3414545 : Blo 1198416 3414545 := bstep (se 2 (by rfl) ⟨1280454, by rfl⟩ : syracuseStep 3414545 = 2560909) B2560909
theorem B2431505 : Blo 1198416 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B2161201 : Blo 1198416 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B3037763 : Blo 1198416 3037763 := bstep (se 1 (by rfl) ⟨2278322, by rfl⟩ : syracuseStep 3037763 = 4556645) B4556645
theorem B1350211 : Blo 1198416 1350211 := bstep (se 1 (by rfl) ⟨1012658, by rfl⟩ : syracuseStep 1350211 = 2025317) B2025317
theorem B7289477 : Blo 1198416 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B6077105 : Blo 1198416 6077105 := bstep (se 2 (by rfl) ⟨2278914, by rfl⟩ : syracuseStep 6077105 = 4557829) B4557829
theorem B1948355 : Blo 1198416 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B13662917 : Blo 1198416 13662917 := bstep (se 4 (by rfl) ⟨1280898, by rfl⟩ : syracuseStep 13662917 = 2561797) B2561797
theorem B4045517 : Blo 1198416 4045517 := bstep (se 3 (by rfl) ⟨758534, by rfl⟩ : syracuseStep 4045517 = 1517069) B1517069
theorem B1350355 : Blo 1198416 1350355 := bstep (se 1 (by rfl) ⟨1012766, by rfl⟩ : syracuseStep 1350355 = 2025533) B2025533
theorem B3840749 : Blo 1198416 3840749 := bstep (se 3 (by rfl) ⟨720140, by rfl⟩ : syracuseStep 3840749 = 1440281) B1440281
theorem B12966641 : Blo 1198416 12966641 := bstep (se 2 (by rfl) ⟨4862490, by rfl⟩ : syracuseStep 12966641 = 9724981) B9724981
theorem B4045571 : Blo 1198416 4045571 := bstep (se 1 (by rfl) ⟨3034178, by rfl⟩ : syracuseStep 4045571 = 6068357) B6068357
theorem B6069005 : Blo 1198416 6069005 := bstep (se 3 (by rfl) ⟨1137938, by rfl⟩ : syracuseStep 6069005 = 2275877) B2275877
theorem B2276113 : Blo 1198416 2276113 := bstep (se 2 (by rfl) ⟨853542, by rfl⟩ : syracuseStep 2276113 = 1707085) B1707085
theorem B2022401 : Blo 1198416 2022401 := bstep (se 2 (by rfl) ⟨758400, by rfl⟩ : syracuseStep 2022401 = 1516801) B1516801
theorem B4045841 : Blo 1198416 4045841 := bstep (se 2 (by rfl) ⟨1517190, by rfl⟩ : syracuseStep 4045841 = 3034381) B3034381
theorem B2022529 : Blo 1198416 2022529 := bstep (se 2 (by rfl) ⟨758448, by rfl⟩ : syracuseStep 2022529 = 1516897) B1516897
theorem B2022563 : Blo 1198416 2022563 := bstep (se 1 (by rfl) ⟨1516922, by rfl⟩ : syracuseStep 2022563 = 3033845) B3033845
theorem B2276515 : Blo 1198416 2276515 := bstep (se 1 (by rfl) ⟨1707386, by rfl⟩ : syracuseStep 2276515 = 3414773) B3414773
theorem B2563267 : Blo 1198416 2563267 := bstep (se 1 (by rfl) ⟨1922450, by rfl⟩ : syracuseStep 2563267 = 3844901) B3844901
theorem B2276561 : Blo 1198416 2276561 := bstep (se 2 (by rfl) ⟨853710, by rfl⟩ : syracuseStep 2276561 = 1707421) B1707421
theorem B13671665 : Blo 1198416 13671665 := bstep (se 2 (by rfl) ⟨5126874, by rfl⟩ : syracuseStep 13671665 = 10253749) B10253749
theorem B2022691 : Blo 1198416 2022691 := bstep (se 1 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 2022691 = 3034037) B3034037
theorem B2596195 : Blo 1198416 2596195 := bstep (se 1 (by rfl) ⟨1947146, by rfl⟩ : syracuseStep 2596195 = 3894293) B3894293
theorem B2022833 : Blo 1198416 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B2276849 : Blo 1198416 2276849 := bstep (se 2 (by rfl) ⟨853818, by rfl⟩ : syracuseStep 2276849 = 1707637) B1707637
theorem B4046381 : Blo 1198416 4046381 := bstep (se 3 (by rfl) ⟨758696, by rfl⟩ : syracuseStep 4046381 = 1517393) B1517393
theorem B2022961 : Blo 1198416 2022961 := bstep (se 2 (by rfl) ⟨758610, by rfl⟩ : syracuseStep 2022961 = 1517221) B1517221
theorem B2022995 : Blo 1198416 2022995 := bstep (se 1 (by rfl) ⟨1517246, by rfl⟩ : syracuseStep 2022995 = 3034493) B3034493
theorem B4046435 : Blo 1198416 4046435 := bstep (se 1 (by rfl) ⟨3034826, by rfl⟩ : syracuseStep 4046435 = 6069653) B6069653
theorem B7397027 : Blo 1198416 7397027 := bstep (se 1 (by rfl) ⟨5547770, by rfl⟩ : syracuseStep 7397027 = 11095541) B11095541
theorem B3464909 : Blo 1198416 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B3079889 : Blo 1198416 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B2023123 : Blo 1198416 2023123 := bstep (se 1 (by rfl) ⟨1517342, by rfl⟩ : syracuseStep 2023123 = 3034685) B3034685
theorem B6479621 : Blo 1198416 6479621 := bstep (se 4 (by rfl) ⟨607464, by rfl⟩ : syracuseStep 6479621 = 1214929) B1214929
theorem B2162513 : Blo 1198416 2162513 := bstep (se 2 (by rfl) ⟨810942, by rfl⟩ : syracuseStep 2162513 = 1621885) B1621885
theorem B2023265 : Blo 1198416 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B4046705 : Blo 1198416 4046705 := bstep (se 2 (by rfl) ⟨1517514, by rfl⟩ : syracuseStep 4046705 = 3035029) B3035029
theorem B1621873 : Blo 1198416 1621873 := bstep (se 2 (by rfl) ⟨608202, by rfl⟩ : syracuseStep 1621873 = 1216405) B1216405
theorem B3416003 : Blo 1198416 3416003 := bstep (se 1 (by rfl) ⟨2562002, by rfl⟩ : syracuseStep 3416003 = 5124005) B5124005
theorem B2465731 : Blo 1198416 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B4554701 : Blo 1198416 4554701 := bstep (se 3 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 4554701 = 1708013) B1708013
theorem B2023393 : Blo 1198416 2023393 := bstep (se 2 (by rfl) ⟨758772, by rfl⟩ : syracuseStep 2023393 = 1517545) B1517545
theorem B2023447 : Blo 1198416 2023447 := bstep (se 1 (by rfl) ⟨1517585, by rfl⟩ : syracuseStep 2023447 = 3035171) B3035171
theorem B19447883 : Blo 1198416 19447883 := bstep (se 1 (by rfl) ⟨14585912, by rfl⟩ : syracuseStep 19447883 = 29171825) B29171825
theorem B18473111 : Blo 1198416 18473111 := bstep (se 1 (by rfl) ⟨13854833, by rfl⟩ : syracuseStep 18473111 = 27709667) B27709667
theorem B5767469 : Blo 1198416 5767469 := bstep (se 3 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 5767469 = 2162801) B2162801
theorem B3948851 : Blo 1198416 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B3416413 : Blo 1198416 3416413 := bstep (se 3 (by rfl) ⟨640577, by rfl⟩ : syracuseStep 3416413 = 1281155) B1281155
theorem B2433395 : Blo 1198416 2433395 := bstep (se 1 (by rfl) ⟨1825046, by rfl⟩ : syracuseStep 2433395 = 3650093) B3650093
theorem B5120435 : Blo 1198416 5120435 := bstep (se 1 (by rfl) ⟨3840326, by rfl⟩ : syracuseStep 5120435 = 7680653) B7680653
theorem B4555187 : Blo 1198416 4555187 := bstep (se 1 (by rfl) ⟨3416390, by rfl⟩ : syracuseStep 4555187 = 6832781) B6832781
theorem B2277875 : Blo 1198416 2277875 := bstep (se 1 (by rfl) ⟨1708406, by rfl⟩ : syracuseStep 2277875 = 3416813) B3416813
theorem B5120587 : Blo 1198416 5120587 := bstep (se 1 (by rfl) ⟨3840440, by rfl⟩ : syracuseStep 5120587 = 7680881) B7680881
theorem B2024075 : Blo 1198416 2024075 := bstep (se 1 (by rfl) ⟨1518056, by rfl⟩ : syracuseStep 2024075 = 3036113) B3036113
theorem B5120657 : Blo 1198416 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B3416755 : Blo 1198416 3416755 := bstep (se 1 (by rfl) ⟨2562566, by rfl⟩ : syracuseStep 3416755 = 5125133) B5125133
theorem B2024203 : Blo 1198416 2024203 := bstep (se 1 (by rfl) ⟨1518152, by rfl⟩ : syracuseStep 2024203 = 3036305) B3036305
theorem B2736985 : Blo 1198416 2736985 := bstep (se 2 (by rfl) ⟨1026369, by rfl⟩ : syracuseStep 2736985 = 2052739) B2052739
theorem B2024345 : Blo 1198416 2024345 := bstep (se 2 (by rfl) ⟨759129, by rfl⟩ : syracuseStep 2024345 = 1518259) B1518259
theorem B5473241 : Blo 1198416 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B2278361 : Blo 1198416 2278361 := bstep (se 2 (by rfl) ⟨854385, by rfl⟩ : syracuseStep 2278361 = 1708771) B1708771
theorem B4326365 : Blo 1198416 4326365 := bstep (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) B1622387
theorem B2024473 : Blo 1198416 2024473 := bstep (se 2 (by rfl) ⟨759177, by rfl⟩ : syracuseStep 2024473 = 1518355) B1518355
theorem B10945601 : Blo 1198416 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B4047947 : Blo 1198416 4047947 := bstep (se 1 (by rfl) ⟨3035960, by rfl⟩ : syracuseStep 4047947 = 6071921) B6071921
theorem B8004701 : Blo 1198416 8004701 := bstep (se 3 (by rfl) ⟨1500881, by rfl⟩ : syracuseStep 8004701 = 3001763) B3001763
theorem B2696471 : Blo 1198416 2696471 := bstep (se 1 (by rfl) ⟨2022353, by rfl⟩ : syracuseStep 2696471 = 4044707) B4044707
theorem B6071597 : Blo 1198416 6071597 := bstep (se 3 (by rfl) ⟨1138424, by rfl⟩ : syracuseStep 6071597 = 2276849) B2276849
theorem B4048217 : Blo 1198416 4048217 := bstep (se 2 (by rfl) ⟨1518081, by rfl⟩ : syracuseStep 4048217 = 3036163) B3036163
theorem B15582581 : Blo 1198416 15582581 := bstep (se 5 (by rfl) ⟨730433, by rfl⟩ : syracuseStep 15582581 = 1460867) B1460867
theorem B10249649 : Blo 1198416 10249649 := bstep (se 2 (by rfl) ⟨3843618, by rfl⟩ : syracuseStep 10249649 = 7687237) B7687237
theorem B2696651 : Blo 1198416 2696651 := bstep (se 1 (by rfl) ⟨2022488, by rfl⟩ : syracuseStep 2696651 = 4044977) B4044977
theorem B2696705 : Blo 1198416 2696705 := bstep (se 2 (by rfl) ⟨1011264, by rfl⟩ : syracuseStep 2696705 = 2022529) B2022529
theorem B3843607 : Blo 1198416 3843607 := bstep (se 1 (by rfl) ⟨2882705, by rfl⟩ : syracuseStep 3843607 = 5765411) B5765411
theorem B2025047 : Blo 1198416 2025047 := bstep (se 1 (by rfl) ⟨1518785, by rfl⟩ : syracuseStep 2025047 = 3037571) B3037571
theorem B3417689 : Blo 1198416 3417689 := bstep (se 2 (by rfl) ⟨1281633, by rfl⟩ : syracuseStep 3417689 = 2563267) B2563267
theorem B10938007 : Blo 1198416 10938007 := bstep (se 1 (by rfl) ⟨8203505, by rfl⟩ : syracuseStep 10938007 = 16407011) B16407011
theorem B1459927 : Blo 1198416 1459927 := bstep (se 1 (by rfl) ⟨1094945, by rfl⟩ : syracuseStep 1459927 = 2189891) B2189891
theorem B2696921 : Blo 1198416 2696921 := bstep (se 2 (by rfl) ⟨1011345, by rfl⟩ : syracuseStep 2696921 = 2022691) B2022691
theorem B2025175 : Blo 1198416 2025175 := bstep (se 1 (by rfl) ⟨1518881, by rfl⟩ : syracuseStep 2025175 = 3037763) B3037763
theorem B4859651 : Blo 1198416 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B2697011 : Blo 1198416 2697011 := bstep (se 1 (by rfl) ⟨2022758, by rfl⟩ : syracuseStep 2697011 = 4045517) B4045517
theorem B8644427 : Blo 1198416 8644427 := bstep (se 1 (by rfl) ⟨6483320, by rfl⟩ : syracuseStep 8644427 = 12966641) B12966641
theorem B2697047 : Blo 1198416 2697047 := bstep (se 1 (by rfl) ⟨2022785, by rfl⟩ : syracuseStep 2697047 = 4045571) B4045571
theorem B13846373 : Blo 1198416 13846373 := bstep (se 4 (by rfl) ⟨1298097, by rfl⟩ : syracuseStep 13846373 = 2596195) B2596195
theorem B4556675 : Blo 1198416 4556675 := bstep (se 1 (by rfl) ⟨3417506, by rfl⟩ : syracuseStep 4556675 = 6835013) B6835013
theorem B9734093 : Blo 1198416 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B2697227 : Blo 1198416 2697227 := bstep (se 1 (by rfl) ⟨2022920, by rfl⟩ : syracuseStep 2697227 = 4045841) B4045841
theorem B4048919 : Blo 1198416 4048919 := bstep (se 1 (by rfl) ⟨3036689, by rfl⟩ : syracuseStep 4048919 = 6073379) B6073379
theorem B2697281 : Blo 1198416 2697281 := bstep (se 2 (by rfl) ⟨1011480, by rfl⟩ : syracuseStep 2697281 = 2022961) B2022961
theorem B10250333 : Blo 1198416 10250333 := bstep (se 3 (by rfl) ⟨1921937, by rfl⟩ : syracuseStep 10250333 = 3843875) B3843875
theorem B1517707 : Blo 1198416 1517707 := bstep (se 1 (by rfl) ⟨1138280, by rfl⟩ : syracuseStep 1517707 = 2276561) B2276561
theorem B2697497 : Blo 1198416 2697497 := bstep (se 2 (by rfl) ⟨1011561, by rfl⟩ : syracuseStep 2697497 = 2023123) B2023123
theorem B5122349 : Blo 1198416 5122349 := bstep (se 3 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 5122349 = 1920881) B1920881
theorem B4557131 : Blo 1198416 4557131 := bstep (se 1 (by rfl) ⟨3417848, by rfl⟩ : syracuseStep 4557131 = 6835697) B6835697
theorem B1198423 : Blo 1198416 1198423 := bstep (se 1 (by rfl) ⟨898817, by rfl⟩ : syracuseStep 1198423 = 1797635) B1797635
theorem B13150565 : Blo 1198416 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B1198443 : Blo 1198416 1198443 := bstep (se 1 (by rfl) ⟨898832, by rfl⟩ : syracuseStep 1198443 = 1797665) B1797665
theorem B2697587 : Blo 1198416 2697587 := bstep (se 1 (by rfl) ⟨2023190, by rfl⟩ : syracuseStep 2697587 = 4046381) B4046381
theorem B1198455 : Blo 1198416 1198455 := bstep (se 1 (by rfl) ⟨898841, by rfl⟩ : syracuseStep 1198455 = 1797683) B1797683
theorem B1198475 : Blo 1198416 1198475 := bstep (se 1 (by rfl) ⟨898856, by rfl⟩ : syracuseStep 1198475 = 1797713) B1797713
theorem B1280395 : Blo 1198416 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B1198487 : Blo 1198416 1198487 := bstep (se 1 (by rfl) ⟨898865, by rfl⟩ : syracuseStep 1198487 = 1797731) B1797731
theorem B2697623 : Blo 1198416 2697623 := bstep (se 1 (by rfl) ⟨2023217, by rfl⟩ : syracuseStep 2697623 = 4046435) B4046435
theorem B1198507 : Blo 1198416 1198507 := bstep (se 1 (by rfl) ⟨898880, by rfl⟩ : syracuseStep 1198507 = 1797761) B1797761
theorem B1198519 : Blo 1198416 1198519 := bstep (se 1 (by rfl) ⟨898889, by rfl⟩ : syracuseStep 1198519 = 1797779) B1797779
theorem B1198539 : Blo 1198416 1198539 := bstep (se 1 (by rfl) ⟨898904, by rfl⟩ : syracuseStep 1198539 = 1797809) B1797809
theorem B9112013 : Blo 1198416 9112013 := bstep (se 3 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 9112013 = 3417005) B3417005
theorem B1198551 : Blo 1198416 1198551 := bstep (se 1 (by rfl) ⟨898913, by rfl⟩ : syracuseStep 1198551 = 1797827) B1797827
theorem B1198571 : Blo 1198416 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B1198583 : Blo 1198416 1198583 := bstep (se 1 (by rfl) ⟨898937, by rfl⟩ : syracuseStep 1198583 = 1797875) B1797875
theorem B4319747 : Blo 1198416 4319747 := bstep (se 1 (by rfl) ⟨3239810, by rfl⟩ : syracuseStep 4319747 = 6479621) B6479621
theorem B1198603 : Blo 1198416 1198603 := bstep (se 1 (by rfl) ⟨898952, by rfl⟩ : syracuseStep 1198603 = 1797905) B1797905
theorem B4557329 : Blo 1198416 4557329 := bstep (se 2 (by rfl) ⟨1708998, by rfl⟩ : syracuseStep 4557329 = 3417997) B3417997
theorem B1198615 : Blo 1198416 1198615 := bstep (se 1 (by rfl) ⟨898961, by rfl⟩ : syracuseStep 1198615 = 1797923) B1797923
theorem B1706521 : Blo 1198416 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B1198635 : Blo 1198416 1198635 := bstep (se 1 (by rfl) ⟨898976, by rfl⟩ : syracuseStep 1198635 = 1797953) B1797953
theorem B4049459 : Blo 1198416 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B1198647 : Blo 1198416 1198647 := bstep (se 1 (by rfl) ⟨898985, by rfl⟩ : syracuseStep 1198647 = 1797971) B1797971
theorem B1198667 : Blo 1198416 1198667 := bstep (se 1 (by rfl) ⟨899000, by rfl⟩ : syracuseStep 1198667 = 1798001) B1798001
theorem B2697803 : Blo 1198416 2697803 := bstep (se 1 (by rfl) ⟨2023352, by rfl⟩ : syracuseStep 2697803 = 4046705) B4046705
theorem B1198679 : Blo 1198416 1198679 := bstep (se 1 (by rfl) ⟨899009, by rfl⟩ : syracuseStep 1198679 = 1798019) B1798019
theorem B1198699 : Blo 1198416 1198699 := bstep (se 1 (by rfl) ⟨899024, by rfl⟩ : syracuseStep 1198699 = 1798049) B1798049
theorem B1198711 : Blo 1198416 1198711 := bstep (se 1 (by rfl) ⟨899033, by rfl⟩ : syracuseStep 1198711 = 1798067) B1798067
theorem B2697857 : Blo 1198416 2697857 := bstep (se 2 (by rfl) ⟨1011696, by rfl⟩ : syracuseStep 2697857 = 2023393) B2023393
theorem B1198731 : Blo 1198416 1198731 := bstep (se 1 (by rfl) ⟨899048, by rfl⟩ : syracuseStep 1198731 = 1798097) B1798097
theorem B1198743 : Blo 1198416 1198743 := bstep (se 1 (by rfl) ⟨899057, by rfl⟩ : syracuseStep 1198743 = 1798115) B1798115
theorem B1198763 : Blo 1198416 1198763 := bstep (se 1 (by rfl) ⟨899072, by rfl⟩ : syracuseStep 1198763 = 1798145) B1798145
theorem B1198775 : Blo 1198416 1198775 := bstep (se 1 (by rfl) ⟨899081, by rfl⟩ : syracuseStep 1198775 = 1798163) B1798163
theorem B1198795 : Blo 1198416 1198795 := bstep (se 1 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 1198795 = 1798193) B1798193
theorem B1198807 : Blo 1198416 1198807 := bstep (se 1 (by rfl) ⟨899105, by rfl⟩ : syracuseStep 1198807 = 1798211) B1798211
theorem B1198827 : Blo 1198416 1198827 := bstep (se 1 (by rfl) ⟨899120, by rfl⟩ : syracuseStep 1198827 = 1798241) B1798241
theorem B19712753 : Blo 1198416 19712753 := bstep (se 2 (by rfl) ⟨7392282, by rfl⟩ : syracuseStep 19712753 = 14784565) B14784565
theorem B1198839 : Blo 1198416 1198839 := bstep (se 1 (by rfl) ⟨899129, by rfl⟩ : syracuseStep 1198839 = 1798259) B1798259
theorem B1198859 : Blo 1198416 1198859 := bstep (se 1 (by rfl) ⟨899144, by rfl⟩ : syracuseStep 1198859 = 1798289) B1798289
theorem B1198871 : Blo 1198416 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B1198891 : Blo 1198416 1198891 := bstep (se 1 (by rfl) ⟨899168, by rfl⟩ : syracuseStep 1198891 = 1798337) B1798337
theorem B1198903 : Blo 1198416 1198903 := bstep (se 1 (by rfl) ⟨899177, by rfl⟩ : syracuseStep 1198903 = 1798355) B1798355
theorem B4049729 : Blo 1198416 4049729 := bstep (se 2 (by rfl) ⟨1518648, by rfl⟩ : syracuseStep 4049729 = 3037297) B3037297
theorem B23071553 : Blo 1198416 23071553 := bstep (se 2 (by rfl) ⟨8651832, by rfl⟩ : syracuseStep 23071553 = 17303665) B17303665
theorem B1198923 : Blo 1198416 1198923 := bstep (se 1 (by rfl) ⟨899192, by rfl⟩ : syracuseStep 1198923 = 1798385) B1798385
theorem B1198935 : Blo 1198416 1198935 := bstep (se 1 (by rfl) ⟨899201, by rfl⟩ : syracuseStep 1198935 = 1798403) B1798403
theorem B1215319 : Blo 1198416 1215319 := bstep (se 1 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 1215319 = 1822979) B1822979
theorem B2698073 : Blo 1198416 2698073 := bstep (se 2 (by rfl) ⟨1011777, by rfl⟩ : syracuseStep 2698073 = 2023555) B2023555
theorem B1198955 : Blo 1198416 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B1198967 : Blo 1198416 1198967 := bstep (se 1 (by rfl) ⟨899225, by rfl⟩ : syracuseStep 1198967 = 1798451) B1798451
theorem B1198987 : Blo 1198416 1198987 := bstep (se 1 (by rfl) ⟨899240, by rfl⟩ : syracuseStep 1198987 = 1798481) B1798481
theorem B3034007 : Blo 1198416 3034007 := bstep (se 1 (by rfl) ⟨2275505, by rfl⟩ : syracuseStep 3034007 = 4551011) B4551011
theorem B1198999 : Blo 1198416 1198999 := bstep (se 1 (by rfl) ⟨899249, by rfl⟩ : syracuseStep 1198999 = 1798499) B1798499
theorem B1199019 : Blo 1198416 1199019 := bstep (se 1 (by rfl) ⟨899264, by rfl⟩ : syracuseStep 1199019 = 1798529) B1798529
theorem B31558577 : Blo 1198416 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B2698163 : Blo 1198416 2698163 := bstep (se 1 (by rfl) ⟨2023622, by rfl⟩ : syracuseStep 2698163 = 4047245) B4047245
theorem B1199031 : Blo 1198416 1199031 := bstep (se 1 (by rfl) ⟨899273, by rfl⟩ : syracuseStep 1199031 = 1798547) B1798547
theorem B9112499 : Blo 1198416 9112499 := bstep (se 1 (by rfl) ⟨6834374, by rfl⟩ : syracuseStep 9112499 = 13668749) B13668749
theorem B1199051 : Blo 1198416 1199051 := bstep (se 1 (by rfl) ⟨899288, by rfl⟩ : syracuseStep 1199051 = 1798577) B1798577
theorem B1199063 : Blo 1198416 1199063 := bstep (se 1 (by rfl) ⟨899297, by rfl⟩ : syracuseStep 1199063 = 1798595) B1798595
theorem B2698199 : Blo 1198416 2698199 := bstep (se 1 (by rfl) ⟨2023649, by rfl⟩ : syracuseStep 2698199 = 4047299) B4047299
theorem B5123033 : Blo 1198416 5123033 := bstep (se 2 (by rfl) ⟨1921137, by rfl⟩ : syracuseStep 5123033 = 3842275) B3842275
theorem B1199083 : Blo 1198416 1199083 := bstep (se 1 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 1199083 = 1798625) B1798625
theorem B1199095 : Blo 1198416 1199095 := bstep (se 1 (by rfl) ⟨899321, by rfl⟩ : syracuseStep 1199095 = 1798643) B1798643
theorem B1199115 : Blo 1198416 1199115 := bstep (se 1 (by rfl) ⟨899336, by rfl⟩ : syracuseStep 1199115 = 1798673) B1798673
theorem B1199127 : Blo 1198416 1199127 := bstep (se 1 (by rfl) ⟨899345, by rfl⟩ : syracuseStep 1199127 = 1798691) B1798691
theorem B1199147 : Blo 1198416 1199147 := bstep (se 1 (by rfl) ⟨899360, by rfl⟩ : syracuseStep 1199147 = 1798721) B1798721
theorem B1199159 : Blo 1198416 1199159 := bstep (se 1 (by rfl) ⟨899369, by rfl⟩ : syracuseStep 1199159 = 1798739) B1798739
theorem B6835265 : Blo 1198416 6835265 := bstep (se 2 (by rfl) ⟨2563224, by rfl⟩ : syracuseStep 6835265 = 5126449) B5126449
theorem B5762123 : Blo 1198416 5762123 := bstep (se 1 (by rfl) ⟨4321592, by rfl⟩ : syracuseStep 5762123 = 8643185) B8643185
theorem B1199179 : Blo 1198416 1199179 := bstep (se 1 (by rfl) ⟨899384, by rfl⟩ : syracuseStep 1199179 = 1798769) B1798769
theorem B1199191 : Blo 1198416 1199191 := bstep (se 1 (by rfl) ⟨899393, by rfl⟩ : syracuseStep 1199191 = 1798787) B1798787
theorem B1518679 : Blo 1198416 1518679 := bstep (se 1 (by rfl) ⟨1139009, by rfl⟩ : syracuseStep 1518679 = 2278019) B2278019
theorem B1199211 : Blo 1198416 1199211 := bstep (se 1 (by rfl) ⟨899408, by rfl⟩ : syracuseStep 1199211 = 1798817) B1798817
theorem B1199223 : Blo 1198416 1199223 := bstep (se 1 (by rfl) ⟨899417, by rfl⟩ : syracuseStep 1199223 = 1798835) B1798835
theorem B1199243 : Blo 1198416 1199243 := bstep (se 1 (by rfl) ⟨899432, by rfl⟩ : syracuseStep 1199243 = 1798865) B1798865
theorem B2698379 : Blo 1198416 2698379 := bstep (se 1 (by rfl) ⟨2023784, by rfl⟩ : syracuseStep 2698379 = 4047569) B4047569
theorem B4861079 : Blo 1198416 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B1199255 : Blo 1198416 1199255 := bstep (se 1 (by rfl) ⟨899441, by rfl⟩ : syracuseStep 1199255 = 1798883) B1798883
theorem B1199275 : Blo 1198416 1199275 := bstep (se 1 (by rfl) ⟨899456, by rfl⟩ : syracuseStep 1199275 = 1798913) B1798913
theorem B1215659 : Blo 1198416 1215659 := bstep (se 1 (by rfl) ⟨911744, by rfl⟩ : syracuseStep 1215659 = 1823489) B1823489
theorem B1199287 : Blo 1198416 1199287 := bstep (se 1 (by rfl) ⟨899465, by rfl⟩ : syracuseStep 1199287 = 1798931) B1798931
theorem B2698433 : Blo 1198416 2698433 := bstep (se 2 (by rfl) ⟨1011912, by rfl⟩ : syracuseStep 2698433 = 2023825) B2023825
theorem B1199307 : Blo 1198416 1199307 := bstep (se 1 (by rfl) ⟨899480, by rfl⟩ : syracuseStep 1199307 = 1798961) B1798961
theorem B1199319 : Blo 1198416 1199319 := bstep (se 1 (by rfl) ⟨899489, by rfl⟩ : syracuseStep 1199319 = 1798979) B1798979
theorem B1199339 : Blo 1198416 1199339 := bstep (se 1 (by rfl) ⟨899504, by rfl⟩ : syracuseStep 1199339 = 1799009) B1799009
theorem B1199351 : Blo 1198416 1199351 := bstep (se 1 (by rfl) ⟨899513, by rfl⟩ : syracuseStep 1199351 = 1799027) B1799027
theorem B1199371 : Blo 1198416 1199371 := bstep (se 1 (by rfl) ⟨899528, by rfl⟩ : syracuseStep 1199371 = 1799057) B1799057
theorem B1199383 : Blo 1198416 1199383 := bstep (se 1 (by rfl) ⟨899537, by rfl⟩ : syracuseStep 1199383 = 1799075) B1799075
theorem B1199403 : Blo 1198416 1199403 := bstep (se 1 (by rfl) ⟨899552, by rfl⟩ : syracuseStep 1199403 = 1799105) B1799105
theorem B1199415 : Blo 1198416 1199415 := bstep (se 1 (by rfl) ⟨899561, by rfl⟩ : syracuseStep 1199415 = 1799123) B1799123
theorem B1199435 : Blo 1198416 1199435 := bstep (se 1 (by rfl) ⟨899576, by rfl⟩ : syracuseStep 1199435 = 1799153) B1799153
theorem B1199447 : Blo 1198416 1199447 := bstep (se 1 (by rfl) ⟨899585, by rfl⟩ : syracuseStep 1199447 = 1799171) B1799171
theorem B3845465 : Blo 1198416 3845465 := bstep (se 2 (by rfl) ⟨1442049, by rfl⟩ : syracuseStep 3845465 = 2884099) B2884099
theorem B4050269 : Blo 1198416 4050269 := bstep (se 3 (by rfl) ⟨759425, by rfl⟩ : syracuseStep 4050269 = 1518851) B1518851
theorem B1199467 : Blo 1198416 1199467 := bstep (se 1 (by rfl) ⟨899600, by rfl⟩ : syracuseStep 1199467 = 1799201) B1799201
theorem B1199479 : Blo 1198416 1199479 := bstep (se 1 (by rfl) ⟨899609, by rfl⟩ : syracuseStep 1199479 = 1799219) B1799219
theorem B1199499 : Blo 1198416 1199499 := bstep (se 1 (by rfl) ⟨899624, by rfl⟩ : syracuseStep 1199499 = 1799249) B1799249
theorem B1199511 : Blo 1198416 1199511 := bstep (se 1 (by rfl) ⟨899633, by rfl⟩ : syracuseStep 1199511 = 1799267) B1799267
theorem B2698649 : Blo 1198416 2698649 := bstep (se 2 (by rfl) ⟨1011993, by rfl⟩ : syracuseStep 2698649 = 2023987) B2023987
theorem B1199531 : Blo 1198416 1199531 := bstep (se 1 (by rfl) ⟨899648, by rfl⟩ : syracuseStep 1199531 = 1799297) B1799297
theorem B19451315 : Blo 1198416 19451315 := bstep (se 1 (by rfl) ⟨14588486, by rfl⟩ : syracuseStep 19451315 = 29176973) B29176973
theorem B1199543 : Blo 1198416 1199543 := bstep (se 1 (by rfl) ⟨899657, by rfl⟩ : syracuseStep 1199543 = 1799315) B1799315
theorem B4320715 : Blo 1198416 4320715 := bstep (se 1 (by rfl) ⟨3240536, by rfl⟩ : syracuseStep 4320715 = 6481073) B6481073
theorem B1199563 : Blo 1198416 1199563 := bstep (se 1 (by rfl) ⟨899672, by rfl⟩ : syracuseStep 1199563 = 1799345) B1799345
theorem B1199575 : Blo 1198416 1199575 := bstep (se 1 (by rfl) ⟨899681, by rfl⟩ : syracuseStep 1199575 = 1799363) B1799363
theorem B1199595 : Blo 1198416 1199595 := bstep (se 1 (by rfl) ⟨899696, by rfl⟩ : syracuseStep 1199595 = 1799393) B1799393
theorem B2698739 : Blo 1198416 2698739 := bstep (se 1 (by rfl) ⟨2024054, by rfl⟩ : syracuseStep 2698739 = 4048109) B4048109
theorem B1199607 : Blo 1198416 1199607 := bstep (se 1 (by rfl) ⟨899705, by rfl⟩ : syracuseStep 1199607 = 1799411) B1799411
theorem B1199627 : Blo 1198416 1199627 := bstep (se 1 (by rfl) ⟨899720, by rfl⟩ : syracuseStep 1199627 = 1799441) B1799441
theorem B2698775 : Blo 1198416 2698775 := bstep (se 1 (by rfl) ⟨2024081, by rfl⟩ : syracuseStep 2698775 = 4048163) B4048163
theorem B1199639 : Blo 1198416 1199639 := bstep (se 1 (by rfl) ⟨899729, by rfl⟩ : syracuseStep 1199639 = 1799459) B1799459
theorem B1199659 : Blo 1198416 1199659 := bstep (se 1 (by rfl) ⟨899744, by rfl⟩ : syracuseStep 1199659 = 1799489) B1799489
theorem B1199671 : Blo 1198416 1199671 := bstep (se 1 (by rfl) ⟨899753, by rfl⟩ : syracuseStep 1199671 = 1799507) B1799507
theorem B1797707 : Blo 1198416 1797707 := bstep (se 1 (by rfl) ⟨1348280, by rfl⟩ : syracuseStep 1797707 = 2696561) B2696561
theorem B3075659 : Blo 1198416 3075659 := bstep (se 1 (by rfl) ⟨2306744, by rfl⟩ : syracuseStep 3075659 = 4613489) B4613489
theorem B2051659 : Blo 1198416 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B1199691 : Blo 1198416 1199691 := bstep (se 1 (by rfl) ⟨899768, by rfl⟩ : syracuseStep 1199691 = 1799537) B1799537
theorem B1797719 : Blo 1198416 1797719 := bstep (se 1 (by rfl) ⟨1348289, by rfl⟩ : syracuseStep 1797719 = 2696579) B2696579
theorem B1199703 : Blo 1198416 1199703 := bstep (se 1 (by rfl) ⟨899777, by rfl⟩ : syracuseStep 1199703 = 1799555) B1799555
theorem B1199723 : Blo 1198416 1199723 := bstep (se 1 (by rfl) ⟨899792, by rfl⟩ : syracuseStep 1199723 = 1799585) B1799585
theorem B1199735 : Blo 1198416 1199735 := bstep (se 1 (by rfl) ⟨899801, by rfl⟩ : syracuseStep 1199735 = 1799603) B1799603
theorem B1199755 : Blo 1198416 1199755 := bstep (se 1 (by rfl) ⟨899816, by rfl⟩ : syracuseStep 1199755 = 1799633) B1799633
theorem B1199767 : Blo 1198416 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B1797785 : Blo 1198416 1797785 := bstep (se 2 (by rfl) ⟨674169, by rfl⟩ : syracuseStep 1797785 = 1348339) B1348339
theorem B1199787 : Blo 1198416 1199787 := bstep (se 1 (by rfl) ⟨899840, by rfl⟩ : syracuseStep 1199787 = 1799681) B1799681
theorem B19451573 : Blo 1198416 19451573 := bstep (se 5 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 19451573 = 1823585) B1823585
theorem B1199799 : Blo 1198416 1199799 := bstep (se 1 (by rfl) ⟨899849, by rfl⟩ : syracuseStep 1199799 = 1799699) B1799699
theorem B3034817 : Blo 1198416 3034817 := bstep (se 2 (by rfl) ⟨1138056, by rfl⟩ : syracuseStep 3034817 = 2276113) B2276113
theorem B2698955 : Blo 1198416 2698955 := bstep (se 1 (by rfl) ⟨2024216, by rfl⟩ : syracuseStep 2698955 = 4048433) B4048433
theorem B1199819 : Blo 1198416 1199819 := bstep (se 1 (by rfl) ⟨899864, by rfl⟩ : syracuseStep 1199819 = 1799729) B1799729
theorem B1199831 : Blo 1198416 1199831 := bstep (se 1 (by rfl) ⟨899873, by rfl⟩ : syracuseStep 1199831 = 1799747) B1799747
theorem B4320989 : Blo 1198416 4320989 := bstep (se 3 (by rfl) ⟨810185, by rfl⟩ : syracuseStep 4320989 = 1620371) B1620371
theorem B1199851 : Blo 1198416 1199851 := bstep (se 1 (by rfl) ⟨899888, by rfl⟩ : syracuseStep 1199851 = 1799777) B1799777
theorem B1199863 : Blo 1198416 1199863 := bstep (se 1 (by rfl) ⟨899897, by rfl⟩ : syracuseStep 1199863 = 1799795) B1799795
theorem B2699009 : Blo 1198416 2699009 := bstep (se 2 (by rfl) ⟨1012128, by rfl⟩ : syracuseStep 2699009 = 2024257) B2024257
theorem B1797899 : Blo 1198416 1797899 := bstep (se 1 (by rfl) ⟨1348424, by rfl⟩ : syracuseStep 1797899 = 2696849) B2696849
theorem B1199883 : Blo 1198416 1199883 := bstep (se 1 (by rfl) ⟨899912, by rfl⟩ : syracuseStep 1199883 = 1799825) B1799825
theorem B1797911 : Blo 1198416 1797911 := bstep (se 1 (by rfl) ⟨1348433, by rfl⟩ : syracuseStep 1797911 = 2696867) B2696867
theorem B1199895 : Blo 1198416 1199895 := bstep (se 1 (by rfl) ⟨899921, by rfl⟩ : syracuseStep 1199895 = 1799843) B1799843
theorem B1199915 : Blo 1198416 1199915 := bstep (se 1 (by rfl) ⟨899936, by rfl⟩ : syracuseStep 1199915 = 1799873) B1799873
theorem B1199927 : Blo 1198416 1199927 := bstep (se 1 (by rfl) ⟨899945, by rfl⟩ : syracuseStep 1199927 = 1799891) B1799891
theorem B1199947 : Blo 1198416 1199947 := bstep (se 1 (by rfl) ⟨899960, by rfl⟩ : syracuseStep 1199947 = 1799921) B1799921
theorem B1199959 : Blo 1198416 1199959 := bstep (se 1 (by rfl) ⟨899969, by rfl⟩ : syracuseStep 1199959 = 1799939) B1799939
theorem B2559833 : Blo 1198416 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B1797977 : Blo 1198416 1797977 := bstep (se 2 (by rfl) ⟨674241, by rfl⟩ : syracuseStep 1797977 = 1348483) B1348483
theorem B1199979 : Blo 1198416 1199979 := bstep (se 1 (by rfl) ⟨899984, by rfl⟩ : syracuseStep 1199979 = 1799969) B1799969
theorem B1199991 : Blo 1198416 1199991 := bstep (se 1 (by rfl) ⟨899993, by rfl⟩ : syracuseStep 1199991 = 1799987) B1799987
theorem B1200011 : Blo 1198416 1200011 := bstep (se 1 (by rfl) ⟨900008, by rfl⟩ : syracuseStep 1200011 = 1800017) B1800017
theorem B1200023 : Blo 1198416 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1200043 : Blo 1198416 1200043 := bstep (se 1 (by rfl) ⟨900032, by rfl⟩ : syracuseStep 1200043 = 1800065) B1800065
theorem B1200055 : Blo 1198416 1200055 := bstep (se 1 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 1200055 = 1800083) B1800083
theorem B1798091 : Blo 1198416 1798091 := bstep (se 1 (by rfl) ⟨1348568, by rfl⟩ : syracuseStep 1798091 = 2697137) B2697137
theorem B1707979 : Blo 1198416 1707979 := bstep (se 1 (by rfl) ⟨1280984, by rfl⟩ : syracuseStep 1707979 = 2561969) B2561969
theorem B1200075 : Blo 1198416 1200075 := bstep (se 1 (by rfl) ⟨900056, by rfl⟩ : syracuseStep 1200075 = 1800113) B1800113
theorem B1798103 : Blo 1198416 1798103 := bstep (se 1 (by rfl) ⟨1348577, by rfl⟩ : syracuseStep 1798103 = 2697155) B2697155
theorem B1200087 : Blo 1198416 1200087 := bstep (se 1 (by rfl) ⟨900065, by rfl⟩ : syracuseStep 1200087 = 1800131) B1800131
theorem B2699225 : Blo 1198416 2699225 := bstep (se 2 (by rfl) ⟨1012209, by rfl⟩ : syracuseStep 2699225 = 2024419) B2024419
theorem B1200107 : Blo 1198416 1200107 := bstep (se 1 (by rfl) ⟨900080, by rfl⟩ : syracuseStep 1200107 = 1800161) B1800161
theorem B1200119 : Blo 1198416 1200119 := bstep (se 1 (by rfl) ⟨900089, by rfl⟩ : syracuseStep 1200119 = 1800179) B1800179
theorem B1200139 : Blo 1198416 1200139 := bstep (se 1 (by rfl) ⟨900104, by rfl⟩ : syracuseStep 1200139 = 1800209) B1800209
theorem B1200151 : Blo 1198416 1200151 := bstep (se 1 (by rfl) ⟨900113, by rfl⟩ : syracuseStep 1200151 = 1800227) B1800227
theorem B1798169 : Blo 1198416 1798169 := bstep (se 2 (by rfl) ⟨674313, by rfl⟩ : syracuseStep 1798169 = 1348627) B1348627
theorem B6926381 : Blo 1198416 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B1200171 : Blo 1198416 1200171 := bstep (se 1 (by rfl) ⟨900128, by rfl⟩ : syracuseStep 1200171 = 1800257) B1800257
theorem B2699315 : Blo 1198416 2699315 := bstep (se 1 (by rfl) ⟨2024486, by rfl⟩ : syracuseStep 2699315 = 4048973) B4048973
theorem B1200183 : Blo 1198416 1200183 := bstep (se 1 (by rfl) ⟨900137, by rfl⟩ : syracuseStep 1200183 = 1800275) B1800275
theorem B1200203 : Blo 1198416 1200203 := bstep (se 1 (by rfl) ⟨900152, by rfl⟩ : syracuseStep 1200203 = 1800305) B1800305
theorem B2699351 : Blo 1198416 2699351 := bstep (se 1 (by rfl) ⟨2024513, by rfl⟩ : syracuseStep 2699351 = 4049027) B4049027
theorem B1200215 : Blo 1198416 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B1200235 : Blo 1198416 1200235 := bstep (se 1 (by rfl) ⟨900176, by rfl⟩ : syracuseStep 1200235 = 1800353) B1800353
theorem B2191475 : Blo 1198416 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B1200247 : Blo 1198416 1200247 := bstep (se 1 (by rfl) ⟨900185, by rfl⟩ : syracuseStep 1200247 = 1800371) B1800371
theorem B1798283 : Blo 1198416 1798283 := bstep (se 1 (by rfl) ⟨1348712, by rfl⟩ : syracuseStep 1798283 = 2697425) B2697425
theorem B1200267 : Blo 1198416 1200267 := bstep (se 1 (by rfl) ⟨900200, by rfl⟩ : syracuseStep 1200267 = 1800401) B1800401
theorem B2879639 : Blo 1198416 2879639 := bstep (se 1 (by rfl) ⟨2159729, by rfl⟩ : syracuseStep 2879639 = 4319459) B4319459
theorem B1798295 : Blo 1198416 1798295 := bstep (se 1 (by rfl) ⟨1348721, by rfl⟩ : syracuseStep 1798295 = 2697443) B2697443
theorem B1200279 : Blo 1198416 1200279 := bstep (se 1 (by rfl) ⟨900209, by rfl⟩ : syracuseStep 1200279 = 1800419) B1800419
theorem B1200299 : Blo 1198416 1200299 := bstep (se 1 (by rfl) ⟨900224, by rfl⟩ : syracuseStep 1200299 = 1800449) B1800449
theorem B1200311 : Blo 1198416 1200311 := bstep (se 1 (by rfl) ⟨900233, by rfl⟩ : syracuseStep 1200311 = 1800467) B1800467
theorem B3895489 : Blo 1198416 3895489 := bstep (se 2 (by rfl) ⟨1460808, by rfl⟩ : syracuseStep 3895489 = 2921617) B2921617
theorem B1200331 : Blo 1198416 1200331 := bstep (se 1 (by rfl) ⟨900248, by rfl⟩ : syracuseStep 1200331 = 1800497) B1800497
theorem B1200343 : Blo 1198416 1200343 := bstep (se 1 (by rfl) ⟨900257, by rfl⟩ : syracuseStep 1200343 = 1800515) B1800515
theorem B1798361 : Blo 1198416 1798361 := bstep (se 2 (by rfl) ⟨674385, by rfl⟩ : syracuseStep 1798361 = 1348771) B1348771
theorem B3035353 : Blo 1198416 3035353 := bstep (se 2 (by rfl) ⟨1138257, by rfl⟩ : syracuseStep 3035353 = 2276515) B2276515
theorem B3240157 : Blo 1198416 3240157 := bstep (se 3 (by rfl) ⟨607529, by rfl⟩ : syracuseStep 3240157 = 1215059) B1215059
theorem B1200363 : Blo 1198416 1200363 := bstep (se 1 (by rfl) ⟨900272, by rfl⟩ : syracuseStep 1200363 = 1800545) B1800545
theorem B2560243 : Blo 1198416 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B1200375 : Blo 1198416 1200375 := bstep (se 1 (by rfl) ⟨900281, by rfl⟩ : syracuseStep 1200375 = 1800563) B1800563
theorem B2699531 : Blo 1198416 2699531 := bstep (se 1 (by rfl) ⟨2024648, by rfl⟩ : syracuseStep 2699531 = 4049297) B4049297
theorem B1200395 : Blo 1198416 1200395 := bstep (se 1 (by rfl) ⟨900296, by rfl⟩ : syracuseStep 1200395 = 1800593) B1800593
theorem B1200407 : Blo 1198416 1200407 := bstep (se 1 (by rfl) ⟨900305, by rfl⟩ : syracuseStep 1200407 = 1800611) B1800611
theorem B2699585 : Blo 1198416 2699585 := bstep (se 2 (by rfl) ⟨1012344, by rfl⟩ : syracuseStep 2699585 = 2024689) B2024689
theorem B1798475 : Blo 1198416 1798475 := bstep (se 1 (by rfl) ⟨1348856, by rfl⟩ : syracuseStep 1798475 = 2697713) B2697713
theorem B1798487 : Blo 1198416 1798487 := bstep (se 1 (by rfl) ⟨1348865, by rfl⟩ : syracuseStep 1798487 = 2697731) B2697731
theorem B9113957 : Blo 1198416 9113957 := bstep (se 4 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 9113957 = 1708867) B1708867
theorem B25932149 : Blo 1198416 25932149 := bstep (se 5 (by rfl) ⟨1215569, by rfl⟩ : syracuseStep 25932149 = 2431139) B2431139
theorem B1798553 : Blo 1198416 1798553 := bstep (se 2 (by rfl) ⟨674457, by rfl⟩ : syracuseStep 1798553 = 1348915) B1348915
theorem B2306497 : Blo 1198416 2306497 := bstep (se 2 (by rfl) ⟨864936, by rfl⟩ : syracuseStep 2306497 = 1729873) B1729873
theorem B4051403 : Blo 1198416 4051403 := bstep (se 1 (by rfl) ⟨3038552, by rfl⟩ : syracuseStep 4051403 = 6077105) B6077105
theorem B1298903 : Blo 1198416 1298903 := bstep (se 1 (by rfl) ⟨974177, by rfl⟩ : syracuseStep 1298903 = 1948355) B1948355
theorem B2560499 : Blo 1198416 2560499 := bstep (se 1 (by rfl) ⟨1920374, by rfl⟩ : syracuseStep 2560499 = 3840749) B3840749
theorem B1798667 : Blo 1198416 1798667 := bstep (se 1 (by rfl) ⟨1349000, by rfl⟩ : syracuseStep 1798667 = 2698001) B2698001
theorem B1798679 : Blo 1198416 1798679 := bstep (se 1 (by rfl) ⟨1349009, by rfl⟩ : syracuseStep 1798679 = 2698019) B2698019
theorem B2699801 : Blo 1198416 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B1798745 : Blo 1198416 1798745 := bstep (se 2 (by rfl) ⟨674529, by rfl⟩ : syracuseStep 1798745 = 1349059) B1349059
theorem B2699891 : Blo 1198416 2699891 := bstep (se 1 (by rfl) ⟨2024918, by rfl⟩ : syracuseStep 2699891 = 4049837) B4049837
theorem B4551299 : Blo 1198416 4551299 := bstep (se 1 (by rfl) ⟨3413474, by rfl⟩ : syracuseStep 4551299 = 6826949) B6826949
theorem B2699927 : Blo 1198416 2699927 := bstep (se 1 (by rfl) ⟨2024945, by rfl⟩ : syracuseStep 2699927 = 4049891) B4049891
theorem B1348267 : Blo 1198416 1348267 := bstep (se 1 (by rfl) ⟨1011200, by rfl⟩ : syracuseStep 1348267 = 2022401) B2022401
theorem B5190317 : Blo 1198416 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B1798859 : Blo 1198416 1798859 := bstep (se 1 (by rfl) ⟨1349144, by rfl⟩ : syracuseStep 1798859 = 2698289) B2698289
theorem B1798871 : Blo 1198416 1798871 := bstep (se 1 (by rfl) ⟨1349153, by rfl⟩ : syracuseStep 1798871 = 2698307) B2698307
theorem B9106181 : Blo 1198416 9106181 := bstep (se 4 (by rfl) ⟨853704, by rfl⟩ : syracuseStep 9106181 = 1707409) B1707409
theorem B1348375 : Blo 1198416 1348375 := bstep (se 1 (by rfl) ⟨1011281, by rfl⟩ : syracuseStep 1348375 = 2022563) B2022563
theorem B1798937 : Blo 1198416 1798937 := bstep (se 2 (by rfl) ⟨674601, by rfl⟩ : syracuseStep 1798937 = 1349203) B1349203
theorem B2700107 : Blo 1198416 2700107 := bstep (se 1 (by rfl) ⟨2025080, by rfl⟩ : syracuseStep 2700107 = 4050161) B4050161
theorem B9114443 : Blo 1198416 9114443 := bstep (se 1 (by rfl) ⟨6835832, by rfl⟩ : syracuseStep 9114443 = 13671665) B13671665
theorem B2700161 : Blo 1198416 2700161 := bstep (se 2 (by rfl) ⟨1012560, by rfl⟩ : syracuseStep 2700161 = 2025121) B2025121
theorem B1799051 : Blo 1198416 1799051 := bstep (se 1 (by rfl) ⟨1349288, by rfl⟩ : syracuseStep 1799051 = 2698577) B2698577
theorem B1799063 : Blo 1198416 1799063 := bstep (se 1 (by rfl) ⟨1349297, by rfl⟩ : syracuseStep 1799063 = 2698595) B2698595
theorem B1348555 : Blo 1198416 1348555 := bstep (se 1 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 1348555 = 2022833) B2022833
theorem B1799129 : Blo 1198416 1799129 := bstep (se 2 (by rfl) ⟨674673, by rfl⟩ : syracuseStep 1799129 = 1349347) B1349347
theorem B1348663 : Blo 1198416 1348663 := bstep (se 1 (by rfl) ⟨1011497, by rfl⟩ : syracuseStep 1348663 = 2022995) B2022995
theorem B1799243 : Blo 1198416 1799243 := bstep (se 1 (by rfl) ⟨1349432, by rfl⟩ : syracuseStep 1799243 = 2698865) B2698865
theorem B1799255 : Blo 1198416 1799255 := bstep (se 1 (by rfl) ⟨1349441, by rfl⟩ : syracuseStep 1799255 = 2698883) B2698883
theorem B2700377 : Blo 1198416 2700377 := bstep (se 2 (by rfl) ⟨1012641, by rfl⟩ : syracuseStep 2700377 = 2025283) B2025283
theorem B6075485 : Blo 1198416 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B2053259 : Blo 1198416 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B1873049 : Blo 1198416 1873049 := bstep (se 2 (by rfl) ⟨702393, by rfl⟩ : syracuseStep 1873049 = 1404787) B1404787
theorem B1799321 : Blo 1198416 1799321 := bstep (se 2 (by rfl) ⟨674745, by rfl⟩ : syracuseStep 1799321 = 1349491) B1349491
theorem B2700467 : Blo 1198416 2700467 := bstep (se 1 (by rfl) ⟨2025350, by rfl⟩ : syracuseStep 2700467 = 4050701) B4050701
theorem B2700503 : Blo 1198416 2700503 := bstep (se 1 (by rfl) ⟨2025377, by rfl⟩ : syracuseStep 2700503 = 4050755) B4050755
theorem B1348843 : Blo 1198416 1348843 := bstep (se 1 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 1348843 = 2023265) B2023265
theorem B1799435 : Blo 1198416 1799435 := bstep (se 1 (by rfl) ⟨1349576, by rfl⟩ : syracuseStep 1799435 = 2699153) B2699153
theorem B1799447 : Blo 1198416 1799447 := bstep (se 1 (by rfl) ⟨1349585, by rfl⟩ : syracuseStep 1799447 = 2699171) B2699171
theorem B3036467 : Blo 1198416 3036467 := bstep (se 1 (by rfl) ⟨2277350, by rfl⟩ : syracuseStep 3036467 = 4554701) B4554701
theorem B1348951 : Blo 1198416 1348951 := bstep (se 1 (by rfl) ⟨1011713, by rfl⟩ : syracuseStep 1348951 = 2023427) B2023427
theorem B2733401 : Blo 1198416 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B1799513 : Blo 1198416 1799513 := bstep (se 2 (by rfl) ⟨674817, by rfl⟩ : syracuseStep 1799513 = 1349635) B1349635
theorem B13841765 : Blo 1198416 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B2700683 : Blo 1198416 2700683 := bstep (se 1 (by rfl) ⟨2025512, by rfl⟩ : syracuseStep 2700683 = 4051025) B4051025
theorem B2430361 : Blo 1198416 2430361 := bstep (se 2 (by rfl) ⟨911385, by rfl⟩ : syracuseStep 2430361 = 1822771) B1822771
theorem B3413441 : Blo 1198416 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2561473 : Blo 1198416 2561473 := bstep (se 2 (by rfl) ⟨960552, by rfl⟩ : syracuseStep 2561473 = 1921105) B1921105
theorem B2700737 : Blo 1198416 2700737 := bstep (se 2 (by rfl) ⟨1012776, by rfl⟩ : syracuseStep 2700737 = 2025553) B2025553
theorem B1799627 : Blo 1198416 1799627 := bstep (se 1 (by rfl) ⟨1349720, by rfl⟩ : syracuseStep 1799627 = 2699441) B2699441
theorem B1799639 : Blo 1198416 1799639 := bstep (se 1 (by rfl) ⟨1349729, by rfl⟩ : syracuseStep 1799639 = 2699459) B2699459
theorem B1349131 : Blo 1198416 1349131 := bstep (se 1 (by rfl) ⟨1011848, by rfl⟩ : syracuseStep 1349131 = 2023697) B2023697
theorem B9729553 : Blo 1198416 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B1799705 : Blo 1198416 1799705 := bstep (se 2 (by rfl) ⟨674889, by rfl⟩ : syracuseStep 1799705 = 1349779) B1349779
theorem B3036761 : Blo 1198416 3036761 := bstep (se 2 (by rfl) ⟨1138785, by rfl⟩ : syracuseStep 3036761 = 2277571) B2277571
theorem B1349239 : Blo 1198416 1349239 := bstep (se 1 (by rfl) ⟨1011929, by rfl⟩ : syracuseStep 1349239 = 2023859) B2023859
theorem B1799819 : Blo 1198416 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B1799831 : Blo 1198416 1799831 := bstep (se 1 (by rfl) ⟨1349873, by rfl⟩ : syracuseStep 1799831 = 2699747) B2699747
theorem B1799897 : Blo 1198416 1799897 := bstep (se 2 (by rfl) ⟨674961, by rfl⟩ : syracuseStep 1799897 = 1349923) B1349923
theorem B1824535 : Blo 1198416 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B1349419 : Blo 1198416 1349419 := bstep (se 1 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 1349419 = 2024129) B2024129
theorem B6068033 : Blo 1198416 6068033 := bstep (se 2 (by rfl) ⟨2275512, by rfl⟩ : syracuseStep 6068033 = 4551025) B4551025
theorem B1800011 : Blo 1198416 1800011 := bstep (se 1 (by rfl) ⟨1350008, by rfl⟩ : syracuseStep 1800011 = 2700017) B2700017
theorem B1800023 : Blo 1198416 1800023 := bstep (se 1 (by rfl) ⟨1350017, by rfl⟩ : syracuseStep 1800023 = 2700035) B2700035
theorem B2881369 : Blo 1198416 2881369 := bstep (se 2 (by rfl) ⟨1080513, by rfl⟩ : syracuseStep 2881369 = 2161027) B2161027
theorem B7690085 : Blo 1198416 7690085 := bstep (se 4 (by rfl) ⟨720945, by rfl⟩ : syracuseStep 7690085 = 1441891) B1441891
theorem B1349527 : Blo 1198416 1349527 := bstep (se 1 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 1349527 = 2024291) B2024291
theorem B1800089 : Blo 1198416 1800089 := bstep (se 2 (by rfl) ⟨675033, by rfl⟩ : syracuseStep 1800089 = 1350067) B1350067
theorem B4044761 : Blo 1198416 4044761 := bstep (se 2 (by rfl) ⟨1516785, by rfl⟩ : syracuseStep 4044761 = 3033571) B3033571
theorem B1800203 : Blo 1198416 1800203 := bstep (se 1 (by rfl) ⟨1350152, by rfl⟩ : syracuseStep 1800203 = 2700305) B2700305
theorem B1800215 : Blo 1198416 1800215 := bstep (se 1 (by rfl) ⟨1350161, by rfl⟩ : syracuseStep 1800215 = 2700323) B2700323
theorem B2881601 : Blo 1198416 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B1349707 : Blo 1198416 1349707 := bstep (se 1 (by rfl) ⟨1012280, by rfl⟩ : syracuseStep 1349707 = 2024561) B2024561
theorem B1800281 : Blo 1198416 1800281 := bstep (se 2 (by rfl) ⟨675105, by rfl⟩ : syracuseStep 1800281 = 1350211) B1350211
theorem B1349815 : Blo 1198416 1349815 := bstep (se 1 (by rfl) ⟨1012361, by rfl⟩ : syracuseStep 1349815 = 2024723) B2024723
theorem B1800395 : Blo 1198416 1800395 := bstep (se 1 (by rfl) ⟨1350296, by rfl⟩ : syracuseStep 1800395 = 2700593) B2700593
theorem B2275543 : Blo 1198416 2275543 := bstep (se 1 (by rfl) ⟨1706657, by rfl⟩ : syracuseStep 2275543 = 3413315) B3413315
theorem B1800407 : Blo 1198416 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B1800473 : Blo 1198416 1800473 := bstep (se 2 (by rfl) ⟨675177, by rfl⟩ : syracuseStep 1800473 = 1350355) B1350355
theorem B5126465 : Blo 1198416 5126465 := bstep (se 2 (by rfl) ⟨1922424, by rfl⟩ : syracuseStep 5126465 = 3844849) B3844849
theorem B7690571 : Blo 1198416 7690571 := bstep (se 1 (by rfl) ⟨5767928, by rfl⟩ : syracuseStep 7690571 = 11535857) B11535857
theorem B1349995 : Blo 1198416 1349995 := bstep (se 1 (by rfl) ⟨1012496, by rfl⟩ : syracuseStep 1349995 = 2024993) B2024993
theorem B1800587 : Blo 1198416 1800587 := bstep (se 1 (by rfl) ⟨1350440, by rfl⟩ : syracuseStep 1800587 = 2700881) B2700881
theorem B1800599 : Blo 1198416 1800599 := bstep (se 1 (by rfl) ⟨1350449, by rfl⟩ : syracuseStep 1800599 = 2700899) B2700899
theorem B4004275 : Blo 1198416 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1350103 : Blo 1198416 1350103 := bstep (se 1 (by rfl) ⟨1012577, by rfl⟩ : syracuseStep 1350103 = 2025155) B2025155
theorem B7682521 : Blo 1198416 7682521 := bstep (se 2 (by rfl) ⟨2880945, by rfl⟩ : syracuseStep 7682521 = 5761891) B5761891
theorem B17291789 : Blo 1198416 17291789 := bstep (se 3 (by rfl) ⟨3242210, by rfl⟩ : syracuseStep 17291789 = 6484421) B6484421
theorem B15358481 : Blo 1198416 15358481 := bstep (se 2 (by rfl) ⟨5759430, by rfl⟩ : syracuseStep 15358481 = 11518861) B11518861
theorem B2882099 : Blo 1198416 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B2431577 : Blo 1198416 2431577 := bstep (se 2 (by rfl) ⟨911841, by rfl⟩ : syracuseStep 2431577 = 1823683) B1823683
theorem B1350283 : Blo 1198416 1350283 := bstep (se 1 (by rfl) ⟨1012712, by rfl⟩ : syracuseStep 1350283 = 2025425) B2025425
theorem B4045463 : Blo 1198416 4045463 := bstep (se 1 (by rfl) ⟨3034097, by rfl⟩ : syracuseStep 4045463 = 6068195) B6068195
theorem B5126807 : Blo 1198416 5126807 := bstep (se 1 (by rfl) ⟨3845105, by rfl⟩ : syracuseStep 5126807 = 7690211) B7690211
theorem B3242699 : Blo 1198416 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B1350391 : Blo 1198416 1350391 := bstep (se 1 (by rfl) ⟨1012793, by rfl⟩ : syracuseStep 1350391 = 2025587) B2025587
theorem B2022347 : Blo 1198416 2022347 := bstep (se 1 (by rfl) ⟨1516760, by rfl⟩ : syracuseStep 2022347 = 3033521) B3033521
theorem B4996099 : Blo 1198416 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B2276363 : Blo 1198416 2276363 := bstep (se 1 (by rfl) ⟨1707272, by rfl⟩ : syracuseStep 2276363 = 3414545) B3414545
theorem B1621003 : Blo 1198416 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B2276417 : Blo 1198416 2276417 := bstep (se 2 (by rfl) ⟨853656, by rfl⟩ : syracuseStep 2276417 = 1707313) B1707313
theorem B7683137 : Blo 1198416 7683137 := bstep (se 2 (by rfl) ⟨2881176, by rfl⟩ : syracuseStep 7683137 = 5762353) B5762353
theorem B2022475 : Blo 1198416 2022475 := bstep (se 1 (by rfl) ⟨1516856, by rfl⟩ : syracuseStep 2022475 = 3033713) B3033713
theorem B3415115 : Blo 1198416 3415115 := bstep (se 1 (by rfl) ⟨2561336, by rfl⟩ : syracuseStep 3415115 = 5122673) B5122673
theorem B9108611 : Blo 1198416 9108611 := bstep (se 1 (by rfl) ⟨6831458, by rfl⟩ : syracuseStep 9108611 = 13662917) B13662917
theorem B4046003 : Blo 1198416 4046003 := bstep (se 1 (by rfl) ⟨3034502, by rfl⟩ : syracuseStep 4046003 = 6069005) B6069005
theorem B3038411 : Blo 1198416 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B2022617 : Blo 1198416 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B8649989 : Blo 1198416 8649989 := bstep (se 4 (by rfl) ⟨810936, by rfl⟩ : syracuseStep 8649989 = 1621873) B1621873
theorem B2022745 : Blo 1198416 2022745 := bstep (se 2 (by rfl) ⟨758529, by rfl⟩ : syracuseStep 2022745 = 1517059) B1517059
theorem B2735489 : Blo 1198416 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B4046273 : Blo 1198416 4046273 := bstep (se 2 (by rfl) ⟨1517352, by rfl⟩ : syracuseStep 4046273 = 3034705) B3034705
theorem B2563609 : Blo 1198416 2563609 := bstep (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) B1922707
theorem B9100835 : Blo 1198416 9100835 := bstep (se 1 (by rfl) ⟨6825626, by rfl⟩ : syracuseStep 9100835 = 13651253) B13651253
theorem B8764973 : Blo 1198416 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B13655627 : Blo 1198416 13655627 := bstep (se 1 (by rfl) ⟨10241720, by rfl⟩ : syracuseStep 13655627 = 20483441) B20483441
theorem B4554413 : Blo 1198416 4554413 := bstep (se 3 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 4554413 = 1707905) B1707905
theorem B6069977 : Blo 1198416 6069977 := bstep (se 2 (by rfl) ⟨2276241, by rfl⟩ : syracuseStep 6069977 = 4552483) B4552483
theorem B4931351 : Blo 1198416 4931351 := bstep (se 1 (by rfl) ⟨3698513, by rfl⟩ : syracuseStep 4931351 = 7397027) B7397027
theorem B2309939 : Blo 1198416 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B1441675 : Blo 1198416 1441675 := bstep (se 1 (by rfl) ⟨1081256, by rfl⟩ : syracuseStep 1441675 = 2162513) B2162513
theorem B2023319 : Blo 1198416 2023319 := bstep (se 1 (by rfl) ⟨1517489, by rfl⟩ : syracuseStep 2023319 = 3034979) B3034979
theorem B2277335 : Blo 1198416 2277335 := bstep (se 1 (by rfl) ⟨1708001, by rfl⟩ : syracuseStep 2277335 = 3416003) B3416003
theorem B4046813 : Blo 1198416 4046813 := bstep (se 3 (by rfl) ⟨758777, by rfl⟩ : syracuseStep 4046813 = 1517555) B1517555
theorem B6070301 : Blo 1198416 6070301 := bstep (se 3 (by rfl) ⟨1138181, by rfl⟩ : syracuseStep 6070301 = 2276363) B2276363
theorem B2023609 : Blo 1198416 2023609 := bstep (se 2 (by rfl) ⟨758853, by rfl⟩ : syracuseStep 2023609 = 1517707) B1517707
theorem B1622263 : Blo 1198416 1622263 := bstep (se 1 (by rfl) ⟨1216697, by rfl⟩ : syracuseStep 1622263 = 2433395) B2433395
theorem B5193985 : Blo 1198416 5193985 := bstep (se 2 (by rfl) ⟨1947744, by rfl⟩ : syracuseStep 5193985 = 3895489) B3895489
theorem B4047137 : Blo 1198416 4047137 := bstep (se 2 (by rfl) ⟨1517676, by rfl⟩ : syracuseStep 4047137 = 3035353) B3035353
theorem B4555217 : Blo 1198416 4555217 := bstep (se 2 (by rfl) ⟨1708206, by rfl⟩ : syracuseStep 4555217 = 3416413) B3416413
theorem B6070787 : Blo 1198416 6070787 := bstep (se 1 (by rfl) ⟨4553090, by rfl⟩ : syracuseStep 6070787 = 9106181) B9106181
theorem B2884243 : Blo 1198416 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B1368839 : Blo 1198416 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B58336037 : Blo 1198416 58336037 := bstep (se 4 (by rfl) ⟨5469003, by rfl⟩ : syracuseStep 58336037 = 10938007) B10938007
theorem B4047731 : Blo 1198416 4047731 := bstep (se 1 (by rfl) ⟨3035798, by rfl⟩ : syracuseStep 4047731 = 6071597) B6071597
theorem B2024311 : Blo 1198416 2024311 := bstep (se 1 (by rfl) ⟨1518233, by rfl⟩ : syracuseStep 2024311 = 3036467) B3036467
theorem B4555673 : Blo 1198416 4555673 := bstep (se 2 (by rfl) ⟨1708377, by rfl⟩ : syracuseStep 4555673 = 3416755) B3416755
theorem B10388387 : Blo 1198416 10388387 := bstep (se 1 (by rfl) ⟨7791290, by rfl⟩ : syracuseStep 10388387 = 15582581) B15582581
theorem B6833099 : Blo 1198416 6833099 := bstep (se 1 (by rfl) ⟨5124824, by rfl⟩ : syracuseStep 6833099 = 10249649) B10249649
theorem B2024507 : Blo 1198416 2024507 := bstep (se 1 (by rfl) ⟨1518380, by rfl⟩ : syracuseStep 2024507 = 3036761) B3036761
theorem B2278459 : Blo 1198416 2278459 := bstep (se 1 (by rfl) ⟨1708844, by rfl⟩ : syracuseStep 2278459 = 3417689) B3417689
theorem B6489395 : Blo 1198416 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B2696507 : Blo 1198416 2696507 := bstep (se 1 (by rfl) ⟨2022380, by rfl⟩ : syracuseStep 2696507 = 4044761) B4044761
theorem B6833555 : Blo 1198416 6833555 := bstep (se 1 (by rfl) ⟨5125166, by rfl⟩ : syracuseStep 6833555 = 10250333) B10250333
theorem B2696633 : Blo 1198416 2696633 := bstep (se 2 (by rfl) ⟨1011237, by rfl⟩ : syracuseStep 2696633 = 2022475) B2022475
theorem B2024905 : Blo 1198416 2024905 := bstep (se 2 (by rfl) ⟨759339, by rfl⟩ : syracuseStep 2024905 = 1518679) B1518679
theorem B7685597 : Blo 1198416 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B3417643 : Blo 1198416 3417643 := bstep (se 1 (by rfl) ⟨2563232, by rfl⟩ : syracuseStep 3417643 = 5126465) B5126465
theorem B8767043 : Blo 1198416 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B11527859 : Blo 1198416 11527859 := bstep (se 1 (by rfl) ⟨8645894, by rfl⟩ : syracuseStep 11527859 = 17291789) B17291789
theorem B2696975 : Blo 1198416 2696975 := bstep (se 1 (by rfl) ⟨2022731, by rfl⟩ : syracuseStep 2696975 = 4045463) B4045463
theorem B3417871 : Blo 1198416 3417871 := bstep (se 1 (by rfl) ⟨2563403, by rfl⟩ : syracuseStep 3417871 = 5126807) B5126807
theorem B2696993 : Blo 1198416 2696993 := bstep (se 2 (by rfl) ⟨1011372, by rfl⟩ : syracuseStep 2696993 = 2022745) B2022745
theorem B13141835 : Blo 1198416 13141835 := bstep (se 1 (by rfl) ⟨9856376, by rfl⟩ : syracuseStep 13141835 = 19712753) B19712753
theorem B5760953 : Blo 1198416 5760953 := bstep (se 2 (by rfl) ⟨2160357, by rfl⟩ : syracuseStep 5760953 = 4320715) B4320715
theorem B3418145 : Blo 1198416 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B1517611 : Blo 1198416 1517611 := bstep (se 1 (by rfl) ⟨1138208, by rfl⟩ : syracuseStep 1517611 = 2276417) B2276417
theorem B5122091 : Blo 1198416 5122091 := bstep (se 1 (by rfl) ⟨3841568, by rfl⟩ : syracuseStep 5122091 = 7683137) B7683137
theorem B4556843 : Blo 1198416 4556843 := bstep (se 1 (by rfl) ⟨3417632, by rfl⟩ : syracuseStep 4556843 = 6835265) B6835265
theorem B6072407 : Blo 1198416 6072407 := bstep (se 1 (by rfl) ⟨4554305, by rfl⟩ : syracuseStep 6072407 = 9108611) B9108611
theorem B2697335 : Blo 1198416 2697335 := bstep (se 1 (by rfl) ⟨2023001, by rfl⟩ : syracuseStep 2697335 = 4046003) B4046003
theorem B2025607 : Blo 1198416 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B2697515 : Blo 1198416 2697515 := bstep (se 1 (by rfl) ⟨2023136, by rfl⟩ : syracuseStep 2697515 = 4046273) B4046273
theorem B5843315 : Blo 1198416 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B1198471 : Blo 1198416 1198471 := bstep (se 1 (by rfl) ⟨898853, by rfl⟩ : syracuseStep 1198471 = 1797707) B1797707
theorem B2050439 : Blo 1198416 2050439 := bstep (se 1 (by rfl) ⟨1537829, by rfl⟩ : syracuseStep 2050439 = 3075659) B3075659
theorem B9103751 : Blo 1198416 9103751 := bstep (se 1 (by rfl) ⟨6827813, by rfl⟩ : syracuseStep 9103751 = 13655627) B13655627
theorem B1198479 : Blo 1198416 1198479 := bstep (se 1 (by rfl) ⟨898859, by rfl⟩ : syracuseStep 1198479 = 1797719) B1797719
theorem B1198523 : Blo 1198416 1198523 := bstep (se 1 (by rfl) ⟨898892, by rfl⟩ : syracuseStep 1198523 = 1797785) B1797785
theorem B1198599 : Blo 1198416 1198599 := bstep (se 1 (by rfl) ⟨898949, by rfl⟩ : syracuseStep 1198599 = 1797899) B1797899
theorem B1198607 : Blo 1198416 1198607 := bstep (se 1 (by rfl) ⟨898955, by rfl⟩ : syracuseStep 1198607 = 1797911) B1797911
theorem B3287567 : Blo 1198416 3287567 := bstep (se 1 (by rfl) ⟨2465675, by rfl⟩ : syracuseStep 3287567 = 4931351) B4931351
theorem B1706555 : Blo 1198416 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B1198651 : Blo 1198416 1198651 := bstep (se 1 (by rfl) ⟨898988, by rfl⟩ : syracuseStep 1198651 = 1797977) B1797977
theorem B6072893 : Blo 1198416 6072893 := bstep (se 3 (by rfl) ⟨1138667, by rfl⟩ : syracuseStep 6072893 = 2277335) B2277335
theorem B1198727 : Blo 1198416 1198727 := bstep (se 1 (by rfl) ⟨899045, by rfl⟩ : syracuseStep 1198727 = 1798091) B1798091
theorem B1198735 : Blo 1198416 1198735 := bstep (se 1 (by rfl) ⟨899051, by rfl⟩ : syracuseStep 1198735 = 1798103) B1798103
theorem B2697875 : Blo 1198416 2697875 := bstep (se 1 (by rfl) ⟨2023406, by rfl⟩ : syracuseStep 2697875 = 4046813) B4046813
theorem B1198779 : Blo 1198416 1198779 := bstep (se 1 (by rfl) ⟨899084, by rfl⟩ : syracuseStep 1198779 = 1798169) B1798169
theorem B2697929 : Blo 1198416 2697929 := bstep (se 2 (by rfl) ⟨1011723, by rfl⟩ : syracuseStep 2697929 = 2023447) B2023447
theorem B1198855 : Blo 1198416 1198855 := bstep (se 1 (by rfl) ⟨899141, by rfl⟩ : syracuseStep 1198855 = 1798283) B1798283
theorem B1919759 : Blo 1198416 1919759 := bstep (se 1 (by rfl) ⟨1439819, by rfl⟩ : syracuseStep 1919759 = 2879639) B2879639
theorem B1198863 : Blo 1198416 1198863 := bstep (se 1 (by rfl) ⟨899147, by rfl⟩ : syracuseStep 1198863 = 1798295) B1798295
theorem B12315407 : Blo 1198416 12315407 := bstep (se 1 (by rfl) ⟨9236555, by rfl⟩ : syracuseStep 12315407 = 18473111) B18473111
theorem B1198907 : Blo 1198416 1198907 := bstep (se 1 (by rfl) ⟨899180, by rfl⟩ : syracuseStep 1198907 = 1798361) B1798361
theorem B3844979 : Blo 1198416 3844979 := bstep (se 1 (by rfl) ⟨2883734, by rfl⟩ : syracuseStep 3844979 = 5767469) B5767469
theorem B1198983 : Blo 1198416 1198983 := bstep (se 1 (by rfl) ⟨899237, by rfl⟩ : syracuseStep 1198983 = 1798475) B1798475
theorem B1198991 : Blo 1198416 1198991 := bstep (se 1 (by rfl) ⟨899243, by rfl⟩ : syracuseStep 1198991 = 1798487) B1798487
theorem B17288099 : Blo 1198416 17288099 := bstep (se 1 (by rfl) ⟨12966074, by rfl⟩ : syracuseStep 17288099 = 25932149) B25932149
theorem B1199035 : Blo 1198416 1199035 := bstep (se 1 (by rfl) ⟨899276, by rfl⟩ : syracuseStep 1199035 = 1798553) B1798553
theorem B3034057 : Blo 1198416 3034057 := bstep (se 2 (by rfl) ⟨1137771, by rfl⟩ : syracuseStep 3034057 = 2275543) B2275543
theorem B4320209 : Blo 1198416 4320209 := bstep (se 2 (by rfl) ⟨1620078, by rfl⟩ : syracuseStep 4320209 = 3240157) B3240157
theorem B5843933 : Blo 1198416 5843933 := bstep (se 3 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 5843933 = 2191475) B2191475
theorem B1706999 : Blo 1198416 1706999 := bstep (se 1 (by rfl) ⟨1280249, by rfl⟩ : syracuseStep 1706999 = 2560499) B2560499
theorem B1518583 : Blo 1198416 1518583 := bstep (se 1 (by rfl) ⟨1138937, by rfl⟩ : syracuseStep 1518583 = 2277875) B2277875
theorem B1199111 : Blo 1198416 1199111 := bstep (se 1 (by rfl) ⟨899333, by rfl⟩ : syracuseStep 1199111 = 1798667) B1798667
theorem B1199119 : Blo 1198416 1199119 := bstep (se 1 (by rfl) ⟨899339, by rfl⟩ : syracuseStep 1199119 = 1798679) B1798679
theorem B1199163 : Blo 1198416 1199163 := bstep (se 1 (by rfl) ⟨899372, by rfl⟩ : syracuseStep 1199163 = 1798745) B1798745
theorem B3034199 : Blo 1198416 3034199 := bstep (se 1 (by rfl) ⟨2275649, by rfl⟩ : syracuseStep 3034199 = 4551299) B4551299
theorem B3460211 : Blo 1198416 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B1199239 : Blo 1198416 1199239 := bstep (se 1 (by rfl) ⟨899429, by rfl⟩ : syracuseStep 1199239 = 1798859) B1798859
theorem B1199247 : Blo 1198416 1199247 := bstep (se 1 (by rfl) ⟨899435, by rfl⟩ : syracuseStep 1199247 = 1798871) B1798871
theorem B1707193 : Blo 1198416 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B1199291 : Blo 1198416 1199291 := bstep (se 1 (by rfl) ⟨899468, by rfl⟩ : syracuseStep 1199291 = 1798937) B1798937
theorem B3075329 : Blo 1198416 3075329 := bstep (se 2 (by rfl) ⟨1153248, by rfl⟩ : syracuseStep 3075329 = 2306497) B2306497
theorem B1199367 : Blo 1198416 1199367 := bstep (se 1 (by rfl) ⟨899525, by rfl⟩ : syracuseStep 1199367 = 1799051) B1799051
theorem B1199375 : Blo 1198416 1199375 := bstep (se 1 (by rfl) ⟨899531, by rfl⟩ : syracuseStep 1199375 = 1799063) B1799063
theorem B10243361 : Blo 1198416 10243361 := bstep (se 2 (by rfl) ⟨3841260, by rfl⟩ : syracuseStep 10243361 = 7682521) B7682521
theorem B1199419 : Blo 1198416 1199419 := bstep (se 1 (by rfl) ⟨899564, by rfl⟩ : syracuseStep 1199419 = 1799129) B1799129
theorem B3648827 : Blo 1198416 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B1518907 : Blo 1198416 1518907 := bstep (se 1 (by rfl) ⟨1139180, by rfl⟩ : syracuseStep 1518907 = 2278361) B2278361
theorem B2698631 : Blo 1198416 2698631 := bstep (se 1 (by rfl) ⟨2023973, by rfl⟩ : syracuseStep 2698631 = 4047947) B4047947
theorem B1199495 : Blo 1198416 1199495 := bstep (se 1 (by rfl) ⟨899621, by rfl⟩ : syracuseStep 1199495 = 1799243) B1799243
theorem B1199503 : Blo 1198416 1199503 := bstep (se 1 (by rfl) ⟨899627, by rfl⟩ : syracuseStep 1199503 = 1799255) B1799255
theorem B4050323 : Blo 1198416 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B6827449 : Blo 1198416 6827449 := bstep (se 2 (by rfl) ⟨2560293, by rfl⟩ : syracuseStep 6827449 = 5120587) B5120587
theorem B1199547 : Blo 1198416 1199547 := bstep (se 1 (by rfl) ⟨899660, by rfl⟩ : syracuseStep 1199547 = 1799321) B1799321
theorem B10530269 : Blo 1198416 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B1199623 : Blo 1198416 1199623 := bstep (se 1 (by rfl) ⟨899717, by rfl⟩ : syracuseStep 1199623 = 1799435) B1799435
theorem B1797647 : Blo 1198416 1797647 := bstep (se 1 (by rfl) ⟨1348235, by rfl⟩ : syracuseStep 1797647 = 2696471) B2696471
theorem B1199631 : Blo 1198416 1199631 := bstep (se 1 (by rfl) ⟨899723, by rfl⟩ : syracuseStep 1199631 = 1799447) B1799447
theorem B1797689 : Blo 1198416 1797689 := bstep (se 2 (by rfl) ⟨674133, by rfl⟩ : syracuseStep 1797689 = 1348267) B1348267
theorem B1822267 : Blo 1198416 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B2698811 : Blo 1198416 2698811 := bstep (se 1 (by rfl) ⟨2024108, by rfl⟩ : syracuseStep 2698811 = 4048217) B4048217
theorem B1199675 : Blo 1198416 1199675 := bstep (se 1 (by rfl) ⟨899756, by rfl⟩ : syracuseStep 1199675 = 1799513) B1799513
theorem B9227843 : Blo 1198416 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B1797767 : Blo 1198416 1797767 := bstep (se 1 (by rfl) ⟨1348325, by rfl⟩ : syracuseStep 1797767 = 2696651) B2696651
theorem B1199751 : Blo 1198416 1199751 := bstep (se 1 (by rfl) ⟨899813, by rfl⟩ : syracuseStep 1199751 = 1799627) B1799627
theorem B1199759 : Blo 1198416 1199759 := bstep (se 1 (by rfl) ⟨899819, by rfl⟩ : syracuseStep 1199759 = 1799639) B1799639
theorem B1797803 : Blo 1198416 1797803 := bstep (se 1 (by rfl) ⟨1348352, by rfl⟩ : syracuseStep 1797803 = 2696705) B2696705
theorem B7294637 : Blo 1198416 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B2698937 : Blo 1198416 2698937 := bstep (se 2 (by rfl) ⟨1012101, by rfl⟩ : syracuseStep 2698937 = 2024203) B2024203
theorem B1199803 : Blo 1198416 1199803 := bstep (se 1 (by rfl) ⟨899852, by rfl⟩ : syracuseStep 1199803 = 1799705) B1799705
theorem B1797833 : Blo 1198416 1797833 := bstep (se 2 (by rfl) ⟨674187, by rfl⟩ : syracuseStep 1797833 = 1348375) B1348375
theorem B1199879 : Blo 1198416 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B1199887 : Blo 1198416 1199887 := bstep (se 1 (by rfl) ⟨899915, by rfl⟩ : syracuseStep 1199887 = 1799831) B1799831
theorem B3649313 : Blo 1198416 3649313 := bstep (se 2 (by rfl) ⟨1368492, by rfl⟩ : syracuseStep 3649313 = 2736985) B2736985
theorem B7786277 : Blo 1198416 7786277 := bstep (se 4 (by rfl) ⟨729963, by rfl⟩ : syracuseStep 7786277 = 1459927) B1459927
theorem B1797947 : Blo 1198416 1797947 := bstep (se 1 (by rfl) ⟨1348460, by rfl⟩ : syracuseStep 1797947 = 2696921) B2696921
theorem B1199931 : Blo 1198416 1199931 := bstep (se 1 (by rfl) ⟨899948, by rfl⟩ : syracuseStep 1199931 = 1799897) B1799897
theorem B3239767 : Blo 1198416 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B1798007 : Blo 1198416 1798007 := bstep (se 1 (by rfl) ⟨1348505, by rfl⟩ : syracuseStep 1798007 = 2697011) B2697011
theorem B5762951 : Blo 1198416 5762951 := bstep (se 1 (by rfl) ⟨4322213, by rfl⟩ : syracuseStep 5762951 = 8644427) B8644427
theorem B1200007 : Blo 1198416 1200007 := bstep (se 1 (by rfl) ⟨900005, by rfl⟩ : syracuseStep 1200007 = 1800011) B1800011
theorem B1798031 : Blo 1198416 1798031 := bstep (se 1 (by rfl) ⟨1348523, by rfl⟩ : syracuseStep 1798031 = 2697047) B2697047
theorem B1200015 : Blo 1198416 1200015 := bstep (se 1 (by rfl) ⟨900011, by rfl⟩ : syracuseStep 1200015 = 1800023) B1800023
theorem B1798073 : Blo 1198416 1798073 := bstep (se 2 (by rfl) ⟨674277, by rfl⟩ : syracuseStep 1798073 = 1348555) B1348555
theorem B1200059 : Blo 1198416 1200059 := bstep (se 1 (by rfl) ⟨900044, by rfl⟩ : syracuseStep 1200059 = 1800089) B1800089
theorem B1798151 : Blo 1198416 1798151 := bstep (se 1 (by rfl) ⟨1348613, by rfl⟩ : syracuseStep 1798151 = 2697227) B2697227
theorem B1200135 : Blo 1198416 1200135 := bstep (se 1 (by rfl) ⟨900101, by rfl⟩ : syracuseStep 1200135 = 1800203) B1800203
theorem B2699279 : Blo 1198416 2699279 := bstep (se 1 (by rfl) ⟨2024459, by rfl⟩ : syracuseStep 2699279 = 4048919) B4048919
theorem B1200143 : Blo 1198416 1200143 := bstep (se 1 (by rfl) ⟨900107, by rfl⟩ : syracuseStep 1200143 = 1800215) B1800215
theorem B2699297 : Blo 1198416 2699297 := bstep (se 2 (by rfl) ⟨1012236, by rfl⟩ : syracuseStep 2699297 = 2024473) B2024473
theorem B1798187 : Blo 1198416 1798187 := bstep (se 1 (by rfl) ⟨1348640, by rfl⟩ : syracuseStep 1798187 = 2697281) B2697281
theorem B1921067 : Blo 1198416 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B1200187 : Blo 1198416 1200187 := bstep (se 1 (by rfl) ⟨900140, by rfl⟩ : syracuseStep 1200187 = 1800281) B1800281
theorem B1798217 : Blo 1198416 1798217 := bstep (se 2 (by rfl) ⟨674331, by rfl⟩ : syracuseStep 1798217 = 1348663) B1348663
theorem B1200263 : Blo 1198416 1200263 := bstep (se 1 (by rfl) ⟨900197, by rfl⟩ : syracuseStep 1200263 = 1800395) B1800395
theorem B1200271 : Blo 1198416 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1798331 : Blo 1198416 1798331 := bstep (se 1 (by rfl) ⟨1348748, by rfl⟩ : syracuseStep 1798331 = 2697497) B2697497
theorem B1200315 : Blo 1198416 1200315 := bstep (se 1 (by rfl) ⟨900236, by rfl⟩ : syracuseStep 1200315 = 1800473) B1800473
theorem B6484205 : Blo 1198416 6484205 := bstep (se 3 (by rfl) ⟨1215788, by rfl⟩ : syracuseStep 6484205 = 2431577) B2431577
theorem B1798391 : Blo 1198416 1798391 := bstep (se 1 (by rfl) ⟨1348793, by rfl⟩ : syracuseStep 1798391 = 2697587) B2697587
theorem B1200391 : Blo 1198416 1200391 := bstep (se 1 (by rfl) ⟨900293, by rfl⟩ : syracuseStep 1200391 = 1800587) B1800587
theorem B1798415 : Blo 1198416 1798415 := bstep (se 1 (by rfl) ⟨1348811, by rfl⟩ : syracuseStep 1798415 = 2697623) B2697623
theorem B1200399 : Blo 1198416 1200399 := bstep (se 1 (by rfl) ⟨900299, by rfl⟩ : syracuseStep 1200399 = 1800599) B1800599
theorem B6074675 : Blo 1198416 6074675 := bstep (se 1 (by rfl) ⟨4556006, by rfl⟩ : syracuseStep 6074675 = 9112013) B9112013
theorem B1798457 : Blo 1198416 1798457 := bstep (se 2 (by rfl) ⟨674421, by rfl⟩ : syracuseStep 1798457 = 1348843) B1348843
theorem B2879831 : Blo 1198416 2879831 := bstep (se 1 (by rfl) ⟨2159873, by rfl⟩ : syracuseStep 2879831 = 4319747) B4319747
theorem B2699639 : Blo 1198416 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B1798535 : Blo 1198416 1798535 := bstep (se 1 (by rfl) ⟨1348901, by rfl⟩ : syracuseStep 1798535 = 2697803) B2697803
theorem B1798571 : Blo 1198416 1798571 := bstep (se 1 (by rfl) ⟨1348928, by rfl⟩ : syracuseStep 1798571 = 2697857) B2697857
theorem B1798601 : Blo 1198416 1798601 := bstep (se 2 (by rfl) ⟨674475, by rfl⟩ : syracuseStep 1798601 = 1348951) B1348951
theorem B3240481 : Blo 1198416 3240481 := bstep (se 2 (by rfl) ⟨1215180, by rfl⟩ : syracuseStep 3240481 = 2430361) B2430361
theorem B2699819 : Blo 1198416 2699819 := bstep (se 1 (by rfl) ⟨2024864, by rfl⟩ : syracuseStep 2699819 = 4049729) B4049729
theorem B15381035 : Blo 1198416 15381035 := bstep (se 1 (by rfl) ⟨11535776, by rfl⟩ : syracuseStep 15381035 = 23071553) B23071553
theorem B1798715 : Blo 1198416 1798715 := bstep (se 1 (by rfl) ⟨1349036, by rfl⟩ : syracuseStep 1798715 = 2698073) B2698073
theorem B1798775 : Blo 1198416 1798775 := bstep (se 1 (by rfl) ⟨1349081, by rfl⟩ : syracuseStep 1798775 = 2698163) B2698163
theorem B6074999 : Blo 1198416 6074999 := bstep (se 1 (by rfl) ⟨4556249, by rfl⟩ : syracuseStep 6074999 = 9112499) B9112499
theorem B1348231 : Blo 1198416 1348231 := bstep (se 1 (by rfl) ⟨1011173, by rfl⟩ : syracuseStep 1348231 = 2022347) B2022347
theorem B1798799 : Blo 1198416 1798799 := bstep (se 1 (by rfl) ⟨1349099, by rfl⟩ : syracuseStep 1798799 = 2698199) B2698199
theorem B1798841 : Blo 1198416 1798841 := bstep (se 2 (by rfl) ⟨674565, by rfl⟩ : syracuseStep 1798841 = 1349131) B1349131
theorem B12972737 : Blo 1198416 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B5124809 : Blo 1198416 5124809 := bstep (se 2 (by rfl) ⟨1921803, by rfl⟩ : syracuseStep 5124809 = 3843607) B3843607
theorem B1798919 : Blo 1198416 1798919 := bstep (se 1 (by rfl) ⟨1349189, by rfl⟩ : syracuseStep 1798919 = 2698379) B2698379
theorem B3240719 : Blo 1198416 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B1798955 : Blo 1198416 1798955 := bstep (se 1 (by rfl) ⟨1349216, by rfl⟩ : syracuseStep 1798955 = 2698433) B2698433
theorem B1348411 : Blo 1198416 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B1798985 : Blo 1198416 1798985 := bstep (se 2 (by rfl) ⟨674619, by rfl⟩ : syracuseStep 1798985 = 1349239) B1349239
theorem B2700179 : Blo 1198416 2700179 := bstep (se 1 (by rfl) ⟨2025134, by rfl⟩ : syracuseStep 2700179 = 4050269) B4050269
theorem B1799099 : Blo 1198416 1799099 := bstep (se 1 (by rfl) ⟨1349324, by rfl⟩ : syracuseStep 1799099 = 2698649) B2698649
theorem B2700233 : Blo 1198416 2700233 := bstep (se 2 (by rfl) ⟨1012587, by rfl⟩ : syracuseStep 2700233 = 2025175) B2025175
theorem B1799159 : Blo 1198416 1799159 := bstep (se 1 (by rfl) ⟨1349369, by rfl⟩ : syracuseStep 1799159 = 2698739) B2698739
theorem B1799183 : Blo 1198416 1799183 := bstep (se 1 (by rfl) ⟨1349387, by rfl⟩ : syracuseStep 1799183 = 2698775) B2698775
theorem B6067223 : Blo 1198416 6067223 := bstep (se 1 (by rfl) ⟨4550417, by rfl⟩ : syracuseStep 6067223 = 9100835) B9100835
theorem B1799225 : Blo 1198416 1799225 := bstep (se 2 (by rfl) ⟨674709, by rfl⟩ : syracuseStep 1799225 = 1349419) B1349419
theorem B3036275 : Blo 1198416 3036275 := bstep (se 1 (by rfl) ⟨2277206, by rfl⟩ : syracuseStep 3036275 = 4554413) B4554413
theorem B1799303 : Blo 1198416 1799303 := bstep (se 1 (by rfl) ⟨1349477, by rfl⟩ : syracuseStep 1799303 = 2698955) B2698955
theorem B2880659 : Blo 1198416 2880659 := bstep (se 1 (by rfl) ⟨2160494, by rfl⟩ : syracuseStep 2880659 = 4320989) B4320989
theorem B1799339 : Blo 1198416 1799339 := bstep (se 1 (by rfl) ⟨1349504, by rfl⟩ : syracuseStep 1799339 = 2699009) B2699009
theorem B1922233 : Blo 1198416 1922233 := bstep (se 2 (by rfl) ⟨720837, by rfl⟩ : syracuseStep 1922233 = 1441675) B1441675
theorem B1799369 : Blo 1198416 1799369 := bstep (se 2 (by rfl) ⟨674763, by rfl⟩ : syracuseStep 1799369 = 1349527) B1349527
theorem B1348879 : Blo 1198416 1348879 := bstep (se 1 (by rfl) ⟨1011659, by rfl⟩ : syracuseStep 1348879 = 2023319) B2023319
theorem B1799483 : Blo 1198416 1799483 := bstep (se 1 (by rfl) ⟨1349612, by rfl⟩ : syracuseStep 1799483 = 2699225) B2699225
theorem B26645861 : Blo 1198416 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B4617587 : Blo 1198416 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B1799543 : Blo 1198416 1799543 := bstep (se 1 (by rfl) ⟨1349657, by rfl⟩ : syracuseStep 1799543 = 2699315) B2699315
theorem B12965255 : Blo 1198416 12965255 := bstep (se 1 (by rfl) ⟨9723941, by rfl⟩ : syracuseStep 12965255 = 19447883) B19447883
theorem B1799567 : Blo 1198416 1799567 := bstep (se 1 (by rfl) ⟨1349675, by rfl⟩ : syracuseStep 1799567 = 2699351) B2699351
theorem B1799609 : Blo 1198416 1799609 := bstep (se 2 (by rfl) ⟨674853, by rfl⟩ : syracuseStep 1799609 = 1349707) B1349707
theorem B1799687 : Blo 1198416 1799687 := bstep (se 1 (by rfl) ⟨1349765, by rfl⟩ : syracuseStep 1799687 = 2699531) B2699531
theorem B1799723 : Blo 1198416 1799723 := bstep (se 1 (by rfl) ⟨1349792, by rfl⟩ : syracuseStep 1799723 = 2699585) B2699585
theorem B6075971 : Blo 1198416 6075971 := bstep (se 1 (by rfl) ⟨4556978, by rfl⟩ : syracuseStep 6075971 = 9113957) B9113957
theorem B1799753 : Blo 1198416 1799753 := bstep (se 2 (by rfl) ⟨674907, by rfl⟩ : syracuseStep 1799753 = 1349815) B1349815
theorem B21345869 : Blo 1198416 21345869 := bstep (se 3 (by rfl) ⟨4002350, by rfl⟩ : syracuseStep 21345869 = 8004701) B8004701
theorem B3413623 : Blo 1198416 3413623 := bstep (se 1 (by rfl) ⟨2560217, by rfl⟩ : syracuseStep 3413623 = 5120435) B5120435
theorem B3036791 : Blo 1198416 3036791 := bstep (se 1 (by rfl) ⟨2277593, by rfl⟩ : syracuseStep 3036791 = 4555187) B4555187
theorem B2700935 : Blo 1198416 2700935 := bstep (se 1 (by rfl) ⟨2025701, by rfl⟩ : syracuseStep 2700935 = 4051403) B4051403
theorem B3413657 : Blo 1198416 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B1799867 : Blo 1198416 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B4994797 : Blo 1198416 4994797 := bstep (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) B1873049
theorem B1799927 : Blo 1198416 1799927 := bstep (se 1 (by rfl) ⟨1349945, by rfl⟩ : syracuseStep 1799927 = 2699891) B2699891
theorem B1349383 : Blo 1198416 1349383 := bstep (se 1 (by rfl) ⟨1012037, by rfl⟩ : syracuseStep 1349383 = 2024075) B2024075
theorem B3413771 : Blo 1198416 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B1799951 : Blo 1198416 1799951 := bstep (se 1 (by rfl) ⟨1349963, by rfl⟩ : syracuseStep 1799951 = 2699927) B2699927
theorem B3241757 : Blo 1198416 3241757 := bstep (se 3 (by rfl) ⟨607829, by rfl⟩ : syracuseStep 3241757 = 1215659) B1215659
theorem B1799993 : Blo 1198416 1799993 := bstep (se 2 (by rfl) ⟨674997, by rfl⟩ : syracuseStep 1799993 = 1349995) B1349995
theorem B1800071 : Blo 1198416 1800071 := bstep (se 1 (by rfl) ⟨1350053, by rfl⟩ : syracuseStep 1800071 = 2700107) B2700107
theorem B6076295 : Blo 1198416 6076295 := bstep (se 1 (by rfl) ⟨4557221, by rfl⟩ : syracuseStep 6076295 = 9114443) B9114443
theorem B5339033 : Blo 1198416 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1800107 : Blo 1198416 1800107 := bstep (se 1 (by rfl) ⟨1350080, by rfl⟩ : syracuseStep 1800107 = 2700161) B2700161
theorem B1349563 : Blo 1198416 1349563 := bstep (se 1 (by rfl) ⟨1012172, by rfl⟩ : syracuseStep 1349563 = 2024345) B2024345
theorem B1800137 : Blo 1198416 1800137 := bstep (se 2 (by rfl) ⟨675051, by rfl⟩ : syracuseStep 1800137 = 1350103) B1350103
theorem B2275361 : Blo 1198416 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B7297067 : Blo 1198416 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B1800251 : Blo 1198416 1800251 := bstep (se 1 (by rfl) ⟨1350188, by rfl⟩ : syracuseStep 1800251 = 2700377) B2700377
theorem B1800311 : Blo 1198416 1800311 := bstep (se 1 (by rfl) ⟨1350233, by rfl⟩ : syracuseStep 1800311 = 2700467) B2700467
theorem B1800335 : Blo 1198416 1800335 := bstep (se 1 (by rfl) ⟨1350251, by rfl⟩ : syracuseStep 1800335 = 2700503) B2700503
theorem B1800377 : Blo 1198416 1800377 := bstep (se 2 (by rfl) ⟨675141, by rfl⟩ : syracuseStep 1800377 = 1350283) B1350283
theorem B1800455 : Blo 1198416 1800455 := bstep (se 1 (by rfl) ⟨1350341, by rfl⟩ : syracuseStep 1800455 = 2700683) B2700683
theorem B2275627 : Blo 1198416 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B1800491 : Blo 1198416 1800491 := bstep (se 1 (by rfl) ⟨1350368, by rfl⟩ : syracuseStep 1800491 = 2700737) B2700737
theorem B1800521 : Blo 1198416 1800521 := bstep (se 2 (by rfl) ⟨675195, by rfl⟩ : syracuseStep 1800521 = 1350391) B1350391
theorem B1350031 : Blo 1198416 1350031 := bstep (se 1 (by rfl) ⟨1012523, by rfl⟩ : syracuseStep 1350031 = 2025047) B2025047
theorem B1620425 : Blo 1198416 1620425 := bstep (se 2 (by rfl) ⟨607659, by rfl⟩ : syracuseStep 1620425 = 1215319) B1215319
theorem B4045355 : Blo 1198416 4045355 := bstep (se 1 (by rfl) ⟨3034016, by rfl⟩ : syracuseStep 4045355 = 6068033) B6068033
theorem B3463741 : Blo 1198416 3463741 := bstep (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) B1298903
theorem B9230915 : Blo 1198416 9230915 := bstep (se 1 (by rfl) ⟨6923186, by rfl⟩ : syracuseStep 9230915 = 13846373) B13846373
theorem B5126723 : Blo 1198416 5126723 := bstep (se 1 (by rfl) ⟨3845042, by rfl⟩ : syracuseStep 5126723 = 7690085) B7690085
theorem B3037783 : Blo 1198416 3037783 := bstep (se 1 (by rfl) ⟨2278337, by rfl⟩ : syracuseStep 3037783 = 4556675) B4556675
theorem B2161337 : Blo 1198416 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B9730853 : Blo 1198416 9730853 := bstep (se 4 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 9730853 = 1824535) B1824535
theorem B3414899 : Blo 1198416 3414899 := bstep (se 1 (by rfl) ⟨2561174, by rfl⟩ : syracuseStep 3414899 = 5122349) B5122349
theorem B3038087 : Blo 1198416 3038087 := bstep (se 1 (by rfl) ⟨2278565, by rfl⟩ : syracuseStep 3038087 = 4557131) B4557131
theorem B5127047 : Blo 1198416 5127047 := bstep (se 1 (by rfl) ⟨3845285, by rfl⟩ : syracuseStep 5127047 = 7690571) B7690571
theorem B10238987 : Blo 1198416 10238987 := bstep (se 1 (by rfl) ⟨7679240, by rfl⟩ : syracuseStep 10238987 = 15358481) B15358481
theorem B3038219 : Blo 1198416 3038219 := bstep (se 1 (by rfl) ⟨2278664, by rfl⟩ : syracuseStep 3038219 = 4557329) B4557329
theorem B2161799 : Blo 1198416 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B3415297 : Blo 1198416 3415297 := bstep (se 2 (by rfl) ⟨1280736, by rfl⟩ : syracuseStep 3415297 = 2561473) B2561473
theorem B2022671 : Blo 1198416 2022671 := bstep (se 1 (by rfl) ⟨1517003, by rfl⟩ : syracuseStep 2022671 = 3034007) B3034007
theorem B3415355 : Blo 1198416 3415355 := bstep (se 1 (by rfl) ⟨2561516, by rfl⟩ : syracuseStep 3415355 = 5123033) B5123033
theorem B3841415 : Blo 1198416 3841415 := bstep (se 1 (by rfl) ⟨2881061, by rfl⟩ : syracuseStep 3841415 = 5762123) B5762123
theorem B2276743 : Blo 1198416 2276743 := bstep (se 1 (by rfl) ⟨1707557, by rfl⟩ : syracuseStep 2276743 = 3415115) B3415115
theorem B2735545 : Blo 1198416 2735545 := bstep (se 2 (by rfl) ⟨1025829, by rfl⟩ : syracuseStep 2735545 = 2051659) B2051659
theorem B98557397 : Blo 1198416 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B5766659 : Blo 1198416 5766659 := bstep (se 1 (by rfl) ⟨4324994, by rfl⟩ : syracuseStep 5766659 = 8649989) B8649989
theorem B2563643 : Blo 1198416 2563643 := bstep (se 1 (by rfl) ⟨1922732, by rfl⟩ : syracuseStep 2563643 = 3845465) B3845465
theorem B12967543 : Blo 1198416 12967543 := bstep (se 1 (by rfl) ⟨9725657, by rfl⟩ : syracuseStep 12967543 = 19451315) B19451315
theorem B3841825 : Blo 1198416 3841825 := bstep (se 2 (by rfl) ⟨1440684, by rfl⟩ : syracuseStep 3841825 = 2881369) B2881369
theorem B12967715 : Blo 1198416 12967715 := bstep (se 1 (by rfl) ⟨9725786, by rfl⟩ : syracuseStep 12967715 = 19451573) B19451573
theorem B2023211 : Blo 1198416 2023211 := bstep (se 1 (by rfl) ⟨1517408, by rfl⟩ : syracuseStep 2023211 = 3034817) B3034817
theorem B84156205 : Blo 1198416 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B4046651 : Blo 1198416 4046651 := bstep (se 1 (by rfl) ⟨3034988, by rfl⟩ : syracuseStep 4046651 = 6069977) B6069977
theorem B2277305 : Blo 1198416 2277305 := bstep (se 2 (by rfl) ⟨853989, by rfl⟩ : syracuseStep 2277305 = 1707979) B1707979
theorem B4046867 : Blo 1198416 4046867 := bstep (se 1 (by rfl) ⟨3035150, by rfl⟩ : syracuseStep 4046867 = 6070301) B6070301
theorem B2023481 : Blo 1198416 2023481 := bstep (se 2 (by rfl) ⟨758805, by rfl⟩ : syracuseStep 2023481 = 1517611) B1517611
theorem B18473285 : Blo 1198416 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B2163017 : Blo 1198416 2163017 := bstep (se 2 (by rfl) ⟨811131, by rfl⟩ : syracuseStep 2163017 = 1622263) B1622263
theorem B4047191 : Blo 1198416 4047191 := bstep (se 1 (by rfl) ⟨3035393, by rfl⟩ : syracuseStep 4047191 = 6070787) B6070787
theorem B3416539 : Blo 1198416 3416539 := bstep (se 1 (by rfl) ⟨2562404, by rfl⟩ : syracuseStep 3416539 = 5124809) B5124809
theorem B4555399 : Blo 1198416 4555399 := bstep (se 1 (by rfl) ⟨3416549, by rfl⟩ : syracuseStep 4555399 = 6833099) B6833099
theorem B8200877 : Blo 1198416 8200877 := bstep (se 3 (by rfl) ⟨1537664, by rfl⟩ : syracuseStep 8200877 = 3075329) B3075329
theorem B2024183 : Blo 1198416 2024183 := bstep (se 1 (by rfl) ⟨1518137, by rfl⟩ : syracuseStep 2024183 = 3036275) B3036275
theorem B4326263 : Blo 1198416 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B8643503 : Blo 1198416 8643503 := bstep (se 1 (by rfl) ⟨6482627, by rfl⟩ : syracuseStep 8643503 = 12965255) B12965255
theorem B4555703 : Blo 1198416 4555703 := bstep (se 1 (by rfl) ⟨3416777, by rfl⟩ : syracuseStep 4555703 = 6833555) B6833555
theorem B14230579 : Blo 1198416 14230579 := bstep (se 1 (by rfl) ⟨10672934, by rfl⟩ : syracuseStep 14230579 = 21345869) B21345869
theorem B2024527 : Blo 1198416 2024527 := bstep (se 1 (by rfl) ⟨1518395, by rfl⟩ : syracuseStep 2024527 = 3036791) B3036791
theorem B7685239 : Blo 1198416 7685239 := bstep (se 1 (by rfl) ⟨5763929, by rfl⟩ : syracuseStep 7685239 = 11527859) B11527859
theorem B2024777 : Blo 1198416 2024777 := bstep (se 2 (by rfl) ⟨759291, by rfl⟩ : syracuseStep 2024777 = 1518583) B1518583
theorem B1516907 : Blo 1198416 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B2278763 : Blo 1198416 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B4048271 : Blo 1198416 4048271 := bstep (se 1 (by rfl) ⟨3036203, by rfl⟩ : syracuseStep 4048271 = 6072407) B6072407
theorem B2696903 : Blo 1198416 2696903 := bstep (se 1 (by rfl) ⟨2022677, by rfl⟩ : syracuseStep 2696903 = 4045355) B4045355
theorem B4048595 : Blo 1198416 4048595 := bstep (se 1 (by rfl) ⟨3036446, by rfl⟩ : syracuseStep 4048595 = 6072893) B6072893
theorem B6153943 : Blo 1198416 6153943 := bstep (se 1 (by rfl) ⟨4615457, by rfl⟩ : syracuseStep 6153943 = 9230915) B9230915
theorem B3417815 : Blo 1198416 3417815 := bstep (se 1 (by rfl) ⟨2563361, by rfl⟩ : syracuseStep 3417815 = 5126723) B5126723
theorem B2025209 : Blo 1198416 2025209 := bstep (se 2 (by rfl) ⟨759453, by rfl⟩ : syracuseStep 2025209 = 1518907) B1518907
theorem B17278757 : Blo 1198416 17278757 := bstep (se 4 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 17278757 = 3239767) B3239767
theorem B9103265 : Blo 1198416 9103265 := bstep (se 2 (by rfl) ⟨3413724, by rfl⟩ : syracuseStep 9103265 = 6827449) B6827449
theorem B3647393 : Blo 1198416 3647393 := bstep (se 2 (by rfl) ⟨1367772, by rfl⟩ : syracuseStep 3647393 = 2735545) B2735545
theorem B2025391 : Blo 1198416 2025391 := bstep (se 1 (by rfl) ⟨1519043, by rfl⟩ : syracuseStep 2025391 = 3038087) B3038087
theorem B3418031 : Blo 1198416 3418031 := bstep (se 1 (by rfl) ⟨2563523, by rfl⟩ : syracuseStep 3418031 = 5127047) B5127047
theorem B6825991 : Blo 1198416 6825991 := bstep (se 1 (by rfl) ⟨5119493, by rfl⟩ : syracuseStep 6825991 = 10238987) B10238987
theorem B2025479 : Blo 1198416 2025479 := bstep (se 1 (by rfl) ⟨1519109, by rfl⟩ : syracuseStep 2025479 = 3038219) B3038219
theorem B4556857 : Blo 1198416 4556857 := bstep (se 2 (by rfl) ⟨1708821, by rfl⟩ : syracuseStep 4556857 = 3417643) B3417643
theorem B3844439 : Blo 1198416 3844439 := bstep (se 1 (by rfl) ⟨2883329, by rfl⟩ : syracuseStep 3844439 = 5766659) B5766659
theorem B1198431 : Blo 1198416 1198431 := bstep (se 1 (by rfl) ⟨898823, by rfl⟩ : syracuseStep 1198431 = 1797647) B1797647
theorem B4557161 : Blo 1198416 4557161 := bstep (se 2 (by rfl) ⟨1708935, by rfl⟩ : syracuseStep 4557161 = 3417871) B3417871
theorem B1198459 : Blo 1198416 1198459 := bstep (se 1 (by rfl) ⟨898844, by rfl⟩ : syracuseStep 1198459 = 1797689) B1797689
theorem B5122433 : Blo 1198416 5122433 := bstep (se 2 (by rfl) ⟨1920912, by rfl⟩ : syracuseStep 5122433 = 3841825) B3841825
theorem B112208273 : Blo 1198416 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B1198511 : Blo 1198416 1198511 := bstep (se 1 (by rfl) ⟨898883, by rfl⟩ : syracuseStep 1198511 = 1797767) B1797767
theorem B1198535 : Blo 1198416 1198535 := bstep (se 1 (by rfl) ⟨898901, by rfl⟩ : syracuseStep 1198535 = 1797803) B1797803
theorem B1198555 : Blo 1198416 1198555 := bstep (se 1 (by rfl) ⟨898916, by rfl⟩ : syracuseStep 1198555 = 1797833) B1797833
theorem B8645143 : Blo 1198416 8645143 := bstep (se 1 (by rfl) ⟨6483857, by rfl⟩ : syracuseStep 8645143 = 12967715) B12967715
theorem B1198631 : Blo 1198416 1198631 := bstep (se 1 (by rfl) ⟨898973, by rfl⟩ : syracuseStep 1198631 = 1797947) B1797947
theorem B2697767 : Blo 1198416 2697767 := bstep (se 1 (by rfl) ⟨2023325, by rfl⟩ : syracuseStep 2697767 = 4046651) B4046651
theorem B1198671 : Blo 1198416 1198671 := bstep (se 1 (by rfl) ⟨899003, by rfl⟩ : syracuseStep 1198671 = 1798007) B1798007
theorem B1198687 : Blo 1198416 1198687 := bstep (se 1 (by rfl) ⟨899015, by rfl⟩ : syracuseStep 1198687 = 1798031) B1798031
theorem B1198715 : Blo 1198416 1198715 := bstep (se 1 (by rfl) ⟨899036, by rfl⟩ : syracuseStep 1198715 = 1798073) B1798073
theorem B1518203 : Blo 1198416 1518203 := bstep (se 1 (by rfl) ⟨1138652, by rfl⟩ : syracuseStep 1518203 = 2277305) B2277305
theorem B1198767 : Blo 1198416 1198767 := bstep (se 1 (by rfl) ⟨899075, by rfl⟩ : syracuseStep 1198767 = 1798151) B1798151
theorem B1198791 : Blo 1198416 1198791 := bstep (se 1 (by rfl) ⟨899093, by rfl⟩ : syracuseStep 1198791 = 1798187) B1798187
theorem B1280711 : Blo 1198416 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B1198811 : Blo 1198416 1198811 := bstep (se 1 (by rfl) ⟨899108, by rfl⟩ : syracuseStep 1198811 = 1798217) B1798217
theorem B1198887 : Blo 1198416 1198887 := bstep (se 1 (by rfl) ⟨899165, by rfl⟩ : syracuseStep 1198887 = 1798331) B1798331
theorem B1198927 : Blo 1198416 1198927 := bstep (se 1 (by rfl) ⟨899195, by rfl⟩ : syracuseStep 1198927 = 1798391) B1798391
theorem B1198943 : Blo 1198416 1198943 := bstep (se 1 (by rfl) ⟨899207, by rfl⟩ : syracuseStep 1198943 = 1798415) B1798415
theorem B2698091 : Blo 1198416 2698091 := bstep (se 1 (by rfl) ⟨2023568, by rfl⟩ : syracuseStep 2698091 = 4047137) B4047137
theorem B4049783 : Blo 1198416 4049783 := bstep (se 1 (by rfl) ⟨3037337, by rfl⟩ : syracuseStep 4049783 = 6074675) B6074675
theorem B1198971 : Blo 1198416 1198971 := bstep (se 1 (by rfl) ⟨899228, by rfl⟩ : syracuseStep 1198971 = 1798457) B1798457
theorem B2698145 : Blo 1198416 2698145 := bstep (se 2 (by rfl) ⟨1011804, by rfl⟩ : syracuseStep 2698145 = 2023609) B2023609
theorem B1199023 : Blo 1198416 1199023 := bstep (se 1 (by rfl) ⟨899267, by rfl⟩ : syracuseStep 1199023 = 1798535) B1798535
theorem B1199047 : Blo 1198416 1199047 := bstep (se 1 (by rfl) ⟨899285, by rfl⟩ : syracuseStep 1199047 = 1798571) B1798571
theorem B1199067 : Blo 1198416 1199067 := bstep (se 1 (by rfl) ⟨899300, by rfl⟩ : syracuseStep 1199067 = 1798601) B1798601
theorem B6925313 : Blo 1198416 6925313 := bstep (se 2 (by rfl) ⟨2596992, by rfl⟩ : syracuseStep 6925313 = 5193985) B5193985
theorem B1199143 : Blo 1198416 1199143 := bstep (se 1 (by rfl) ⟨899357, by rfl⟩ : syracuseStep 1199143 = 1798715) B1798715
theorem B3034169 : Blo 1198416 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B1199183 : Blo 1198416 1199183 := bstep (se 1 (by rfl) ⟨899387, by rfl⟩ : syracuseStep 1199183 = 1798775) B1798775
theorem B4049999 : Blo 1198416 4049999 := bstep (se 1 (by rfl) ⟨3037499, by rfl⟩ : syracuseStep 4049999 = 6074999) B6074999
theorem B1199199 : Blo 1198416 1199199 := bstep (se 1 (by rfl) ⟨899399, by rfl⟩ : syracuseStep 1199199 = 1798799) B1798799
theorem B1199227 : Blo 1198416 1199227 := bstep (se 1 (by rfl) ⟨899420, by rfl⟩ : syracuseStep 1199227 = 1798841) B1798841
theorem B1199279 : Blo 1198416 1199279 := bstep (se 1 (by rfl) ⟨899459, by rfl⟩ : syracuseStep 1199279 = 1798919) B1798919
theorem B38890691 : Blo 1198416 38890691 := bstep (se 1 (by rfl) ⟨29168018, by rfl⟩ : syracuseStep 38890691 = 58336037) B58336037
theorem B1199303 : Blo 1198416 1199303 := bstep (se 1 (by rfl) ⟨899477, by rfl⟩ : syracuseStep 1199303 = 1798955) B1798955
theorem B1199323 : Blo 1198416 1199323 := bstep (se 1 (by rfl) ⟨899492, by rfl⟩ : syracuseStep 1199323 = 1798985) B1798985
theorem B2698487 : Blo 1198416 2698487 := bstep (se 1 (by rfl) ⟨2023865, by rfl⟩ : syracuseStep 2698487 = 4047731) B4047731
theorem B6925591 : Blo 1198416 6925591 := bstep (se 1 (by rfl) ⟨5194193, by rfl⟩ : syracuseStep 6925591 = 10388387) B10388387
theorem B1199399 : Blo 1198416 1199399 := bstep (se 1 (by rfl) ⟨899549, by rfl⟩ : syracuseStep 1199399 = 1799099) B1799099
theorem B1199439 : Blo 1198416 1199439 := bstep (se 1 (by rfl) ⟨899579, by rfl⟩ : syracuseStep 1199439 = 1799159) B1799159
theorem B1199455 : Blo 1198416 1199455 := bstep (se 1 (by rfl) ⟨899591, by rfl⟩ : syracuseStep 1199455 = 1799183) B1799183
theorem B1199483 : Blo 1198416 1199483 := bstep (se 1 (by rfl) ⟨899612, by rfl⟩ : syracuseStep 1199483 = 1799225) B1799225
theorem B4320641 : Blo 1198416 4320641 := bstep (se 2 (by rfl) ⟨1620240, by rfl⟩ : syracuseStep 4320641 = 3240481) B3240481
theorem B1199535 : Blo 1198416 1199535 := bstep (se 1 (by rfl) ⟨899651, by rfl⟩ : syracuseStep 1199535 = 1799303) B1799303
theorem B1920439 : Blo 1198416 1920439 := bstep (se 1 (by rfl) ⟨1440329, by rfl⟩ : syracuseStep 1920439 = 2880659) B2880659
theorem B1199559 : Blo 1198416 1199559 := bstep (se 1 (by rfl) ⟨899669, by rfl⟩ : syracuseStep 1199559 = 1799339) B1799339
theorem B4050377 : Blo 1198416 4050377 := bstep (se 2 (by rfl) ⟨1518891, by rfl⟩ : syracuseStep 4050377 = 3037783) B3037783
theorem B1199579 : Blo 1198416 1199579 := bstep (se 1 (by rfl) ⟨899684, by rfl⟩ : syracuseStep 1199579 = 1799369) B1799369
theorem B1797641 : Blo 1198416 1797641 := bstep (se 2 (by rfl) ⟨674115, by rfl⟩ : syracuseStep 1797641 = 1348231) B1348231
theorem B3845657 : Blo 1198416 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B1797671 : Blo 1198416 1797671 := bstep (se 1 (by rfl) ⟨1348253, by rfl⟩ : syracuseStep 1797671 = 2696507) B2696507
theorem B1199655 : Blo 1198416 1199655 := bstep (se 1 (by rfl) ⟨899741, by rfl⟩ : syracuseStep 1199655 = 1799483) B1799483
theorem B7679549 : Blo 1198416 7679549 := bstep (se 3 (by rfl) ⟨1439915, by rfl⟩ : syracuseStep 7679549 = 2879831) B2879831
theorem B17763907 : Blo 1198416 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B1199695 : Blo 1198416 1199695 := bstep (se 1 (by rfl) ⟨899771, by rfl⟩ : syracuseStep 1199695 = 1799543) B1799543
theorem B1199711 : Blo 1198416 1199711 := bstep (se 1 (by rfl) ⟨899783, by rfl⟩ : syracuseStep 1199711 = 1799567) B1799567
theorem B1797755 : Blo 1198416 1797755 := bstep (se 1 (by rfl) ⟨1348316, by rfl⟩ : syracuseStep 1797755 = 2696633) B2696633
theorem B1199739 : Blo 1198416 1199739 := bstep (se 1 (by rfl) ⟨899804, by rfl⟩ : syracuseStep 1199739 = 1799609) B1799609
theorem B5123731 : Blo 1198416 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B1199791 : Blo 1198416 1199791 := bstep (se 1 (by rfl) ⟨899843, by rfl⟩ : syracuseStep 1199791 = 1799687) B1799687
theorem B5467837 : Blo 1198416 5467837 := bstep (se 3 (by rfl) ⟨1025219, by rfl⟩ : syracuseStep 5467837 = 2050439) B2050439
theorem B1199815 : Blo 1198416 1199815 := bstep (se 1 (by rfl) ⟨899861, by rfl⟩ : syracuseStep 1199815 = 1799723) B1799723
theorem B5844695 : Blo 1198416 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B4050647 : Blo 1198416 4050647 := bstep (se 1 (by rfl) ⟨3037985, by rfl⟩ : syracuseStep 4050647 = 6075971) B6075971
theorem B1199835 : Blo 1198416 1199835 := bstep (se 1 (by rfl) ⟨899876, by rfl⟩ : syracuseStep 1199835 = 1799753) B1799753
theorem B1797881 : Blo 1198416 1797881 := bstep (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) B1348411
theorem B1199911 : Blo 1198416 1199911 := bstep (se 1 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 1199911 = 1799867) B1799867
theorem B2699081 : Blo 1198416 2699081 := bstep (se 2 (by rfl) ⟨1012155, by rfl⟩ : syracuseStep 2699081 = 2024311) B2024311
theorem B1199951 : Blo 1198416 1199951 := bstep (se 1 (by rfl) ⟨899963, by rfl⟩ : syracuseStep 1199951 = 1799927) B1799927
theorem B1797983 : Blo 1198416 1797983 := bstep (se 1 (by rfl) ⟨1348487, by rfl⟩ : syracuseStep 1797983 = 2696975) B2696975
theorem B1199967 : Blo 1198416 1199967 := bstep (se 1 (by rfl) ⟨899975, by rfl⟩ : syracuseStep 1199967 = 1799951) B1799951
theorem B1797995 : Blo 1198416 1797995 := bstep (se 1 (by rfl) ⟨1348496, by rfl⟩ : syracuseStep 1797995 = 2696993) B2696993
theorem B4321133 : Blo 1198416 4321133 := bstep (se 3 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 4321133 = 1620425) B1620425
theorem B1199995 : Blo 1198416 1199995 := bstep (se 1 (by rfl) ⟨899996, by rfl⟩ : syracuseStep 1199995 = 1799993) B1799993
theorem B8761223 : Blo 1198416 8761223 := bstep (se 1 (by rfl) ⟨6570917, by rfl⟩ : syracuseStep 8761223 = 13141835) B13141835
theorem B1200047 : Blo 1198416 1200047 := bstep (se 1 (by rfl) ⟨900035, by rfl⟩ : syracuseStep 1200047 = 1800071) B1800071
theorem B4050863 : Blo 1198416 4050863 := bstep (se 1 (by rfl) ⟨3038147, by rfl⟩ : syracuseStep 4050863 = 6076295) B6076295
theorem B3559355 : Blo 1198416 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B1200071 : Blo 1198416 1200071 := bstep (se 1 (by rfl) ⟨900053, by rfl⟩ : syracuseStep 1200071 = 1800107) B1800107
theorem B1200091 : Blo 1198416 1200091 := bstep (se 1 (by rfl) ⟨900068, by rfl⟩ : syracuseStep 1200091 = 1800137) B1800137
theorem B1200167 : Blo 1198416 1200167 := bstep (se 1 (by rfl) ⟨900125, by rfl⟩ : syracuseStep 1200167 = 1800251) B1800251
theorem B1798223 : Blo 1198416 1798223 := bstep (se 1 (by rfl) ⟨1348667, by rfl⟩ : syracuseStep 1798223 = 2697335) B2697335
theorem B1200207 : Blo 1198416 1200207 := bstep (se 1 (by rfl) ⟨900155, by rfl⟩ : syracuseStep 1200207 = 1800311) B1800311
theorem B1200223 : Blo 1198416 1200223 := bstep (se 1 (by rfl) ⟨900167, by rfl⟩ : syracuseStep 1200223 = 1800335) B1800335
theorem B1200251 : Blo 1198416 1200251 := bstep (se 1 (by rfl) ⟨900188, by rfl⟩ : syracuseStep 1200251 = 1800377) B1800377
theorem B4550813 : Blo 1198416 4550813 := bstep (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) B1706555
theorem B1200303 : Blo 1198416 1200303 := bstep (se 1 (by rfl) ⟨900227, by rfl⟩ : syracuseStep 1200303 = 1800455) B1800455
theorem B1798343 : Blo 1198416 1798343 := bstep (se 1 (by rfl) ⟨1348757, by rfl⟩ : syracuseStep 1798343 = 2697515) B2697515
theorem B1200327 : Blo 1198416 1200327 := bstep (se 1 (by rfl) ⟨900245, by rfl⟩ : syracuseStep 1200327 = 1800491) B1800491
theorem B1200347 : Blo 1198416 1200347 := bstep (se 1 (by rfl) ⟨900260, by rfl⟩ : syracuseStep 1200347 = 1800521) B1800521
theorem B3895543 : Blo 1198416 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B2191711 : Blo 1198416 2191711 := bstep (se 1 (by rfl) ⟨1643783, by rfl⟩ : syracuseStep 2191711 = 3287567) B3287567
theorem B1798505 : Blo 1198416 1798505 := bstep (se 2 (by rfl) ⟨674439, by rfl⟩ : syracuseStep 1798505 = 1348879) B1348879
theorem B1798583 : Blo 1198416 1798583 := bstep (se 1 (by rfl) ⟨1348937, by rfl⟩ : syracuseStep 1798583 = 2697875) B2697875
theorem B1798619 : Blo 1198416 1798619 := bstep (se 1 (by rfl) ⟨1348964, by rfl⟩ : syracuseStep 1798619 = 2697929) B2697929
theorem B5763565 : Blo 1198416 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B3035657 : Blo 1198416 3035657 := bstep (se 2 (by rfl) ⟨1138371, by rfl⟩ : syracuseStep 3035657 = 2276743) B2276743
theorem B2699873 : Blo 1198416 2699873 := bstep (se 2 (by rfl) ⟨1012452, by rfl⟩ : syracuseStep 2699873 = 2024905) B2024905
theorem B2880139 : Blo 1198416 2880139 := bstep (se 1 (by rfl) ⟨2160104, by rfl⟩ : syracuseStep 2880139 = 4320209) B4320209
theorem B3895955 : Blo 1198416 3895955 := bstep (se 1 (by rfl) ⟨2921966, by rfl⟩ : syracuseStep 3895955 = 5843933) B5843933
theorem B3650237 : Blo 1198416 3650237 := bstep (se 3 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 3650237 = 1368839) B1368839
theorem B2306807 : Blo 1198416 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B2429689 : Blo 1198416 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B4551497 : Blo 1198416 4551497 := bstep (se 2 (by rfl) ⟨1706811, by rfl⟩ : syracuseStep 4551497 = 3413623) B3413623
theorem B17290057 : Blo 1198416 17290057 := bstep (se 2 (by rfl) ⟨6483771, by rfl⟩ : syracuseStep 17290057 = 12967543) B12967543
theorem B1348447 : Blo 1198416 1348447 := bstep (se 1 (by rfl) ⟨1011335, by rfl⟩ : syracuseStep 1348447 = 2022671) B2022671
theorem B6828907 : Blo 1198416 6828907 := bstep (se 1 (by rfl) ⟨5121680, by rfl⟩ : syracuseStep 6828907 = 10243361) B10243361
theorem B2560943 : Blo 1198416 2560943 := bstep (se 1 (by rfl) ⟨1920707, by rfl⟩ : syracuseStep 2560943 = 3841415) B3841415
theorem B1799087 : Blo 1198416 1799087 := bstep (se 1 (by rfl) ⟨1349315, by rfl⟩ : syracuseStep 1799087 = 2698631) B2698631
theorem B2700215 : Blo 1198416 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B65704931 : Blo 1198416 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B1799177 : Blo 1198416 1799177 := bstep (se 2 (by rfl) ⟨674691, by rfl⟩ : syracuseStep 1799177 = 1349383) B1349383
theorem B1799207 : Blo 1198416 1799207 := bstep (se 1 (by rfl) ⟨1349405, by rfl⟩ : syracuseStep 1799207 = 2698811) B2698811
theorem B1709095 : Blo 1198416 1709095 := bstep (se 1 (by rfl) ⟨1281821, by rfl⟩ : syracuseStep 1709095 = 2563643) B2563643
theorem B4863091 : Blo 1198416 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B1799291 : Blo 1198416 1799291 := bstep (se 1 (by rfl) ⟨1349468, by rfl⟩ : syracuseStep 1799291 = 2698937) B2698937
theorem B5190851 : Blo 1198416 5190851 := bstep (se 1 (by rfl) ⟨3893138, by rfl⟩ : syracuseStep 5190851 = 7786277) B7786277
theorem B1348807 : Blo 1198416 1348807 := bstep (se 1 (by rfl) ⟨1011605, by rfl⟩ : syracuseStep 1348807 = 2023211) B2023211
theorem B1799417 : Blo 1198416 1799417 := bstep (se 2 (by rfl) ⟨674781, by rfl⟩ : syracuseStep 1799417 = 1349563) B1349563
theorem B4551997 : Blo 1198416 4551997 := bstep (se 3 (by rfl) ⟨853499, by rfl⟩ : syracuseStep 4551997 = 1706999) B1706999
theorem B1799519 : Blo 1198416 1799519 := bstep (se 1 (by rfl) ⟨1349639, by rfl⟩ : syracuseStep 1799519 = 2699279) B2699279
theorem B1799531 : Blo 1198416 1799531 := bstep (se 1 (by rfl) ⟨1349648, by rfl⟩ : syracuseStep 1799531 = 2699297) B2699297
theorem B4322803 : Blo 1198416 4322803 := bstep (se 1 (by rfl) ⟨3242102, by rfl⟩ : syracuseStep 4322803 = 6484205) B6484205
theorem B2700809 : Blo 1198416 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B1799759 : Blo 1198416 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B3036811 : Blo 1198416 3036811 := bstep (se 1 (by rfl) ⟨2277608, by rfl⟩ : syracuseStep 3036811 = 4555217) B4555217
theorem B1799879 : Blo 1198416 1799879 := bstep (se 1 (by rfl) ⟨1349909, by rfl⟩ : syracuseStep 1799879 = 2699819) B2699819
theorem B10254023 : Blo 1198416 10254023 := bstep (se 1 (by rfl) ⟨7690517, by rfl⟩ : syracuseStep 10254023 = 15381035) B15381035
theorem B8648491 : Blo 1198416 8648491 := bstep (se 1 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 8648491 = 12972737) B12972737
theorem B2160479 : Blo 1198416 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B1800041 : Blo 1198416 1800041 := bstep (se 2 (by rfl) ⟨675015, by rfl⟩ : syracuseStep 1800041 = 1350031) B1350031
theorem B1800119 : Blo 1198416 1800119 := bstep (se 1 (by rfl) ⟨1350089, by rfl⟩ : syracuseStep 1800119 = 2700179) B2700179
theorem B3037115 : Blo 1198416 3037115 := bstep (se 1 (by rfl) ⟨2277836, by rfl⟩ : syracuseStep 3037115 = 4555673) B4555673
theorem B1800155 : Blo 1198416 1800155 := bstep (se 1 (by rfl) ⟨1350116, by rfl⟩ : syracuseStep 1800155 = 2700233) B2700233
theorem B4044815 : Blo 1198416 4044815 := bstep (se 1 (by rfl) ⟨3033611, by rfl⟩ : syracuseStep 4044815 = 6067223) B6067223
theorem B1349671 : Blo 1198416 1349671 := bstep (se 1 (by rfl) ⟨1012253, by rfl⟩ : syracuseStep 1349671 = 2024507) B2024507
theorem B9730205 : Blo 1198416 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B3078391 : Blo 1198416 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B1800623 : Blo 1198416 1800623 := bstep (se 1 (by rfl) ⟨1350467, by rfl⟩ : syracuseStep 1800623 = 2700935) B2700935
theorem B2275771 : Blo 1198416 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B2275847 : Blo 1198416 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B2161171 : Blo 1198416 2161171 := bstep (se 1 (by rfl) ⟨1620878, by rfl⟩ : syracuseStep 2161171 = 3241757) B3241757
theorem B4045409 : Blo 1198416 4045409 := bstep (se 2 (by rfl) ⟨1517028, by rfl⟩ : syracuseStep 4045409 = 3034057) B3034057
theorem B3840635 : Blo 1198416 3840635 := bstep (se 1 (by rfl) ⟨2880476, by rfl⟩ : syracuseStep 3840635 = 5760953) B5760953
theorem B3414727 : Blo 1198416 3414727 := bstep (se 1 (by rfl) ⟨2561045, by rfl⟩ : syracuseStep 3414727 = 5122091) B5122091
theorem B4864711 : Blo 1198416 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B3037895 : Blo 1198416 3037895 := bstep (se 1 (by rfl) ⟨2278421, by rfl⟩ : syracuseStep 3037895 = 4556843) B4556843
theorem B3037945 : Blo 1198416 3037945 := bstep (se 2 (by rfl) ⟨1139229, by rfl⟩ : syracuseStep 3037945 = 2278459) B2278459
theorem B2276257 : Blo 1198416 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B2562977 : Blo 1198416 2562977 := bstep (se 2 (by rfl) ⟨961116, by rfl⟩ : syracuseStep 2562977 = 1922233) B1922233
theorem B6069167 : Blo 1198416 6069167 := bstep (se 1 (by rfl) ⟨4551875, by rfl⟩ : syracuseStep 6069167 = 9103751) B9103751
theorem B4553729 : Blo 1198416 4553729 := bstep (se 2 (by rfl) ⟨1707648, by rfl⟩ : syracuseStep 4553729 = 3415297) B3415297
theorem B6487235 : Blo 1198416 6487235 := bstep (se 1 (by rfl) ⟨4865426, by rfl⟩ : syracuseStep 6487235 = 9730853) B9730853
theorem B2276599 : Blo 1198416 2276599 := bstep (se 1 (by rfl) ⟨1707449, by rfl⟩ : syracuseStep 2276599 = 3414899) B3414899
theorem B2563319 : Blo 1198416 2563319 := bstep (se 1 (by rfl) ⟨1922489, by rfl⟩ : syracuseStep 2563319 = 3844979) B3844979
theorem B11525399 : Blo 1198416 11525399 := bstep (se 1 (by rfl) ⟨8644049, by rfl⟩ : syracuseStep 11525399 = 17288099) B17288099
theorem B5119357 : Blo 1198416 5119357 := bstep (se 3 (by rfl) ⟨959879, by rfl⟩ : syracuseStep 5119357 = 1919759) B1919759
theorem B32841085 : Blo 1198416 32841085 := bstep (se 3 (by rfl) ⟨6157703, by rfl⟩ : syracuseStep 32841085 = 12315407) B12315407
theorem B2022799 : Blo 1198416 2022799 := bstep (se 1 (by rfl) ⟨1517099, by rfl⟩ : syracuseStep 2022799 = 3034199) B3034199
theorem B1441199 : Blo 1198416 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B2276903 : Blo 1198416 2276903 := bstep (se 1 (by rfl) ⟨1707677, by rfl⟩ : syracuseStep 2276903 = 3415355) B3415355
theorem B6659729 : Blo 1198416 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B7020179 : Blo 1198416 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B6151895 : Blo 1198416 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B2432875 : Blo 1198416 2432875 := bstep (se 1 (by rfl) ⟨1824656, by rfl⟩ : syracuseStep 2432875 = 3649313) B3649313
theorem B3841967 : Blo 1198416 3841967 := bstep (se 1 (by rfl) ⟨2881475, by rfl⟩ : syracuseStep 3841967 = 5762951) B5762951
theorem B9101321 : Blo 1198416 9101321 := bstep (se 2 (by rfl) ⟨3412995, by rfl⟩ : syracuseStep 9101321 = 6825991) B6825991
theorem B1442011 : Blo 1198416 1442011 := bstep (se 1 (by rfl) ⟨1081508, by rfl⟩ : syracuseStep 1442011 = 2163017) B2163017
theorem B5194057 : Blo 1198416 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B4104521 : Blo 1198416 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B2023771 : Blo 1198416 2023771 := bstep (se 1 (by rfl) ⟨1517828, by rfl⟩ : syracuseStep 2023771 = 3035657) B3035657
theorem B2597303 : Blo 1198416 2597303 := bstep (se 1 (by rfl) ⟨1947977, by rfl⟩ : syracuseStep 2597303 = 3895955) B3895955
theorem B2433491 : Blo 1198416 2433491 := bstep (se 1 (by rfl) ⟨1825118, by rfl⟩ : syracuseStep 2433491 = 3650237) B3650237
theorem B2884175 : Blo 1198416 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B4555385 : Blo 1198416 4555385 := bstep (se 2 (by rfl) ⟨1708269, by rfl⟩ : syracuseStep 4555385 = 3416539) B3416539
theorem B7684753 : Blo 1198416 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B43803287 : Blo 1198416 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B11526857 : Blo 1198416 11526857 := bstep (se 2 (by rfl) ⟨4322571, by rfl⟩ : syracuseStep 11526857 = 8645143) B8645143
theorem B23053409 : Blo 1198416 23053409 := bstep (se 2 (by rfl) ⟨8645028, by rfl⟩ : syracuseStep 23053409 = 17290057) B17290057
theorem B3843197 : Blo 1198416 3843197 := bstep (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) B1441199
theorem B2278543 : Blo 1198416 2278543 := bstep (se 1 (by rfl) ⟨1708907, by rfl⟩ : syracuseStep 2278543 = 3417815) B3417815
theorem B11519171 : Blo 1198416 11519171 := bstep (se 1 (by rfl) ⟨8639378, by rfl⟩ : syracuseStep 11519171 = 17278757) B17278757
theorem B2278687 : Blo 1198416 2278687 := bstep (se 1 (by rfl) ⟨1709015, by rfl⟩ : syracuseStep 2278687 = 3418031) B3418031
theorem B2024743 : Blo 1198416 2024743 := bstep (se 1 (by rfl) ⟨1518557, by rfl⟩ : syracuseStep 2024743 = 3037115) B3037115
theorem B2696543 : Blo 1198416 2696543 := bstep (se 1 (by rfl) ⟨2022407, by rfl⟩ : syracuseStep 2696543 = 4044815) B4044815
theorem B2278793 : Blo 1198416 2278793 := bstep (se 2 (by rfl) ⟨854547, by rfl⟩ : syracuseStep 2278793 = 1709095) B1709095
theorem B18974105 : Blo 1198416 18974105 := bstep (se 2 (by rfl) ⟨7115289, by rfl⟩ : syracuseStep 18974105 = 14230579) B14230579
theorem B4048541 : Blo 1198416 4048541 := bstep (se 3 (by rfl) ⟨759101, by rfl⟩ : syracuseStep 4048541 = 1518203) B1518203
theorem B1517231 : Blo 1198416 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B2696939 : Blo 1198416 2696939 := bstep (se 1 (by rfl) ⟨2022704, by rfl⟩ : syracuseStep 2696939 = 4045409) B4045409
theorem B2025263 : Blo 1198416 2025263 := bstep (se 1 (by rfl) ⟨1518947, by rfl⟩ : syracuseStep 2025263 = 3037895) B3037895
theorem B87476021 : Blo 1198416 87476021 := bstep (se 5 (by rfl) ⟨4100438, by rfl⟩ : syracuseStep 87476021 = 8200877) B8200877
theorem B6825809 : Blo 1198416 6825809 := bstep (se 2 (by rfl) ⟨2559678, by rfl⟩ : syracuseStep 6825809 = 5119357) B5119357
theorem B43788113 : Blo 1198416 43788113 := bstep (se 2 (by rfl) ⟨16420542, by rfl⟩ : syracuseStep 43788113 = 32841085) B32841085
theorem B2697065 : Blo 1198416 2697065 := bstep (se 2 (by rfl) ⟨1011399, by rfl⟩ : syracuseStep 2697065 = 2022799) B2022799
theorem B23685209 : Blo 1198416 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B4049081 : Blo 1198416 4049081 := bstep (se 2 (by rfl) ⟨1518405, by rfl⟩ : syracuseStep 4049081 = 3036811) B3036811
theorem B5761277 : Blo 1198416 5761277 := bstep (se 3 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 5761277 = 2160479) B2160479
theorem B1198427 : Blo 1198416 1198427 := bstep (se 1 (by rfl) ⟨898820, by rfl⟩ : syracuseStep 1198427 = 1797641) B1797641
theorem B1198447 : Blo 1198416 1198447 := bstep (se 1 (by rfl) ⟨898835, by rfl⟩ : syracuseStep 1198447 = 1797671) B1797671
theorem B1517935 : Blo 1198416 1517935 := bstep (se 1 (by rfl) ⟨1138451, by rfl⟩ : syracuseStep 1517935 = 2276903) B2276903
theorem B1198503 : Blo 1198416 1198503 := bstep (se 1 (by rfl) ⟨898877, by rfl⟩ : syracuseStep 1198503 = 1797755) B1797755
theorem B4680119 : Blo 1198416 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B1198587 : Blo 1198416 1198587 := bstep (se 1 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 1198587 = 1797881) B1797881
theorem B1198655 : Blo 1198416 1198655 := bstep (se 1 (by rfl) ⟨898991, by rfl⟩ : syracuseStep 1198655 = 1797983) B1797983
theorem B1198663 : Blo 1198416 1198663 := bstep (se 1 (by rfl) ⟨898997, by rfl⟩ : syracuseStep 1198663 = 1797995) B1797995
theorem B2697911 : Blo 1198416 2697911 := bstep (se 1 (by rfl) ⟨2023433, by rfl⟩ : syracuseStep 2697911 = 4046867) B4046867
theorem B1198815 : Blo 1198416 1198815 := bstep (se 1 (by rfl) ⟨899111, by rfl⟩ : syracuseStep 1198815 = 1798223) B1798223
theorem B3033875 : Blo 1198416 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B1198895 : Blo 1198416 1198895 := bstep (se 1 (by rfl) ⟨899171, by rfl⟩ : syracuseStep 1198895 = 1798343) B1798343
theorem B2698127 : Blo 1198416 2698127 := bstep (se 1 (by rfl) ⟨2023595, by rfl⟩ : syracuseStep 2698127 = 4047191) B4047191
theorem B1199003 : Blo 1198416 1199003 := bstep (se 1 (by rfl) ⟨899252, by rfl⟩ : syracuseStep 1199003 = 1798505) B1798505
theorem B1199055 : Blo 1198416 1199055 := bstep (se 1 (by rfl) ⟨899291, by rfl⟩ : syracuseStep 1199055 = 1798583) B1798583
theorem B1199079 : Blo 1198416 1199079 := bstep (se 1 (by rfl) ⟨899309, by rfl⟩ : syracuseStep 1199079 = 1798619) B1798619
theorem B3034331 : Blo 1198416 3034331 := bstep (se 1 (by rfl) ⟨2275748, by rfl⟩ : syracuseStep 3034331 = 4551497) B4551497
theorem B3034361 : Blo 1198416 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B5762335 : Blo 1198416 5762335 := bstep (se 1 (by rfl) ⟨4321751, by rfl⟩ : syracuseStep 5762335 = 8643503) B8643503
theorem B1199391 : Blo 1198416 1199391 := bstep (se 1 (by rfl) ⟨899543, by rfl⟩ : syracuseStep 1199391 = 1799087) B1799087
theorem B1199451 : Blo 1198416 1199451 := bstep (se 1 (by rfl) ⟨899588, by rfl⟩ : syracuseStep 1199451 = 1799177) B1799177
theorem B1199471 : Blo 1198416 1199471 := bstep (se 1 (by rfl) ⟨899603, by rfl⟩ : syracuseStep 1199471 = 1799207) B1799207
theorem B1199527 : Blo 1198416 1199527 := bstep (se 1 (by rfl) ⟨899645, by rfl⟩ : syracuseStep 1199527 = 1799291) B1799291
theorem B3460567 : Blo 1198416 3460567 := bstep (se 1 (by rfl) ⟨2595425, by rfl⟩ : syracuseStep 3460567 = 5190851) B5190851
theorem B1199611 : Blo 1198416 1199611 := bstep (se 1 (by rfl) ⟨899708, by rfl⟩ : syracuseStep 1199611 = 1799417) B1799417
theorem B6073865 : Blo 1198416 6073865 := bstep (se 2 (by rfl) ⟨2277699, by rfl⟩ : syracuseStep 6073865 = 4555399) B4555399
theorem B49262093 : Blo 1198416 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B1199679 : Blo 1198416 1199679 := bstep (se 1 (by rfl) ⟨899759, by rfl⟩ : syracuseStep 1199679 = 1799519) B1799519
theorem B1199687 : Blo 1198416 1199687 := bstep (se 1 (by rfl) ⟨899765, by rfl⟩ : syracuseStep 1199687 = 1799531) B1799531
theorem B1519175 : Blo 1198416 1519175 := bstep (se 1 (by rfl) ⟨1139381, by rfl⟩ : syracuseStep 1519175 = 2278763) B2278763
theorem B2698847 : Blo 1198416 2698847 := bstep (se 1 (by rfl) ⟨2024135, by rfl⟩ : syracuseStep 2698847 = 4048271) B4048271
theorem B3239585 : Blo 1198416 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B4050593 : Blo 1198416 4050593 := bstep (se 2 (by rfl) ⟨1518972, by rfl⟩ : syracuseStep 4050593 = 3037945) B3037945
theorem B11521709 : Blo 1198416 11521709 := bstep (se 3 (by rfl) ⟨2160320, by rfl⟩ : syracuseStep 11521709 = 4320641) B4320641
theorem B1199839 : Blo 1198416 1199839 := bstep (se 1 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 1199839 = 1799759) B1799759
theorem B1797929 : Blo 1198416 1797929 := bstep (se 2 (by rfl) ⟨674223, by rfl⟩ : syracuseStep 1797929 = 1348447) B1348447
theorem B1797935 : Blo 1198416 1797935 := bstep (se 1 (by rfl) ⟨1348451, by rfl⟩ : syracuseStep 1797935 = 2696903) B2696903
theorem B1199919 : Blo 1198416 1199919 := bstep (se 1 (by rfl) ⟨899939, by rfl⟩ : syracuseStep 1199919 = 1799879) B1799879
theorem B6836015 : Blo 1198416 6836015 := bstep (se 1 (by rfl) ⟨5127011, by rfl⟩ : syracuseStep 6836015 = 10254023) B10254023
theorem B2699063 : Blo 1198416 2699063 := bstep (se 1 (by rfl) ⟨2024297, by rfl⟩ : syracuseStep 2699063 = 4048595) B4048595
theorem B9105209 : Blo 1198416 9105209 := bstep (se 2 (by rfl) ⟨3414453, by rfl⟩ : syracuseStep 9105209 = 6828907) B6828907
theorem B3035009 : Blo 1198416 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B1200027 : Blo 1198416 1200027 := bstep (se 1 (by rfl) ⟨900020, by rfl⟩ : syracuseStep 1200027 = 1800041) B1800041
theorem B1200079 : Blo 1198416 1200079 := bstep (se 1 (by rfl) ⟨900059, by rfl⟩ : syracuseStep 1200079 = 1800119) B1800119
theorem B1200103 : Blo 1198416 1200103 := bstep (se 1 (by rfl) ⟨900077, by rfl⟩ : syracuseStep 1200103 = 1800155) B1800155
theorem B2699369 : Blo 1198416 2699369 := bstep (se 2 (by rfl) ⟨1012263, by rfl⟩ : syracuseStep 2699369 = 2024527) B2024527
theorem B6484121 : Blo 1198416 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B1798409 : Blo 1198416 1798409 := bstep (se 2 (by rfl) ⟨674403, by rfl⟩ : syracuseStep 1798409 = 1348807) B1348807
theorem B74805515 : Blo 1198416 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B1200415 : Blo 1198416 1200415 := bstep (se 1 (by rfl) ⟨900311, by rfl⟩ : syracuseStep 1200415 = 1800623) B1800623
theorem B3035465 : Blo 1198416 3035465 := bstep (se 2 (by rfl) ⟨1138299, by rfl⟩ : syracuseStep 3035465 = 2276599) B2276599
theorem B1798511 : Blo 1198416 1798511 := bstep (se 1 (by rfl) ⟨1348883, by rfl⟩ : syracuseStep 1798511 = 2697767) B2697767
theorem B2560423 : Blo 1198416 2560423 := bstep (se 1 (by rfl) ⟨1920317, by rfl⟩ : syracuseStep 2560423 = 3840635) B3840635
theorem B15585853 : Blo 1198416 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B1798727 : Blo 1198416 1798727 := bstep (se 1 (by rfl) ⟨1349045, by rfl⟩ : syracuseStep 1798727 = 2698091) B2698091
theorem B2560585 : Blo 1198416 2560585 := bstep (se 2 (by rfl) ⟨960219, by rfl⟩ : syracuseStep 2560585 = 1920439) B1920439
theorem B2699855 : Blo 1198416 2699855 := bstep (se 1 (by rfl) ⟨2024891, by rfl⟩ : syracuseStep 2699855 = 4049783) B4049783
theorem B1798763 : Blo 1198416 1798763 := bstep (se 1 (by rfl) ⟨1349072, by rfl⟩ : syracuseStep 1798763 = 2698145) B2698145
theorem B1708651 : Blo 1198416 1708651 := bstep (se 1 (by rfl) ⟨1281488, by rfl⟩ : syracuseStep 1708651 = 2562977) B2562977
theorem B5763737 : Blo 1198416 5763737 := bstep (se 2 (by rfl) ⟨2161401, by rfl⟩ : syracuseStep 5763737 = 4322803) B4322803
theorem B3035819 : Blo 1198416 3035819 := bstep (se 1 (by rfl) ⟨2276864, by rfl⟩ : syracuseStep 3035819 = 4553729) B4553729
theorem B4616875 : Blo 1198416 4616875 := bstep (se 1 (by rfl) ⟨3462656, by rfl⟩ : syracuseStep 4616875 = 6925313) B6925313
theorem B2699999 : Blo 1198416 2699999 := bstep (se 1 (by rfl) ⟨2024999, by rfl⟩ : syracuseStep 2699999 = 4049999) B4049999
theorem B1798991 : Blo 1198416 1798991 := bstep (se 1 (by rfl) ⟨1349243, by rfl⟩ : syracuseStep 1798991 = 2698487) B2698487
theorem B1708879 : Blo 1198416 1708879 := bstep (se 1 (by rfl) ⟨1281659, by rfl⟩ : syracuseStep 1708879 = 2563319) B2563319
theorem B8205257 : Blo 1198416 8205257 := bstep (se 2 (by rfl) ⟨3076971, by rfl⟩ : syracuseStep 8205257 = 6153943) B6153943
theorem B2700251 : Blo 1198416 2700251 := bstep (se 1 (by rfl) ⟨2025188, by rfl⟩ : syracuseStep 2700251 = 4050377) B4050377
theorem B11531321 : Blo 1198416 11531321 := bstep (se 2 (by rfl) ⟨4324245, by rfl⟩ : syracuseStep 11531321 = 8648491) B8648491
theorem B6829181 : Blo 1198416 6829181 := bstep (se 3 (by rfl) ⟨1280471, by rfl⟩ : syracuseStep 6829181 = 2560943) B2560943
theorem B4101263 : Blo 1198416 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B2700431 : Blo 1198416 2700431 := bstep (se 1 (by rfl) ⟨2025323, by rfl⟩ : syracuseStep 2700431 = 4050647) B4050647
theorem B1799387 : Blo 1198416 1799387 := bstep (se 1 (by rfl) ⟨1349540, by rfl⟩ : syracuseStep 1799387 = 2699081) B2699081
theorem B2700521 : Blo 1198416 2700521 := bstep (se 2 (by rfl) ⟨1012695, by rfl⟩ : syracuseStep 2700521 = 2025391) B2025391
theorem B2880755 : Blo 1198416 2880755 := bstep (se 1 (by rfl) ⟨2160566, by rfl⟩ : syracuseStep 2880755 = 4321133) B4321133
theorem B2561311 : Blo 1198416 2561311 := bstep (se 1 (by rfl) ⟨1920983, by rfl⟩ : syracuseStep 2561311 = 3841967) B3841967
theorem B2700575 : Blo 1198416 2700575 := bstep (se 1 (by rfl) ⟨2025431, by rfl⟩ : syracuseStep 2700575 = 4050863) B4050863
theorem B2372903 : Blo 1198416 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B1348987 : Blo 1198416 1348987 := bstep (se 1 (by rfl) ⟨1011740, by rfl⟩ : syracuseStep 1348987 = 2023481) B2023481
theorem B1799561 : Blo 1198416 1799561 := bstep (se 2 (by rfl) ⟨674835, by rfl⟩ : syracuseStep 1799561 = 1349671) B1349671
theorem B6075809 : Blo 1198416 6075809 := bstep (se 2 (by rfl) ⟨2278428, by rfl⟩ : syracuseStep 6075809 = 4556857) B4556857
theorem B1799915 : Blo 1198416 1799915 := bstep (se 1 (by rfl) ⟨1349936, by rfl⟩ : syracuseStep 1799915 = 2699873) B2699873
theorem B2922281 : Blo 1198416 2922281 := bstep (se 2 (by rfl) ⟨1095855, by rfl⟩ : syracuseStep 2922281 = 2191711) B2191711
theorem B1537871 : Blo 1198416 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B1349455 : Blo 1198416 1349455 := bstep (se 1 (by rfl) ⟨1012091, by rfl⟩ : syracuseStep 1349455 = 2024183) B2024183
theorem B3037135 : Blo 1198416 3037135 := bstep (se 1 (by rfl) ⟨2277851, by rfl⟩ : syracuseStep 3037135 = 4555703) B4555703
theorem B1800143 : Blo 1198416 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B2881561 : Blo 1198416 2881561 := bstep (se 2 (by rfl) ⟨1080585, by rfl⟩ : syracuseStep 2881561 = 2161171) B2161171
theorem B3840185 : Blo 1198416 3840185 := bstep (se 2 (by rfl) ⟨1440069, by rfl⟩ : syracuseStep 3840185 = 2880139) B2880139
theorem B1349851 : Blo 1198416 1349851 := bstep (se 1 (by rfl) ⟨1012388, by rfl⟩ : syracuseStep 1349851 = 2024777) B2024777
theorem B4552969 : Blo 1198416 4552969 := bstep (se 2 (by rfl) ⟨1707363, by rfl⟩ : syracuseStep 4552969 = 3414727) B3414727
theorem B6486281 : Blo 1198416 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B4045085 : Blo 1198416 4045085 := bstep (se 3 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 4045085 = 1516907) B1516907
theorem B1800539 : Blo 1198416 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B1350139 : Blo 1198416 1350139 := bstep (se 1 (by rfl) ⟨1012604, by rfl⟩ : syracuseStep 1350139 = 2025209) B2025209
theorem B6068843 : Blo 1198416 6068843 := bstep (se 1 (by rfl) ⟨4551632, by rfl⟩ : syracuseStep 6068843 = 9103265) B9103265
theorem B2431595 : Blo 1198416 2431595 := bstep (se 1 (by rfl) ⟨1823696, by rfl⟩ : syracuseStep 2431595 = 3647393) B3647393
theorem B1350319 : Blo 1198416 1350319 := bstep (se 1 (by rfl) ⟨1012739, by rfl⟩ : syracuseStep 1350319 = 2025479) B2025479
theorem B10255085 : Blo 1198416 10255085 := bstep (se 3 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 10255085 = 3845657) B3845657
theorem B6486803 : Blo 1198416 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B36936485 : Blo 1198416 36936485 := bstep (se 4 (by rfl) ⟨3462795, by rfl⟩ : syracuseStep 36936485 = 6925591) B6925591
theorem B10246985 : Blo 1198416 10246985 := bstep (se 2 (by rfl) ⟨3842619, by rfl⟩ : syracuseStep 10246985 = 7685239) B7685239
theorem B2562959 : Blo 1198416 2562959 := bstep (se 1 (by rfl) ⟨1922219, by rfl⟩ : syracuseStep 2562959 = 3844439) B3844439
theorem B3038107 : Blo 1198416 3038107 := bstep (se 1 (by rfl) ⟨2278580, by rfl⟩ : syracuseStep 3038107 = 4557161) B4557161
theorem B3414955 : Blo 1198416 3414955 := bstep (se 1 (by rfl) ⟨2561216, by rfl⟩ : syracuseStep 3414955 = 5122433) B5122433
theorem B6069329 : Blo 1198416 6069329 := bstep (se 2 (by rfl) ⟨2275998, by rfl⟩ : syracuseStep 6069329 = 4551997) B4551997
theorem B3415229 : Blo 1198416 3415229 := bstep (se 3 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 3415229 = 1280711) B1280711
theorem B4046111 : Blo 1198416 4046111 := bstep (se 1 (by rfl) ⟨3034583, by rfl⟩ : syracuseStep 4046111 = 6069167) B6069167
theorem B2022779 : Blo 1198416 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B25927127 : Blo 1198416 25927127 := bstep (se 1 (by rfl) ⟨19445345, by rfl⟩ : syracuseStep 25927127 = 38890691) B38890691
theorem B4324823 : Blo 1198416 4324823 := bstep (se 1 (by rfl) ⟨3243617, by rfl⟩ : syracuseStep 4324823 = 6487235) B6487235
theorem B7683599 : Blo 1198416 7683599 := bstep (se 1 (by rfl) ⟨5762699, by rfl⟩ : syracuseStep 7683599 = 11525399) B11525399
theorem B6831641 : Blo 1198416 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B7290449 : Blo 1198416 7290449 := bstep (se 2 (by rfl) ⟨2733918, by rfl⟩ : syracuseStep 7290449 = 5467837) B5467837
theorem B23363261 : Blo 1198416 23363261 := bstep (se 3 (by rfl) ⟨4380611, by rfl⟩ : syracuseStep 23363261 = 8761223) B8761223
theorem B5119699 : Blo 1198416 5119699 := bstep (se 1 (by rfl) ⟨3839774, by rfl⟩ : syracuseStep 5119699 = 7679549) B7679549
theorem B4439819 : Blo 1198416 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B3243833 : Blo 1198416 3243833 := bstep (se 2 (by rfl) ⟨1216437, by rfl⟩ : syracuseStep 3243833 = 2432875) B2432875
theorem B3842081 : Blo 1198416 3842081 := bstep (se 2 (by rfl) ⟨1440780, by rfl⟩ : syracuseStep 3842081 = 2881561) B2881561
theorem B2023643 : Blo 1198416 2023643 := bstep (se 1 (by rfl) ⟨1517732, by rfl⟩ : syracuseStep 2023643 = 3035465) B3035465
theorem B2736347 : Blo 1198416 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B1622327 : Blo 1198416 1622327 := bstep (se 1 (by rfl) ⟨1216745, by rfl⟩ : syracuseStep 1622327 = 2433491) B2433491
theorem B6070625 : Blo 1198416 6070625 := bstep (se 2 (by rfl) ⟨2276484, by rfl⟩ : syracuseStep 6070625 = 4552969) B4552969
theorem B3842491 : Blo 1198416 3842491 := bstep (se 1 (by rfl) ⟨2881868, by rfl⟩ : syracuseStep 3842491 = 5763737) B5763737
theorem B2023879 : Blo 1198416 2023879 := bstep (se 1 (by rfl) ⟨1517909, by rfl⟩ : syracuseStep 2023879 = 3035819) B3035819
theorem B7684571 : Blo 1198416 7684571 := bstep (se 1 (by rfl) ⟨5763428, by rfl⟩ : syracuseStep 7684571 = 11526857) B11526857
theorem B2023913 : Blo 1198416 2023913 := bstep (se 2 (by rfl) ⟨758967, by rfl⟩ : syracuseStep 2023913 = 1517935) B1517935
theorem B15368939 : Blo 1198416 15368939 := bstep (se 1 (by rfl) ⟨11526704, by rfl⟩ : syracuseStep 15368939 = 23053409) B23053409
theorem B2278201 : Blo 1198416 2278201 := bstep (se 2 (by rfl) ⟨854325, by rfl⟩ : syracuseStep 2278201 = 1708651) B1708651
theorem B1581935 : Blo 1198416 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B12649403 : Blo 1198416 12649403 := bstep (se 1 (by rfl) ⟨9487052, by rfl⟩ : syracuseStep 12649403 = 18974105) B18974105
theorem B2278505 : Blo 1198416 2278505 := bstep (se 2 (by rfl) ⟨854439, by rfl⟩ : syracuseStep 2278505 = 1708879) B1708879
theorem B2696723 : Blo 1198416 2696723 := bstep (se 1 (by rfl) ⟨2022542, by rfl⟩ : syracuseStep 2696723 = 4045085) B4045085
theorem B4614089 : Blo 1198416 4614089 := bstep (se 2 (by rfl) ⟨1730283, by rfl⟩ : syracuseStep 4614089 = 3460567) B3460567
theorem B11839517 : Blo 1198416 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B2697407 : Blo 1198416 2697407 := bstep (se 1 (by rfl) ⟨2023055, by rfl⟩ : syracuseStep 2697407 = 4046111) B4046111
theorem B6826265 : Blo 1198416 6826265 := bstep (se 2 (by rfl) ⟨2559849, by rfl⟩ : syracuseStep 6826265 = 5119699) B5119699
theorem B4049243 : Blo 1198416 4049243 := bstep (se 1 (by rfl) ⟨3036932, by rfl⟩ : syracuseStep 4049243 = 6073865) B6073865
theorem B5122399 : Blo 1198416 5122399 := bstep (se 1 (by rfl) ⟨3841799, by rfl⟩ : syracuseStep 5122399 = 7683599) B7683599
theorem B6834557 : Blo 1198416 6834557 := bstep (se 3 (by rfl) ⟨1281479, by rfl⟩ : syracuseStep 6834557 = 2562959) B2562959
theorem B4860299 : Blo 1198416 4860299 := bstep (se 1 (by rfl) ⟨3645224, by rfl⟩ : syracuseStep 4860299 = 7290449) B7290449
theorem B15575507 : Blo 1198416 15575507 := bstep (se 1 (by rfl) ⟨11681630, by rfl⟩ : syracuseStep 15575507 = 23363261) B23363261
theorem B1198619 : Blo 1198416 1198619 := bstep (se 1 (by rfl) ⟨898964, by rfl⟩ : syracuseStep 1198619 = 1797929) B1797929
theorem B1198623 : Blo 1198416 1198623 := bstep (se 1 (by rfl) ⟨898967, by rfl⟩ : syracuseStep 1198623 = 1797935) B1797935
theorem B4557343 : Blo 1198416 4557343 := bstep (se 1 (by rfl) ⟨3418007, by rfl⟩ : syracuseStep 4557343 = 6836015) B6836015
theorem B4049513 : Blo 1198416 4049513 := bstep (se 2 (by rfl) ⟨1518567, by rfl⟩ : syracuseStep 4049513 = 3037135) B3037135
theorem B1198939 : Blo 1198416 1198939 := bstep (se 1 (by rfl) ⟨899204, by rfl⟩ : syracuseStep 1198939 = 1798409) B1798409
theorem B1199007 : Blo 1198416 1199007 := bstep (se 1 (by rfl) ⟨899255, by rfl⟩ : syracuseStep 1199007 = 1798511) B1798511
theorem B1199151 : Blo 1198416 1199151 := bstep (se 1 (by rfl) ⟨899363, by rfl⟩ : syracuseStep 1199151 = 1798727) B1798727
theorem B1199175 : Blo 1198416 1199175 := bstep (se 1 (by rfl) ⟨899381, by rfl⟩ : syracuseStep 1199175 = 1798763) B1798763
theorem B6925409 : Blo 1198416 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B2698361 : Blo 1198416 2698361 := bstep (se 2 (by rfl) ⟨1011885, by rfl⟩ : syracuseStep 2698361 = 2023771) B2023771
theorem B1199327 : Blo 1198416 1199327 := bstep (se 1 (by rfl) ⟨899495, by rfl⟩ : syracuseStep 1199327 = 1798991) B1798991
theorem B7687547 : Blo 1198416 7687547 := bstep (se 1 (by rfl) ⟨5765660, by rfl⟩ : syracuseStep 7687547 = 11531321) B11531321
theorem B7679447 : Blo 1198416 7679447 := bstep (se 1 (by rfl) ⟨5759585, by rfl⟩ : syracuseStep 7679447 = 11519171) B11519171
theorem B1199591 : Blo 1198416 1199591 := bstep (se 1 (by rfl) ⟨899693, by rfl⟩ : syracuseStep 1199591 = 1799387) B1799387
theorem B16403957 : Blo 1198416 16403957 := bstep (se 5 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 16403957 = 1537871) B1537871
theorem B1920503 : Blo 1198416 1920503 := bstep (se 1 (by rfl) ⟨1440377, by rfl⟩ : syracuseStep 1920503 = 2880755) B2880755
theorem B6155833 : Blo 1198416 6155833 := bstep (se 2 (by rfl) ⟨2308437, by rfl⟩ : syracuseStep 6155833 = 4616875) B4616875
theorem B1797695 : Blo 1198416 1797695 := bstep (se 1 (by rfl) ⟨1348271, by rfl⟩ : syracuseStep 1797695 = 2696543) B2696543
theorem B1199707 : Blo 1198416 1199707 := bstep (se 1 (by rfl) ⟨899780, by rfl⟩ : syracuseStep 1199707 = 1799561) B1799561
theorem B4050539 : Blo 1198416 4050539 := bstep (se 1 (by rfl) ⟨3037904, by rfl⟩ : syracuseStep 4050539 = 6075809) B6075809
theorem B2699027 : Blo 1198416 2699027 := bstep (se 1 (by rfl) ⟨2024270, by rfl⟩ : syracuseStep 2699027 = 4048541) B4048541
theorem B6926141 : Blo 1198416 6926141 := bstep (se 3 (by rfl) ⟨1298651, by rfl⟩ : syracuseStep 6926141 = 2597303) B2597303
theorem B1797959 : Blo 1198416 1797959 := bstep (se 1 (by rfl) ⟨1348469, by rfl⟩ : syracuseStep 1797959 = 2696939) B2696939
theorem B1199943 : Blo 1198416 1199943 := bstep (se 1 (by rfl) ⟨899957, by rfl⟩ : syracuseStep 1199943 = 1799915) B1799915
theorem B4050809 : Blo 1198416 4050809 := bstep (se 2 (by rfl) ⟨1519053, by rfl⟩ : syracuseStep 4050809 = 3038107) B3038107
theorem B4550539 : Blo 1198416 4550539 := bstep (se 1 (by rfl) ⟨3412904, by rfl⟩ : syracuseStep 4550539 = 6825809) B6825809
theorem B29192075 : Blo 1198416 29192075 := bstep (se 1 (by rfl) ⟨21894056, by rfl⟩ : syracuseStep 29192075 = 43788113) B43788113
theorem B1798043 : Blo 1198416 1798043 := bstep (se 1 (by rfl) ⟨1348532, by rfl⟩ : syracuseStep 1798043 = 2697065) B2697065
theorem B1200095 : Blo 1198416 1200095 := bstep (se 1 (by rfl) ⟨900071, by rfl⟩ : syracuseStep 1200095 = 1800143) B1800143
theorem B15790139 : Blo 1198416 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B2560123 : Blo 1198416 2560123 := bstep (se 1 (by rfl) ⟨1920092, by rfl⟩ : syracuseStep 2560123 = 3840185) B3840185
theorem B2699387 : Blo 1198416 2699387 := bstep (se 1 (by rfl) ⟨2024540, by rfl⟩ : syracuseStep 2699387 = 4049081) B4049081
theorem B4051133 : Blo 1198416 4051133 := bstep (se 3 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 4051133 = 1519175) B1519175
theorem B1200359 : Blo 1198416 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B2699657 : Blo 1198416 2699657 := bstep (se 2 (by rfl) ⟨1012371, by rfl⟩ : syracuseStep 2699657 = 2024743) B2024743
theorem B1798607 : Blo 1198416 1798607 := bstep (se 1 (by rfl) ⟨1348955, by rfl⟩ : syracuseStep 1798607 = 2697911) B2697911
theorem B6836723 : Blo 1198416 6836723 := bstep (se 1 (by rfl) ⟨5127542, by rfl⟩ : syracuseStep 6836723 = 10255085) B10255085
theorem B1798649 : Blo 1198416 1798649 := bstep (se 2 (by rfl) ⟨674493, by rfl⟩ : syracuseStep 1798649 = 1348987) B1348987
theorem B1798751 : Blo 1198416 1798751 := bstep (se 1 (by rfl) ⟨1349063, by rfl⟩ : syracuseStep 1798751 = 2698127) B2698127
theorem B1348519 : Blo 1198416 1348519 := bstep (se 1 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 1348519 = 2022779) B2022779
theorem B1799231 : Blo 1198416 1799231 := bstep (se 1 (by rfl) ⟨1349423, by rfl⟩ : syracuseStep 1799231 = 2698847) B2698847
theorem B1799273 : Blo 1198416 1799273 := bstep (se 2 (by rfl) ⟨674727, by rfl⟩ : syracuseStep 1799273 = 1349455) B1349455
theorem B2159723 : Blo 1198416 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B2700395 : Blo 1198416 2700395 := bstep (se 1 (by rfl) ⟨2025296, by rfl⟩ : syracuseStep 2700395 = 4050593) B4050593
theorem B7681139 : Blo 1198416 7681139 := bstep (se 1 (by rfl) ⟨5760854, by rfl⟩ : syracuseStep 7681139 = 11521709) B11521709
theorem B1799375 : Blo 1198416 1799375 := bstep (se 1 (by rfl) ⟨1349531, by rfl⟩ : syracuseStep 1799375 = 2699063) B2699063
theorem B6067547 : Blo 1198416 6067547 := bstep (se 1 (by rfl) ⟨4550660, by rfl⟩ : syracuseStep 6067547 = 9101321) B9101321
theorem B1799579 : Blo 1198416 1799579 := bstep (se 1 (by rfl) ⟨1349684, by rfl⟩ : syracuseStep 1799579 = 2699369) B2699369
theorem B4322747 : Blo 1198416 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B49870343 : Blo 1198416 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B1799801 : Blo 1198416 1799801 := bstep (se 2 (by rfl) ⟨674925, by rfl⟩ : syracuseStep 1799801 = 1349851) B1349851
theorem B1922681 : Blo 1198416 1922681 := bstep (se 2 (by rfl) ⟨721005, by rfl⟩ : syracuseStep 1922681 = 1442011) B1442011
theorem B1799903 : Blo 1198416 1799903 := bstep (se 1 (by rfl) ⟨1349927, by rfl⟩ : syracuseStep 1799903 = 2699855) B2699855
theorem B1922783 : Blo 1198416 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B3036923 : Blo 1198416 3036923 := bstep (se 1 (by rfl) ⟨2277692, by rfl⟩ : syracuseStep 3036923 = 4555385) B4555385
theorem B29202191 : Blo 1198416 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B1799999 : Blo 1198416 1799999 := bstep (se 1 (by rfl) ⟨1349999, by rfl⟩ : syracuseStep 1799999 = 2699999) B2699999
theorem B3413897 : Blo 1198416 3413897 := bstep (se 2 (by rfl) ⟨1280211, by rfl⟩ : syracuseStep 3413897 = 2560423) B2560423
theorem B1800167 : Blo 1198416 1800167 := bstep (se 1 (by rfl) ⟨1350125, by rfl⟩ : syracuseStep 1800167 = 2700251) B2700251
theorem B1800185 : Blo 1198416 1800185 := bstep (se 2 (by rfl) ⟨675069, by rfl⟩ : syracuseStep 1800185 = 1350139) B1350139
theorem B20781137 : Blo 1198416 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B4552787 : Blo 1198416 4552787 := bstep (se 1 (by rfl) ⟨3414590, by rfl⟩ : syracuseStep 4552787 = 6829181) B6829181
theorem B2562131 : Blo 1198416 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B2734175 : Blo 1198416 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B1800287 : Blo 1198416 1800287 := bstep (se 1 (by rfl) ⟨1350215, by rfl⟩ : syracuseStep 1800287 = 2700431) B2700431
theorem B3414113 : Blo 1198416 3414113 := bstep (se 2 (by rfl) ⟨1280292, by rfl⟩ : syracuseStep 3414113 = 2560585) B2560585
theorem B1800347 : Blo 1198416 1800347 := bstep (se 1 (by rfl) ⟨1350260, by rfl⟩ : syracuseStep 1800347 = 2700521) B2700521
theorem B1800383 : Blo 1198416 1800383 := bstep (se 1 (by rfl) ⟨1350287, by rfl⟩ : syracuseStep 1800383 = 2700575) B2700575
theorem B10246337 : Blo 1198416 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B1800425 : Blo 1198416 1800425 := bstep (se 2 (by rfl) ⟨675159, by rfl⟩ : syracuseStep 1800425 = 1350319) B1350319
theorem B6076781 : Blo 1198416 6076781 := bstep (se 3 (by rfl) ⟨1139396, by rfl⟩ : syracuseStep 6076781 = 2278793) B2278793
theorem B1948187 : Blo 1198416 1948187 := bstep (se 1 (by rfl) ⟨1461140, by rfl⟩ : syracuseStep 1948187 = 2922281) B2922281
theorem B1350175 : Blo 1198416 1350175 := bstep (se 1 (by rfl) ⟨1012631, by rfl⟩ : syracuseStep 1350175 = 2025263) B2025263
theorem B58317347 : Blo 1198416 58317347 := bstep (se 1 (by rfl) ⟨43738010, by rfl⟩ : syracuseStep 58317347 = 87476021) B87476021
theorem B4553273 : Blo 1198416 4553273 := bstep (se 2 (by rfl) ⟨1707477, by rfl⟩ : syracuseStep 4553273 = 3414955) B3414955
theorem B3840851 : Blo 1198416 3840851 := bstep (se 1 (by rfl) ⟨2880638, by rfl⟩ : syracuseStep 3840851 = 5761277) B5761277
theorem B4324187 : Blo 1198416 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B3038057 : Blo 1198416 3038057 := bstep (se 2 (by rfl) ⟨1139271, by rfl⟩ : syracuseStep 3038057 = 2278543) B2278543
theorem B3120079 : Blo 1198416 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B7683113 : Blo 1198416 7683113 := bstep (se 2 (by rfl) ⟨2881167, by rfl⟩ : syracuseStep 7683113 = 5762335) B5762335
theorem B3415081 : Blo 1198416 3415081 := bstep (se 2 (by rfl) ⟨1280655, by rfl⟩ : syracuseStep 3415081 = 2561311) B2561311
theorem B3038249 : Blo 1198416 3038249 := bstep (se 2 (by rfl) ⟨1139343, by rfl⟩ : syracuseStep 3038249 = 2278687) B2278687
theorem B4045895 : Blo 1198416 4045895 := bstep (se 1 (by rfl) ⟨3034421, by rfl⟩ : syracuseStep 4045895 = 6068843) B6068843
theorem B1621063 : Blo 1198416 1621063 := bstep (se 1 (by rfl) ⟨1215797, by rfl⟩ : syracuseStep 1621063 = 2431595) B2431595
theorem B4045949 : Blo 1198416 4045949 := bstep (se 3 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 4045949 = 1517231) B1517231
theorem B2022583 : Blo 1198416 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B4324535 : Blo 1198416 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B24624323 : Blo 1198416 24624323 := bstep (se 1 (by rfl) ⟨18468242, by rfl⟩ : syracuseStep 24624323 = 36936485) B36936485
theorem B6831323 : Blo 1198416 6831323 := bstep (se 1 (by rfl) ⟨5123492, by rfl⟩ : syracuseStep 6831323 = 10246985) B10246985
theorem B4046219 : Blo 1198416 4046219 := bstep (se 1 (by rfl) ⟨3034664, by rfl⟩ : syracuseStep 4046219 = 6069329) B6069329
theorem B2276819 : Blo 1198416 2276819 := bstep (se 1 (by rfl) ⟨1707614, by rfl⟩ : syracuseStep 2276819 = 3415229) B3415229
theorem B2022887 : Blo 1198416 2022887 := bstep (se 1 (by rfl) ⟨1517165, by rfl⟩ : syracuseStep 2022887 = 3034331) B3034331
theorem B2022907 : Blo 1198416 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B17284751 : Blo 1198416 17284751 := bstep (se 1 (by rfl) ⟨12963563, by rfl⟩ : syracuseStep 17284751 = 25927127) B25927127
theorem B2883215 : Blo 1198416 2883215 := bstep (se 1 (by rfl) ⟨2162411, by rfl⟩ : syracuseStep 2883215 = 4324823) B4324823
theorem B32841395 : Blo 1198416 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B4554427 : Blo 1198416 4554427 := bstep (se 1 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 4554427 = 6831641) B6831641
theorem B21880685 : Blo 1198416 21880685 := bstep (se 3 (by rfl) ⟨4102628, by rfl⟩ : syracuseStep 21880685 = 8205257) B8205257
theorem B6070139 : Blo 1198416 6070139 := bstep (se 1 (by rfl) ⟨4552604, by rfl⟩ : syracuseStep 6070139 = 9105209) B9105209
theorem B2162555 : Blo 1198416 2162555 := bstep (se 1 (by rfl) ⟨1621916, by rfl⟩ : syracuseStep 2162555 = 3243833) B3243833
theorem B2023339 : Blo 1198416 2023339 := bstep (se 1 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 2023339 = 3035009) B3035009
theorem B10526759 : Blo 1198416 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B6832349 : Blo 1198416 6832349 := bstep (se 3 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 6832349 = 2562131) B2562131
theorem B4047083 : Blo 1198416 4047083 := bstep (se 1 (by rfl) ⟨3035312, by rfl⟩ : syracuseStep 4047083 = 6070625) B6070625
theorem B7291133 : Blo 1198416 7291133 := bstep (se 3 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 7291133 = 2734175) B2734175
theorem B5759261 : Blo 1198416 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B5120759 : Blo 1198416 5120759 := bstep (se 1 (by rfl) ⟨3840569, by rfl⟩ : syracuseStep 5120759 = 7681139) B7681139
theorem B4326205 : Blo 1198416 4326205 := bstep (se 3 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 4326205 = 1622327) B1622327
theorem B2024615 : Blo 1198416 2024615 := bstep (se 1 (by rfl) ⟨1518461, by rfl⟩ : syracuseStep 2024615 = 3036923) B3036923
theorem B13854091 : Blo 1198416 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B2696777 : Blo 1198416 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B4556371 : Blo 1198416 4556371 := bstep (se 1 (by rfl) ⟨3417278, by rfl⟩ : syracuseStep 4556371 = 6834557) B6834557
theorem B2025371 : Blo 1198416 2025371 := bstep (se 1 (by rfl) ⟨1519028, by rfl⟩ : syracuseStep 2025371 = 3038057) B3038057
theorem B2697209 : Blo 1198416 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B5122075 : Blo 1198416 5122075 := bstep (se 1 (by rfl) ⟨3841556, by rfl⟩ : syracuseStep 5122075 = 7683113) B7683113
theorem B2025499 : Blo 1198416 2025499 := bstep (se 1 (by rfl) ⟨1519124, by rfl⟩ : syracuseStep 2025499 = 3038249) B3038249
theorem B2697263 : Blo 1198416 2697263 := bstep (se 1 (by rfl) ⟨2022947, by rfl⟩ : syracuseStep 2697263 = 4045895) B4045895
theorem B2697299 : Blo 1198416 2697299 := bstep (se 1 (by rfl) ⟨2022974, by rfl⟩ : syracuseStep 2697299 = 4045949) B4045949
theorem B6072569 : Blo 1198416 6072569 := bstep (se 2 (by rfl) ⟨2277213, by rfl⟩ : syracuseStep 6072569 = 4554427) B4554427
theorem B2697479 : Blo 1198416 2697479 := bstep (se 1 (by rfl) ⟨2023109, by rfl⟩ : syracuseStep 2697479 = 4046219) B4046219
theorem B1517879 : Blo 1198416 1517879 := bstep (se 1 (by rfl) ⟨1138409, by rfl⟩ : syracuseStep 1517879 = 2276819) B2276819
theorem B1280335 : Blo 1198416 1280335 := bstep (se 1 (by rfl) ⟨960251, by rfl⟩ : syracuseStep 1280335 = 1920503) B1920503
theorem B1198463 : Blo 1198416 1198463 := bstep (se 1 (by rfl) ⟨898847, by rfl⟩ : syracuseStep 1198463 = 1797695) B1797695
theorem B1198639 : Blo 1198416 1198639 := bstep (se 1 (by rfl) ⟨898979, by rfl⟩ : syracuseStep 1198639 = 1797959) B1797959
theorem B2697785 : Blo 1198416 2697785 := bstep (se 2 (by rfl) ⟨1011669, by rfl⟩ : syracuseStep 2697785 = 2023339) B2023339
theorem B1198695 : Blo 1198416 1198695 := bstep (se 1 (by rfl) ⟨899021, by rfl⟩ : syracuseStep 1198695 = 1798043) B1798043
theorem B1199071 : Blo 1198416 1199071 := bstep (se 1 (by rfl) ⟨899303, by rfl⟩ : syracuseStep 1199071 = 1798607) B1798607
theorem B4557815 : Blo 1198416 4557815 := bstep (se 1 (by rfl) ⟨3418361, by rfl⟩ : syracuseStep 4557815 = 6836723) B6836723
theorem B1199099 : Blo 1198416 1199099 := bstep (se 1 (by rfl) ⟨899324, by rfl⟩ : syracuseStep 1199099 = 1798649) B1798649
theorem B1199167 : Blo 1198416 1199167 := bstep (se 1 (by rfl) ⟨899375, by rfl⟩ : syracuseStep 1199167 = 1798751) B1798751
theorem B5123321 : Blo 1198416 5123321 := bstep (se 2 (by rfl) ⟨1921245, by rfl⟩ : syracuseStep 5123321 = 3842491) B3842491
theorem B2698505 : Blo 1198416 2698505 := bstep (se 2 (by rfl) ⟨1011939, by rfl⟩ : syracuseStep 2698505 = 2023879) B2023879
theorem B1199487 : Blo 1198416 1199487 := bstep (se 1 (by rfl) ⟨899615, by rfl⟩ : syracuseStep 1199487 = 1799231) B1799231
theorem B1199515 : Blo 1198416 1199515 := bstep (se 1 (by rfl) ⟨899636, by rfl⟩ : syracuseStep 1199515 = 1799273) B1799273
theorem B1519003 : Blo 1198416 1519003 := bstep (se 1 (by rfl) ⟨1139252, by rfl⟩ : syracuseStep 1519003 = 2278505) B2278505
theorem B1199583 : Blo 1198416 1199583 := bstep (se 1 (by rfl) ⟨899687, by rfl⟩ : syracuseStep 1199583 = 1799375) B1799375
theorem B1199719 : Blo 1198416 1199719 := bstep (se 1 (by rfl) ⟨899789, by rfl⟩ : syracuseStep 1199719 = 1799579) B1799579
theorem B33246895 : Blo 1198416 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B1797815 : Blo 1198416 1797815 := bstep (se 1 (by rfl) ⟨1348361, by rfl⟩ : syracuseStep 1797815 = 2696723) B2696723
theorem B1199867 : Blo 1198416 1199867 := bstep (se 1 (by rfl) ⟨899900, by rfl⟩ : syracuseStep 1199867 = 1799801) B1799801
theorem B1281787 : Blo 1198416 1281787 := bstep (se 1 (by rfl) ⟨961340, by rfl⟩ : syracuseStep 1281787 = 1922681) B1922681
theorem B1199935 : Blo 1198416 1199935 := bstep (se 1 (by rfl) ⟨899951, by rfl⟩ : syracuseStep 1199935 = 1799903) B1799903
theorem B19468127 : Blo 1198416 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B1199999 : Blo 1198416 1199999 := bstep (se 1 (by rfl) ⟨899999, by rfl⟩ : syracuseStep 1199999 = 1799999) B1799999
theorem B1798025 : Blo 1198416 1798025 := bstep (se 2 (by rfl) ⟨674259, by rfl⟩ : syracuseStep 1798025 = 1348519) B1348519
theorem B20492189 : Blo 1198416 20492189 := bstep (se 3 (by rfl) ⟨3842285, by rfl⟩ : syracuseStep 20492189 = 7684571) B7684571
theorem B1200111 : Blo 1198416 1200111 := bstep (se 1 (by rfl) ⟨900083, by rfl⟩ : syracuseStep 1200111 = 1800167) B1800167
theorem B1200123 : Blo 1198416 1200123 := bstep (se 1 (by rfl) ⟨900092, by rfl⟩ : syracuseStep 1200123 = 1800185) B1800185
theorem B7893011 : Blo 1198416 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B3035191 : Blo 1198416 3035191 := bstep (se 1 (by rfl) ⟨2276393, by rfl⟩ : syracuseStep 3035191 = 4552787) B4552787
theorem B1200191 : Blo 1198416 1200191 := bstep (se 1 (by rfl) ⟨900143, by rfl⟩ : syracuseStep 1200191 = 1800287) B1800287
theorem B1200231 : Blo 1198416 1200231 := bstep (se 1 (by rfl) ⟨900173, by rfl⟩ : syracuseStep 1200231 = 1800347) B1800347
theorem B1798271 : Blo 1198416 1798271 := bstep (se 1 (by rfl) ⟨1348703, by rfl⟩ : syracuseStep 1798271 = 2697407) B2697407
theorem B1200255 : Blo 1198416 1200255 := bstep (se 1 (by rfl) ⟨900191, by rfl⟩ : syracuseStep 1200255 = 1800383) B1800383
theorem B1200283 : Blo 1198416 1200283 := bstep (se 1 (by rfl) ⟨900212, by rfl⟩ : syracuseStep 1200283 = 1800425) B1800425
theorem B4550843 : Blo 1198416 4550843 := bstep (se 1 (by rfl) ⟨3413132, by rfl⟩ : syracuseStep 4550843 = 6826265) B6826265
theorem B2699495 : Blo 1198416 2699495 := bstep (se 1 (by rfl) ⟨2024621, by rfl⟩ : syracuseStep 2699495 = 4049243) B4049243
theorem B4051187 : Blo 1198416 4051187 := bstep (se 1 (by rfl) ⟨3038390, by rfl⟩ : syracuseStep 4051187 = 6076781) B6076781
theorem B3240199 : Blo 1198416 3240199 := bstep (se 1 (by rfl) ⟨2430149, by rfl⟩ : syracuseStep 3240199 = 4860299) B4860299
theorem B10383671 : Blo 1198416 10383671 := bstep (se 1 (by rfl) ⟨7787753, by rfl⟩ : syracuseStep 10383671 = 15575507) B15575507
theorem B1298791 : Blo 1198416 1298791 := bstep (se 1 (by rfl) ⟨974093, by rfl⟩ : syracuseStep 1298791 = 1948187) B1948187
theorem B3035515 : Blo 1198416 3035515 := bstep (se 1 (by rfl) ⟨2276636, by rfl⟩ : syracuseStep 3035515 = 4553273) B4553273
theorem B2699675 : Blo 1198416 2699675 := bstep (se 1 (by rfl) ⟨2024756, by rfl⟩ : syracuseStep 2699675 = 4049513) B4049513
theorem B2560567 : Blo 1198416 2560567 := bstep (se 1 (by rfl) ⟨1920425, by rfl⟩ : syracuseStep 2560567 = 3840851) B3840851
theorem B4616939 : Blo 1198416 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B1798907 : Blo 1198416 1798907 := bstep (se 1 (by rfl) ⟨1349180, by rfl⟩ : syracuseStep 1798907 = 2698361) B2698361
theorem B18469709 : Blo 1198416 18469709 := bstep (se 3 (by rfl) ⟨3463070, by rfl⟩ : syracuseStep 18469709 = 6926141) B6926141
theorem B5125031 : Blo 1198416 5125031 := bstep (se 1 (by rfl) ⟨3843773, by rfl⟩ : syracuseStep 5125031 = 7687547) B7687547
theorem B1348591 : Blo 1198416 1348591 := bstep (se 1 (by rfl) ⟨1011443, by rfl⟩ : syracuseStep 1348591 = 2022887) B2022887
theorem B20509685 : Blo 1198416 20509685 := bstep (se 5 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 20509685 = 1922783) B1922783
theorem B2700359 : Blo 1198416 2700359 := bstep (se 1 (by rfl) ⟨2025269, by rfl⟩ : syracuseStep 2700359 = 4050539) B4050539
theorem B11523167 : Blo 1198416 11523167 := bstep (se 1 (by rfl) ⟨8642375, by rfl⟩ : syracuseStep 11523167 = 17284751) B17284751
theorem B1922143 : Blo 1198416 1922143 := bstep (se 1 (by rfl) ⟨1441607, by rfl⟩ : syracuseStep 1922143 = 2883215) B2883215
theorem B21894263 : Blo 1198416 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B33731741 : Blo 1198416 33731741 := bstep (se 3 (by rfl) ⟨6324701, by rfl⟩ : syracuseStep 33731741 = 12649403) B12649403
theorem B1799351 : Blo 1198416 1799351 := bstep (se 1 (by rfl) ⟨1349513, by rfl⟩ : syracuseStep 1799351 = 2699027) B2699027
theorem B6067385 : Blo 1198416 6067385 := bstep (se 2 (by rfl) ⟨2275269, by rfl⟩ : syracuseStep 6067385 = 4550539) B4550539
theorem B14587123 : Blo 1198416 14587123 := bstep (se 1 (by rfl) ⟨10940342, by rfl⟩ : syracuseStep 14587123 = 21880685) B21880685
theorem B2700539 : Blo 1198416 2700539 := bstep (se 1 (by rfl) ⟨2025404, by rfl⟩ : syracuseStep 2700539 = 4050809) B4050809
theorem B19461383 : Blo 1198416 19461383 := bstep (se 1 (by rfl) ⟨14596037, by rfl⟩ : syracuseStep 19461383 = 29192075) B29192075
theorem B2561387 : Blo 1198416 2561387 := bstep (se 1 (by rfl) ⟨1921040, by rfl⟩ : syracuseStep 2561387 = 3842081) B3842081
theorem B1799591 : Blo 1198416 1799591 := bstep (se 1 (by rfl) ⟨1349693, by rfl⟩ : syracuseStep 1799591 = 2699387) B2699387
theorem B2700755 : Blo 1198416 2700755 := bstep (se 1 (by rfl) ⟨2025566, by rfl⟩ : syracuseStep 2700755 = 4051133) B4051133
theorem B1349095 : Blo 1198416 1349095 := bstep (se 1 (by rfl) ⟨1011821, by rfl⟩ : syracuseStep 1349095 = 2023643) B2023643
theorem B3413497 : Blo 1198416 3413497 := bstep (se 2 (by rfl) ⟨1280061, by rfl⟩ : syracuseStep 3413497 = 2560123) B2560123
theorem B1799771 : Blo 1198416 1799771 := bstep (se 1 (by rfl) ⟨1349828, by rfl⟩ : syracuseStep 1799771 = 2699657) B2699657
theorem B1349275 : Blo 1198416 1349275 := bstep (se 1 (by rfl) ⟨1011956, by rfl⟩ : syracuseStep 1349275 = 2023913) B2023913
theorem B6829865 : Blo 1198416 6829865 := bstep (se 2 (by rfl) ⟨2561199, by rfl⟩ : syracuseStep 6829865 = 5122399) B5122399
theorem B10245959 : Blo 1198416 10245959 := bstep (se 1 (by rfl) ⟨7684469, by rfl⟩ : syracuseStep 10245959 = 15368939) B15368939
theorem B7296925 : Blo 1198416 7296925 := bstep (se 3 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 7296925 = 2736347) B2736347
theorem B1800233 : Blo 1198416 1800233 := bstep (se 2 (by rfl) ⟨675087, by rfl⟩ : syracuseStep 1800233 = 1350175) B1350175
theorem B6076457 : Blo 1198416 6076457 := bstep (se 2 (by rfl) ⟨2278671, by rfl⟩ : syracuseStep 6076457 = 4557343) B4557343
theorem B1800263 : Blo 1198416 1800263 := bstep (se 1 (by rfl) ⟨1350197, by rfl⟩ : syracuseStep 1800263 = 2700395) B2700395
theorem B4045031 : Blo 1198416 4045031 := bstep (se 1 (by rfl) ⟨3033773, by rfl⟩ : syracuseStep 4045031 = 6067547) B6067547
theorem B2881831 : Blo 1198416 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B3037601 : Blo 1198416 3037601 := bstep (se 2 (by rfl) ⟨1139100, by rfl⟩ : syracuseStep 3037601 = 2278201) B2278201
theorem B2275931 : Blo 1198416 2275931 := bstep (se 1 (by rfl) ⟨1706948, by rfl⟩ : syracuseStep 2275931 = 3413897) B3413897
theorem B4160105 : Blo 1198416 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B4553441 : Blo 1198416 4553441 := bstep (se 2 (by rfl) ⟨1707540, by rfl⟩ : syracuseStep 4553441 = 3415081) B3415081
theorem B2276075 : Blo 1198416 2276075 := bstep (se 1 (by rfl) ⟨1707056, by rfl⟩ : syracuseStep 2276075 = 3414113) B3414113
theorem B2161417 : Blo 1198416 2161417 := bstep (se 2 (by rfl) ⟨810531, by rfl⟩ : syracuseStep 2161417 = 1621063) B1621063
theorem B6830891 : Blo 1198416 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B38878231 : Blo 1198416 38878231 := bstep (se 1 (by rfl) ⟨29158673, by rfl⟩ : syracuseStep 38878231 = 58317347) B58317347
theorem B2882791 : Blo 1198416 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B8207777 : Blo 1198416 8207777 := bstep (se 2 (by rfl) ⟨3077916, by rfl⟩ : syracuseStep 8207777 = 6155833) B6155833
theorem B2883023 : Blo 1198416 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B16416215 : Blo 1198416 16416215 := bstep (se 1 (by rfl) ⟨12312161, by rfl⟩ : syracuseStep 16416215 = 24624323) B24624323
theorem B4554215 : Blo 1198416 4554215 := bstep (se 1 (by rfl) ⟨3415661, by rfl⟩ : syracuseStep 4554215 = 6831323) B6831323
theorem B4218493 : Blo 1198416 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B5119631 : Blo 1198416 5119631 := bstep (se 1 (by rfl) ⟨3839723, by rfl⟩ : syracuseStep 5119631 = 7679447) B7679447
theorem B10935971 : Blo 1198416 10935971 := bstep (se 1 (by rfl) ⟨8201978, by rfl⟩ : syracuseStep 10935971 = 16403957) B16403957
theorem B12304237 : Blo 1198416 12304237 := bstep (se 3 (by rfl) ⟨2307044, by rfl⟩ : syracuseStep 12304237 = 4614089) B4614089
theorem B4046759 : Blo 1198416 4046759 := bstep (se 1 (by rfl) ⟨3035069, by rfl⟩ : syracuseStep 4046759 = 6070139) B6070139
theorem B1441703 : Blo 1198416 1441703 := bstep (se 1 (by rfl) ⟨1081277, by rfl⟩ : syracuseStep 1441703 = 2162555) B2162555
theorem B4046921 : Blo 1198416 4046921 := bstep (se 2 (by rfl) ⟨1517595, by rfl⟩ : syracuseStep 4046921 = 3035191) B3035191
theorem B4554899 : Blo 1198416 4554899 := bstep (se 1 (by rfl) ⟨3416174, by rfl⟩ : syracuseStep 4554899 = 6832349) B6832349
theorem B3842441 : Blo 1198416 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B4047353 : Blo 1198416 4047353 := bstep (se 2 (by rfl) ⟨1517757, by rfl⟩ : syracuseStep 4047353 = 3035515) B3035515
theorem B12313139 : Blo 1198416 12313139 := bstep (se 1 (by rfl) ⟨9234854, by rfl⟩ : syracuseStep 12313139 = 18469709) B18469709
theorem B3416687 : Blo 1198416 3416687 := bstep (se 1 (by rfl) ⟨2562515, by rfl⟩ : syracuseStep 3416687 = 5125031) B5125031
theorem B13673123 : Blo 1198416 13673123 := bstep (se 1 (by rfl) ⟨10254842, by rfl⟩ : syracuseStep 13673123 = 20509685) B20509685
theorem B22487827 : Blo 1198416 22487827 := bstep (se 1 (by rfl) ⟨16865870, by rfl⟩ : syracuseStep 22487827 = 33731741) B33731741
theorem B27689789 : Blo 1198416 27689789 := bstep (se 3 (by rfl) ⟨5191835, by rfl⟩ : syracuseStep 27689789 = 10383671) B10383671
theorem B4047677 : Blo 1198416 4047677 := bstep (se 3 (by rfl) ⟨758939, by rfl⟩ : syracuseStep 4047677 = 1517879) B1517879
theorem B5768273 : Blo 1198416 5768273 := bstep (se 2 (by rfl) ⟨2163102, by rfl⟩ : syracuseStep 5768273 = 4326205) B4326205
theorem B2696687 : Blo 1198416 2696687 := bstep (se 1 (by rfl) ⟨2022515, by rfl⟩ : syracuseStep 2696687 = 4045031) B4045031
theorem B4048379 : Blo 1198416 4048379 := bstep (se 1 (by rfl) ⟨3036284, by rfl⟩ : syracuseStep 4048379 = 6072569) B6072569
theorem B2025067 : Blo 1198416 2025067 := bstep (se 1 (by rfl) ⟨1518800, by rfl⟩ : syracuseStep 2025067 = 3037601) B3037601
theorem B3843721 : Blo 1198416 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B19449497 : Blo 1198416 19449497 := bstep (se 2 (by rfl) ⟨7293561, by rfl⟩ : syracuseStep 19449497 = 14587123) B14587123
theorem B1517287 : Blo 1198416 1517287 := bstep (se 1 (by rfl) ⟨1137965, by rfl⟩ : syracuseStep 1517287 = 2275931) B2275931
theorem B1517383 : Blo 1198416 1517383 := bstep (se 1 (by rfl) ⟨1138037, by rfl⟩ : syracuseStep 1517383 = 2276075) B2276075
theorem B2025337 : Blo 1198416 2025337 := bstep (se 2 (by rfl) ⟨759501, by rfl⟩ : syracuseStep 2025337 = 1519003) B1519003
theorem B44329193 : Blo 1198416 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B3844541 : Blo 1198416 3844541 := bstep (se 3 (by rfl) ⟨720851, by rfl⟩ : syracuseStep 3844541 = 1441703) B1441703
theorem B1198543 : Blo 1198416 1198543 := bstep (se 1 (by rfl) ⟨898907, by rfl⟩ : syracuseStep 1198543 = 1797815) B1797815
theorem B12978751 : Blo 1198416 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B1198683 : Blo 1198416 1198683 := bstep (se 1 (by rfl) ⟨899012, by rfl⟩ : syracuseStep 1198683 = 1798025) B1798025
theorem B2697839 : Blo 1198416 2697839 := bstep (se 1 (by rfl) ⟨2023379, by rfl⟩ : syracuseStep 2697839 = 4046759) B4046759
theorem B21048029 : Blo 1198416 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B1198847 : Blo 1198416 1198847 := bstep (se 1 (by rfl) ⟨899135, by rfl⟩ : syracuseStep 1198847 = 1798271) B1798271
theorem B3033895 : Blo 1198416 3033895 := bstep (se 1 (by rfl) ⟨2275421, by rfl⟩ : syracuseStep 3033895 = 4550843) B4550843
theorem B2698055 : Blo 1198416 2698055 := bstep (se 1 (by rfl) ⟨2023541, by rfl⟩ : syracuseStep 2698055 = 4047083) B4047083
theorem B4860755 : Blo 1198416 4860755 := bstep (se 1 (by rfl) ⟨3645566, by rfl⟩ : syracuseStep 4860755 = 7291133) B7291133
theorem B4320265 : Blo 1198416 4320265 := bstep (se 2 (by rfl) ⟨1620099, by rfl⟩ : syracuseStep 4320265 = 3240199) B3240199
theorem B1707113 : Blo 1198416 1707113 := bstep (se 2 (by rfl) ⟨640167, by rfl⟩ : syracuseStep 1707113 = 1280335) B1280335
theorem B1731721 : Blo 1198416 1731721 := bstep (se 2 (by rfl) ⟨649395, by rfl⟩ : syracuseStep 1731721 = 1298791) B1298791
theorem B1199271 : Blo 1198416 1199271 := bstep (se 1 (by rfl) ⟨899453, by rfl⟩ : syracuseStep 1199271 = 1798907) B1798907
theorem B1199567 : Blo 1198416 1199567 := bstep (se 1 (by rfl) ⟨899675, by rfl⟩ : syracuseStep 1199567 = 1799351) B1799351
theorem B1199727 : Blo 1198416 1199727 := bstep (se 1 (by rfl) ⟨899795, by rfl⟩ : syracuseStep 1199727 = 1799591) B1799591
theorem B1797851 : Blo 1198416 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B1199847 : Blo 1198416 1199847 := bstep (se 1 (by rfl) ⟨899885, by rfl⟩ : syracuseStep 1199847 = 1799771) B1799771
theorem B6836197 : Blo 1198416 6836197 := bstep (se 4 (by rfl) ⟨640893, by rfl⟩ : syracuseStep 6836197 = 1281787) B1281787
theorem B1798121 : Blo 1198416 1798121 := bstep (se 2 (by rfl) ⟨674295, by rfl⟩ : syracuseStep 1798121 = 1348591) B1348591
theorem B1798139 : Blo 1198416 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B1200155 : Blo 1198416 1200155 := bstep (se 1 (by rfl) ⟨900116, by rfl⟩ : syracuseStep 1200155 = 1800233) B1800233
theorem B4050971 : Blo 1198416 4050971 := bstep (se 1 (by rfl) ⟨3038228, by rfl⟩ : syracuseStep 4050971 = 6076457) B6076457
theorem B1798175 : Blo 1198416 1798175 := bstep (se 1 (by rfl) ⟨1348631, by rfl⟩ : syracuseStep 1798175 = 2697263) B2697263
theorem B1200175 : Blo 1198416 1200175 := bstep (se 1 (by rfl) ⟨900131, by rfl⟩ : syracuseStep 1200175 = 1800263) B1800263
theorem B1798199 : Blo 1198416 1798199 := bstep (se 1 (by rfl) ⟨1348649, by rfl⟩ : syracuseStep 1798199 = 2697299) B2697299
theorem B1798319 : Blo 1198416 1798319 := bstep (se 1 (by rfl) ⟨1348739, by rfl⟩ : syracuseStep 1798319 = 2697479) B2697479
theorem B1798523 : Blo 1198416 1798523 := bstep (se 1 (by rfl) ⟨1348892, by rfl⟩ : syracuseStep 1798523 = 2697785) B2697785
theorem B2773403 : Blo 1198416 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B3035627 : Blo 1198416 3035627 := bstep (se 1 (by rfl) ⟨2276720, by rfl⟩ : syracuseStep 3035627 = 4553441) B4553441
theorem B1798793 : Blo 1198416 1798793 := bstep (se 2 (by rfl) ⟨674547, by rfl⟩ : syracuseStep 1798793 = 1349095) B1349095
theorem B4551329 : Blo 1198416 4551329 := bstep (se 2 (by rfl) ⟨1706748, by rfl⟩ : syracuseStep 4551329 = 3413497) B3413497
theorem B6075161 : Blo 1198416 6075161 := bstep (se 2 (by rfl) ⟨2278185, by rfl⟩ : syracuseStep 6075161 = 4556371) B4556371
theorem B5624657 : Blo 1198416 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B1799003 : Blo 1198416 1799003 := bstep (se 1 (by rfl) ⟨1349252, by rfl⟩ : syracuseStep 1799003 = 2698505) B2698505
theorem B1799033 : Blo 1198416 1799033 := bstep (se 2 (by rfl) ⟨674637, by rfl⟩ : syracuseStep 1799033 = 1349275) B1349275
theorem B1922015 : Blo 1198416 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B3036143 : Blo 1198416 3036143 := bstep (se 1 (by rfl) ⟨2277107, by rfl⟩ : syracuseStep 3036143 = 4554215) B4554215
theorem B3413087 : Blo 1198416 3413087 := bstep (se 1 (by rfl) ⟨2559815, by rfl⟩ : syracuseStep 3413087 = 5119631) B5119631
theorem B16405649 : Blo 1198416 16405649 := bstep (se 2 (by rfl) ⟨6152118, by rfl⟩ : syracuseStep 16405649 = 12304237) B12304237
theorem B9729233 : Blo 1198416 9729233 := bstep (se 2 (by rfl) ⟨3648462, by rfl⟩ : syracuseStep 9729233 = 7296925) B7296925
theorem B13661459 : Blo 1198416 13661459 := bstep (se 1 (by rfl) ⟨10246094, by rfl⟩ : syracuseStep 13661459 = 20492189) B20492189
theorem B7017839 : Blo 1198416 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B6829433 : Blo 1198416 6829433 := bstep (se 2 (by rfl) ⟨2561037, by rfl⟩ : syracuseStep 6829433 = 5122075) B5122075
theorem B2700665 : Blo 1198416 2700665 := bstep (se 2 (by rfl) ⟨1012749, by rfl⟩ : syracuseStep 2700665 = 2025499) B2025499
theorem B1799663 : Blo 1198416 1799663 := bstep (se 1 (by rfl) ⟨1349747, by rfl⟩ : syracuseStep 1799663 = 2699495) B2699495
theorem B2700791 : Blo 1198416 2700791 := bstep (se 1 (by rfl) ⟨2025593, by rfl⟩ : syracuseStep 2700791 = 4051187) B4051187
theorem B3839507 : Blo 1198416 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B1799783 : Blo 1198416 1799783 := bstep (se 1 (by rfl) ⟨1349837, by rfl⟩ : syracuseStep 1799783 = 2699675) B2699675
theorem B3077959 : Blo 1198416 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B3413839 : Blo 1198416 3413839 := bstep (se 1 (by rfl) ⟨2560379, by rfl⟩ : syracuseStep 3413839 = 5120759) B5120759
theorem B1800239 : Blo 1198416 1800239 := bstep (se 1 (by rfl) ⟨1350179, by rfl⟩ : syracuseStep 1800239 = 2700359) B2700359
theorem B7682111 : Blo 1198416 7682111 := bstep (se 1 (by rfl) ⟨5761583, by rfl⟩ : syracuseStep 7682111 = 11523167) B11523167
theorem B3414089 : Blo 1198416 3414089 := bstep (se 2 (by rfl) ⟨1280283, by rfl⟩ : syracuseStep 3414089 = 2560567) B2560567
theorem B14596175 : Blo 1198416 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B1349743 : Blo 1198416 1349743 := bstep (se 1 (by rfl) ⟨1012307, by rfl⟩ : syracuseStep 1349743 = 2024615) B2024615
theorem B4044923 : Blo 1198416 4044923 := bstep (se 1 (by rfl) ⟨3033692, by rfl⟩ : syracuseStep 4044923 = 6067385) B6067385
theorem B1800359 : Blo 1198416 1800359 := bstep (se 1 (by rfl) ⟨1350269, by rfl⟩ : syracuseStep 1800359 = 2700539) B2700539
theorem B12974255 : Blo 1198416 12974255 := bstep (se 1 (by rfl) ⟨9730691, by rfl⟩ : syracuseStep 12974255 = 19461383) B19461383
theorem B6830365 : Blo 1198416 6830365 := bstep (se 3 (by rfl) ⟨1280693, by rfl⟩ : syracuseStep 6830365 = 2561387) B2561387
theorem B1800503 : Blo 1198416 1800503 := bstep (se 1 (by rfl) ⟨1350377, by rfl⟩ : syracuseStep 1800503 = 2700755) B2700755
theorem B2881889 : Blo 1198416 2881889 := bstep (se 2 (by rfl) ⟨1080708, by rfl⟩ : syracuseStep 2881889 = 2161417) B2161417
theorem B21887405 : Blo 1198416 21887405 := bstep (se 3 (by rfl) ⟨4103888, by rfl⟩ : syracuseStep 21887405 = 8207777) B8207777
theorem B4553243 : Blo 1198416 4553243 := bstep (se 1 (by rfl) ⟨3414932, by rfl⟩ : syracuseStep 4553243 = 6829865) B6829865
theorem B6830639 : Blo 1198416 6830639 := bstep (se 1 (by rfl) ⟨5122979, by rfl⟩ : syracuseStep 6830639 = 10245959) B10245959
theorem B1350247 : Blo 1198416 1350247 := bstep (se 1 (by rfl) ⟨1012685, by rfl⟩ : syracuseStep 1350247 = 2025371) B2025371
theorem B51837641 : Blo 1198416 51837641 := bstep (se 2 (by rfl) ⟨19439115, by rfl⟩ : syracuseStep 51837641 = 38878231) B38878231
theorem B2562857 : Blo 1198416 2562857 := bstep (se 2 (by rfl) ⟨961071, by rfl⟩ : syracuseStep 2562857 = 1922143) B1922143
theorem B18472121 : Blo 1198416 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B4553927 : Blo 1198416 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B3038543 : Blo 1198416 3038543 := bstep (se 1 (by rfl) ⟨2278907, by rfl⟩ : syracuseStep 3038543 = 4557815) B4557815
theorem B3415547 : Blo 1198416 3415547 := bstep (se 1 (by rfl) ⟨2561660, by rfl⟩ : syracuseStep 3415547 = 5123321) B5123321
theorem B10944143 : Blo 1198416 10944143 := bstep (se 1 (by rfl) ⟨8208107, by rfl⟩ : syracuseStep 10944143 = 16416215) B16416215
theorem B7290647 : Blo 1198416 7290647 := bstep (se 1 (by rfl) ⟨5467985, by rfl⟩ : syracuseStep 7290647 = 10935971) B10935971
theorem B2023751 : Blo 1198416 2023751 := bstep (se 1 (by rfl) ⟨1517813, by rfl⟩ : syracuseStep 2023751 = 3035627) B3035627
theorem B2277791 : Blo 1198416 2277791 := bstep (se 1 (by rfl) ⟨1708343, by rfl⟩ : syracuseStep 2277791 = 3416687) B3416687
theorem B2024095 : Blo 1198416 2024095 := bstep (se 1 (by rfl) ⟨1518071, by rfl⟩ : syracuseStep 2024095 = 3036143) B3036143
theorem B10937099 : Blo 1198416 10937099 := bstep (se 1 (by rfl) ⟨8202824, by rfl⟩ : syracuseStep 10937099 = 16405649) B16405649
theorem B4678559 : Blo 1198416 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B29983769 : Blo 1198416 29983769 := bstep (se 2 (by rfl) ⟨11243913, by rfl⟩ : syracuseStep 29983769 = 22487827) B22487827
theorem B5760353 : Blo 1198416 5760353 := bstep (se 2 (by rfl) ⟨2160132, by rfl⟩ : syracuseStep 5760353 = 4320265) B4320265
theorem B5121407 : Blo 1198416 5121407 := bstep (se 1 (by rfl) ⟨3841055, by rfl⟩ : syracuseStep 5121407 = 7682111) B7682111
theorem B2696615 : Blo 1198416 2696615 := bstep (se 1 (by rfl) ⟨2022461, by rfl⟩ : syracuseStep 2696615 = 4044923) B4044923
theorem B14591603 : Blo 1198416 14591603 := bstep (se 1 (by rfl) ⟨10943702, by rfl⟩ : syracuseStep 14591603 = 21887405) B21887405
theorem B12314747 : Blo 1198416 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B2025695 : Blo 1198416 2025695 := bstep (se 1 (by rfl) ⟨1519271, by rfl⟩ : syracuseStep 2025695 = 3038543) B3038543
theorem B1198567 : Blo 1198416 1198567 := bstep (se 1 (by rfl) ⟨898925, by rfl⟩ : syracuseStep 1198567 = 1797851) B1797851
theorem B4860431 : Blo 1198416 4860431 := bstep (se 1 (by rfl) ⟨3645323, by rfl⟩ : syracuseStep 4860431 = 7290647) B7290647
theorem B1198747 : Blo 1198416 1198747 := bstep (se 1 (by rfl) ⟨899060, by rfl⟩ : syracuseStep 1198747 = 1798121) B1798121
theorem B1198759 : Blo 1198416 1198759 := bstep (se 1 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 1198759 = 1798139) B1798139
theorem B1198783 : Blo 1198416 1198783 := bstep (se 1 (by rfl) ⟨899087, by rfl⟩ : syracuseStep 1198783 = 1798175) B1798175
theorem B1198799 : Blo 1198416 1198799 := bstep (se 1 (by rfl) ⟨899099, by rfl⟩ : syracuseStep 1198799 = 1798199) B1798199
theorem B2697947 : Blo 1198416 2697947 := bstep (se 1 (by rfl) ⟨2023460, by rfl⟩ : syracuseStep 2697947 = 4046921) B4046921
theorem B1198879 : Blo 1198416 1198879 := bstep (se 1 (by rfl) ⟨899159, by rfl⟩ : syracuseStep 1198879 = 1798319) B1798319
theorem B9104237 : Blo 1198416 9104237 := bstep (se 3 (by rfl) ⟨1707044, by rfl⟩ : syracuseStep 9104237 = 3414089) B3414089
theorem B1199015 : Blo 1198416 1199015 := bstep (se 1 (by rfl) ⟨899261, by rfl⟩ : syracuseStep 1199015 = 1798523) B1798523
theorem B2698235 : Blo 1198416 2698235 := bstep (se 1 (by rfl) ⟨2023676, by rfl⟩ : syracuseStep 2698235 = 4047353) B4047353
theorem B1199195 : Blo 1198416 1199195 := bstep (se 1 (by rfl) ⟨899396, by rfl⟩ : syracuseStep 1199195 = 1798793) B1798793
theorem B3034219 : Blo 1198416 3034219 := bstep (se 1 (by rfl) ⟨2275664, by rfl⟩ : syracuseStep 3034219 = 4551329) B4551329
theorem B4050107 : Blo 1198416 4050107 := bstep (se 1 (by rfl) ⟨3037580, by rfl⟩ : syracuseStep 4050107 = 6075161) B6075161
theorem B18459859 : Blo 1198416 18459859 := bstep (se 1 (by rfl) ⟨13844894, by rfl⟩ : syracuseStep 18459859 = 27689789) B27689789
theorem B2698451 : Blo 1198416 2698451 := bstep (se 1 (by rfl) ⟨2023838, by rfl⟩ : syracuseStep 2698451 = 4047677) B4047677
theorem B1199335 : Blo 1198416 1199335 := bstep (se 1 (by rfl) ⟨899501, by rfl⟩ : syracuseStep 1199335 = 1799003) B1799003
theorem B1199355 : Blo 1198416 1199355 := bstep (se 1 (by rfl) ⟨899516, by rfl⟩ : syracuseStep 1199355 = 1799033) B1799033
theorem B1281343 : Blo 1198416 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B17305001 : Blo 1198416 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B1797791 : Blo 1198416 1797791 := bstep (se 1 (by rfl) ⟨1348343, by rfl⟩ : syracuseStep 1797791 = 2696687) B2696687
theorem B1199775 : Blo 1198416 1199775 := bstep (se 1 (by rfl) ⟨899831, by rfl⟩ : syracuseStep 1199775 = 1799663) B1799663
theorem B2698919 : Blo 1198416 2698919 := bstep (se 1 (by rfl) ⟨2024189, by rfl⟩ : syracuseStep 2698919 = 4048379) B4048379
theorem B2559671 : Blo 1198416 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B1199855 : Blo 1198416 1199855 := bstep (se 1 (by rfl) ⟨899891, by rfl⟩ : syracuseStep 1199855 = 1799783) B1799783
theorem B10252109 : Blo 1198416 10252109 := bstep (se 3 (by rfl) ⟨1922270, by rfl⟩ : syracuseStep 10252109 = 3844541) B3844541
theorem B1200159 : Blo 1198416 1200159 := bstep (se 1 (by rfl) ⟨900119, by rfl⟩ : syracuseStep 1200159 = 1800239) B1800239
theorem B1200239 : Blo 1198416 1200239 := bstep (se 1 (by rfl) ⟨900179, by rfl⟩ : syracuseStep 1200239 = 1800359) B1800359
theorem B29552795 : Blo 1198416 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B1200335 : Blo 1198416 1200335 := bstep (se 1 (by rfl) ⟨900251, by rfl⟩ : syracuseStep 1200335 = 1800503) B1800503
theorem B1921259 : Blo 1198416 1921259 := bstep (se 1 (by rfl) ⟨1440944, by rfl⟩ : syracuseStep 1921259 = 2881889) B2881889
theorem B3035495 : Blo 1198416 3035495 := bstep (se 1 (by rfl) ⟨2276621, by rfl⟩ : syracuseStep 3035495 = 4553243) B4553243
theorem B1798559 : Blo 1198416 1798559 := bstep (se 1 (by rfl) ⟨1348919, by rfl⟩ : syracuseStep 1798559 = 2697839) B2697839
theorem B34558427 : Blo 1198416 34558427 := bstep (se 1 (by rfl) ⟨25918820, by rfl⟩ : syracuseStep 34558427 = 51837641) B51837641
theorem B1708571 : Blo 1198416 1708571 := bstep (se 1 (by rfl) ⟨1281428, by rfl⟩ : syracuseStep 1708571 = 2562857) B2562857
theorem B1798703 : Blo 1198416 1798703 := bstep (se 1 (by rfl) ⟨1349027, by rfl⟩ : syracuseStep 1798703 = 2698055) B2698055
theorem B3240503 : Blo 1198416 3240503 := bstep (se 1 (by rfl) ⟨2430377, by rfl⟩ : syracuseStep 3240503 = 4860755) B4860755
theorem B3035951 : Blo 1198416 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B2700089 : Blo 1198416 2700089 := bstep (se 2 (by rfl) ⟨1012533, by rfl⟩ : syracuseStep 2700089 = 2025067) B2025067
theorem B5124961 : Blo 1198416 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B7296095 : Blo 1198416 7296095 := bstep (se 1 (by rfl) ⟨5472071, by rfl⟩ : syracuseStep 7296095 = 10944143) B10944143
theorem B4551785 : Blo 1198416 4551785 := bstep (se 2 (by rfl) ⟨1706919, by rfl⟩ : syracuseStep 4551785 = 3413839) B3413839
theorem B2700449 : Blo 1198416 2700449 := bstep (se 2 (by rfl) ⟨1012668, by rfl⟩ : syracuseStep 2700449 = 2025337) B2025337
theorem B9114929 : Blo 1198416 9114929 := bstep (se 2 (by rfl) ⟨3418098, by rfl⟩ : syracuseStep 9114929 = 6836197) B6836197
theorem B2700647 : Blo 1198416 2700647 := bstep (se 1 (by rfl) ⟨2025485, by rfl⟩ : syracuseStep 2700647 = 4050971) B4050971
theorem B3036599 : Blo 1198416 3036599 := bstep (se 1 (by rfl) ⟨2277449, by rfl⟩ : syracuseStep 3036599 = 4554899) B4554899
theorem B1799657 : Blo 1198416 1799657 := bstep (se 2 (by rfl) ⟨674871, by rfl⟩ : syracuseStep 1799657 = 1349743) B1349743
theorem B15382061 : Blo 1198416 15382061 := bstep (se 3 (by rfl) ⟨2884136, by rfl⟩ : syracuseStep 15382061 = 5768273) B5768273
theorem B2561627 : Blo 1198416 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B1848935 : Blo 1198416 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B4552301 : Blo 1198416 4552301 := bstep (se 3 (by rfl) ⟨853556, by rfl⟩ : syracuseStep 4552301 = 1707113) B1707113
theorem B9107153 : Blo 1198416 9107153 := bstep (se 2 (by rfl) ⟨3415182, by rfl⟩ : syracuseStep 9107153 = 6830365) B6830365
theorem B9115415 : Blo 1198416 9115415 := bstep (se 1 (by rfl) ⟨6836561, by rfl⟩ : syracuseStep 9115415 = 13673123) B13673123
theorem B131340149 : Blo 1198416 131340149 := bstep (se 5 (by rfl) ⟨6156569, by rfl⟩ : syracuseStep 131340149 = 12313139) B12313139
theorem B3749771 : Blo 1198416 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B2275391 : Blo 1198416 2275391 := bstep (se 1 (by rfl) ⟨1706543, by rfl⟩ : syracuseStep 2275391 = 3413087) B3413087
theorem B1800329 : Blo 1198416 1800329 := bstep (se 2 (by rfl) ⟨675123, by rfl⟩ : syracuseStep 1800329 = 1350247) B1350247
theorem B6486155 : Blo 1198416 6486155 := bstep (se 1 (by rfl) ⟨4864616, by rfl⟩ : syracuseStep 6486155 = 9729233) B9729233
theorem B9107639 : Blo 1198416 9107639 := bstep (se 1 (by rfl) ⟨6830729, by rfl⟩ : syracuseStep 9107639 = 13661459) B13661459
theorem B4552955 : Blo 1198416 4552955 := bstep (se 1 (by rfl) ⟨3414716, by rfl⟩ : syracuseStep 4552955 = 6829433) B6829433
theorem B1800443 : Blo 1198416 1800443 := bstep (se 1 (by rfl) ⟨1350332, by rfl⟩ : syracuseStep 1800443 = 2700665) B2700665
theorem B1800527 : Blo 1198416 1800527 := bstep (se 1 (by rfl) ⟨1350395, by rfl⟩ : syracuseStep 1800527 = 2700791) B2700791
theorem B4045193 : Blo 1198416 4045193 := bstep (se 2 (by rfl) ⟨1516947, by rfl⟩ : syracuseStep 4045193 = 3033895) B3033895
theorem B12966331 : Blo 1198416 12966331 := bstep (se 1 (by rfl) ⟨9724748, by rfl⟩ : syracuseStep 12966331 = 19449497) B19449497
theorem B9108125 : Blo 1198416 9108125 := bstep (se 3 (by rfl) ⟨1707773, by rfl⟩ : syracuseStep 9108125 = 3415547) B3415547
theorem B9730783 : Blo 1198416 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B8649503 : Blo 1198416 8649503 := bstep (se 1 (by rfl) ⟨6487127, by rfl⟩ : syracuseStep 8649503 = 12974255) B12974255
theorem B2308961 : Blo 1198416 2308961 := bstep (se 2 (by rfl) ⟨865860, by rfl⟩ : syracuseStep 2308961 = 1731721) B1731721
theorem B4553759 : Blo 1198416 4553759 := bstep (se 1 (by rfl) ⟨3415319, by rfl⟩ : syracuseStep 4553759 = 6830639) B6830639
theorem B14032019 : Blo 1198416 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B2023049 : Blo 1198416 2023049 := bstep (se 2 (by rfl) ⟨758643, by rfl⟩ : syracuseStep 2023049 = 1517287) B1517287
theorem B2023177 : Blo 1198416 2023177 := bstep (se 2 (by rfl) ⟨758691, by rfl⟩ : syracuseStep 2023177 = 1517383) B1517383
theorem B4103945 : Blo 1198416 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B19701863 : Blo 1198416 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B2023663 : Blo 1198416 2023663 := bstep (se 1 (by rfl) ⟨1517747, by rfl⟩ : syracuseStep 2023663 = 3035495) B3035495
theorem B7291399 : Blo 1198416 7291399 := bstep (se 1 (by rfl) ⟨5468549, by rfl⟩ : syracuseStep 7291399 = 10937099) B10937099
theorem B2023967 : Blo 1198416 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B19989179 : Blo 1198416 19989179 := bstep (se 1 (by rfl) ⟨14991884, by rfl⟩ : syracuseStep 19989179 = 29983769) B29983769
theorem B15360941 : Blo 1198416 15360941 := bstep (se 3 (by rfl) ⟨2880176, by rfl⟩ : syracuseStep 15360941 = 5760353) B5760353
theorem B2024399 : Blo 1198416 2024399 := bstep (se 1 (by rfl) ⟨1518299, by rfl⟩ : syracuseStep 2024399 = 3036599) B3036599
theorem B13657085 : Blo 1198416 13657085 := bstep (se 3 (by rfl) ⟨2560703, by rfl⟩ : syracuseStep 13657085 = 5121407) B5121407
theorem B6833281 : Blo 1198416 6833281 := bstep (se 2 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 6833281 = 5124961) B5124961
theorem B6071435 : Blo 1198416 6071435 := bstep (se 1 (by rfl) ⟨4553576, by rfl⟩ : syracuseStep 6071435 = 9107153) B9107153
theorem B51897509 : Blo 1198416 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B4556189 : Blo 1198416 4556189 := bstep (se 3 (by rfl) ⟨854285, by rfl⟩ : syracuseStep 4556189 = 1708571) B1708571
theorem B8209831 : Blo 1198416 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B6071759 : Blo 1198416 6071759 := bstep (se 1 (by rfl) ⟨4553819, by rfl⟩ : syracuseStep 6071759 = 9107639) B9107639
theorem B2696795 : Blo 1198416 2696795 := bstep (se 1 (by rfl) ⟨2022596, by rfl⟩ : syracuseStep 2696795 = 4045193) B4045193
theorem B6072083 : Blo 1198416 6072083 := bstep (se 1 (by rfl) ⟨4554062, by rfl⟩ : syracuseStep 6072083 = 9108125) B9108125
theorem B11536667 : Blo 1198416 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B2697569 : Blo 1198416 2697569 := bstep (se 2 (by rfl) ⟨1011588, by rfl⟩ : syracuseStep 2697569 = 2023177) B2023177
theorem B1198527 : Blo 1198416 1198527 := bstep (se 1 (by rfl) ⟨898895, by rfl⟩ : syracuseStep 1198527 = 1797791) B1797791
theorem B1706447 : Blo 1198416 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B6834739 : Blo 1198416 6834739 := bstep (se 1 (by rfl) ⟨5126054, by rfl⟩ : syracuseStep 6834739 = 10252109) B10252109
theorem B1199039 : Blo 1198416 1199039 := bstep (se 1 (by rfl) ⟨899279, by rfl⟩ : syracuseStep 1199039 = 1798559) B1798559
theorem B1518527 : Blo 1198416 1518527 := bstep (se 1 (by rfl) ⟨1138895, by rfl⟩ : syracuseStep 1518527 = 2277791) B2277791
theorem B23038951 : Blo 1198416 23038951 := bstep (se 1 (by rfl) ⟨17279213, by rfl⟩ : syracuseStep 23038951 = 34558427) B34558427
theorem B1199135 : Blo 1198416 1199135 := bstep (se 1 (by rfl) ⟨899351, by rfl⟩ : syracuseStep 1199135 = 1798703) B1798703
theorem B17288441 : Blo 1198416 17288441 := bstep (se 2 (by rfl) ⟨6483165, by rfl⟩ : syracuseStep 17288441 = 12966331) B12966331
theorem B5123357 : Blo 1198416 5123357 := bstep (se 3 (by rfl) ⟨960629, by rfl⟩ : syracuseStep 5123357 = 1921259) B1921259
theorem B3034523 : Blo 1198416 3034523 := bstep (se 1 (by rfl) ⟨2275892, by rfl⟩ : syracuseStep 3034523 = 4551785) B4551785
theorem B2698793 : Blo 1198416 2698793 := bstep (se 2 (by rfl) ⟨1012047, by rfl⟩ : syracuseStep 2698793 = 2024095) B2024095
theorem B1797743 : Blo 1198416 1797743 := bstep (se 1 (by rfl) ⟨1348307, by rfl⟩ : syracuseStep 1797743 = 2696615) B2696615
theorem B1199771 : Blo 1198416 1199771 := bstep (se 1 (by rfl) ⟨899828, by rfl⟩ : syracuseStep 1199771 = 1799657) B1799657
theorem B1707751 : Blo 1198416 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B1232623 : Blo 1198416 1232623 := bstep (se 1 (by rfl) ⟨924467, by rfl⟩ : syracuseStep 1232623 = 1848935) B1848935
theorem B3034867 : Blo 1198416 3034867 := bstep (se 1 (by rfl) ⟨2276150, by rfl⟩ : syracuseStep 3034867 = 4552301) B4552301
theorem B9727735 : Blo 1198416 9727735 := bstep (se 1 (by rfl) ⟨7295801, by rfl⟩ : syracuseStep 9727735 = 14591603) B14591603
theorem B87560099 : Blo 1198416 87560099 := bstep (se 1 (by rfl) ⟨65670074, by rfl⟩ : syracuseStep 87560099 = 131340149) B131340149
theorem B1200219 : Blo 1198416 1200219 := bstep (se 1 (by rfl) ⟨900164, by rfl⟩ : syracuseStep 1200219 = 1800329) B1800329
theorem B3035303 : Blo 1198416 3035303 := bstep (se 1 (by rfl) ⟨2276477, by rfl⟩ : syracuseStep 3035303 = 4552955) B4552955
theorem B1200295 : Blo 1198416 1200295 := bstep (se 1 (by rfl) ⟨900221, by rfl⟩ : syracuseStep 1200295 = 1800443) B1800443
theorem B1200351 : Blo 1198416 1200351 := bstep (se 1 (by rfl) ⟨900263, by rfl⟩ : syracuseStep 1200351 = 1800527) B1800527
theorem B24613145 : Blo 1198416 24613145 := bstep (se 2 (by rfl) ⟨9229929, by rfl⟩ : syracuseStep 24613145 = 18459859) B18459859
theorem B3240287 : Blo 1198416 3240287 := bstep (se 1 (by rfl) ⟨2430215, by rfl⟩ : syracuseStep 3240287 = 4860431) B4860431
theorem B1708457 : Blo 1198416 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B1798631 : Blo 1198416 1798631 := bstep (se 1 (by rfl) ⟨1348973, by rfl⟩ : syracuseStep 1798631 = 2697947) B2697947
theorem B1798823 : Blo 1198416 1798823 := bstep (se 1 (by rfl) ⟨1349117, by rfl⟩ : syracuseStep 1798823 = 2698235) B2698235
theorem B3035839 : Blo 1198416 3035839 := bstep (se 1 (by rfl) ⟨2276879, by rfl⟩ : syracuseStep 3035839 = 4553759) B4553759
theorem B2700071 : Blo 1198416 2700071 := bstep (se 1 (by rfl) ⟨2025053, by rfl⟩ : syracuseStep 2700071 = 4050107) B4050107
theorem B1798967 : Blo 1198416 1798967 := bstep (se 1 (by rfl) ⟨1349225, by rfl⟩ : syracuseStep 1798967 = 2698451) B2698451
theorem B9999389 : Blo 1198416 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1348699 : Blo 1198416 1348699 := bstep (se 1 (by rfl) ⟨1011524, by rfl⟩ : syracuseStep 1348699 = 2023049) B2023049
theorem B1799279 : Blo 1198416 1799279 := bstep (se 1 (by rfl) ⟨1349459, by rfl⟩ : syracuseStep 1799279 = 2698919) B2698919
theorem B6067709 : Blo 1198416 6067709 := bstep (se 3 (by rfl) ⟨1137695, by rfl⟩ : syracuseStep 6067709 = 2275391) B2275391
theorem B1349167 : Blo 1198416 1349167 := bstep (se 1 (by rfl) ⟨1011875, by rfl⟩ : syracuseStep 1349167 = 2023751) B2023751
theorem B2160335 : Blo 1198416 2160335 := bstep (se 1 (by rfl) ⟨1620251, by rfl⟩ : syracuseStep 2160335 = 3240503) B3240503
theorem B1800059 : Blo 1198416 1800059 := bstep (se 1 (by rfl) ⟨1350044, by rfl⟩ : syracuseStep 1800059 = 2700089) B2700089
theorem B3119039 : Blo 1198416 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B4864063 : Blo 1198416 4864063 := bstep (se 1 (by rfl) ⟨3648047, by rfl⟩ : syracuseStep 4864063 = 7296095) B7296095
theorem B1800299 : Blo 1198416 1800299 := bstep (se 1 (by rfl) ⟨1350224, by rfl⟩ : syracuseStep 1800299 = 2700449) B2700449
theorem B6076619 : Blo 1198416 6076619 := bstep (se 1 (by rfl) ⟨4557464, by rfl⟩ : syracuseStep 6076619 = 9114929) B9114929
theorem B1800431 : Blo 1198416 1800431 := bstep (se 1 (by rfl) ⟨1350323, by rfl⟩ : syracuseStep 1800431 = 2700647) B2700647
theorem B10254707 : Blo 1198416 10254707 := bstep (se 1 (by rfl) ⟨7691030, by rfl⟩ : syracuseStep 10254707 = 15382061) B15382061
theorem B6076943 : Blo 1198416 6076943 := bstep (se 1 (by rfl) ⟨4557707, by rfl⟩ : syracuseStep 6076943 = 9115415) B9115415
theorem B4324103 : Blo 1198416 4324103 := bstep (se 1 (by rfl) ⟨3243077, by rfl⟩ : syracuseStep 4324103 = 6486155) B6486155
theorem B4045625 : Blo 1198416 4045625 := bstep (se 2 (by rfl) ⟨1517109, by rfl⟩ : syracuseStep 4045625 = 3034219) B3034219
theorem B1350463 : Blo 1198416 1350463 := bstep (se 1 (by rfl) ⟨1012847, by rfl⟩ : syracuseStep 1350463 = 2025695) B2025695
theorem B5766335 : Blo 1198416 5766335 := bstep (se 1 (by rfl) ⟨4324751, by rfl⟩ : syracuseStep 5766335 = 8649503) B8649503
theorem B1539307 : Blo 1198416 1539307 := bstep (se 1 (by rfl) ⟨1154480, by rfl⟩ : syracuseStep 1539307 = 2308961) B2308961
theorem B6069491 : Blo 1198416 6069491 := bstep (se 1 (by rfl) ⟨4552118, by rfl⟩ : syracuseStep 6069491 = 9104237) B9104237
theorem B9354679 : Blo 1198416 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B2735963 : Blo 1198416 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B2023535 : Blo 1198416 2023535 := bstep (se 1 (by rfl) ⟨1517651, by rfl⟩ : syracuseStep 2023535 = 3035303) B3035303
theorem B16408763 : Blo 1198416 16408763 := bstep (se 1 (by rfl) ⟨12306572, by rfl⟩ : syracuseStep 16408763 = 24613145) B24613145
theorem B10240627 : Blo 1198416 10240627 := bstep (se 1 (by rfl) ⟨7680470, by rfl⟩ : syracuseStep 10240627 = 15360941) B15360941
theorem B4047623 : Blo 1198416 4047623 := bstep (se 1 (by rfl) ⟨3035717, by rfl⟩ : syracuseStep 4047623 = 6071435) B6071435
theorem B4047785 : Blo 1198416 4047785 := bstep (se 2 (by rfl) ⟨1517919, by rfl⟩ : syracuseStep 4047785 = 3035839) B3035839
theorem B4047839 : Blo 1198416 4047839 := bstep (se 1 (by rfl) ⟨3035879, by rfl⟩ : syracuseStep 4047839 = 6071759) B6071759
theorem B4555885 : Blo 1198416 4555885 := bstep (se 3 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 4555885 = 1708457) B1708457
theorem B4048055 : Blo 1198416 4048055 := bstep (se 1 (by rfl) ⟨3036041, by rfl⟩ : syracuseStep 4048055 = 6072083) B6072083
theorem B8209637 : Blo 1198416 8209637 := bstep (se 4 (by rfl) ⟨769653, by rfl⟩ : syracuseStep 8209637 = 1539307) B1539307
theorem B9111041 : Blo 1198416 9111041 := bstep (se 2 (by rfl) ⟨3416640, by rfl⟩ : syracuseStep 9111041 = 6833281) B6833281
theorem B2697083 : Blo 1198416 2697083 := bstep (se 1 (by rfl) ⟨2022812, by rfl⟩ : syracuseStep 2697083 = 4045625) B4045625
theorem B10946441 : Blo 1198416 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B3844223 : Blo 1198416 3844223 := bstep (se 1 (by rfl) ⟨2883167, by rfl⟩ : syracuseStep 3844223 = 5766335) B5766335
theorem B49891621 : Blo 1198416 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B12970313 : Blo 1198416 12970313 := bstep (se 2 (by rfl) ⟨4863867, by rfl⟩ : syracuseStep 12970313 = 9727735) B9727735
theorem B1198495 : Blo 1198416 1198495 := bstep (se 1 (by rfl) ⟨898871, by rfl⟩ : syracuseStep 1198495 = 1797743) B1797743
theorem B4049405 : Blo 1198416 4049405 := bstep (se 3 (by rfl) ⟨759263, by rfl⟩ : syracuseStep 4049405 = 1518527) B1518527
theorem B13134575 : Blo 1198416 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B2698217 : Blo 1198416 2698217 := bstep (se 2 (by rfl) ⟨1011831, by rfl⟩ : syracuseStep 2698217 = 2023663) B2023663
theorem B1199087 : Blo 1198416 1199087 := bstep (se 1 (by rfl) ⟨899315, by rfl⟩ : syracuseStep 1199087 = 1798631) B1798631
theorem B1199215 : Blo 1198416 1199215 := bstep (se 1 (by rfl) ⟨899411, by rfl⟩ : syracuseStep 1199215 = 1798823) B1798823
theorem B1199311 : Blo 1198416 1199311 := bstep (se 1 (by rfl) ⟨899483, by rfl⟩ : syracuseStep 1199311 = 1798967) B1798967
theorem B9104723 : Blo 1198416 9104723 := bstep (se 1 (by rfl) ⟨6828542, by rfl⟩ : syracuseStep 9104723 = 13657085) B13657085
theorem B9112985 : Blo 1198416 9112985 := bstep (se 2 (by rfl) ⟨3417369, by rfl⟩ : syracuseStep 9112985 = 6834739) B6834739
theorem B1199519 : Blo 1198416 1199519 := bstep (se 1 (by rfl) ⟨899639, by rfl⟩ : syracuseStep 1199519 = 1799279) B1799279
theorem B34598339 : Blo 1198416 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B1797863 : Blo 1198416 1797863 := bstep (se 1 (by rfl) ⟨1348397, by rfl⟩ : syracuseStep 1797863 = 2696795) B2696795
theorem B4550525 : Blo 1198416 4550525 := bstep (se 3 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 4550525 = 1706447) B1706447
theorem B1200039 : Blo 1198416 1200039 := bstep (se 1 (by rfl) ⟨900029, by rfl⟩ : syracuseStep 1200039 = 1800059) B1800059
theorem B1200199 : Blo 1198416 1200199 := bstep (se 1 (by rfl) ⟨900149, by rfl⟩ : syracuseStep 1200199 = 1800299) B1800299
theorem B1798265 : Blo 1198416 1798265 := bstep (se 2 (by rfl) ⟨674349, by rfl⟩ : syracuseStep 1798265 = 1348699) B1348699
theorem B4051079 : Blo 1198416 4051079 := bstep (se 1 (by rfl) ⟨3038309, by rfl⟩ : syracuseStep 4051079 = 6076619) B6076619
theorem B1200287 : Blo 1198416 1200287 := bstep (se 1 (by rfl) ⟨900215, by rfl⟩ : syracuseStep 1200287 = 1800431) B1800431
theorem B1798379 : Blo 1198416 1798379 := bstep (se 1 (by rfl) ⟨1348784, by rfl⟩ : syracuseStep 1798379 = 2697569) B2697569
theorem B6836471 : Blo 1198416 6836471 := bstep (se 1 (by rfl) ⟨5127353, by rfl⟩ : syracuseStep 6836471 = 10254707) B10254707
theorem B4051295 : Blo 1198416 4051295 := bstep (se 1 (by rfl) ⟨3038471, by rfl⟩ : syracuseStep 4051295 = 6076943) B6076943
theorem B1798889 : Blo 1198416 1798889 := bstep (se 2 (by rfl) ⟨674583, by rfl⟩ : syracuseStep 1798889 = 1349167) B1349167
theorem B1643497 : Blo 1198416 1643497 := bstep (se 2 (by rfl) ⟨616311, by rfl⟩ : syracuseStep 1643497 = 1232623) B1232623
theorem B1799195 : Blo 1198416 1799195 := bstep (se 1 (by rfl) ⟨1349396, by rfl⟩ : syracuseStep 1799195 = 2698793) B2698793
theorem B1823975 : Blo 1198416 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B58373399 : Blo 1198416 58373399 := bstep (se 1 (by rfl) ⟨43780049, by rfl⟩ : syracuseStep 58373399 = 87560099) B87560099
theorem B6485417 : Blo 1198416 6485417 := bstep (se 2 (by rfl) ⟨2432031, by rfl⟩ : syracuseStep 6485417 = 4864063) B4864063
theorem B2160191 : Blo 1198416 2160191 := bstep (se 1 (by rfl) ⟨1620143, by rfl⟩ : syracuseStep 2160191 = 3240287) B3240287
theorem B1349311 : Blo 1198416 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B13326119 : Blo 1198416 13326119 := bstep (se 1 (by rfl) ⟨9994589, by rfl⟩ : syracuseStep 13326119 = 19989179) B19989179
theorem B1800047 : Blo 1198416 1800047 := bstep (se 1 (by rfl) ⟨1350035, by rfl⟩ : syracuseStep 1800047 = 2700071) B2700071
theorem B1349599 : Blo 1198416 1349599 := bstep (se 1 (by rfl) ⟨1012199, by rfl⟩ : syracuseStep 1349599 = 2024399) B2024399
theorem B9721865 : Blo 1198416 9721865 := bstep (se 2 (by rfl) ⟨3645699, by rfl⟩ : syracuseStep 9721865 = 7291399) B7291399
theorem B6666259 : Blo 1198416 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B3037459 : Blo 1198416 3037459 := bstep (se 1 (by rfl) ⟨2278094, by rfl⟩ : syracuseStep 3037459 = 4556189) B4556189
theorem B4045139 : Blo 1198416 4045139 := bstep (se 1 (by rfl) ⟨3033854, by rfl⟩ : syracuseStep 4045139 = 6067709) B6067709
theorem B1800617 : Blo 1198416 1800617 := bstep (se 2 (by rfl) ⟨675231, by rfl⟩ : syracuseStep 1800617 = 1350463) B1350463
theorem B1440223 : Blo 1198416 1440223 := bstep (se 1 (by rfl) ⟨1080167, by rfl⟩ : syracuseStep 1440223 = 2160335) B2160335
theorem B2079359 : Blo 1198416 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B30718601 : Blo 1198416 30718601 := bstep (se 2 (by rfl) ⟨11519475, by rfl⟩ : syracuseStep 30718601 = 23038951) B23038951
theorem B7691111 : Blo 1198416 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B2882735 : Blo 1198416 2882735 := bstep (se 1 (by rfl) ⟨2162051, by rfl⟩ : syracuseStep 2882735 = 4324103) B4324103
theorem B4046327 : Blo 1198416 4046327 := bstep (se 1 (by rfl) ⟨3034745, by rfl⟩ : syracuseStep 4046327 = 6069491) B6069491
theorem B11525627 : Blo 1198416 11525627 := bstep (se 1 (by rfl) ⟨8644220, by rfl⟩ : syracuseStep 11525627 = 17288441) B17288441
theorem B3415571 : Blo 1198416 3415571 := bstep (se 1 (by rfl) ⟨2561678, by rfl⟩ : syracuseStep 3415571 = 5123357) B5123357
theorem B2023015 : Blo 1198416 2023015 := bstep (se 1 (by rfl) ⟨1517261, by rfl⟩ : syracuseStep 2023015 = 3034523) B3034523
theorem B2277001 : Blo 1198416 2277001 := bstep (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) B1707751
theorem B4046489 : Blo 1198416 4046489 := bstep (se 2 (by rfl) ⟨1517433, by rfl⟩ : syracuseStep 4046489 = 3034867) B3034867
theorem B8888345 : Blo 1198416 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B5473091 : Blo 1198416 5473091 := bstep (se 1 (by rfl) ⟨4104818, by rfl⟩ : syracuseStep 5473091 = 8209637) B8209637
theorem B6481243 : Blo 1198416 6481243 := bstep (se 1 (by rfl) ⟨4860932, by rfl⟩ : syracuseStep 6481243 = 9721865) B9721865
theorem B2696759 : Blo 1198416 2696759 := bstep (se 1 (by rfl) ⟨2022569, by rfl⟩ : syracuseStep 2696759 = 4045139) B4045139
theorem B1386239 : Blo 1198416 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B2697353 : Blo 1198416 2697353 := bstep (se 2 (by rfl) ⟨1011507, by rfl⟩ : syracuseStep 2697353 = 2023015) B2023015
theorem B2697551 : Blo 1198416 2697551 := bstep (se 1 (by rfl) ⟨2023163, by rfl⟩ : syracuseStep 2697551 = 4046327) B4046327
theorem B2697659 : Blo 1198416 2697659 := bstep (se 1 (by rfl) ⟨2023244, by rfl⟩ : syracuseStep 2697659 = 4046489) B4046489
theorem B1198575 : Blo 1198416 1198575 := bstep (se 1 (by rfl) ⟨898931, by rfl⟩ : syracuseStep 1198575 = 1797863) B1797863
theorem B3033683 : Blo 1198416 3033683 := bstep (se 1 (by rfl) ⟨2275262, by rfl⟩ : syracuseStep 3033683 = 4550525) B4550525
theorem B1198843 : Blo 1198416 1198843 := bstep (se 1 (by rfl) ⟨899132, by rfl⟩ : syracuseStep 1198843 = 1798265) B1798265
theorem B10939175 : Blo 1198416 10939175 := bstep (se 1 (by rfl) ⟨8204381, by rfl⟩ : syracuseStep 10939175 = 16408763) B16408763
theorem B1198919 : Blo 1198416 1198919 := bstep (se 1 (by rfl) ⟨899189, by rfl⟩ : syracuseStep 1198919 = 1798379) B1798379
theorem B4557647 : Blo 1198416 4557647 := bstep (se 1 (by rfl) ⟨3418235, by rfl⟩ : syracuseStep 4557647 = 6836471) B6836471
theorem B4049945 : Blo 1198416 4049945 := bstep (se 2 (by rfl) ⟨1518729, by rfl⟩ : syracuseStep 4049945 = 3037459) B3037459
theorem B66522161 : Blo 1198416 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B1199259 : Blo 1198416 1199259 := bstep (se 1 (by rfl) ⟨899444, by rfl⟩ : syracuseStep 1199259 = 1798889) B1798889
theorem B2698415 : Blo 1198416 2698415 := bstep (se 1 (by rfl) ⟨2023811, by rfl⟩ : syracuseStep 2698415 = 4047623) B4047623
theorem B2698523 : Blo 1198416 2698523 := bstep (se 1 (by rfl) ⟨2023892, by rfl⟩ : syracuseStep 2698523 = 4047785) B4047785
theorem B2698559 : Blo 1198416 2698559 := bstep (se 1 (by rfl) ⟨2023919, by rfl⟩ : syracuseStep 2698559 = 4047839) B4047839
theorem B1199463 : Blo 1198416 1199463 := bstep (se 1 (by rfl) ⟨899597, by rfl⟩ : syracuseStep 1199463 = 1799195) B1799195
theorem B2698703 : Blo 1198416 2698703 := bstep (se 1 (by rfl) ⟨2024027, by rfl⟩ : syracuseStep 2698703 = 4048055) B4048055
theorem B1215983 : Blo 1198416 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B38915599 : Blo 1198416 38915599 := bstep (se 1 (by rfl) ⟨29186699, by rfl⟩ : syracuseStep 38915599 = 58373399) B58373399
theorem B6074027 : Blo 1198416 6074027 := bstep (se 1 (by rfl) ⟨4555520, by rfl⟩ : syracuseStep 6074027 = 9111041) B9111041
theorem B8884079 : Blo 1198416 8884079 := bstep (se 1 (by rfl) ⟨6663059, by rfl⟩ : syracuseStep 8884079 = 13326119) B13326119
theorem B1200031 : Blo 1198416 1200031 := bstep (se 1 (by rfl) ⟨900023, by rfl⟩ : syracuseStep 1200031 = 1800047) B1800047
theorem B1798055 : Blo 1198416 1798055 := bstep (se 1 (by rfl) ⟨1348541, by rfl⟩ : syracuseStep 1798055 = 2697083) B2697083
theorem B6074513 : Blo 1198416 6074513 := bstep (se 2 (by rfl) ⟨2277942, by rfl⟩ : syracuseStep 6074513 = 4555885) B4555885
theorem B8646875 : Blo 1198416 8646875 := bstep (se 1 (by rfl) ⟨6485156, by rfl⟩ : syracuseStep 8646875 = 12970313) B12970313
theorem B1200411 : Blo 1198416 1200411 := bstep (se 1 (by rfl) ⟨900308, by rfl⟩ : syracuseStep 1200411 = 1800617) B1800617
theorem B2699603 : Blo 1198416 2699603 := bstep (se 1 (by rfl) ⟨2024702, by rfl⟩ : syracuseStep 2699603 = 4049405) B4049405
theorem B1798811 : Blo 1198416 1798811 := bstep (se 1 (by rfl) ⟨1349108, by rfl⟩ : syracuseStep 1798811 = 2698217) B2698217
theorem B1921823 : Blo 1198416 1921823 := bstep (se 1 (by rfl) ⟨1441367, by rfl⟩ : syracuseStep 1921823 = 2882735) B2882735
theorem B3036001 : Blo 1198416 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B1799081 : Blo 1198416 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B6075323 : Blo 1198416 6075323 := bstep (se 1 (by rfl) ⟨4556492, by rfl⟩ : syracuseStep 6075323 = 9112985) B9112985
theorem B23065559 : Blo 1198416 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B7681189 : Blo 1198416 7681189 := bstep (se 4 (by rfl) ⟨720111, by rfl⟩ : syracuseStep 7681189 = 1440223) B1440223
theorem B1799465 : Blo 1198416 1799465 := bstep (se 2 (by rfl) ⟨674799, by rfl⟩ : syracuseStep 1799465 = 1349599) B1349599
theorem B1349023 : Blo 1198416 1349023 := bstep (se 1 (by rfl) ⟨1011767, by rfl⟩ : syracuseStep 1349023 = 2023535) B2023535
theorem B2700719 : Blo 1198416 2700719 := bstep (se 1 (by rfl) ⟨2025539, by rfl⟩ : syracuseStep 2700719 = 4051079) B4051079
theorem B2700863 : Blo 1198416 2700863 := bstep (se 1 (by rfl) ⟨2025647, by rfl⟩ : syracuseStep 2700863 = 4051295) B4051295
theorem B13654169 : Blo 1198416 13654169 := bstep (se 2 (by rfl) ⟨5120313, by rfl⟩ : syracuseStep 13654169 = 10240627) B10240627
theorem B4323611 : Blo 1198416 4323611 := bstep (se 1 (by rfl) ⟨3242708, by rfl⟩ : syracuseStep 4323611 = 6485417) B6485417
theorem B1440127 : Blo 1198416 1440127 := bstep (se 1 (by rfl) ⟨1080095, by rfl⟩ : syracuseStep 1440127 = 2160191) B2160191
theorem B7297627 : Blo 1198416 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B2562815 : Blo 1198416 2562815 := bstep (se 1 (by rfl) ⟨1922111, by rfl⟩ : syracuseStep 2562815 = 3844223) B3844223
theorem B20479067 : Blo 1198416 20479067 := bstep (se 1 (by rfl) ⟨15359300, by rfl⟩ : syracuseStep 20479067 = 30718601) B30718601
theorem B8756383 : Blo 1198416 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B5127407 : Blo 1198416 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B6069815 : Blo 1198416 6069815 := bstep (se 1 (by rfl) ⟨4552361, by rfl⟩ : syracuseStep 6069815 = 9104723) B9104723
theorem B7683751 : Blo 1198416 7683751 := bstep (se 1 (by rfl) ⟨5762813, by rfl⟩ : syracuseStep 7683751 = 11525627) B11525627
theorem B2277047 : Blo 1198416 2277047 := bstep (se 1 (by rfl) ⟨1707785, by rfl⟩ : syracuseStep 2277047 = 3415571) B3415571
theorem B8765317 : Blo 1198416 8765317 := bstep (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) B1643497
theorem B15377039 : Blo 1198416 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B4048001 : Blo 1198416 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B9102779 : Blo 1198416 9102779 := bstep (se 1 (by rfl) ⟨6827084, by rfl⟩ : syracuseStep 9102779 = 13654169) B13654169
theorem B11675177 : Blo 1198416 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B10241585 : Blo 1198416 10241585 := bstep (se 2 (by rfl) ⟨3840594, by rfl⟩ : syracuseStep 10241585 = 7681189) B7681189
theorem B7292783 : Blo 1198416 7292783 := bstep (se 1 (by rfl) ⟨5469587, by rfl⟩ : syracuseStep 7292783 = 10939175) B10939175
theorem B3418271 : Blo 1198416 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B4049351 : Blo 1198416 4049351 := bstep (se 1 (by rfl) ⟨3037013, by rfl⟩ : syracuseStep 4049351 = 6074027) B6074027
theorem B1518031 : Blo 1198416 1518031 := bstep (se 1 (by rfl) ⟨1138523, by rfl⟩ : syracuseStep 1518031 = 2277047) B2277047
theorem B1198703 : Blo 1198416 1198703 := bstep (se 1 (by rfl) ⟨899027, by rfl⟩ : syracuseStep 1198703 = 1798055) B1798055
theorem B5925563 : Blo 1198416 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B4049675 : Blo 1198416 4049675 := bstep (se 1 (by rfl) ⟨3037256, by rfl⟩ : syracuseStep 4049675 = 6074513) B6074513
theorem B1199207 : Blo 1198416 1199207 := bstep (se 1 (by rfl) ⟨899405, by rfl⟩ : syracuseStep 1199207 = 1798811) B1798811
theorem B1920169 : Blo 1198416 1920169 := bstep (se 2 (by rfl) ⟨720063, by rfl⟩ : syracuseStep 1920169 = 1440127) B1440127
theorem B1281215 : Blo 1198416 1281215 := bstep (se 1 (by rfl) ⟨960911, by rfl⟩ : syracuseStep 1281215 = 1921823) B1921823
theorem B3648727 : Blo 1198416 3648727 := bstep (se 1 (by rfl) ⟨2736545, by rfl⟩ : syracuseStep 3648727 = 5473091) B5473091
theorem B1199387 : Blo 1198416 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B4050215 : Blo 1198416 4050215 := bstep (se 1 (by rfl) ⟨3037661, by rfl⟩ : syracuseStep 4050215 = 6075323) B6075323
theorem B1199643 : Blo 1198416 1199643 := bstep (se 1 (by rfl) ⟨899732, by rfl⟩ : syracuseStep 1199643 = 1799465) B1799465
theorem B1797839 : Blo 1198416 1797839 := bstep (se 1 (by rfl) ⟨1348379, by rfl⟩ : syracuseStep 1797839 = 2696759) B2696759
theorem B1798235 : Blo 1198416 1798235 := bstep (se 1 (by rfl) ⟨1348676, by rfl⟩ : syracuseStep 1798235 = 2697353) B2697353
theorem B1798367 : Blo 1198416 1798367 := bstep (se 1 (by rfl) ⟨1348775, by rfl⟩ : syracuseStep 1798367 = 2697551) B2697551
theorem B1798439 : Blo 1198416 1798439 := bstep (se 1 (by rfl) ⟨1348829, by rfl⟩ : syracuseStep 1798439 = 2697659) B2697659
theorem B1708543 : Blo 1198416 1708543 := bstep (se 1 (by rfl) ⟨1281407, by rfl⟩ : syracuseStep 1708543 = 2562815) B2562815
theorem B1798697 : Blo 1198416 1798697 := bstep (se 2 (by rfl) ⟨674511, by rfl⟩ : syracuseStep 1798697 = 1349023) B1349023
theorem B2699963 : Blo 1198416 2699963 := bstep (se 1 (by rfl) ⟨2024972, by rfl⟩ : syracuseStep 2699963 = 4049945) B4049945
theorem B44348107 : Blo 1198416 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B13652711 : Blo 1198416 13652711 := bstep (se 1 (by rfl) ⟨10239533, by rfl⟩ : syracuseStep 13652711 = 20479067) B20479067
theorem B1798943 : Blo 1198416 1798943 := bstep (se 1 (by rfl) ⟨1349207, by rfl⟩ : syracuseStep 1798943 = 2698415) B2698415
theorem B1799015 : Blo 1198416 1799015 := bstep (se 1 (by rfl) ⟨1349261, by rfl⟩ : syracuseStep 1799015 = 2698523) B2698523
theorem B1799039 : Blo 1198416 1799039 := bstep (se 1 (by rfl) ⟨1349279, by rfl⟩ : syracuseStep 1799039 = 2698559) B2698559
theorem B10245001 : Blo 1198416 10245001 := bstep (se 2 (by rfl) ⟨3841875, by rfl⟩ : syracuseStep 10245001 = 7683751) B7683751
theorem B1799135 : Blo 1198416 1799135 := bstep (se 1 (by rfl) ⟨1349351, by rfl⟩ : syracuseStep 1799135 = 2698703) B2698703
theorem B11687089 : Blo 1198416 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B5764583 : Blo 1198416 5764583 := bstep (se 1 (by rfl) ⟨4323437, by rfl⟩ : syracuseStep 5764583 = 8646875) B8646875
theorem B1799735 : Blo 1198416 1799735 := bstep (se 1 (by rfl) ⟨1349801, by rfl⟩ : syracuseStep 1799735 = 2699603) B2699603
theorem B9730169 : Blo 1198416 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B1800479 : Blo 1198416 1800479 := bstep (se 1 (by rfl) ⟨1350359, by rfl⟩ : syracuseStep 1800479 = 2700719) B2700719
theorem B1800575 : Blo 1198416 1800575 := bstep (se 1 (by rfl) ⟨1350431, by rfl⟩ : syracuseStep 1800575 = 2700863) B2700863
theorem B3242621 : Blo 1198416 3242621 := bstep (se 3 (by rfl) ⟨607991, by rfl⟩ : syracuseStep 3242621 = 1215983) B1215983
theorem B2882407 : Blo 1198416 2882407 := bstep (se 1 (by rfl) ⟨2161805, by rfl⟩ : syracuseStep 2882407 = 4323611) B4323611
theorem B2022455 : Blo 1198416 2022455 := bstep (se 1 (by rfl) ⟨1516841, by rfl⟩ : syracuseStep 2022455 = 3033683) B3033683
theorem B8641657 : Blo 1198416 8641657 := bstep (se 2 (by rfl) ⟨3240621, by rfl⟩ : syracuseStep 8641657 = 6481243) B6481243
theorem B3038431 : Blo 1198416 3038431 := bstep (se 1 (by rfl) ⟨2278823, by rfl⟩ : syracuseStep 3038431 = 4557647) B4557647
theorem B51887465 : Blo 1198416 51887465 := bstep (se 2 (by rfl) ⟨19457799, by rfl⟩ : syracuseStep 51887465 = 38915599) B38915599
theorem B4046543 : Blo 1198416 4046543 := bstep (se 1 (by rfl) ⟨3034907, by rfl⟩ : syracuseStep 4046543 = 6069815) B6069815
theorem B5922719 : Blo 1198416 5922719 := bstep (se 1 (by rfl) ⟨4442039, by rfl⟩ : syracuseStep 5922719 = 8884079) B8884079
theorem B14786549 : Blo 1198416 14786549 := bstep (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) B1386239
theorem B9101807 : Blo 1198416 9101807 := bstep (se 1 (by rfl) ⟨6826355, by rfl⟩ : syracuseStep 9101807 = 13652711) B13652711
theorem B3416573 : Blo 1198416 3416573 := bstep (se 3 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 3416573 = 1281215) B1281215
theorem B2024041 : Blo 1198416 2024041 := bstep (se 2 (by rfl) ⟨759015, by rfl⟩ : syracuseStep 2024041 = 1518031) B1518031
theorem B2278057 : Blo 1198416 2278057 := bstep (se 2 (by rfl) ⟨854271, by rfl⟩ : syracuseStep 2278057 = 1708543) B1708543
theorem B10240901 : Blo 1198416 10240901 := bstep (se 4 (by rfl) ⟨960084, by rfl⟩ : syracuseStep 10240901 = 1920169) B1920169
theorem B59130809 : Blo 1198416 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B3843055 : Blo 1198416 3843055 := bstep (se 1 (by rfl) ⟨2882291, by rfl⟩ : syracuseStep 3843055 = 5764583) B5764583
theorem B7783451 : Blo 1198416 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B3843209 : Blo 1198416 3843209 := bstep (se 2 (by rfl) ⟨1441203, by rfl⟩ : syracuseStep 3843209 = 2882407) B2882407
theorem B2278847 : Blo 1198416 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B15582785 : Blo 1198416 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B3950375 : Blo 1198416 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B1198559 : Blo 1198416 1198559 := bstep (se 1 (by rfl) ⟨898919, by rfl⟩ : syracuseStep 1198559 = 1797839) B1797839
theorem B2697695 : Blo 1198416 2697695 := bstep (se 1 (by rfl) ⟨2023271, by rfl⟩ : syracuseStep 2697695 = 4046543) B4046543
theorem B9857699 : Blo 1198416 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B1198823 : Blo 1198416 1198823 := bstep (se 1 (by rfl) ⟨899117, by rfl⟩ : syracuseStep 1198823 = 1798235) B1798235
theorem B1198911 : Blo 1198416 1198911 := bstep (se 1 (by rfl) ⟨899183, by rfl⟩ : syracuseStep 1198911 = 1798367) B1798367
theorem B1198959 : Blo 1198416 1198959 := bstep (se 1 (by rfl) ⟨899219, by rfl⟩ : syracuseStep 1198959 = 1798439) B1798439
theorem B1199131 : Blo 1198416 1199131 := bstep (se 1 (by rfl) ⟨899348, by rfl⟩ : syracuseStep 1199131 = 1798697) B1798697
theorem B10251359 : Blo 1198416 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B1199295 : Blo 1198416 1199295 := bstep (se 1 (by rfl) ⟨899471, by rfl⟩ : syracuseStep 1199295 = 1798943) B1798943
theorem B1199343 : Blo 1198416 1199343 := bstep (se 1 (by rfl) ⟨899507, by rfl⟩ : syracuseStep 1199343 = 1799015) B1799015
theorem B1199359 : Blo 1198416 1199359 := bstep (se 1 (by rfl) ⟨899519, by rfl⟩ : syracuseStep 1199359 = 1799039) B1799039
theorem B1199423 : Blo 1198416 1199423 := bstep (se 1 (by rfl) ⟨899567, by rfl⟩ : syracuseStep 1199423 = 1799135) B1799135
theorem B2698667 : Blo 1198416 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B6827723 : Blo 1198416 6827723 := bstep (se 1 (by rfl) ⟨5120792, by rfl⟩ : syracuseStep 6827723 = 10241585) B10241585
theorem B1199823 : Blo 1198416 1199823 := bstep (se 1 (by rfl) ⟨899867, by rfl⟩ : syracuseStep 1199823 = 1799735) B1799735
theorem B13660001 : Blo 1198416 13660001 := bstep (se 2 (by rfl) ⟨5122500, by rfl⟩ : syracuseStep 13660001 = 10245001) B10245001
theorem B4861855 : Blo 1198416 4861855 := bstep (se 1 (by rfl) ⟨3646391, by rfl⟩ : syracuseStep 4861855 = 7292783) B7292783
theorem B11522209 : Blo 1198416 11522209 := bstep (se 2 (by rfl) ⟨4320828, by rfl⟩ : syracuseStep 11522209 = 8641657) B8641657
theorem B1200319 : Blo 1198416 1200319 := bstep (se 1 (by rfl) ⟨900239, by rfl⟩ : syracuseStep 1200319 = 1800479) B1800479
theorem B1200383 : Blo 1198416 1200383 := bstep (se 1 (by rfl) ⟨900287, by rfl⟩ : syracuseStep 1200383 = 1800575) B1800575
theorem B4051241 : Blo 1198416 4051241 := bstep (se 2 (by rfl) ⟨1519215, by rfl⟩ : syracuseStep 4051241 = 3038431) B3038431
theorem B2699567 : Blo 1198416 2699567 := bstep (se 1 (by rfl) ⟨2024675, by rfl⟩ : syracuseStep 2699567 = 4049351) B4049351
theorem B2699783 : Blo 1198416 2699783 := bstep (se 1 (by rfl) ⟨2024837, by rfl⟩ : syracuseStep 2699783 = 4049675) B4049675
theorem B1348303 : Blo 1198416 1348303 := bstep (se 1 (by rfl) ⟨1011227, by rfl⟩ : syracuseStep 1348303 = 2022455) B2022455
theorem B2700143 : Blo 1198416 2700143 := bstep (se 1 (by rfl) ⟨2025107, by rfl⟩ : syracuseStep 2700143 = 4050215) B4050215
theorem B34591643 : Blo 1198416 34591643 := bstep (se 1 (by rfl) ⟨25943732, by rfl⟩ : syracuseStep 34591643 = 51887465) B51887465
theorem B1799975 : Blo 1198416 1799975 := bstep (se 1 (by rfl) ⟨1349981, by rfl⟩ : syracuseStep 1799975 = 2699963) B2699963
theorem B6068519 : Blo 1198416 6068519 := bstep (se 1 (by rfl) ⟨4551389, by rfl⟩ : syracuseStep 6068519 = 9102779) B9102779
theorem B6486779 : Blo 1198416 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B4864969 : Blo 1198416 4864969 := bstep (se 2 (by rfl) ⟨1824363, by rfl⟩ : syracuseStep 4864969 = 3648727) B3648727
theorem B2161747 : Blo 1198416 2161747 := bstep (se 1 (by rfl) ⟨1621310, by rfl⟩ : syracuseStep 2161747 = 3242621) B3242621
theorem B3948479 : Blo 1198416 3948479 := bstep (se 1 (by rfl) ⟨2961359, by rfl⟩ : syracuseStep 3948479 = 5922719) B5922719
theorem B2277715 : Blo 1198416 2277715 := bstep (se 1 (by rfl) ⟨1708286, by rfl⟩ : syracuseStep 2277715 = 3416573) B3416573
theorem B23061095 : Blo 1198416 23061095 := bstep (se 1 (by rfl) ⟨17295821, by rfl⟩ : syracuseStep 23061095 = 34591643) B34591643
theorem B39420539 : Blo 1198416 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B166216373 : Blo 1198416 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B6571799 : Blo 1198416 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B6834239 : Blo 1198416 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B6482473 : Blo 1198416 6482473 := bstep (se 2 (by rfl) ⟨2430927, by rfl⟩ : syracuseStep 6482473 = 4861855) B4861855
theorem B2632319 : Blo 1198416 2632319 := bstep (se 1 (by rfl) ⟨1974239, by rfl⟩ : syracuseStep 2632319 = 3948479) B3948479
theorem B15362945 : Blo 1198416 15362945 := bstep (se 2 (by rfl) ⟨5761104, by rfl⟩ : syracuseStep 15362945 = 11522209) B11522209
theorem B11529317 : Blo 1198416 11529317 := bstep (se 4 (by rfl) ⟨1080873, by rfl⟩ : syracuseStep 11529317 = 2161747) B2161747
theorem B6827267 : Blo 1198416 6827267 := bstep (se 1 (by rfl) ⟨5120450, by rfl⟩ : syracuseStep 6827267 = 10240901) B10240901
theorem B5188967 : Blo 1198416 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B2698721 : Blo 1198416 2698721 := bstep (se 2 (by rfl) ⟨1012020, by rfl⟩ : syracuseStep 2698721 = 2024041) B2024041
theorem B1797737 : Blo 1198416 1797737 := bstep (se 2 (by rfl) ⟨674151, by rfl⟩ : syracuseStep 1797737 = 1348303) B1348303
theorem B1519231 : Blo 1198416 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B1199983 : Blo 1198416 1199983 := bstep (se 1 (by rfl) ⟨899987, by rfl⟩ : syracuseStep 1199983 = 1799975) B1799975
theorem B5124073 : Blo 1198416 5124073 := bstep (se 2 (by rfl) ⟨1921527, by rfl⟩ : syracuseStep 5124073 = 3843055) B3843055
theorem B1798463 : Blo 1198416 1798463 := bstep (se 1 (by rfl) ⟨1348847, by rfl⟩ : syracuseStep 1798463 = 2697695) B2697695
theorem B1799111 : Blo 1198416 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B4551815 : Blo 1198416 4551815 := bstep (se 1 (by rfl) ⟨3413861, by rfl⟩ : syracuseStep 4551815 = 6827723) B6827723
theorem B9106667 : Blo 1198416 9106667 := bstep (se 1 (by rfl) ⟨6830000, by rfl⟩ : syracuseStep 9106667 = 13660001) B13660001
theorem B2700827 : Blo 1198416 2700827 := bstep (se 1 (by rfl) ⟨2025620, by rfl⟩ : syracuseStep 2700827 = 4051241) B4051241
theorem B1799711 : Blo 1198416 1799711 := bstep (se 1 (by rfl) ⟨1349783, by rfl⟩ : syracuseStep 1799711 = 2699567) B2699567
theorem B6067871 : Blo 1198416 6067871 := bstep (se 1 (by rfl) ⟨4550903, by rfl⟩ : syracuseStep 6067871 = 9101807) B9101807
theorem B1799855 : Blo 1198416 1799855 := bstep (se 1 (by rfl) ⟨1349891, by rfl⟩ : syracuseStep 1799855 = 2699783) B2699783
theorem B42137333 : Blo 1198416 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B1800095 : Blo 1198416 1800095 := bstep (se 1 (by rfl) ⟨1350071, by rfl⟩ : syracuseStep 1800095 = 2700143) B2700143
theorem B2562139 : Blo 1198416 2562139 := bstep (se 1 (by rfl) ⟨1921604, by rfl⟩ : syracuseStep 2562139 = 3843209) B3843209
theorem B3037409 : Blo 1198416 3037409 := bstep (se 2 (by rfl) ⟨1139028, by rfl⟩ : syracuseStep 3037409 = 2278057) B2278057
theorem B6486625 : Blo 1198416 6486625 := bstep (se 2 (by rfl) ⟨2432484, by rfl⟩ : syracuseStep 6486625 = 4864969) B4864969
theorem B4045679 : Blo 1198416 4045679 := bstep (se 1 (by rfl) ⟨3034259, by rfl⟩ : syracuseStep 4045679 = 6068519) B6068519
theorem B4324519 : Blo 1198416 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B3416185 : Blo 1198416 3416185 := bstep (se 2 (by rfl) ⟨1281069, by rfl⟩ : syracuseStep 3416185 = 2562139) B2562139
theorem B30744845 : Blo 1198416 30744845 := bstep (se 3 (by rfl) ⟨5764658, by rfl⟩ : syracuseStep 30744845 = 11529317) B11529317
theorem B26280359 : Blo 1198416 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B34595333 : Blo 1198416 34595333 := bstep (se 4 (by rfl) ⟨3243312, by rfl⟩ : syracuseStep 34595333 = 6486625) B6486625
theorem B6071111 : Blo 1198416 6071111 := bstep (se 1 (by rfl) ⟨4553333, by rfl⟩ : syracuseStep 6071111 = 9106667) B9106667
theorem B28091555 : Blo 1198416 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B4556159 : Blo 1198416 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B2024939 : Blo 1198416 2024939 := bstep (se 1 (by rfl) ⟨1518704, by rfl⟩ : syracuseStep 2024939 = 3037409) B3037409
theorem B1754879 : Blo 1198416 1754879 := bstep (se 1 (by rfl) ⟨1316159, by rfl⟩ : syracuseStep 1754879 = 2632319) B2632319
theorem B2697119 : Blo 1198416 2697119 := bstep (se 1 (by rfl) ⟨2022839, by rfl⟩ : syracuseStep 2697119 = 4045679) B4045679
theorem B10241963 : Blo 1198416 10241963 := bstep (se 1 (by rfl) ⟨7681472, by rfl⟩ : syracuseStep 10241963 = 15362945) B15362945
theorem B2025641 : Blo 1198416 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B3459311 : Blo 1198416 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B1198491 : Blo 1198416 1198491 := bstep (se 1 (by rfl) ⟨898868, by rfl⟩ : syracuseStep 1198491 = 1797737) B1797737
theorem B1198975 : Blo 1198416 1198975 := bstep (se 1 (by rfl) ⟨899231, by rfl⟩ : syracuseStep 1198975 = 1798463) B1798463
theorem B34573189 : Blo 1198416 34573189 := bstep (se 4 (by rfl) ⟨3241236, by rfl⟩ : syracuseStep 34573189 = 6482473) B6482473
theorem B1199407 : Blo 1198416 1199407 := bstep (se 1 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 1199407 = 1799111) B1799111
theorem B3034543 : Blo 1198416 3034543 := bstep (se 1 (by rfl) ⟨2275907, by rfl⟩ : syracuseStep 3034543 = 4551815) B4551815
theorem B23064101 : Blo 1198416 23064101 := bstep (se 4 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 23064101 = 4324519) B4324519
theorem B1199807 : Blo 1198416 1199807 := bstep (se 1 (by rfl) ⟨899855, by rfl⟩ : syracuseStep 1199807 = 1799711) B1799711
theorem B1199903 : Blo 1198416 1199903 := bstep (se 1 (by rfl) ⟨899927, by rfl⟩ : syracuseStep 1199903 = 1799855) B1799855
theorem B1200063 : Blo 1198416 1200063 := bstep (se 1 (by rfl) ⟨900047, by rfl⟩ : syracuseStep 1200063 = 1800095) B1800095
theorem B4551511 : Blo 1198416 4551511 := bstep (se 1 (by rfl) ⟨3413633, by rfl⟩ : syracuseStep 4551511 = 6827267) B6827267
theorem B1799147 : Blo 1198416 1799147 := bstep (se 1 (by rfl) ⟨1349360, by rfl⟩ : syracuseStep 1799147 = 2698721) B2698721
theorem B15374063 : Blo 1198416 15374063 := bstep (se 1 (by rfl) ⟨11530547, by rfl⟩ : syracuseStep 15374063 = 23061095) B23061095
theorem B3036953 : Blo 1198416 3036953 := bstep (se 2 (by rfl) ⟨1138857, by rfl⟩ : syracuseStep 3036953 = 2277715) B2277715
theorem B110810915 : Blo 1198416 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B1800551 : Blo 1198416 1800551 := bstep (se 1 (by rfl) ⟨1350413, by rfl⟩ : syracuseStep 1800551 = 2700827) B2700827
theorem B4045247 : Blo 1198416 4045247 := bstep (se 1 (by rfl) ⟨3033935, by rfl⟩ : syracuseStep 4045247 = 6067871) B6067871
theorem B4381199 : Blo 1198416 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B6832097 : Blo 1198416 6832097 := bstep (se 2 (by rfl) ⟨2562036, by rfl⟩ : syracuseStep 6832097 = 5124073) B5124073
theorem B4554913 : Blo 1198416 4554913 := bstep (se 2 (by rfl) ⟨1708092, by rfl⟩ : syracuseStep 4554913 = 3416185) B3416185
theorem B20496563 : Blo 1198416 20496563 := bstep (se 1 (by rfl) ⟨15372422, by rfl⟩ : syracuseStep 20496563 = 30744845) B30744845
theorem B4047407 : Blo 1198416 4047407 := bstep (se 1 (by rfl) ⟨3035555, by rfl⟩ : syracuseStep 4047407 = 6071111) B6071111
theorem B18727703 : Blo 1198416 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B10249375 : Blo 1198416 10249375 := bstep (se 1 (by rfl) ⟨7687031, by rfl⟩ : syracuseStep 10249375 = 15374063) B15374063
theorem B46097585 : Blo 1198416 46097585 := bstep (se 2 (by rfl) ⟨17286594, by rfl⟩ : syracuseStep 46097585 = 34573189) B34573189
theorem B2024635 : Blo 1198416 2024635 := bstep (se 1 (by rfl) ⟨1518476, by rfl⟩ : syracuseStep 2024635 = 3036953) B3036953
theorem B2696831 : Blo 1198416 2696831 := bstep (se 1 (by rfl) ⟨2022623, by rfl⟩ : syracuseStep 2696831 = 4045247) B4045247
theorem B4679677 : Blo 1198416 4679677 := bstep (se 3 (by rfl) ⟨877439, by rfl⟩ : syracuseStep 4679677 = 1754879) B1754879
theorem B23063555 : Blo 1198416 23063555 := bstep (se 1 (by rfl) ⟨17297666, by rfl⟩ : syracuseStep 23063555 = 34595333) B34595333
theorem B1199431 : Blo 1198416 1199431 := bstep (se 1 (by rfl) ⟨899573, by rfl⟩ : syracuseStep 1199431 = 1799147) B1799147
theorem B1798079 : Blo 1198416 1798079 := bstep (se 1 (by rfl) ⟨1348559, by rfl⟩ : syracuseStep 1798079 = 2697119) B2697119
theorem B6827975 : Blo 1198416 6827975 := bstep (se 1 (by rfl) ⟨5120981, by rfl⟩ : syracuseStep 6827975 = 10241963) B10241963
theorem B2306207 : Blo 1198416 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B1200367 : Blo 1198416 1200367 := bstep (se 1 (by rfl) ⟨900275, by rfl⟩ : syracuseStep 1200367 = 1800551) B1800551
theorem B2920799 : Blo 1198416 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B17520239 : Blo 1198416 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B3037439 : Blo 1198416 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B1349959 : Blo 1198416 1349959 := bstep (se 1 (by rfl) ⟨1012469, by rfl⟩ : syracuseStep 1349959 = 2024939) B2024939
theorem B6068681 : Blo 1198416 6068681 := bstep (se 2 (by rfl) ⟨2275755, by rfl⟩ : syracuseStep 6068681 = 4551511) B4551511
theorem B73873943 : Blo 1198416 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B1350427 : Blo 1198416 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B4046057 : Blo 1198416 4046057 := bstep (se 2 (by rfl) ⟨1517271, by rfl⟩ : syracuseStep 4046057 = 3034543) B3034543
theorem B15376067 : Blo 1198416 15376067 := bstep (se 1 (by rfl) ⟨11532050, by rfl⟩ : syracuseStep 15376067 = 23064101) B23064101
theorem B4554731 : Blo 1198416 4554731 := bstep (se 1 (by rfl) ⟨3416048, by rfl⟩ : syracuseStep 4554731 = 6832097) B6832097
theorem B13664375 : Blo 1198416 13664375 := bstep (se 1 (by rfl) ⟨10248281, by rfl⟩ : syracuseStep 13664375 = 20496563) B20496563
theorem B12485135 : Blo 1198416 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B2024959 : Blo 1198416 2024959 := bstep (se 1 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 2024959 = 3037439) B3037439
theorem B13665833 : Blo 1198416 13665833 := bstep (se 2 (by rfl) ⟨5124687, by rfl⟩ : syracuseStep 13665833 = 10249375) B10249375
theorem B2697371 : Blo 1198416 2697371 := bstep (se 1 (by rfl) ⟨2023028, by rfl⟩ : syracuseStep 2697371 = 4046057) B4046057
theorem B10250711 : Blo 1198416 10250711 := bstep (se 1 (by rfl) ⟨7688033, by rfl⟩ : syracuseStep 10250711 = 15376067) B15376067
theorem B1198719 : Blo 1198416 1198719 := bstep (se 1 (by rfl) ⟨899039, by rfl⟩ : syracuseStep 1198719 = 1798079) B1798079
theorem B6073217 : Blo 1198416 6073217 := bstep (se 2 (by rfl) ⟨2277456, by rfl⟩ : syracuseStep 6073217 = 4554913) B4554913
theorem B2698271 : Blo 1198416 2698271 := bstep (se 1 (by rfl) ⟨2023703, by rfl⟩ : syracuseStep 2698271 = 4047407) B4047407
theorem B30731723 : Blo 1198416 30731723 := bstep (se 1 (by rfl) ⟨23048792, by rfl⟩ : syracuseStep 30731723 = 46097585) B46097585
theorem B1797887 : Blo 1198416 1797887 := bstep (se 1 (by rfl) ⟨1348415, by rfl⟩ : syracuseStep 1797887 = 2696831) B2696831
theorem B2699513 : Blo 1198416 2699513 := bstep (se 2 (by rfl) ⟨1012317, by rfl⟩ : syracuseStep 2699513 = 2024635) B2024635
theorem B4551983 : Blo 1198416 4551983 := bstep (se 1 (by rfl) ⟨3413987, by rfl⟩ : syracuseStep 4551983 = 6827975) B6827975
theorem B24958277 : Blo 1198416 24958277 := bstep (se 4 (by rfl) ⟨2339838, by rfl⟩ : syracuseStep 24958277 = 4679677) B4679677
theorem B3036487 : Blo 1198416 3036487 := bstep (se 1 (by rfl) ⟨2277365, by rfl⟩ : syracuseStep 3036487 = 4554731) B4554731
theorem B1537471 : Blo 1198416 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B1799945 : Blo 1198416 1799945 := bstep (se 2 (by rfl) ⟨674979, by rfl⟩ : syracuseStep 1799945 = 1349959) B1349959
theorem B7788797 : Blo 1198416 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B1800569 : Blo 1198416 1800569 := bstep (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) B1350427
theorem B11680159 : Blo 1198416 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B4045787 : Blo 1198416 4045787 := bstep (se 1 (by rfl) ⟨3034340, by rfl⟩ : syracuseStep 4045787 = 6068681) B6068681
theorem B49249295 : Blo 1198416 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B15375703 : Blo 1198416 15375703 := bstep (se 1 (by rfl) ⟨11531777, by rfl⟩ : syracuseStep 15375703 = 23063555) B23063555
theorem B9109583 : Blo 1198416 9109583 := bstep (se 1 (by rfl) ⟨6832187, by rfl⟩ : syracuseStep 9109583 = 13664375) B13664375
theorem B15573545 : Blo 1198416 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B16638851 : Blo 1198416 16638851 := bstep (se 1 (by rfl) ⟨12479138, by rfl⟩ : syracuseStep 16638851 = 24958277) B24958277
theorem B9110555 : Blo 1198416 9110555 := bstep (se 1 (by rfl) ⟨6832916, by rfl⟩ : syracuseStep 9110555 = 13665833) B13665833
theorem B33293693 : Blo 1198416 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B6833807 : Blo 1198416 6833807 := bstep (se 1 (by rfl) ⟨5125355, by rfl⟩ : syracuseStep 6833807 = 10250711) B10250711
theorem B4048649 : Blo 1198416 4048649 := bstep (se 2 (by rfl) ⟨1518243, by rfl⟩ : syracuseStep 4048649 = 3036487) B3036487
theorem B2049961 : Blo 1198416 2049961 := bstep (se 2 (by rfl) ⟨768735, by rfl⟩ : syracuseStep 2049961 = 1537471) B1537471
theorem B4048811 : Blo 1198416 4048811 := bstep (se 1 (by rfl) ⟨3036608, by rfl⟩ : syracuseStep 4048811 = 6073217) B6073217
theorem B2697191 : Blo 1198416 2697191 := bstep (se 1 (by rfl) ⟨2022893, by rfl⟩ : syracuseStep 2697191 = 4045787) B4045787
theorem B1198591 : Blo 1198416 1198591 := bstep (se 1 (by rfl) ⟨898943, by rfl⟩ : syracuseStep 1198591 = 1797887) B1797887
theorem B3034655 : Blo 1198416 3034655 := bstep (se 1 (by rfl) ⟨2275991, by rfl⟩ : syracuseStep 3034655 = 4551983) B4551983
theorem B1199963 : Blo 1198416 1199963 := bstep (se 1 (by rfl) ⟨899972, by rfl⟩ : syracuseStep 1199963 = 1799945) B1799945
theorem B1798247 : Blo 1198416 1798247 := bstep (se 1 (by rfl) ⟨1348685, by rfl⟩ : syracuseStep 1798247 = 2697371) B2697371
theorem B1200379 : Blo 1198416 1200379 := bstep (se 1 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 1200379 = 1800569) B1800569
theorem B20500937 : Blo 1198416 20500937 := bstep (se 2 (by rfl) ⟨7687851, by rfl⟩ : syracuseStep 20500937 = 15375703) B15375703
theorem B2699945 : Blo 1198416 2699945 := bstep (se 2 (by rfl) ⟨1012479, by rfl⟩ : syracuseStep 2699945 = 2024959) B2024959
theorem B1798847 : Blo 1198416 1798847 := bstep (se 1 (by rfl) ⟨1349135, by rfl⟩ : syracuseStep 1798847 = 2698271) B2698271
theorem B1799675 : Blo 1198416 1799675 := bstep (se 1 (by rfl) ⟨1349756, by rfl⟩ : syracuseStep 1799675 = 2699513) B2699513
theorem B5192531 : Blo 1198416 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B32832863 : Blo 1198416 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B20487815 : Blo 1198416 20487815 := bstep (se 1 (by rfl) ⟨15365861, by rfl⟩ : syracuseStep 20487815 = 30731723) B30731723
theorem B11092567 : Blo 1198416 11092567 := bstep (se 1 (by rfl) ⟨8319425, by rfl⟩ : syracuseStep 11092567 = 16638851) B16638851
theorem B4555871 : Blo 1198416 4555871 := bstep (se 1 (by rfl) ⟨3416903, by rfl⟩ : syracuseStep 4555871 = 6833807) B6833807
theorem B13658543 : Blo 1198416 13658543 := bstep (se 1 (by rfl) ⟨10243907, by rfl⟩ : syracuseStep 13658543 = 20487815) B20487815
theorem B6073055 : Blo 1198416 6073055 := bstep (se 1 (by rfl) ⟨4554791, by rfl⟩ : syracuseStep 6073055 = 9109583) B9109583
theorem B1198831 : Blo 1198416 1198831 := bstep (se 1 (by rfl) ⟨899123, by rfl⟩ : syracuseStep 1198831 = 1798247) B1798247
theorem B13667291 : Blo 1198416 13667291 := bstep (se 1 (by rfl) ⟨10250468, by rfl⟩ : syracuseStep 13667291 = 20500937) B20500937
theorem B10382363 : Blo 1198416 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B1199231 : Blo 1198416 1199231 := bstep (se 1 (by rfl) ⟨899423, by rfl⟩ : syracuseStep 1199231 = 1798847) B1798847
theorem B6073703 : Blo 1198416 6073703 := bstep (se 1 (by rfl) ⟨4555277, by rfl⟩ : syracuseStep 6073703 = 9110555) B9110555
theorem B22195795 : Blo 1198416 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B1199783 : Blo 1198416 1199783 := bstep (se 1 (by rfl) ⟨899837, by rfl⟩ : syracuseStep 1199783 = 1799675) B1799675
theorem B2699099 : Blo 1198416 2699099 := bstep (se 1 (by rfl) ⟨2024324, by rfl⟩ : syracuseStep 2699099 = 4048649) B4048649
theorem B2699207 : Blo 1198416 2699207 := bstep (se 1 (by rfl) ⟨2024405, by rfl⟩ : syracuseStep 2699207 = 4048811) B4048811
theorem B1798127 : Blo 1198416 1798127 := bstep (se 1 (by rfl) ⟨1348595, by rfl⟩ : syracuseStep 1798127 = 2697191) B2697191
theorem B3461687 : Blo 1198416 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B2733281 : Blo 1198416 2733281 := bstep (se 2 (by rfl) ⟨1024980, by rfl⟩ : syracuseStep 2733281 = 2049961) B2049961
theorem B1799963 : Blo 1198416 1799963 := bstep (se 1 (by rfl) ⟨1349972, by rfl⟩ : syracuseStep 1799963 = 2699945) B2699945
theorem B21888575 : Blo 1198416 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B2023103 : Blo 1198416 2023103 := bstep (se 1 (by rfl) ⟨1517327, by rfl⟩ : syracuseStep 2023103 = 3034655) B3034655
theorem B4048703 : Blo 1198416 4048703 := bstep (se 1 (by rfl) ⟨3036527, by rfl⟩ : syracuseStep 4048703 = 6073055) B6073055
theorem B9111527 : Blo 1198416 9111527 := bstep (se 1 (by rfl) ⟨6833645, by rfl⟩ : syracuseStep 9111527 = 13667291) B13667291
theorem B4049135 : Blo 1198416 4049135 := bstep (se 1 (by rfl) ⟨3036851, by rfl⟩ : syracuseStep 4049135 = 6073703) B6073703
theorem B14592383 : Blo 1198416 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B1198751 : Blo 1198416 1198751 := bstep (se 1 (by rfl) ⟨899063, by rfl⟩ : syracuseStep 1198751 = 1798127) B1798127
theorem B14790089 : Blo 1198416 14790089 := bstep (se 2 (by rfl) ⟨5546283, by rfl⟩ : syracuseStep 14790089 = 11092567) B11092567
theorem B1822187 : Blo 1198416 1822187 := bstep (se 1 (by rfl) ⟨1366640, by rfl⟩ : syracuseStep 1822187 = 2733281) B2733281
theorem B1199975 : Blo 1198416 1199975 := bstep (se 1 (by rfl) ⟨899981, by rfl⟩ : syracuseStep 1199975 = 1799963) B1799963
theorem B9105695 : Blo 1198416 9105695 := bstep (se 1 (by rfl) ⟨6829271, by rfl⟩ : syracuseStep 9105695 = 13658543) B13658543
theorem B29594393 : Blo 1198416 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B1348735 : Blo 1198416 1348735 := bstep (se 1 (by rfl) ⟨1011551, by rfl⟩ : syracuseStep 1348735 = 2023103) B2023103
theorem B1799399 : Blo 1198416 1799399 := bstep (se 1 (by rfl) ⟨1349549, by rfl⟩ : syracuseStep 1799399 = 2699099) B2699099
theorem B1799471 : Blo 1198416 1799471 := bstep (se 1 (by rfl) ⟨1349603, by rfl⟩ : syracuseStep 1799471 = 2699207) B2699207
theorem B2307791 : Blo 1198416 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B3037247 : Blo 1198416 3037247 := bstep (se 1 (by rfl) ⟨2277935, by rfl⟩ : syracuseStep 3037247 = 4555871) B4555871
theorem B6921575 : Blo 1198416 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B6070463 : Blo 1198416 6070463 := bstep (se 1 (by rfl) ⟨4552847, by rfl⟩ : syracuseStep 6070463 = 9105695) B9105695
theorem B4859165 : Blo 1198416 4859165 := bstep (se 3 (by rfl) ⟨911093, by rfl⟩ : syracuseStep 4859165 = 1822187) B1822187
theorem B2024831 : Blo 1198416 2024831 := bstep (se 1 (by rfl) ⟨1518623, by rfl⟩ : syracuseStep 2024831 = 3037247) B3037247
theorem B4614383 : Blo 1198416 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B19729595 : Blo 1198416 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B1199599 : Blo 1198416 1199599 := bstep (se 1 (by rfl) ⟨899699, by rfl⟩ : syracuseStep 1199599 = 1799399) B1799399
theorem B1199647 : Blo 1198416 1199647 := bstep (se 1 (by rfl) ⟨899735, by rfl⟩ : syracuseStep 1199647 = 1799471) B1799471
theorem B2699135 : Blo 1198416 2699135 := bstep (se 1 (by rfl) ⟨2024351, by rfl⟩ : syracuseStep 2699135 = 4048703) B4048703
theorem B6074351 : Blo 1198416 6074351 := bstep (se 1 (by rfl) ⟨4555763, by rfl⟩ : syracuseStep 6074351 = 9111527) B9111527
theorem B2699423 : Blo 1198416 2699423 := bstep (se 1 (by rfl) ⟨2024567, by rfl⟩ : syracuseStep 2699423 = 4049135) B4049135
theorem B1798313 : Blo 1198416 1798313 := bstep (se 2 (by rfl) ⟨674367, by rfl⟩ : syracuseStep 1798313 = 1348735) B1348735
theorem B9728255 : Blo 1198416 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B9860059 : Blo 1198416 9860059 := bstep (se 1 (by rfl) ⟨7395044, by rfl⟩ : syracuseStep 9860059 = 14790089) B14790089
theorem B1538527 : Blo 1198416 1538527 := bstep (se 1 (by rfl) ⟨1153895, by rfl⟩ : syracuseStep 1538527 = 2307791) B2307791
theorem B4046975 : Blo 1198416 4046975 := bstep (se 1 (by rfl) ⟨3035231, by rfl⟩ : syracuseStep 4046975 = 6070463) B6070463
theorem B4049567 : Blo 1198416 4049567 := bstep (se 1 (by rfl) ⟨3037175, by rfl⟩ : syracuseStep 4049567 = 6074351) B6074351
theorem B1198875 : Blo 1198416 1198875 := bstep (se 1 (by rfl) ⟨899156, by rfl⟩ : syracuseStep 1198875 = 1798313) B1798313
theorem B2051369 : Blo 1198416 2051369 := bstep (se 2 (by rfl) ⟨769263, by rfl⟩ : syracuseStep 2051369 = 1538527) B1538527
theorem B3239443 : Blo 1198416 3239443 := bstep (se 1 (by rfl) ⟨2429582, by rfl⟩ : syracuseStep 3239443 = 4859165) B4859165
theorem B3076255 : Blo 1198416 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B13153063 : Blo 1198416 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B1799423 : Blo 1198416 1799423 := bstep (se 1 (by rfl) ⟨1349567, by rfl⟩ : syracuseStep 1799423 = 2699135) B2699135
theorem B1799615 : Blo 1198416 1799615 := bstep (se 1 (by rfl) ⟨1349711, by rfl⟩ : syracuseStep 1799615 = 2699423) B2699423
theorem B6485503 : Blo 1198416 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B1349887 : Blo 1198416 1349887 := bstep (se 1 (by rfl) ⟨1012415, by rfl⟩ : syracuseStep 1349887 = 2024831) B2024831
theorem B13146745 : Blo 1198416 13146745 := bstep (se 2 (by rfl) ⟨4930029, by rfl⟩ : syracuseStep 13146745 = 9860059) B9860059
theorem B21881269 : Blo 1198416 21881269 := bstep (se 5 (by rfl) ⟨1025684, by rfl⟩ : syracuseStep 21881269 = 2051369) B2051369
theorem B4319257 : Blo 1198416 4319257 := bstep (se 2 (by rfl) ⟨1619721, by rfl⟩ : syracuseStep 4319257 = 3239443) B3239443
theorem B2697983 : Blo 1198416 2697983 := bstep (se 1 (by rfl) ⟨2023487, by rfl⟩ : syracuseStep 2697983 = 4046975) B4046975
theorem B1199615 : Blo 1198416 1199615 := bstep (se 1 (by rfl) ⟨899711, by rfl⟩ : syracuseStep 1199615 = 1799423) B1799423
theorem B1199743 : Blo 1198416 1199743 := bstep (se 1 (by rfl) ⟨899807, by rfl⟩ : syracuseStep 1199743 = 1799615) B1799615
theorem B2699711 : Blo 1198416 2699711 := bstep (se 1 (by rfl) ⟨2024783, by rfl⟩ : syracuseStep 2699711 = 4049567) B4049567
theorem B8647337 : Blo 1198416 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B4101673 : Blo 1198416 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B1799849 : Blo 1198416 1799849 := bstep (se 2 (by rfl) ⟨674943, by rfl⟩ : syracuseStep 1799849 = 1349887) B1349887
theorem B17528993 : Blo 1198416 17528993 := bstep (se 2 (by rfl) ⟨6573372, by rfl⟩ : syracuseStep 17528993 = 13146745) B13146745
theorem B17537417 : Blo 1198416 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B5759009 : Blo 1198416 5759009 := bstep (se 2 (by rfl) ⟨2159628, by rfl⟩ : syracuseStep 5759009 = 4319257) B4319257
theorem B11691611 : Blo 1198416 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B29175025 : Blo 1198416 29175025 := bstep (se 2 (by rfl) ⟨10940634, by rfl⟩ : syracuseStep 29175025 = 21881269) B21881269
theorem B1199899 : Blo 1198416 1199899 := bstep (se 1 (by rfl) ⟨899924, by rfl⟩ : syracuseStep 1199899 = 1799849) B1799849
theorem B11685995 : Blo 1198416 11685995 := bstep (se 1 (by rfl) ⟨8764496, by rfl⟩ : syracuseStep 11685995 = 17528993) B17528993
theorem B1798655 : Blo 1198416 1798655 := bstep (se 1 (by rfl) ⟨1348991, by rfl⟩ : syracuseStep 1798655 = 2697983) B2697983
theorem B5468897 : Blo 1198416 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B1799807 : Blo 1198416 1799807 := bstep (se 1 (by rfl) ⟨1349855, by rfl⟩ : syracuseStep 1799807 = 2699711) B2699711
theorem B5764891 : Blo 1198416 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B7790663 : Blo 1198416 7790663 := bstep (se 1 (by rfl) ⟨5842997, by rfl⟩ : syracuseStep 7790663 = 11685995) B11685995
theorem B3645931 : Blo 1198416 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B7686521 : Blo 1198416 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B1199103 : Blo 1198416 1199103 := bstep (se 1 (by rfl) ⟨899327, by rfl⟩ : syracuseStep 1199103 = 1798655) B1798655
theorem B7794407 : Blo 1198416 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1199871 : Blo 1198416 1199871 := bstep (se 1 (by rfl) ⟨899903, by rfl⟩ : syracuseStep 1199871 = 1799807) B1799807
theorem B38900033 : Blo 1198416 38900033 := bstep (se 2 (by rfl) ⟨14587512, by rfl⟩ : syracuseStep 38900033 = 29175025) B29175025
theorem B3839339 : Blo 1198416 3839339 := bstep (se 1 (by rfl) ⟨2879504, by rfl⟩ : syracuseStep 3839339 = 5759009) B5759009
theorem B5193775 : Blo 1198416 5193775 := bstep (se 1 (by rfl) ⟨3895331, by rfl⟩ : syracuseStep 5193775 = 7790663) B7790663
theorem B5196271 : Blo 1198416 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B4861241 : Blo 1198416 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B5124347 : Blo 1198416 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B25933355 : Blo 1198416 25933355 := bstep (se 1 (by rfl) ⟨19450016, by rfl⟩ : syracuseStep 25933355 = 38900033) B38900033
theorem B10238237 : Blo 1198416 10238237 := bstep (se 3 (by rfl) ⟨1919669, by rfl⟩ : syracuseStep 10238237 = 3839339) B3839339
theorem B3416231 : Blo 1198416 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B6825491 : Blo 1198416 6825491 := bstep (se 1 (by rfl) ⟨5119118, by rfl⟩ : syracuseStep 6825491 = 10238237) B10238237
theorem B6925033 : Blo 1198416 6925033 := bstep (se 2 (by rfl) ⟨2596887, by rfl⟩ : syracuseStep 6925033 = 5193775) B5193775
theorem B17288903 : Blo 1198416 17288903 := bstep (se 1 (by rfl) ⟨12966677, by rfl⟩ : syracuseStep 17288903 = 25933355) B25933355
theorem B3240827 : Blo 1198416 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B6928361 : Blo 1198416 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B2277487 : Blo 1198416 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B4550327 : Blo 1198416 4550327 := bstep (se 1 (by rfl) ⟨3412745, by rfl⟩ : syracuseStep 4550327 = 6825491) B6825491
theorem B36933509 : Blo 1198416 36933509 := bstep (se 4 (by rfl) ⟨3462516, by rfl⟩ : syracuseStep 36933509 = 6925033) B6925033
theorem B2160551 : Blo 1198416 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B4618907 : Blo 1198416 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B11525935 : Blo 1198416 11525935 := bstep (se 1 (by rfl) ⟨8644451, by rfl⟩ : syracuseStep 11525935 = 17288903) B17288903
theorem B5761469 : Blo 1198416 5761469 := bstep (se 3 (by rfl) ⟨1080275, by rfl⟩ : syracuseStep 5761469 = 2160551) B2160551
theorem B3033551 : Blo 1198416 3033551 := bstep (se 1 (by rfl) ⟨2275163, by rfl⟩ : syracuseStep 3033551 = 4550327) B4550327
theorem B98489357 : Blo 1198416 98489357 := bstep (se 3 (by rfl) ⟨18466754, by rfl⟩ : syracuseStep 98489357 = 36933509) B36933509
theorem B3036649 : Blo 1198416 3036649 := bstep (se 2 (by rfl) ⟨1138743, by rfl⟩ : syracuseStep 3036649 = 2277487) B2277487
theorem B3079271 : Blo 1198416 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B15367913 : Blo 1198416 15367913 := bstep (se 2 (by rfl) ⟨5762967, by rfl⟩ : syracuseStep 15367913 = 11525935) B11525935
theorem B65659571 : Blo 1198416 65659571 := bstep (se 1 (by rfl) ⟨49244678, by rfl⟩ : syracuseStep 65659571 = 98489357) B98489357
theorem B4048865 : Blo 1198416 4048865 := bstep (se 2 (by rfl) ⟨1518324, by rfl⟩ : syracuseStep 4048865 = 3036649) B3036649
theorem B15363917 : Blo 1198416 15363917 := bstep (se 3 (by rfl) ⟨2880734, by rfl⟩ : syracuseStep 15363917 = 5761469) B5761469
theorem B2052847 : Blo 1198416 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B10245275 : Blo 1198416 10245275 := bstep (se 1 (by rfl) ⟨7683956, by rfl⟩ : syracuseStep 10245275 = 15367913) B15367913
theorem B2022367 : Blo 1198416 2022367 := bstep (se 1 (by rfl) ⟨1516775, by rfl⟩ : syracuseStep 2022367 = 3033551) B3033551
theorem B2737129 : Blo 1198416 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B2696489 : Blo 1198416 2696489 := bstep (se 2 (by rfl) ⟨1011183, by rfl⟩ : syracuseStep 2696489 = 2022367) B2022367
theorem B10242611 : Blo 1198416 10242611 := bstep (se 1 (by rfl) ⟨7681958, by rfl⟩ : syracuseStep 10242611 = 15363917) B15363917
theorem B43773047 : Blo 1198416 43773047 := bstep (se 1 (by rfl) ⟨32829785, by rfl⟩ : syracuseStep 43773047 = 65659571) B65659571
theorem B2699243 : Blo 1198416 2699243 := bstep (se 1 (by rfl) ⟨2024432, by rfl⟩ : syracuseStep 2699243 = 4048865) B4048865
theorem B6830183 : Blo 1198416 6830183 := bstep (se 1 (by rfl) ⟨5122637, by rfl⟩ : syracuseStep 6830183 = 10245275) B10245275
theorem B29182031 : Blo 1198416 29182031 := bstep (se 1 (by rfl) ⟨21886523, by rfl⟩ : syracuseStep 29182031 = 43773047) B43773047
theorem B1797659 : Blo 1198416 1797659 := bstep (se 1 (by rfl) ⟨1348244, by rfl⟩ : syracuseStep 1797659 = 2696489) B2696489
theorem B3649505 : Blo 1198416 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B6828407 : Blo 1198416 6828407 := bstep (se 1 (by rfl) ⟨5121305, by rfl⟩ : syracuseStep 6828407 = 10242611) B10242611
theorem B1799495 : Blo 1198416 1799495 := bstep (se 1 (by rfl) ⟨1349621, by rfl⟩ : syracuseStep 1799495 = 2699243) B2699243
theorem B4553455 : Blo 1198416 4553455 := bstep (se 1 (by rfl) ⟨3415091, by rfl⟩ : syracuseStep 4553455 = 6830183) B6830183
theorem B6071273 : Blo 1198416 6071273 := bstep (se 2 (by rfl) ⟨2276727, by rfl⟩ : syracuseStep 6071273 = 4553455) B4553455
theorem B1198439 : Blo 1198416 1198439 := bstep (se 1 (by rfl) ⟨898829, by rfl⟩ : syracuseStep 1198439 = 1797659) B1797659
theorem B1199663 : Blo 1198416 1199663 := bstep (se 1 (by rfl) ⟨899747, by rfl⟩ : syracuseStep 1199663 = 1799495) B1799495
theorem B4552271 : Blo 1198416 4552271 := bstep (se 1 (by rfl) ⟨3414203, by rfl⟩ : syracuseStep 4552271 = 6828407) B6828407
theorem B19454687 : Blo 1198416 19454687 := bstep (se 1 (by rfl) ⟨14591015, by rfl⟩ : syracuseStep 19454687 = 29182031) B29182031
theorem B38928053 : Blo 1198416 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B4047515 : Blo 1198416 4047515 := bstep (se 1 (by rfl) ⟨3035636, by rfl⟩ : syracuseStep 4047515 = 6071273) B6071273
theorem B12969791 : Blo 1198416 12969791 := bstep (se 1 (by rfl) ⟨9727343, by rfl⟩ : syracuseStep 12969791 = 19454687) B19454687
theorem B3034847 : Blo 1198416 3034847 := bstep (se 1 (by rfl) ⟨2276135, by rfl⟩ : syracuseStep 3034847 = 4552271) B4552271
theorem B103808141 : Blo 1198416 103808141 := bstep (se 3 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 103808141 = 38928053) B38928053
theorem B2698343 : Blo 1198416 2698343 := bstep (se 1 (by rfl) ⟨2023757, by rfl⟩ : syracuseStep 2698343 = 4047515) B4047515
theorem B8646527 : Blo 1198416 8646527 := bstep (se 1 (by rfl) ⟨6484895, by rfl⟩ : syracuseStep 8646527 = 12969791) B12969791
theorem B69205427 : Blo 1198416 69205427 := bstep (se 1 (by rfl) ⟨51904070, by rfl⟩ : syracuseStep 69205427 = 103808141) B103808141
theorem B2023231 : Blo 1198416 2023231 := bstep (se 1 (by rfl) ⟨1517423, by rfl⟩ : syracuseStep 2023231 = 3034847) B3034847
theorem B2697641 : Blo 1198416 2697641 := bstep (se 2 (by rfl) ⟨1011615, by rfl⟩ : syracuseStep 2697641 = 2023231) B2023231
theorem B1798895 : Blo 1198416 1798895 := bstep (se 1 (by rfl) ⟨1349171, by rfl⟩ : syracuseStep 1798895 = 2698343) B2698343
theorem B23057405 : Blo 1198416 23057405 := bstep (se 3 (by rfl) ⟨4323263, by rfl⟩ : syracuseStep 23057405 = 8646527) B8646527
theorem B46136951 : Blo 1198416 46136951 := bstep (se 1 (by rfl) ⟨34602713, by rfl⟩ : syracuseStep 46136951 = 69205427) B69205427
theorem B1199263 : Blo 1198416 1199263 := bstep (se 1 (by rfl) ⟨899447, by rfl⟩ : syracuseStep 1199263 = 1798895) B1798895
theorem B15371603 : Blo 1198416 15371603 := bstep (se 1 (by rfl) ⟨11528702, by rfl⟩ : syracuseStep 15371603 = 23057405) B23057405
theorem B1798427 : Blo 1198416 1798427 := bstep (se 1 (by rfl) ⟨1348820, by rfl⟩ : syracuseStep 1798427 = 2697641) B2697641
theorem B30757967 : Blo 1198416 30757967 := bstep (se 1 (by rfl) ⟨23068475, by rfl⟩ : syracuseStep 30757967 = 46136951) B46136951
theorem B20505311 : Blo 1198416 20505311 := bstep (se 1 (by rfl) ⟨15378983, by rfl⟩ : syracuseStep 20505311 = 30757967) B30757967
theorem B1198951 : Blo 1198416 1198951 := bstep (se 1 (by rfl) ⟨899213, by rfl⟩ : syracuseStep 1198951 = 1798427) B1798427
theorem B10247735 : Blo 1198416 10247735 := bstep (se 1 (by rfl) ⟨7685801, by rfl⟩ : syracuseStep 10247735 = 15371603) B15371603
theorem B13670207 : Blo 1198416 13670207 := bstep (se 1 (by rfl) ⟨10252655, by rfl⟩ : syracuseStep 13670207 = 20505311) B20505311
theorem B6831823 : Blo 1198416 6831823 := bstep (se 1 (by rfl) ⟨5123867, by rfl⟩ : syracuseStep 6831823 = 10247735) B10247735
theorem B9113471 : Blo 1198416 9113471 := bstep (se 1 (by rfl) ⟨6835103, by rfl⟩ : syracuseStep 9113471 = 13670207) B13670207
theorem B9109097 : Blo 1198416 9109097 := bstep (se 2 (by rfl) ⟨3415911, by rfl⟩ : syracuseStep 9109097 = 6831823) B6831823
theorem B6072731 : Blo 1198416 6072731 := bstep (se 1 (by rfl) ⟨4554548, by rfl⟩ : syracuseStep 6072731 = 9109097) B9109097
theorem B6075647 : Blo 1198416 6075647 := bstep (se 1 (by rfl) ⟨4556735, by rfl⟩ : syracuseStep 6075647 = 9113471) B9113471
theorem B4048487 : Blo 1198416 4048487 := bstep (se 1 (by rfl) ⟨3036365, by rfl⟩ : syracuseStep 4048487 = 6072731) B6072731
theorem B4050431 : Blo 1198416 4050431 := bstep (se 1 (by rfl) ⟨3037823, by rfl⟩ : syracuseStep 4050431 = 6075647) B6075647
theorem B2698991 : Blo 1198416 2698991 := bstep (se 1 (by rfl) ⟨2024243, by rfl⟩ : syracuseStep 2698991 = 4048487) B4048487
theorem B2700287 : Blo 1198416 2700287 := bstep (se 1 (by rfl) ⟨2025215, by rfl⟩ : syracuseStep 2700287 = 4050431) B4050431
theorem B1799327 : Blo 1198416 1799327 := bstep (se 1 (by rfl) ⟨1349495, by rfl⟩ : syracuseStep 1799327 = 2698991) B2698991
theorem B1800191 : Blo 1198416 1800191 := bstep (se 1 (by rfl) ⟨1350143, by rfl⟩ : syracuseStep 1800191 = 2700287) B2700287
theorem B1199551 : Blo 1198416 1199551 := bstep (se 1 (by rfl) ⟨899663, by rfl⟩ : syracuseStep 1199551 = 1799327) B1799327
theorem B1200127 : Blo 1198416 1200127 := bstep (se 1 (by rfl) ⟨900095, by rfl⟩ : syracuseStep 1200127 = 1800191) B1800191

theorem C0 (j : ℕ) (h1 : 299604 ≤ j) (h2 : j ≤ 300103) : Blo 1198416 (4 * j + 3) := by
  interval_cases j
  · exact B1198419
  · exact B1198423
  · exact B1198427
  · exact B1198431
  · exact B1198435
  · exact B1198439
  · exact B1198443
  · exact B1198447
  · exact B1198451
  · exact B1198455
  · exact B1198459
  · exact B1198463
  · exact B1198467
  · exact B1198471
  · exact B1198475
  · exact B1198479
  · exact B1198483
  · exact B1198487
  · exact B1198491
  · exact B1198495
  · exact B1198499
  · exact B1198503
  · exact B1198507
  · exact B1198511
  · exact B1198515
  · exact B1198519
  · exact B1198523
  · exact B1198527
  · exact B1198531
  · exact B1198535
  · exact B1198539
  · exact B1198543
  · exact B1198547
  · exact B1198551
  · exact B1198555
  · exact B1198559
  · exact B1198563
  · exact B1198567
  · exact B1198571
  · exact B1198575
  · exact B1198579
  · exact B1198583
  · exact B1198587
  · exact B1198591
  · exact B1198595
  · exact B1198599
  · exact B1198603
  · exact B1198607
  · exact B1198611
  · exact B1198615
  · exact B1198619
  · exact B1198623
  · exact B1198627
  · exact B1198631
  · exact B1198635
  · exact B1198639
  · exact B1198643
  · exact B1198647
  · exact B1198651
  · exact B1198655
  · exact B1198659
  · exact B1198663
  · exact B1198667
  · exact B1198671
  · exact B1198675
  · exact B1198679
  · exact B1198683
  · exact B1198687
  · exact B1198691
  · exact B1198695
  · exact B1198699
  · exact B1198703
  · exact B1198707
  · exact B1198711
  · exact B1198715
  · exact B1198719
  · exact B1198723
  · exact B1198727
  · exact B1198731
  · exact B1198735
  · exact B1198739
  · exact B1198743
  · exact B1198747
  · exact B1198751
  · exact B1198755
  · exact B1198759
  · exact B1198763
  · exact B1198767
  · exact B1198771
  · exact B1198775
  · exact B1198779
  · exact B1198783
  · exact B1198787
  · exact B1198791
  · exact B1198795
  · exact B1198799
  · exact B1198803
  · exact B1198807
  · exact B1198811
  · exact B1198815
  · exact B1198819
  · exact B1198823
  · exact B1198827
  · exact B1198831
  · exact B1198835
  · exact B1198839
  · exact B1198843
  · exact B1198847
  · exact B1198851
  · exact B1198855
  · exact B1198859
  · exact B1198863
  · exact B1198867
  · exact B1198871
  · exact B1198875
  · exact B1198879
  · exact B1198883
  · exact B1198887
  · exact B1198891
  · exact B1198895
  · exact B1198899
  · exact B1198903
  · exact B1198907
  · exact B1198911
  · exact B1198915
  · exact B1198919
  · exact B1198923
  · exact B1198927
  · exact B1198931
  · exact B1198935
  · exact B1198939
  · exact B1198943
  · exact B1198947
  · exact B1198951
  · exact B1198955
  · exact B1198959
  · exact B1198963
  · exact B1198967
  · exact B1198971
  · exact B1198975
  · exact B1198979
  · exact B1198983
  · exact B1198987
  · exact B1198991
  · exact B1198995
  · exact B1198999
  · exact B1199003
  · exact B1199007
  · exact B1199011
  · exact B1199015
  · exact B1199019
  · exact B1199023
  · exact B1199027
  · exact B1199031
  · exact B1199035
  · exact B1199039
  · exact B1199043
  · exact B1199047
  · exact B1199051
  · exact B1199055
  · exact B1199059
  · exact B1199063
  · exact B1199067
  · exact B1199071
  · exact B1199075
  · exact B1199079
  · exact B1199083
  · exact B1199087
  · exact B1199091
  · exact B1199095
  · exact B1199099
  · exact B1199103
  · exact B1199107
  · exact B1199111
  · exact B1199115
  · exact B1199119
  · exact B1199123
  · exact B1199127
  · exact B1199131
  · exact B1199135
  · exact B1199139
  · exact B1199143
  · exact B1199147
  · exact B1199151
  · exact B1199155
  · exact B1199159
  · exact B1199163
  · exact B1199167
  · exact B1199171
  · exact B1199175
  · exact B1199179
  · exact B1199183
  · exact B1199187
  · exact B1199191
  · exact B1199195
  · exact B1199199
  · exact B1199203
  · exact B1199207
  · exact B1199211
  · exact B1199215
  · exact B1199219
  · exact B1199223
  · exact B1199227
  · exact B1199231
  · exact B1199235
  · exact B1199239
  · exact B1199243
  · exact B1199247
  · exact B1199251
  · exact B1199255
  · exact B1199259
  · exact B1199263
  · exact B1199267
  · exact B1199271
  · exact B1199275
  · exact B1199279
  · exact B1199283
  · exact B1199287
  · exact B1199291
  · exact B1199295
  · exact B1199299
  · exact B1199303
  · exact B1199307
  · exact B1199311
  · exact B1199315
  · exact B1199319
  · exact B1199323
  · exact B1199327
  · exact B1199331
  · exact B1199335
  · exact B1199339
  · exact B1199343
  · exact B1199347
  · exact B1199351
  · exact B1199355
  · exact B1199359
  · exact B1199363
  · exact B1199367
  · exact B1199371
  · exact B1199375
  · exact B1199379
  · exact B1199383
  · exact B1199387
  · exact B1199391
  · exact B1199395
  · exact B1199399
  · exact B1199403
  · exact B1199407
  · exact B1199411
  · exact B1199415
  · exact B1199419
  · exact B1199423
  · exact B1199427
  · exact B1199431
  · exact B1199435
  · exact B1199439
  · exact B1199443
  · exact B1199447
  · exact B1199451
  · exact B1199455
  · exact B1199459
  · exact B1199463
  · exact B1199467
  · exact B1199471
  · exact B1199475
  · exact B1199479
  · exact B1199483
  · exact B1199487
  · exact B1199491
  · exact B1199495
  · exact B1199499
  · exact B1199503
  · exact B1199507
  · exact B1199511
  · exact B1199515
  · exact B1199519
  · exact B1199523
  · exact B1199527
  · exact B1199531
  · exact B1199535
  · exact B1199539
  · exact B1199543
  · exact B1199547
  · exact B1199551
  · exact B1199555
  · exact B1199559
  · exact B1199563
  · exact B1199567
  · exact B1199571
  · exact B1199575
  · exact B1199579
  · exact B1199583
  · exact B1199587
  · exact B1199591
  · exact B1199595
  · exact B1199599
  · exact B1199603
  · exact B1199607
  · exact B1199611
  · exact B1199615
  · exact B1199619
  · exact B1199623
  · exact B1199627
  · exact B1199631
  · exact B1199635
  · exact B1199639
  · exact B1199643
  · exact B1199647
  · exact B1199651
  · exact B1199655
  · exact B1199659
  · exact B1199663
  · exact B1199667
  · exact B1199671
  · exact B1199675
  · exact B1199679
  · exact B1199683
  · exact B1199687
  · exact B1199691
  · exact B1199695
  · exact B1199699
  · exact B1199703
  · exact B1199707
  · exact B1199711
  · exact B1199715
  · exact B1199719
  · exact B1199723
  · exact B1199727
  · exact B1199731
  · exact B1199735
  · exact B1199739
  · exact B1199743
  · exact B1199747
  · exact B1199751
  · exact B1199755
  · exact B1199759
  · exact B1199763
  · exact B1199767
  · exact B1199771
  · exact B1199775
  · exact B1199779
  · exact B1199783
  · exact B1199787
  · exact B1199791
  · exact B1199795
  · exact B1199799
  · exact B1199803
  · exact B1199807
  · exact B1199811
  · exact B1199815
  · exact B1199819
  · exact B1199823
  · exact B1199827
  · exact B1199831
  · exact B1199835
  · exact B1199839
  · exact B1199843
  · exact B1199847
  · exact B1199851
  · exact B1199855
  · exact B1199859
  · exact B1199863
  · exact B1199867
  · exact B1199871
  · exact B1199875
  · exact B1199879
  · exact B1199883
  · exact B1199887
  · exact B1199891
  · exact B1199895
  · exact B1199899
  · exact B1199903
  · exact B1199907
  · exact B1199911
  · exact B1199915
  · exact B1199919
  · exact B1199923
  · exact B1199927
  · exact B1199931
  · exact B1199935
  · exact B1199939
  · exact B1199943
  · exact B1199947
  · exact B1199951
  · exact B1199955
  · exact B1199959
  · exact B1199963
  · exact B1199967
  · exact B1199971
  · exact B1199975
  · exact B1199979
  · exact B1199983
  · exact B1199987
  · exact B1199991
  · exact B1199995
  · exact B1199999
  · exact B1200003
  · exact B1200007
  · exact B1200011
  · exact B1200015
  · exact B1200019
  · exact B1200023
  · exact B1200027
  · exact B1200031
  · exact B1200035
  · exact B1200039
  · exact B1200043
  · exact B1200047
  · exact B1200051
  · exact B1200055
  · exact B1200059
  · exact B1200063
  · exact B1200067
  · exact B1200071
  · exact B1200075
  · exact B1200079
  · exact B1200083
  · exact B1200087
  · exact B1200091
  · exact B1200095
  · exact B1200099
  · exact B1200103
  · exact B1200107
  · exact B1200111
  · exact B1200115
  · exact B1200119
  · exact B1200123
  · exact B1200127
  · exact B1200131
  · exact B1200135
  · exact B1200139
  · exact B1200143
  · exact B1200147
  · exact B1200151
  · exact B1200155
  · exact B1200159
  · exact B1200163
  · exact B1200167
  · exact B1200171
  · exact B1200175
  · exact B1200179
  · exact B1200183
  · exact B1200187
  · exact B1200191
  · exact B1200195
  · exact B1200199
  · exact B1200203
  · exact B1200207
  · exact B1200211
  · exact B1200215
  · exact B1200219
  · exact B1200223
  · exact B1200227
  · exact B1200231
  · exact B1200235
  · exact B1200239
  · exact B1200243
  · exact B1200247
  · exact B1200251
  · exact B1200255
  · exact B1200259
  · exact B1200263
  · exact B1200267
  · exact B1200271
  · exact B1200275
  · exact B1200279
  · exact B1200283
  · exact B1200287
  · exact B1200291
  · exact B1200295
  · exact B1200299
  · exact B1200303
  · exact B1200307
  · exact B1200311
  · exact B1200315
  · exact B1200319
  · exact B1200323
  · exact B1200327
  · exact B1200331
  · exact B1200335
  · exact B1200339
  · exact B1200343
  · exact B1200347
  · exact B1200351
  · exact B1200355
  · exact B1200359
  · exact B1200363
  · exact B1200367
  · exact B1200371
  · exact B1200375
  · exact B1200379
  · exact B1200383
  · exact B1200387
  · exact B1200391
  · exact B1200395
  · exact B1200399
  · exact B1200403
  · exact B1200407
  · exact B1200411
  · exact B1200415

theorem solution (m : ℕ) (hlo : 1198416 ≤ m) (hhi : m ≤ 1200416) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 299604 ≤ j := by omega
    have hj2 : j ≤ 300103 := by omega
    have hb : Blo 1198416 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
