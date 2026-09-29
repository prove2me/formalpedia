-- Prove2me | solution 1 for syracuse_descends_range_610295_614295
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:30.937085+00:00
-- url     : https://prove2.me/submissions/ea8513f9-3f3f-41a2-aa46-0a24063234ee

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


theorem B1376261 : Blo 610295 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B917525 : Blo 610295 917525 := bbase (se 6 (by rfl) ⟨21504, by rfl⟩ : syracuseStep 917525 = 43009) (by norm_num)
theorem B688153 : Blo 610295 688153 := bbase (se 2 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 688153 = 516115) (by norm_num)
theorem B917549 : Blo 610295 917549 := bbase (se 3 (by rfl) ⟨172040, by rfl⟩ : syracuseStep 917549 = 344081) (by norm_num)
theorem B688189 : Blo 610295 688189 := bbase (se 3 (by rfl) ⟨129035, by rfl⟩ : syracuseStep 688189 = 258071) (by norm_num)
theorem B917573 : Blo 610295 917573 := bbase (se 4 (by rfl) ⟨86022, by rfl⟩ : syracuseStep 917573 = 172045) (by norm_num)
theorem B1376333 : Blo 610295 1376333 := bbase (se 3 (by rfl) ⟨258062, by rfl⟩ : syracuseStep 1376333 = 516125) (by norm_num)
theorem B983125 : Blo 610295 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B917597 : Blo 610295 917597 := bbase (se 3 (by rfl) ⟨172049, by rfl⟩ : syracuseStep 917597 = 344099) (by norm_num)
theorem B688225 : Blo 610295 688225 := bbase (se 2 (by rfl) ⟨258084, by rfl⟩ : syracuseStep 688225 = 516169) (by norm_num)
theorem B917621 : Blo 610295 917621 := bbase (se 5 (by rfl) ⟨43013, by rfl⟩ : syracuseStep 917621 = 86027) (by norm_num)
theorem B688261 : Blo 610295 688261 := bbase (se 4 (by rfl) ⟨64524, by rfl⟩ : syracuseStep 688261 = 129049) (by norm_num)
theorem B917645 : Blo 610295 917645 := bbase (se 3 (by rfl) ⟨172058, by rfl⟩ : syracuseStep 917645 = 344117) (by norm_num)
theorem B1376405 : Blo 610295 1376405 := bbase (se 6 (by rfl) ⟨32259, by rfl⟩ : syracuseStep 1376405 = 64519) (by norm_num)
theorem B917669 : Blo 610295 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B688297 : Blo 610295 688297 := bbase (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) (by norm_num)
theorem B1179821 : Blo 610295 1179821 := bbase (se 3 (by rfl) ⟨221216, by rfl⟩ : syracuseStep 1179821 = 442433) (by norm_num)
theorem B917693 : Blo 610295 917693 := bbase (se 3 (by rfl) ⟨172067, by rfl⟩ : syracuseStep 917693 = 344135) (by norm_num)
theorem B2064581 : Blo 610295 2064581 := bbase (se 4 (by rfl) ⟨193554, by rfl⟩ : syracuseStep 2064581 = 387109) (by norm_num)
theorem B1474757 : Blo 610295 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B688333 : Blo 610295 688333 := bbase (se 3 (by rfl) ⟨129062, by rfl⟩ : syracuseStep 688333 = 258125) (by norm_num)
theorem B917717 : Blo 610295 917717 := bbase (se 7 (by rfl) ⟨10754, by rfl⟩ : syracuseStep 917717 = 21509) (by norm_num)
theorem B1376477 : Blo 610295 1376477 := bbase (se 3 (by rfl) ⟨258089, by rfl⟩ : syracuseStep 1376477 = 516179) (by norm_num)
theorem B917741 : Blo 610295 917741 := bbase (se 3 (by rfl) ⟨172076, by rfl⟩ : syracuseStep 917741 = 344153) (by norm_num)
theorem B688369 : Blo 610295 688369 := bbase (se 2 (by rfl) ⟨258138, by rfl⟩ : syracuseStep 688369 = 516277) (by norm_num)
theorem B917765 : Blo 610295 917765 := bbase (se 4 (by rfl) ⟨86040, by rfl⟩ : syracuseStep 917765 = 172081) (by norm_num)
theorem B688405 : Blo 610295 688405 := bbase (se 6 (by rfl) ⟨16134, by rfl⟩ : syracuseStep 688405 = 32269) (by norm_num)
theorem B917789 : Blo 610295 917789 := bbase (se 3 (by rfl) ⟨172085, by rfl⟩ : syracuseStep 917789 = 344171) (by norm_num)
theorem B1311005 : Blo 610295 1311005 := bbase (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) (by norm_num)
theorem B1376549 : Blo 610295 1376549 := bbase (se 4 (by rfl) ⟨129051, by rfl⟩ : syracuseStep 1376549 = 258103) (by norm_num)
theorem B917813 : Blo 610295 917813 := bbase (se 5 (by rfl) ⟨43022, by rfl⟩ : syracuseStep 917813 = 86045) (by norm_num)
theorem B688441 : Blo 610295 688441 := bbase (se 2 (by rfl) ⟨258165, by rfl⟩ : syracuseStep 688441 = 516331) (by norm_num)
theorem B655673 : Blo 610295 655673 := bbase (se 2 (by rfl) ⟨245877, by rfl⟩ : syracuseStep 655673 = 491755) (by norm_num)
theorem B917837 : Blo 610295 917837 := bbase (se 3 (by rfl) ⟨172094, by rfl⟩ : syracuseStep 917837 = 344189) (by norm_num)
theorem B688477 : Blo 610295 688477 := bbase (se 3 (by rfl) ⟨129089, by rfl⟩ : syracuseStep 688477 = 258179) (by norm_num)
theorem B917861 : Blo 610295 917861 := bbase (se 4 (by rfl) ⟨86049, by rfl⟩ : syracuseStep 917861 = 172099) (by norm_num)
theorem B1376621 : Blo 610295 1376621 := bbase (se 3 (by rfl) ⟨258116, by rfl⟩ : syracuseStep 1376621 = 516233) (by norm_num)
theorem B655733 : Blo 610295 655733 := bbase (se 5 (by rfl) ⟨30737, by rfl⟩ : syracuseStep 655733 = 61475) (by norm_num)
theorem B917885 : Blo 610295 917885 := bbase (se 3 (by rfl) ⟨172103, by rfl⟩ : syracuseStep 917885 = 344207) (by norm_num)
theorem B688513 : Blo 610295 688513 := bbase (se 2 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 688513 = 516385) (by norm_num)
theorem B1474957 : Blo 610295 1474957 := bbase (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) (by norm_num)
theorem B917909 : Blo 610295 917909 := bbase (se 6 (by rfl) ⟨21513, by rfl⟩ : syracuseStep 917909 = 43027) (by norm_num)
theorem B688549 : Blo 610295 688549 := bbase (se 4 (by rfl) ⟨64551, by rfl⟩ : syracuseStep 688549 = 129103) (by norm_num)
theorem B917933 : Blo 610295 917933 := bbase (se 3 (by rfl) ⟨172112, by rfl⟩ : syracuseStep 917933 = 344225) (by norm_num)
theorem B1376693 : Blo 610295 1376693 := bbase (se 5 (by rfl) ⟨64532, by rfl⟩ : syracuseStep 1376693 = 129065) (by norm_num)
theorem B917957 : Blo 610295 917957 := bbase (se 4 (by rfl) ⟨86058, by rfl⟩ : syracuseStep 917957 = 172117) (by norm_num)
theorem B688585 : Blo 610295 688585 := bbase (se 2 (by rfl) ⟨258219, by rfl⟩ : syracuseStep 688585 = 516439) (by norm_num)
theorem B786893 : Blo 610295 786893 := bbase (se 3 (by rfl) ⟨147542, by rfl⟩ : syracuseStep 786893 = 295085) (by norm_num)
theorem B917981 : Blo 610295 917981 := bbase (se 3 (by rfl) ⟨172121, by rfl⟩ : syracuseStep 917981 = 344243) (by norm_num)
theorem B688621 : Blo 610295 688621 := bbase (se 3 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 688621 = 258233) (by norm_num)
theorem B918005 : Blo 610295 918005 := bbase (se 5 (by rfl) ⟨43031, by rfl⟩ : syracuseStep 918005 = 86063) (by norm_num)
theorem B655861 : Blo 610295 655861 := bbase (se 5 (by rfl) ⟨30743, by rfl⟩ : syracuseStep 655861 = 61487) (by norm_num)
theorem B1376765 : Blo 610295 1376765 := bbase (se 3 (by rfl) ⟨258143, by rfl⟩ : syracuseStep 1376765 = 516287) (by norm_num)
theorem B918029 : Blo 610295 918029 := bbase (se 3 (by rfl) ⟨172130, by rfl⟩ : syracuseStep 918029 = 344261) (by norm_num)
theorem B688657 : Blo 610295 688657 := bbase (se 2 (by rfl) ⟨258246, by rfl⟩ : syracuseStep 688657 = 516493) (by norm_num)
theorem B918053 : Blo 610295 918053 := bbase (se 4 (by rfl) ⟨86067, by rfl⟩ : syracuseStep 918053 = 172135) (by norm_num)
theorem B688693 : Blo 610295 688693 := bbase (se 5 (by rfl) ⟨32282, by rfl⟩ : syracuseStep 688693 = 64565) (by norm_num)
theorem B918077 : Blo 610295 918077 := bbase (se 3 (by rfl) ⟨172139, by rfl⟩ : syracuseStep 918077 = 344279) (by norm_num)
theorem B1376837 : Blo 610295 1376837 := bbase (se 4 (by rfl) ⟨129078, by rfl⟩ : syracuseStep 1376837 = 258157) (by norm_num)
theorem B918101 : Blo 610295 918101 := bbase (se 8 (by rfl) ⟨5379, by rfl⟩ : syracuseStep 918101 = 10759) (by norm_num)
theorem B688729 : Blo 610295 688729 := bbase (se 2 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 688729 = 516547) (by norm_num)
theorem B918125 : Blo 610295 918125 := bbase (se 3 (by rfl) ⟨172148, by rfl⟩ : syracuseStep 918125 = 344297) (by norm_num)
theorem B2065013 : Blo 610295 2065013 := bbase (se 5 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 2065013 = 193595) (by norm_num)
theorem B688765 : Blo 610295 688765 := bbase (se 3 (by rfl) ⟨129143, by rfl⟩ : syracuseStep 688765 = 258287) (by norm_num)
theorem B918149 : Blo 610295 918149 := bbase (se 4 (by rfl) ⟨86076, by rfl⟩ : syracuseStep 918149 = 172153) (by norm_num)
theorem B1376909 : Blo 610295 1376909 := bbase (se 3 (by rfl) ⟨258170, by rfl⟩ : syracuseStep 1376909 = 516341) (by norm_num)
theorem B918173 : Blo 610295 918173 := bbase (se 3 (by rfl) ⟨172157, by rfl⟩ : syracuseStep 918173 = 344315) (by norm_num)
theorem B688801 : Blo 610295 688801 := bbase (se 2 (by rfl) ⟨258300, by rfl⟩ : syracuseStep 688801 = 516601) (by norm_num)
theorem B918197 : Blo 610295 918197 := bbase (se 5 (by rfl) ⟨43040, by rfl⟩ : syracuseStep 918197 = 86081) (by norm_num)
theorem B688837 : Blo 610295 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B918221 : Blo 610295 918221 := bbase (se 3 (by rfl) ⟨172166, by rfl⟩ : syracuseStep 918221 = 344333) (by norm_num)
theorem B1376981 : Blo 610295 1376981 := bbase (se 7 (by rfl) ⟨16136, by rfl⟩ : syracuseStep 1376981 = 32273) (by norm_num)
theorem B918245 : Blo 610295 918245 := bbase (se 4 (by rfl) ⟨86085, by rfl⟩ : syracuseStep 918245 = 172171) (by norm_num)
theorem B688873 : Blo 610295 688873 := bbase (se 2 (by rfl) ⟨258327, by rfl⟩ : syracuseStep 688873 = 516655) (by norm_num)
theorem B918269 : Blo 610295 918269 := bbase (se 3 (by rfl) ⟨172175, by rfl⟩ : syracuseStep 918269 = 344351) (by norm_num)
theorem B688909 : Blo 610295 688909 := bbase (se 3 (by rfl) ⟨129170, by rfl⟩ : syracuseStep 688909 = 258341) (by norm_num)
theorem B918293 : Blo 610295 918293 := bbase (se 6 (by rfl) ⟨21522, by rfl⟩ : syracuseStep 918293 = 43045) (by norm_num)
theorem B1377053 : Blo 610295 1377053 := bbase (se 3 (by rfl) ⟨258197, by rfl⟩ : syracuseStep 1377053 = 516395) (by norm_num)
theorem B918317 : Blo 610295 918317 := bbase (se 3 (by rfl) ⟨172184, by rfl⟩ : syracuseStep 918317 = 344369) (by norm_num)
theorem B688945 : Blo 610295 688945 := bbase (se 2 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 688945 = 516709) (by norm_num)
theorem B918341 : Blo 610295 918341 := bbase (se 4 (by rfl) ⟨86094, by rfl⟩ : syracuseStep 918341 = 172189) (by norm_num)
theorem B688981 : Blo 610295 688981 := bbase (se 9 (by rfl) ⟨2018, by rfl⟩ : syracuseStep 688981 = 4037) (by norm_num)
theorem B918365 : Blo 610295 918365 := bbase (se 3 (by rfl) ⟨172193, by rfl⟩ : syracuseStep 918365 = 344387) (by norm_num)
theorem B1377125 : Blo 610295 1377125 := bbase (se 4 (by rfl) ⟨129105, by rfl⟩ : syracuseStep 1377125 = 258211) (by norm_num)
theorem B918389 : Blo 610295 918389 := bbase (se 5 (by rfl) ⟨43049, by rfl⟩ : syracuseStep 918389 = 86099) (by norm_num)
theorem B689017 : Blo 610295 689017 := bbase (se 2 (by rfl) ⟨258381, by rfl⟩ : syracuseStep 689017 = 516763) (by norm_num)
theorem B918413 : Blo 610295 918413 := bbase (se 3 (by rfl) ⟨172202, by rfl⟩ : syracuseStep 918413 = 344405) (by norm_num)
theorem B689053 : Blo 610295 689053 := bbase (se 3 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 689053 = 258395) (by norm_num)
theorem B918437 : Blo 610295 918437 := bbase (se 4 (by rfl) ⟨86103, by rfl⟩ : syracuseStep 918437 = 172207) (by norm_num)
theorem B1377197 : Blo 610295 1377197 := bbase (se 3 (by rfl) ⟨258224, by rfl⟩ : syracuseStep 1377197 = 516449) (by norm_num)
theorem B918461 : Blo 610295 918461 := bbase (se 3 (by rfl) ⟨172211, by rfl⟩ : syracuseStep 918461 = 344423) (by norm_num)
theorem B689089 : Blo 610295 689089 := bbase (se 2 (by rfl) ⟨258408, by rfl⟩ : syracuseStep 689089 = 516817) (by norm_num)
theorem B918485 : Blo 610295 918485 := bbase (se 7 (by rfl) ⟨10763, by rfl⟩ : syracuseStep 918485 = 21527) (by norm_num)
theorem B689125 : Blo 610295 689125 := bbase (se 4 (by rfl) ⟨64605, by rfl⟩ : syracuseStep 689125 = 129211) (by norm_num)
theorem B918509 : Blo 610295 918509 := bbase (se 3 (by rfl) ⟨172220, by rfl⟩ : syracuseStep 918509 = 344441) (by norm_num)
theorem B1377269 : Blo 610295 1377269 := bbase (se 5 (by rfl) ⟨64559, by rfl⟩ : syracuseStep 1377269 = 129119) (by norm_num)
theorem B1180669 : Blo 610295 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B918533 : Blo 610295 918533 := bbase (se 4 (by rfl) ⟨86112, by rfl⟩ : syracuseStep 918533 = 172225) (by norm_num)
theorem B689161 : Blo 610295 689161 := bbase (se 2 (by rfl) ⟨258435, by rfl⟩ : syracuseStep 689161 = 516871) (by norm_num)
theorem B918557 : Blo 610295 918557 := bbase (se 3 (by rfl) ⟨172229, by rfl⟩ : syracuseStep 918557 = 344459) (by norm_num)
theorem B2065445 : Blo 610295 2065445 := bbase (se 4 (by rfl) ⟨193635, by rfl⟩ : syracuseStep 2065445 = 387271) (by norm_num)
theorem B689197 : Blo 610295 689197 := bbase (se 3 (by rfl) ⟨129224, by rfl⟩ : syracuseStep 689197 = 258449) (by norm_num)
theorem B918581 : Blo 610295 918581 := bbase (se 5 (by rfl) ⟨43058, by rfl⟩ : syracuseStep 918581 = 86117) (by norm_num)
theorem B1377341 : Blo 610295 1377341 := bbase (se 3 (by rfl) ⟨258251, by rfl⟩ : syracuseStep 1377341 = 516503) (by norm_num)
theorem B918605 : Blo 610295 918605 := bbase (se 3 (by rfl) ⟨172238, by rfl⟩ : syracuseStep 918605 = 344477) (by norm_num)
theorem B689233 : Blo 610295 689233 := bbase (se 2 (by rfl) ⟨258462, by rfl⟩ : syracuseStep 689233 = 516925) (by norm_num)
theorem B918629 : Blo 610295 918629 := bbase (se 4 (by rfl) ⟨86121, by rfl⟩ : syracuseStep 918629 = 172243) (by norm_num)
theorem B5866613 : Blo 610295 5866613 := bbase (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) (by norm_num)
theorem B689269 : Blo 610295 689269 := bbase (se 5 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 689269 = 64619) (by norm_num)
theorem B918653 : Blo 610295 918653 := bbase (se 3 (by rfl) ⟨172247, by rfl⟩ : syracuseStep 918653 = 344495) (by norm_num)
theorem B1377413 : Blo 610295 1377413 := bbase (se 4 (by rfl) ⟨129132, by rfl⟩ : syracuseStep 1377413 = 258265) (by norm_num)
theorem B918677 : Blo 610295 918677 := bbase (se 6 (by rfl) ⟨21531, by rfl⟩ : syracuseStep 918677 = 43063) (by norm_num)
theorem B1311893 : Blo 610295 1311893 := bbase (se 6 (by rfl) ⟨30747, by rfl⟩ : syracuseStep 1311893 = 61495) (by norm_num)
theorem B689305 : Blo 610295 689305 := bbase (se 2 (by rfl) ⟨258489, by rfl⟩ : syracuseStep 689305 = 516979) (by norm_num)
theorem B918701 : Blo 610295 918701 := bbase (se 3 (by rfl) ⟨172256, by rfl⟩ : syracuseStep 918701 = 344513) (by norm_num)
theorem B1475765 : Blo 610295 1475765 := bbase (se 5 (by rfl) ⟨69176, by rfl⟩ : syracuseStep 1475765 = 138353) (by norm_num)
theorem B689341 : Blo 610295 689341 := bbase (se 3 (by rfl) ⟨129251, by rfl⟩ : syracuseStep 689341 = 258503) (by norm_num)
theorem B918725 : Blo 610295 918725 := bbase (se 4 (by rfl) ⟨86130, by rfl⟩ : syracuseStep 918725 = 172261) (by norm_num)
theorem B1377485 : Blo 610295 1377485 := bbase (se 3 (by rfl) ⟨258278, by rfl⟩ : syracuseStep 1377485 = 516557) (by norm_num)
theorem B918749 : Blo 610295 918749 := bbase (se 3 (by rfl) ⟨172265, by rfl⟩ : syracuseStep 918749 = 344531) (by norm_num)
theorem B689377 : Blo 610295 689377 := bbase (se 2 (by rfl) ⟨258516, by rfl⟩ : syracuseStep 689377 = 517033) (by norm_num)
theorem B885997 : Blo 610295 885997 := bbase (se 3 (by rfl) ⟨166124, by rfl⟩ : syracuseStep 885997 = 332249) (by norm_num)
theorem B918773 : Blo 610295 918773 := bbase (se 5 (by rfl) ⟨43067, by rfl⟩ : syracuseStep 918773 = 86135) (by norm_num)
theorem B689413 : Blo 610295 689413 := bbase (se 4 (by rfl) ⟨64632, by rfl⟩ : syracuseStep 689413 = 129265) (by norm_num)
theorem B918797 : Blo 610295 918797 := bbase (se 3 (by rfl) ⟨172274, by rfl⟩ : syracuseStep 918797 = 344549) (by norm_num)
theorem B1377557 : Blo 610295 1377557 := bbase (se 6 (by rfl) ⟨32286, by rfl⟩ : syracuseStep 1377557 = 64573) (by norm_num)
theorem B918821 : Blo 610295 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B689449 : Blo 610295 689449 := bbase (se 2 (by rfl) ⟨258543, by rfl⟩ : syracuseStep 689449 = 517087) (by norm_num)
theorem B918845 : Blo 610295 918845 := bbase (se 3 (by rfl) ⟨172283, by rfl⟩ : syracuseStep 918845 = 344567) (by norm_num)
theorem B1967429 : Blo 610295 1967429 := bbase (se 4 (by rfl) ⟨184446, by rfl⟩ : syracuseStep 1967429 = 368893) (by norm_num)
theorem B689485 : Blo 610295 689485 := bbase (se 3 (by rfl) ⟨129278, by rfl⟩ : syracuseStep 689485 = 258557) (by norm_num)
theorem B918869 : Blo 610295 918869 := bbase (se 12 (by rfl) ⟨336, by rfl⟩ : syracuseStep 918869 = 673) (by norm_num)
theorem B4654421 : Blo 610295 4654421 := bbase (se 12 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 4654421 = 3409) (by norm_num)
theorem B1377629 : Blo 610295 1377629 := bbase (se 3 (by rfl) ⟨258305, by rfl⟩ : syracuseStep 1377629 = 516611) (by norm_num)
theorem B918893 : Blo 610295 918893 := bbase (se 3 (by rfl) ⟨172292, by rfl⟩ : syracuseStep 918893 = 344585) (by norm_num)
theorem B689521 : Blo 610295 689521 := bbase (se 2 (by rfl) ⟨258570, by rfl⟩ : syracuseStep 689521 = 517141) (by norm_num)
theorem B918917 : Blo 610295 918917 := bbase (se 4 (by rfl) ⟨86148, by rfl⟩ : syracuseStep 918917 = 172297) (by norm_num)
theorem B689557 : Blo 610295 689557 := bbase (se 6 (by rfl) ⟨16161, by rfl⟩ : syracuseStep 689557 = 32323) (by norm_num)
theorem B918941 : Blo 610295 918941 := bbase (se 3 (by rfl) ⟨172301, by rfl⟩ : syracuseStep 918941 = 344603) (by norm_num)
theorem B1377701 : Blo 610295 1377701 := bbase (se 4 (by rfl) ⟨129159, by rfl⟩ : syracuseStep 1377701 = 258319) (by norm_num)
theorem B918965 : Blo 610295 918965 := bbase (se 5 (by rfl) ⟨43076, by rfl⟩ : syracuseStep 918965 = 86153) (by norm_num)
theorem B689593 : Blo 610295 689593 := bbase (se 2 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 689593 = 517195) (by norm_num)
theorem B918989 : Blo 610295 918989 := bbase (se 3 (by rfl) ⟨172310, by rfl⟩ : syracuseStep 918989 = 344621) (by norm_num)
theorem B2065877 : Blo 610295 2065877 := bbase (se 7 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 2065877 = 48419) (by norm_num)
theorem B689629 : Blo 610295 689629 := bbase (se 3 (by rfl) ⟨129305, by rfl⟩ : syracuseStep 689629 = 258611) (by norm_num)
theorem B919013 : Blo 610295 919013 := bbase (se 4 (by rfl) ⟨86157, by rfl⟩ : syracuseStep 919013 = 172315) (by norm_num)
theorem B1377773 : Blo 610295 1377773 := bbase (se 3 (by rfl) ⟨258332, by rfl⟩ : syracuseStep 1377773 = 516665) (by norm_num)
theorem B919037 : Blo 610295 919037 := bbase (se 3 (by rfl) ⟨172319, by rfl⟩ : syracuseStep 919037 = 344639) (by norm_num)
theorem B689665 : Blo 610295 689665 := bbase (se 2 (by rfl) ⟨258624, by rfl⟩ : syracuseStep 689665 = 517249) (by norm_num)
theorem B919061 : Blo 610295 919061 := bbase (se 6 (by rfl) ⟨21540, by rfl⟩ : syracuseStep 919061 = 43081) (by norm_num)
theorem B689701 : Blo 610295 689701 := bbase (se 4 (by rfl) ⟨64659, by rfl⟩ : syracuseStep 689701 = 129319) (by norm_num)
theorem B919085 : Blo 610295 919085 := bbase (se 3 (by rfl) ⟨172328, by rfl⟩ : syracuseStep 919085 = 344657) (by norm_num)
theorem B1377845 : Blo 610295 1377845 := bbase (se 5 (by rfl) ⟨64586, by rfl⟩ : syracuseStep 1377845 = 129173) (by norm_num)
theorem B919109 : Blo 610295 919109 := bbase (se 4 (by rfl) ⟨86166, by rfl⟩ : syracuseStep 919109 = 172333) (by norm_num)
theorem B689737 : Blo 610295 689737 := bbase (se 2 (by rfl) ⟨258651, by rfl⟩ : syracuseStep 689737 = 517303) (by norm_num)
theorem B919133 : Blo 610295 919133 := bbase (se 3 (by rfl) ⟨172337, by rfl⟩ : syracuseStep 919133 = 344675) (by norm_num)
theorem B689773 : Blo 610295 689773 := bbase (se 3 (by rfl) ⟨129332, by rfl⟩ : syracuseStep 689773 = 258665) (by norm_num)
theorem B919157 : Blo 610295 919157 := bbase (se 5 (by rfl) ⟨43085, by rfl⟩ : syracuseStep 919157 = 86171) (by norm_num)
theorem B1377917 : Blo 610295 1377917 := bbase (se 3 (by rfl) ⟨258359, by rfl⟩ : syracuseStep 1377917 = 516719) (by norm_num)
theorem B919181 : Blo 610295 919181 := bbase (se 3 (by rfl) ⟨172346, by rfl⟩ : syracuseStep 919181 = 344693) (by norm_num)
theorem B689809 : Blo 610295 689809 := bbase (se 2 (by rfl) ⟨258678, by rfl⟩ : syracuseStep 689809 = 517357) (by norm_num)
theorem B919205 : Blo 610295 919205 := bbase (se 4 (by rfl) ⟨86175, by rfl⟩ : syracuseStep 919205 = 172351) (by norm_num)
theorem B689845 : Blo 610295 689845 := bbase (se 5 (by rfl) ⟨32336, by rfl⟩ : syracuseStep 689845 = 64673) (by norm_num)
theorem B919229 : Blo 610295 919229 := bbase (se 3 (by rfl) ⟨172355, by rfl⟩ : syracuseStep 919229 = 344711) (by norm_num)
theorem B1377989 : Blo 610295 1377989 := bbase (se 4 (by rfl) ⟨129186, by rfl⟩ : syracuseStep 1377989 = 258373) (by norm_num)
theorem B919253 : Blo 610295 919253 := bbase (se 7 (by rfl) ⟨10772, by rfl⟩ : syracuseStep 919253 = 21545) (by norm_num)
theorem B689881 : Blo 610295 689881 := bbase (se 2 (by rfl) ⟨258705, by rfl⟩ : syracuseStep 689881 = 517411) (by norm_num)
theorem B2623205 : Blo 610295 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B919277 : Blo 610295 919277 := bbase (se 3 (by rfl) ⟨172364, by rfl⟩ : syracuseStep 919277 = 344729) (by norm_num)
theorem B689917 : Blo 610295 689917 := bbase (se 3 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 689917 = 258719) (by norm_num)
theorem B919301 : Blo 610295 919301 := bbase (se 4 (by rfl) ⟨86184, by rfl⟩ : syracuseStep 919301 = 172369) (by norm_num)
theorem B1378061 : Blo 610295 1378061 := bbase (se 3 (by rfl) ⟨258386, by rfl⟩ : syracuseStep 1378061 = 516773) (by norm_num)
theorem B919325 : Blo 610295 919325 := bbase (se 3 (by rfl) ⟨172373, by rfl⟩ : syracuseStep 919325 = 344747) (by norm_num)
theorem B689953 : Blo 610295 689953 := bbase (se 2 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 689953 = 517465) (by norm_num)
theorem B919349 : Blo 610295 919349 := bbase (se 5 (by rfl) ⟨43094, by rfl⟩ : syracuseStep 919349 = 86189) (by norm_num)
theorem B689989 : Blo 610295 689989 := bbase (se 4 (by rfl) ⟨64686, by rfl⟩ : syracuseStep 689989 = 129373) (by norm_num)
theorem B919373 : Blo 610295 919373 := bbase (se 3 (by rfl) ⟨172382, by rfl⟩ : syracuseStep 919373 = 344765) (by norm_num)
theorem B1378133 : Blo 610295 1378133 := bbase (se 9 (by rfl) ⟨4037, by rfl⟩ : syracuseStep 1378133 = 8075) (by norm_num)
theorem B1738597 : Blo 610295 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B919397 : Blo 610295 919397 := bbase (se 4 (by rfl) ⟨86193, by rfl⟩ : syracuseStep 919397 = 172387) (by norm_num)
theorem B690025 : Blo 610295 690025 := bbase (se 2 (by rfl) ⟨258759, by rfl⟩ : syracuseStep 690025 = 517519) (by norm_num)
theorem B919421 : Blo 610295 919421 := bbase (se 3 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 919421 = 344783) (by norm_num)
theorem B2066309 : Blo 610295 2066309 := bbase (se 4 (by rfl) ⟨193716, by rfl⟩ : syracuseStep 2066309 = 387433) (by norm_num)
theorem B690061 : Blo 610295 690061 := bbase (se 3 (by rfl) ⟨129386, by rfl⟩ : syracuseStep 690061 = 258773) (by norm_num)
theorem B919445 : Blo 610295 919445 := bbase (se 6 (by rfl) ⟨21549, by rfl⟩ : syracuseStep 919445 = 43099) (by norm_num)
theorem B1378205 : Blo 610295 1378205 := bbase (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) (by norm_num)
theorem B919469 : Blo 610295 919469 := bbase (se 3 (by rfl) ⟨172400, by rfl⟩ : syracuseStep 919469 = 344801) (by norm_num)
theorem B690097 : Blo 610295 690097 := bbase (se 2 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 690097 = 517573) (by norm_num)
theorem B2787269 : Blo 610295 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B919493 : Blo 610295 919493 := bbase (se 4 (by rfl) ⟨86202, by rfl⟩ : syracuseStep 919493 = 172405) (by norm_num)
theorem B2328533 : Blo 610295 2328533 := bbase (se 7 (by rfl) ⟨27287, by rfl⟩ : syracuseStep 2328533 = 54575) (by norm_num)
theorem B690133 : Blo 610295 690133 := bbase (se 7 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 690133 = 16175) (by norm_num)
theorem B919517 : Blo 610295 919517 := bbase (se 3 (by rfl) ⟨172409, by rfl⟩ : syracuseStep 919517 = 344819) (by norm_num)
theorem B1378277 : Blo 610295 1378277 := bbase (se 4 (by rfl) ⟨129213, by rfl⟩ : syracuseStep 1378277 = 258427) (by norm_num)
theorem B919541 : Blo 610295 919541 := bbase (se 5 (by rfl) ⟨43103, by rfl⟩ : syracuseStep 919541 = 86207) (by norm_num)
theorem B690169 : Blo 610295 690169 := bbase (se 2 (by rfl) ⟨258813, by rfl⟩ : syracuseStep 690169 = 517627) (by norm_num)
theorem B919565 : Blo 610295 919565 := bbase (se 3 (by rfl) ⟨172418, by rfl⟩ : syracuseStep 919565 = 344837) (by norm_num)
theorem B690205 : Blo 610295 690205 := bbase (se 3 (by rfl) ⟨129413, by rfl⟩ : syracuseStep 690205 = 258827) (by norm_num)
theorem B919589 : Blo 610295 919589 := bbase (se 4 (by rfl) ⟨86211, by rfl⟩ : syracuseStep 919589 = 172423) (by norm_num)
theorem B1378349 : Blo 610295 1378349 := bbase (se 3 (by rfl) ⟨258440, by rfl⟩ : syracuseStep 1378349 = 516881) (by norm_num)
theorem B919613 : Blo 610295 919613 := bbase (se 3 (by rfl) ⟨172427, by rfl⟩ : syracuseStep 919613 = 344855) (by norm_num)
theorem B690241 : Blo 610295 690241 := bbase (se 2 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 690241 = 517681) (by norm_num)
theorem B919637 : Blo 610295 919637 := bbase (se 8 (by rfl) ⟨5388, by rfl⟩ : syracuseStep 919637 = 10777) (by norm_num)
theorem B690277 : Blo 610295 690277 := bbase (se 4 (by rfl) ⟨64713, by rfl⟩ : syracuseStep 690277 = 129427) (by norm_num)
theorem B919661 : Blo 610295 919661 := bbase (se 3 (by rfl) ⟨172436, by rfl⟩ : syracuseStep 919661 = 344873) (by norm_num)
theorem B1378421 : Blo 610295 1378421 := bbase (se 5 (by rfl) ⟨64613, by rfl⟩ : syracuseStep 1378421 = 129227) (by norm_num)
theorem B1181821 : Blo 610295 1181821 := bbase (se 3 (by rfl) ⟨221591, by rfl⟩ : syracuseStep 1181821 = 443183) (by norm_num)
theorem B919685 : Blo 610295 919685 := bbase (se 4 (by rfl) ⟨86220, by rfl⟩ : syracuseStep 919685 = 172441) (by norm_num)
theorem B690313 : Blo 610295 690313 := bbase (se 2 (by rfl) ⟨258867, by rfl⟩ : syracuseStep 690313 = 517735) (by norm_num)
theorem B919709 : Blo 610295 919709 := bbase (se 3 (by rfl) ⟨172445, by rfl⟩ : syracuseStep 919709 = 344891) (by norm_num)
theorem B690349 : Blo 610295 690349 := bbase (se 3 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 690349 = 258881) (by norm_num)
theorem B919733 : Blo 610295 919733 := bbase (se 5 (by rfl) ⟨43112, by rfl⟩ : syracuseStep 919733 = 86225) (by norm_num)
theorem B1378493 : Blo 610295 1378493 := bbase (se 3 (by rfl) ⟨258467, by rfl⟩ : syracuseStep 1378493 = 516935) (by norm_num)
theorem B919757 : Blo 610295 919757 := bbase (se 3 (by rfl) ⟨172454, by rfl⟩ : syracuseStep 919757 = 344909) (by norm_num)
theorem B690385 : Blo 610295 690385 := bbase (se 2 (by rfl) ⟨258894, by rfl⟩ : syracuseStep 690385 = 517789) (by norm_num)
theorem B919781 : Blo 610295 919781 := bbase (se 4 (by rfl) ⟨86229, by rfl⟩ : syracuseStep 919781 = 172459) (by norm_num)
theorem B2328821 : Blo 610295 2328821 := bbase (se 5 (by rfl) ⟨109163, by rfl⟩ : syracuseStep 2328821 = 218327) (by norm_num)
theorem B690421 : Blo 610295 690421 := bbase (se 5 (by rfl) ⟨32363, by rfl⟩ : syracuseStep 690421 = 64727) (by norm_num)
theorem B919805 : Blo 610295 919805 := bbase (se 3 (by rfl) ⟨172463, by rfl⟩ : syracuseStep 919805 = 344927) (by norm_num)
theorem B1378565 : Blo 610295 1378565 := bbase (se 4 (by rfl) ⟨129240, by rfl⟩ : syracuseStep 1378565 = 258481) (by norm_num)
theorem B919829 : Blo 610295 919829 := bbase (se 6 (by rfl) ⟨21558, by rfl⟩ : syracuseStep 919829 = 43117) (by norm_num)
theorem B690457 : Blo 610295 690457 := bbase (se 2 (by rfl) ⟨258921, by rfl⟩ : syracuseStep 690457 = 517843) (by norm_num)
theorem B919853 : Blo 610295 919853 := bbase (se 3 (by rfl) ⟨172472, by rfl⟩ : syracuseStep 919853 = 344945) (by norm_num)
theorem B2066741 : Blo 610295 2066741 := bbase (se 5 (by rfl) ⟨96878, by rfl⟩ : syracuseStep 2066741 = 193757) (by norm_num)
theorem B690493 : Blo 610295 690493 := bbase (se 3 (by rfl) ⟨129467, by rfl⟩ : syracuseStep 690493 = 258935) (by norm_num)
theorem B919877 : Blo 610295 919877 := bbase (se 4 (by rfl) ⟨86238, by rfl⟩ : syracuseStep 919877 = 172477) (by norm_num)
theorem B1378637 : Blo 610295 1378637 := bbase (se 3 (by rfl) ⟨258494, by rfl⟩ : syracuseStep 1378637 = 516989) (by norm_num)
theorem B919901 : Blo 610295 919901 := bbase (se 3 (by rfl) ⟨172481, by rfl⟩ : syracuseStep 919901 = 344963) (by norm_num)
theorem B690529 : Blo 610295 690529 := bbase (se 2 (by rfl) ⟨258948, by rfl⟩ : syracuseStep 690529 = 517897) (by norm_num)
theorem B919925 : Blo 610295 919925 := bbase (se 5 (by rfl) ⟨43121, by rfl⟩ : syracuseStep 919925 = 86243) (by norm_num)
theorem B690565 : Blo 610295 690565 := bbase (se 4 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 690565 = 129481) (by norm_num)
theorem B919949 : Blo 610295 919949 := bbase (se 3 (by rfl) ⟨172490, by rfl⟩ : syracuseStep 919949 = 344981) (by norm_num)
theorem B1378709 : Blo 610295 1378709 := bbase (se 6 (by rfl) ⟨32313, by rfl⟩ : syracuseStep 1378709 = 64627) (by norm_num)
theorem B919973 : Blo 610295 919973 := bbase (se 4 (by rfl) ⟨86247, by rfl⟩ : syracuseStep 919973 = 172495) (by norm_num)
theorem B2099621 : Blo 610295 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B690601 : Blo 610295 690601 := bbase (se 2 (by rfl) ⟨258975, by rfl⟩ : syracuseStep 690601 = 517951) (by norm_num)
theorem B919997 : Blo 610295 919997 := bbase (se 3 (by rfl) ⟨172499, by rfl⟩ : syracuseStep 919997 = 344999) (by norm_num)
theorem B690637 : Blo 610295 690637 := bbase (se 3 (by rfl) ⟨129494, by rfl⟩ : syracuseStep 690637 = 258989) (by norm_num)
theorem B920021 : Blo 610295 920021 := bbase (se 7 (by rfl) ⟨10781, by rfl⟩ : syracuseStep 920021 = 21563) (by norm_num)
theorem B1378781 : Blo 610295 1378781 := bbase (se 3 (by rfl) ⟨258521, by rfl⟩ : syracuseStep 1378781 = 517043) (by norm_num)
theorem B920045 : Blo 610295 920045 := bbase (se 3 (by rfl) ⟨172508, by rfl⟩ : syracuseStep 920045 = 345017) (by norm_num)
theorem B690673 : Blo 610295 690673 := bbase (se 2 (by rfl) ⟨259002, by rfl⟩ : syracuseStep 690673 = 518005) (by norm_num)
theorem B920069 : Blo 610295 920069 := bbase (se 4 (by rfl) ⟨86256, by rfl⟩ : syracuseStep 920069 = 172513) (by norm_num)
theorem B690709 : Blo 610295 690709 := bbase (se 6 (by rfl) ⟨16188, by rfl⟩ : syracuseStep 690709 = 32377) (by norm_num)
theorem B920093 : Blo 610295 920093 := bbase (se 3 (by rfl) ⟨172517, by rfl⟩ : syracuseStep 920093 = 345035) (by norm_num)
theorem B1378853 : Blo 610295 1378853 := bbase (se 4 (by rfl) ⟨129267, by rfl⟩ : syracuseStep 1378853 = 258535) (by norm_num)
theorem B920117 : Blo 610295 920117 := bbase (se 5 (by rfl) ⟨43130, by rfl⟩ : syracuseStep 920117 = 86261) (by norm_num)
theorem B690745 : Blo 610295 690745 := bbase (se 2 (by rfl) ⟨259029, by rfl⟩ : syracuseStep 690745 = 518059) (by norm_num)
theorem B920141 : Blo 610295 920141 := bbase (se 3 (by rfl) ⟨172526, by rfl⟩ : syracuseStep 920141 = 345053) (by norm_num)
theorem B690781 : Blo 610295 690781 := bbase (se 3 (by rfl) ⟨129521, by rfl⟩ : syracuseStep 690781 = 259043) (by norm_num)
theorem B920165 : Blo 610295 920165 := bbase (se 4 (by rfl) ⟨86265, by rfl⟩ : syracuseStep 920165 = 172531) (by norm_num)
theorem B1378925 : Blo 610295 1378925 := bbase (se 3 (by rfl) ⟨258548, by rfl⟩ : syracuseStep 1378925 = 517097) (by norm_num)
theorem B920189 : Blo 610295 920189 := bbase (se 3 (by rfl) ⟨172535, by rfl⟩ : syracuseStep 920189 = 345071) (by norm_num)
theorem B690817 : Blo 610295 690817 := bbase (se 2 (by rfl) ⟨259056, by rfl⟩ : syracuseStep 690817 = 518113) (by norm_num)
theorem B920213 : Blo 610295 920213 := bbase (se 6 (by rfl) ⟨21567, by rfl⟩ : syracuseStep 920213 = 43135) (by norm_num)
theorem B690853 : Blo 610295 690853 := bbase (se 4 (by rfl) ⟨64767, by rfl⟩ : syracuseStep 690853 = 129535) (by norm_num)
theorem B920237 : Blo 610295 920237 := bbase (se 3 (by rfl) ⟨172544, by rfl⟩ : syracuseStep 920237 = 345089) (by norm_num)
theorem B1378997 : Blo 610295 1378997 := bbase (se 5 (by rfl) ⟨64640, by rfl⟩ : syracuseStep 1378997 = 129281) (by norm_num)
theorem B920261 : Blo 610295 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B690889 : Blo 610295 690889 := bbase (se 2 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 690889 = 518167) (by norm_num)
theorem B920285 : Blo 610295 920285 := bbase (se 3 (by rfl) ⟨172553, by rfl⟩ : syracuseStep 920285 = 345107) (by norm_num)
theorem B2067173 : Blo 610295 2067173 := bbase (se 4 (by rfl) ⟨193797, by rfl⟩ : syracuseStep 2067173 = 387595) (by norm_num)
theorem B690925 : Blo 610295 690925 := bbase (se 3 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 690925 = 259097) (by norm_num)
theorem B920309 : Blo 610295 920309 := bbase (se 5 (by rfl) ⟨43139, by rfl⟩ : syracuseStep 920309 = 86279) (by norm_num)
theorem B1379069 : Blo 610295 1379069 := bbase (se 3 (by rfl) ⟨258575, by rfl⟩ : syracuseStep 1379069 = 517151) (by norm_num)
theorem B920333 : Blo 610295 920333 := bbase (se 3 (by rfl) ⟨172562, by rfl⟩ : syracuseStep 920333 = 345125) (by norm_num)
theorem B690961 : Blo 610295 690961 := bbase (se 2 (by rfl) ⟨259110, by rfl⟩ : syracuseStep 690961 = 518221) (by norm_num)
theorem B920357 : Blo 610295 920357 := bbase (se 4 (by rfl) ⟨86283, by rfl⟩ : syracuseStep 920357 = 172567) (by norm_num)
theorem B690997 : Blo 610295 690997 := bbase (se 5 (by rfl) ⟨32390, by rfl⟩ : syracuseStep 690997 = 64781) (by norm_num)
theorem B920381 : Blo 610295 920381 := bbase (se 3 (by rfl) ⟨172571, by rfl⟩ : syracuseStep 920381 = 345143) (by norm_num)
theorem B1379141 : Blo 610295 1379141 := bbase (se 4 (by rfl) ⟨129294, by rfl⟩ : syracuseStep 1379141 = 258589) (by norm_num)
theorem B920405 : Blo 610295 920405 := bbase (se 9 (by rfl) ⟨2696, by rfl⟩ : syracuseStep 920405 = 5393) (by norm_num)
theorem B691033 : Blo 610295 691033 := bbase (se 2 (by rfl) ⟨259137, by rfl⟩ : syracuseStep 691033 = 518275) (by norm_num)
theorem B920429 : Blo 610295 920429 := bbase (se 3 (by rfl) ⟨172580, by rfl⟩ : syracuseStep 920429 = 345161) (by norm_num)
theorem B691069 : Blo 610295 691069 := bbase (se 3 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 691069 = 259151) (by norm_num)
theorem B920453 : Blo 610295 920453 := bbase (se 4 (by rfl) ⟨86292, by rfl⟩ : syracuseStep 920453 = 172585) (by norm_num)
theorem B1379213 : Blo 610295 1379213 := bbase (se 3 (by rfl) ⟨258602, by rfl⟩ : syracuseStep 1379213 = 517205) (by norm_num)
theorem B920477 : Blo 610295 920477 := bbase (se 3 (by rfl) ⟨172589, by rfl⟩ : syracuseStep 920477 = 345179) (by norm_num)
theorem B920501 : Blo 610295 920501 := bbase (se 5 (by rfl) ⟨43148, by rfl⟩ : syracuseStep 920501 = 86297) (by norm_num)
theorem B920525 : Blo 610295 920525 := bbase (se 3 (by rfl) ⟨172598, by rfl⟩ : syracuseStep 920525 = 345197) (by norm_num)
theorem B1379285 : Blo 610295 1379285 := bbase (se 7 (by rfl) ⟨16163, by rfl⟩ : syracuseStep 1379285 = 32327) (by norm_num)
theorem B920549 : Blo 610295 920549 := bbase (se 4 (by rfl) ⟨86301, by rfl⟩ : syracuseStep 920549 = 172603) (by norm_num)
theorem B920573 : Blo 610295 920573 := bbase (se 3 (by rfl) ⟨172607, by rfl⟩ : syracuseStep 920573 = 345215) (by norm_num)
theorem B920597 : Blo 610295 920597 := bbase (se 6 (by rfl) ⟨21576, by rfl⟩ : syracuseStep 920597 = 43153) (by norm_num)
theorem B1379357 : Blo 610295 1379357 := bbase (se 3 (by rfl) ⟨258629, by rfl⟩ : syracuseStep 1379357 = 517259) (by norm_num)
theorem B920621 : Blo 610295 920621 := bbase (se 3 (by rfl) ⟨172616, by rfl⟩ : syracuseStep 920621 = 345233) (by norm_num)
theorem B920645 : Blo 610295 920645 := bbase (se 4 (by rfl) ⟨86310, by rfl⟩ : syracuseStep 920645 = 172621) (by norm_num)
theorem B920669 : Blo 610295 920669 := bbase (se 3 (by rfl) ⟨172625, by rfl⟩ : syracuseStep 920669 = 345251) (by norm_num)
theorem B1379429 : Blo 610295 1379429 := bbase (se 4 (by rfl) ⟨129321, by rfl⟩ : syracuseStep 1379429 = 258643) (by norm_num)
theorem B920693 : Blo 610295 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B920717 : Blo 610295 920717 := bbase (se 3 (by rfl) ⟨172634, by rfl⟩ : syracuseStep 920717 = 345269) (by norm_num)
theorem B2067605 : Blo 610295 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B1576093 : Blo 610295 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B920741 : Blo 610295 920741 := bbase (se 4 (by rfl) ⟨86319, by rfl⟩ : syracuseStep 920741 = 172639) (by norm_num)
theorem B1379501 : Blo 610295 1379501 := bbase (se 3 (by rfl) ⟨258656, by rfl⟩ : syracuseStep 1379501 = 517313) (by norm_num)
theorem B920765 : Blo 610295 920765 := bbase (se 3 (by rfl) ⟨172643, by rfl⟩ : syracuseStep 920765 = 345287) (by norm_num)
theorem B11144405 : Blo 610295 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B920789 : Blo 610295 920789 := bbase (se 7 (by rfl) ⟨10790, by rfl⟩ : syracuseStep 920789 = 21581) (by norm_num)
theorem B920813 : Blo 610295 920813 := bbase (se 3 (by rfl) ⟨172652, by rfl⟩ : syracuseStep 920813 = 345305) (by norm_num)
theorem B1379573 : Blo 610295 1379573 := bbase (se 5 (by rfl) ⟨64667, by rfl⟩ : syracuseStep 1379573 = 129335) (by norm_num)
theorem B920837 : Blo 610295 920837 := bbase (se 4 (by rfl) ⟨86328, by rfl⟩ : syracuseStep 920837 = 172657) (by norm_num)
theorem B4197653 : Blo 610295 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B920861 : Blo 610295 920861 := bbase (se 3 (by rfl) ⟨172661, by rfl⟩ : syracuseStep 920861 = 345323) (by norm_num)
theorem B920885 : Blo 610295 920885 := bbase (se 5 (by rfl) ⟨43166, by rfl⟩ : syracuseStep 920885 = 86333) (by norm_num)
theorem B1379645 : Blo 610295 1379645 := bbase (se 3 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 1379645 = 517367) (by norm_num)
theorem B920909 : Blo 610295 920909 := bbase (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) (by norm_num)
theorem B920933 : Blo 610295 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B920957 : Blo 610295 920957 := bbase (se 3 (by rfl) ⟨172679, by rfl⟩ : syracuseStep 920957 = 345359) (by norm_num)
theorem B1379717 : Blo 610295 1379717 := bbase (se 4 (by rfl) ⟨129348, by rfl⟩ : syracuseStep 1379717 = 258697) (by norm_num)
theorem B2330005 : Blo 610295 2330005 := bbase (se 6 (by rfl) ⟨54609, by rfl⟩ : syracuseStep 2330005 = 109219) (by norm_num)
theorem B920981 : Blo 610295 920981 := bbase (se 6 (by rfl) ⟨21585, by rfl⟩ : syracuseStep 920981 = 43171) (by norm_num)
theorem B921005 : Blo 610295 921005 := bbase (se 3 (by rfl) ⟨172688, by rfl⟩ : syracuseStep 921005 = 345377) (by norm_num)
theorem B921029 : Blo 610295 921029 := bbase (se 4 (by rfl) ⟨86346, by rfl⟩ : syracuseStep 921029 = 172693) (by norm_num)
theorem B1379789 : Blo 610295 1379789 := bbase (se 3 (by rfl) ⟨258710, by rfl⟩ : syracuseStep 1379789 = 517421) (by norm_num)
theorem B921053 : Blo 610295 921053 := bbase (se 3 (by rfl) ⟨172697, by rfl⟩ : syracuseStep 921053 = 345395) (by norm_num)
theorem B921077 : Blo 610295 921077 := bbase (se 5 (by rfl) ⟨43175, by rfl⟩ : syracuseStep 921077 = 86351) (by norm_num)
theorem B921101 : Blo 610295 921101 := bbase (se 3 (by rfl) ⟨172706, by rfl⟩ : syracuseStep 921101 = 345413) (by norm_num)
theorem B1379861 : Blo 610295 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B921125 : Blo 610295 921125 := bbase (se 4 (by rfl) ⟨86355, by rfl⟩ : syracuseStep 921125 = 172711) (by norm_num)
theorem B921149 : Blo 610295 921149 := bbase (se 3 (by rfl) ⟨172715, by rfl⟩ : syracuseStep 921149 = 345431) (by norm_num)
theorem B1674821 : Blo 610295 1674821 := bbase (se 4 (by rfl) ⟨157014, by rfl⟩ : syracuseStep 1674821 = 314029) (by norm_num)
theorem B2068037 : Blo 610295 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B921173 : Blo 610295 921173 := bbase (se 8 (by rfl) ⟨5397, by rfl⟩ : syracuseStep 921173 = 10795) (by norm_num)
theorem B1379933 : Blo 610295 1379933 := bbase (se 3 (by rfl) ⟨258737, by rfl⟩ : syracuseStep 1379933 = 517475) (by norm_num)
theorem B921197 : Blo 610295 921197 := bbase (se 3 (by rfl) ⟨172724, by rfl⟩ : syracuseStep 921197 = 345449) (by norm_num)
theorem B921221 : Blo 610295 921221 := bbase (se 4 (by rfl) ⟨86364, by rfl⟩ : syracuseStep 921221 = 172729) (by norm_num)
theorem B921245 : Blo 610295 921245 := bbase (se 3 (by rfl) ⟨172733, by rfl⟩ : syracuseStep 921245 = 345467) (by norm_num)
theorem B1380005 : Blo 610295 1380005 := bbase (se 4 (by rfl) ⟨129375, by rfl⟩ : syracuseStep 1380005 = 258751) (by norm_num)
theorem B921269 : Blo 610295 921269 := bbase (se 5 (by rfl) ⟨43184, by rfl⟩ : syracuseStep 921269 = 86369) (by norm_num)
theorem B2330309 : Blo 610295 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B921293 : Blo 610295 921293 := bbase (se 3 (by rfl) ⟨172742, by rfl⟩ : syracuseStep 921293 = 345485) (by norm_num)
theorem B921317 : Blo 610295 921317 := bbase (se 4 (by rfl) ⟨86373, by rfl⟩ : syracuseStep 921317 = 172747) (by norm_num)
theorem B1380077 : Blo 610295 1380077 := bbase (se 3 (by rfl) ⟨258764, by rfl⟩ : syracuseStep 1380077 = 517529) (by norm_num)
theorem B921341 : Blo 610295 921341 := bbase (se 3 (by rfl) ⟨172751, by rfl⟩ : syracuseStep 921341 = 345503) (by norm_num)
theorem B921365 : Blo 610295 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B921389 : Blo 610295 921389 := bbase (se 3 (by rfl) ⟨172760, by rfl⟩ : syracuseStep 921389 = 345521) (by norm_num)
theorem B1380149 : Blo 610295 1380149 := bbase (se 5 (by rfl) ⟨64694, by rfl⟩ : syracuseStep 1380149 = 129389) (by norm_num)
theorem B921413 : Blo 610295 921413 := bbase (se 4 (by rfl) ⟨86382, by rfl⟩ : syracuseStep 921413 = 172765) (by norm_num)
theorem B921437 : Blo 610295 921437 := bbase (se 3 (by rfl) ⟨172769, by rfl⟩ : syracuseStep 921437 = 345539) (by norm_num)
theorem B1380221 : Blo 610295 1380221 := bbase (se 3 (by rfl) ⟨258791, by rfl⟩ : syracuseStep 1380221 = 517583) (by norm_num)
theorem B1380293 : Blo 610295 1380293 := bbase (se 4 (by rfl) ⟨129402, by rfl⟩ : syracuseStep 1380293 = 258805) (by norm_num)
theorem B2068469 : Blo 610295 2068469 := bbase (se 5 (by rfl) ⟨96959, by rfl⟩ : syracuseStep 2068469 = 193919) (by norm_num)
theorem B1380365 : Blo 610295 1380365 := bbase (se 3 (by rfl) ⟨258818, by rfl⟩ : syracuseStep 1380365 = 517637) (by norm_num)
theorem B1380437 : Blo 610295 1380437 := bbase (se 8 (by rfl) ⟨8088, by rfl⟩ : syracuseStep 1380437 = 16177) (by norm_num)
theorem B1380509 : Blo 610295 1380509 := bbase (se 3 (by rfl) ⟨258845, by rfl⟩ : syracuseStep 1380509 = 517691) (by norm_num)
theorem B1380581 : Blo 610295 1380581 := bbase (se 4 (by rfl) ⟨129429, by rfl⟩ : syracuseStep 1380581 = 258859) (by norm_num)
theorem B1380653 : Blo 610295 1380653 := bbase (se 3 (by rfl) ⟨258872, by rfl⟩ : syracuseStep 1380653 = 517745) (by norm_num)
theorem B1380725 : Blo 610295 1380725 := bbase (se 5 (by rfl) ⟨64721, by rfl⟩ : syracuseStep 1380725 = 129443) (by norm_num)
theorem B2068901 : Blo 610295 2068901 := bbase (se 4 (by rfl) ⟨193959, by rfl⟩ : syracuseStep 2068901 = 387919) (by norm_num)
theorem B1380797 : Blo 610295 1380797 := bbase (se 3 (by rfl) ⟨258899, by rfl⟩ : syracuseStep 1380797 = 517799) (by norm_num)
theorem B1380869 : Blo 610295 1380869 := bbase (se 4 (by rfl) ⟨129456, by rfl⟩ : syracuseStep 1380869 = 258913) (by norm_num)
theorem B1380941 : Blo 610295 1380941 := bbase (se 3 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 1380941 = 517853) (by norm_num)
theorem B7967317 : Blo 610295 7967317 := bbase (se 8 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 7967317 = 93367) (by norm_num)
theorem B1741445 : Blo 610295 1741445 := bbase (se 4 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 1741445 = 326521) (by norm_num)
theorem B1381013 : Blo 610295 1381013 := bbase (se 6 (by rfl) ⟨32367, by rfl⟩ : syracuseStep 1381013 = 64735) (by norm_num)
theorem B5214901 : Blo 610295 5214901 := bbase (se 5 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 5214901 = 488897) (by norm_num)
theorem B1381085 : Blo 610295 1381085 := bbase (se 3 (by rfl) ⟨258953, by rfl⟩ : syracuseStep 1381085 = 517907) (by norm_num)
theorem B1544933 : Blo 610295 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1381157 : Blo 610295 1381157 := bbase (se 4 (by rfl) ⟨129483, by rfl⟩ : syracuseStep 1381157 = 258967) (by norm_num)
theorem B2069333 : Blo 610295 2069333 := bbase (se 9 (by rfl) ⟨6062, by rfl⟩ : syracuseStep 2069333 = 12125) (by norm_num)
theorem B1381229 : Blo 610295 1381229 := bbase (se 3 (by rfl) ⟨258980, by rfl⟩ : syracuseStep 1381229 = 517961) (by norm_num)
theorem B1381301 : Blo 610295 1381301 := bbase (se 5 (by rfl) ⟨64748, by rfl⟩ : syracuseStep 1381301 = 129497) (by norm_num)
theorem B1381373 : Blo 610295 1381373 := bbase (se 3 (by rfl) ⟨259007, by rfl⟩ : syracuseStep 1381373 = 518015) (by norm_num)
theorem B1545277 : Blo 610295 1545277 := bbase (se 3 (by rfl) ⟨289739, by rfl⟩ : syracuseStep 1545277 = 579479) (by norm_num)
theorem B1381445 : Blo 610295 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B1381517 : Blo 610295 1381517 := bbase (se 3 (by rfl) ⟨259034, by rfl⟩ : syracuseStep 1381517 = 518069) (by norm_num)
theorem B1545389 : Blo 610295 1545389 := bbase (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) (by norm_num)
theorem B1381589 : Blo 610295 1381589 := bbase (se 7 (by rfl) ⟨16190, by rfl⟩ : syracuseStep 1381589 = 32381) (by norm_num)
theorem B2069765 : Blo 610295 2069765 := bbase (se 4 (by rfl) ⟨194040, by rfl⟩ : syracuseStep 2069765 = 388081) (by norm_num)
theorem B1381661 : Blo 610295 1381661 := bbase (se 3 (by rfl) ⟨259061, by rfl⟩ : syracuseStep 1381661 = 518123) (by norm_num)
theorem B1381733 : Blo 610295 1381733 := bbase (se 4 (by rfl) ⟨129537, by rfl⟩ : syracuseStep 1381733 = 259075) (by norm_num)
theorem B1545581 : Blo 610295 1545581 := bbase (se 3 (by rfl) ⟨289796, by rfl⟩ : syracuseStep 1545581 = 579593) (by norm_num)
theorem B1381805 : Blo 610295 1381805 := bbase (se 3 (by rfl) ⟨259088, by rfl⟩ : syracuseStep 1381805 = 518177) (by norm_num)
theorem B1381877 : Blo 610295 1381877 := bbase (se 5 (by rfl) ⟨64775, by rfl⟩ : syracuseStep 1381877 = 129551) (by norm_num)
theorem B1381949 : Blo 610295 1381949 := bbase (se 3 (by rfl) ⟨259115, by rfl⟩ : syracuseStep 1381949 = 518231) (by norm_num)
theorem B661069 : Blo 610295 661069 := bbase (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) (by norm_num)
theorem B1382021 : Blo 610295 1382021 := bbase (se 4 (by rfl) ⟨129564, by rfl⟩ : syracuseStep 1382021 = 259129) (by norm_num)
theorem B2070197 : Blo 610295 2070197 := bbase (se 5 (by rfl) ⟨97040, by rfl⟩ : syracuseStep 2070197 = 194081) (by norm_num)
theorem B1545925 : Blo 610295 1545925 := bbase (se 4 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 1545925 = 289861) (by norm_num)
theorem B1382093 : Blo 610295 1382093 := bbase (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) (by norm_num)
theorem B1382165 : Blo 610295 1382165 := bbase (se 6 (by rfl) ⟨32394, by rfl⟩ : syracuseStep 1382165 = 64789) (by norm_num)
theorem B1742629 : Blo 610295 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B1546037 : Blo 610295 1546037 := bbase (se 5 (by rfl) ⟨72470, by rfl⟩ : syracuseStep 1546037 = 144941) (by norm_num)
theorem B3479381 : Blo 610295 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B2201525 : Blo 610295 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B1742789 : Blo 610295 1742789 := bbase (se 4 (by rfl) ⟨163386, by rfl⟩ : syracuseStep 1742789 = 326773) (by norm_num)
theorem B1546229 : Blo 610295 1546229 := bbase (se 5 (by rfl) ⟨72479, by rfl⟩ : syracuseStep 1546229 = 144959) (by norm_num)
theorem B2070629 : Blo 610295 2070629 := bbase (se 4 (by rfl) ⟨194121, by rfl⟩ : syracuseStep 2070629 = 388243) (by norm_num)
theorem B1743029 : Blo 610295 1743029 := bbase (se 5 (by rfl) ⟨81704, by rfl⟩ : syracuseStep 1743029 = 163409) (by norm_num)
theorem B1546573 : Blo 610295 1546573 := bbase (se 3 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 1546573 = 579965) (by norm_num)
theorem B1743221 : Blo 610295 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B1546685 : Blo 610295 1546685 := bbase (se 3 (by rfl) ⟨290003, by rfl⟩ : syracuseStep 1546685 = 580007) (by norm_num)
theorem B2071061 : Blo 610295 2071061 := bbase (se 6 (by rfl) ⟨48540, by rfl⟩ : syracuseStep 2071061 = 97081) (by norm_num)
theorem B5216885 : Blo 610295 5216885 := bbase (se 5 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 5216885 = 489083) (by norm_num)
theorem B1546877 : Blo 610295 1546877 := bbase (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) (by norm_num)
theorem B662177 : Blo 610295 662177 := bbase (se 2 (by rfl) ⟨248316, by rfl⟩ : syracuseStep 662177 = 496633) (by norm_num)
theorem B2071493 : Blo 610295 2071493 := bbase (se 4 (by rfl) ⟨194202, by rfl⟩ : syracuseStep 2071493 = 388405) (by norm_num)
theorem B1547221 : Blo 610295 1547221 := bbase (se 7 (by rfl) ⟨18131, by rfl⟩ : syracuseStep 1547221 = 36263) (by norm_num)
theorem B1547333 : Blo 610295 1547333 := bbase (se 4 (by rfl) ⟨145062, by rfl⟩ : syracuseStep 1547333 = 290125) (by norm_num)
theorem B826453 : Blo 610295 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B2202805 : Blo 610295 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1547525 : Blo 610295 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B826669 : Blo 610295 826669 := bbase (se 3 (by rfl) ⟨155000, by rfl⟩ : syracuseStep 826669 = 310001) (by norm_num)
theorem B1744213 : Blo 610295 1744213 := bbase (se 11 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 1744213 = 2555) (by norm_num)
theorem B23928149 : Blo 610295 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B2071925 : Blo 610295 2071925 := bbase (se 5 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 2071925 = 194243) (by norm_num)
theorem B826853 : Blo 610295 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B3317269 : Blo 610295 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B663113 : Blo 610295 663113 := bbase (se 2 (by rfl) ⟨248667, by rfl⟩ : syracuseStep 663113 = 497335) (by norm_num)
theorem B1547869 : Blo 610295 1547869 := bbase (se 3 (by rfl) ⟨290225, by rfl⟩ : syracuseStep 1547869 = 580451) (by norm_num)
theorem B1547981 : Blo 610295 1547981 := bbase (se 3 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 1547981 = 580493) (by norm_num)
theorem B2072357 : Blo 610295 2072357 := bbase (se 4 (by rfl) ⟨194283, by rfl⟩ : syracuseStep 2072357 = 388567) (by norm_num)
theorem B1548173 : Blo 610295 1548173 := bbase (se 3 (by rfl) ⟨290282, by rfl⟩ : syracuseStep 1548173 = 580565) (by norm_num)
theorem B696325 : Blo 610295 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B663697 : Blo 610295 663697 := bbase (se 2 (by rfl) ⟨248886, by rfl⟩ : syracuseStep 663697 = 497773) (by norm_num)
theorem B827605 : Blo 610295 827605 := bbase (se 7 (by rfl) ⟨9698, by rfl⟩ : syracuseStep 827605 = 19397) (by norm_num)
theorem B2072789 : Blo 610295 2072789 := bbase (se 7 (by rfl) ⟨24290, by rfl⟩ : syracuseStep 2072789 = 48581) (by norm_num)
theorem B1548517 : Blo 610295 1548517 := bbase (se 4 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 1548517 = 290347) (by norm_num)
theorem B827653 : Blo 610295 827653 := bbase (se 4 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 827653 = 155185) (by norm_num)
theorem B1548629 : Blo 610295 1548629 := bbase (se 10 (by rfl) ⟨2268, by rfl⟩ : syracuseStep 1548629 = 4537) (by norm_num)
theorem B1745317 : Blo 610295 1745317 := bbase (se 4 (by rfl) ⟨163623, by rfl⟩ : syracuseStep 1745317 = 327247) (by norm_num)
theorem B1548821 : Blo 610295 1548821 := bbase (se 6 (by rfl) ⟨36300, by rfl⟩ : syracuseStep 1548821 = 72601) (by norm_num)
theorem B2073221 : Blo 610295 2073221 := bbase (se 4 (by rfl) ⟨194364, by rfl⟩ : syracuseStep 2073221 = 388729) (by norm_num)
theorem B2794277 : Blo 610295 2794277 := bbase (se 4 (by rfl) ⟨261963, by rfl⟩ : syracuseStep 2794277 = 523927) (by norm_num)
theorem B1549165 : Blo 610295 1549165 := bbase (se 3 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 1549165 = 580937) (by norm_num)
theorem B4662197 : Blo 610295 4662197 := bbase (se 5 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 4662197 = 437081) (by norm_num)
theorem B1549277 : Blo 610295 1549277 := bbase (se 3 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 1549277 = 580979) (by norm_num)
theorem B6956117 : Blo 610295 6956117 := bbase (se 8 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 6956117 = 81517) (by norm_num)
theorem B1549469 : Blo 610295 1549469 := bbase (se 3 (by rfl) ⟨290525, by rfl⟩ : syracuseStep 1549469 = 581051) (by norm_num)
theorem B1254637 : Blo 610295 1254637 := bbase (se 3 (by rfl) ⟨235244, by rfl⟩ : syracuseStep 1254637 = 470489) (by norm_num)
theorem B1549813 : Blo 610295 1549813 := bbase (se 5 (by rfl) ⟨72647, by rfl⟩ : syracuseStep 1549813 = 145295) (by norm_num)
theorem B1549925 : Blo 610295 1549925 := bbase (se 4 (by rfl) ⟨145305, by rfl⟩ : syracuseStep 1549925 = 290611) (by norm_num)
theorem B3090149 : Blo 610295 3090149 := bbase (se 4 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 3090149 = 579403) (by norm_num)
theorem B1550117 : Blo 610295 1550117 := bbase (se 4 (by rfl) ⟨145323, by rfl⟩ : syracuseStep 1550117 = 290647) (by norm_num)
theorem B1812325 : Blo 610295 1812325 := bbase (se 4 (by rfl) ⟨169905, by rfl⟩ : syracuseStep 1812325 = 339811) (by norm_num)
theorem B1746821 : Blo 610295 1746821 := bbase (se 4 (by rfl) ⟨163764, by rfl⟩ : syracuseStep 1746821 = 327529) (by norm_num)
theorem B1550461 : Blo 610295 1550461 := bbase (se 3 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 1550461 = 581423) (by norm_num)
theorem B6629525 : Blo 610295 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B698533 : Blo 610295 698533 := bbase (se 4 (by rfl) ⟨65487, by rfl⟩ : syracuseStep 698533 = 130975) (by norm_num)
theorem B1550573 : Blo 610295 1550573 := bbase (se 3 (by rfl) ⟨290732, by rfl⟩ : syracuseStep 1550573 = 581465) (by norm_num)
theorem B993629 : Blo 610295 993629 := bbase (se 3 (by rfl) ⟨186305, by rfl⟩ : syracuseStep 993629 = 372611) (by norm_num)
theorem B1550765 : Blo 610295 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B830069 : Blo 610295 830069 := bbase (se 5 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 830069 = 77819) (by norm_num)
theorem B1551109 : Blo 610295 1551109 := bbase (se 4 (by rfl) ⟨145416, by rfl⟩ : syracuseStep 1551109 = 290833) (by norm_num)
theorem B1551221 : Blo 610295 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B6269845 : Blo 610295 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B3091445 : Blo 610295 3091445 := bbase (se 5 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 3091445 = 289823) (by norm_num)
theorem B1551413 : Blo 610295 1551413 := bbase (se 5 (by rfl) ⟨72722, by rfl⟩ : syracuseStep 1551413 = 145445) (by norm_num)
theorem B1551757 : Blo 610295 1551757 := bbase (se 3 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 1551757 = 581909) (by norm_num)
theorem B4402613 : Blo 610295 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B1748405 : Blo 610295 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B2207189 : Blo 610295 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B1551869 : Blo 610295 1551869 := bbase (se 3 (by rfl) ⟨290975, by rfl⟩ : syracuseStep 1551869 = 581951) (by norm_num)
theorem B2207333 : Blo 610295 2207333 := bbase (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) (by norm_num)
theorem B1552061 : Blo 610295 1552061 := bbase (se 3 (by rfl) ⟨291011, by rfl⟩ : syracuseStep 1552061 = 582023) (by norm_num)
theorem B1552405 : Blo 610295 1552405 := bbase (se 6 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 1552405 = 72769) (by norm_num)
theorem B700445 : Blo 610295 700445 := bbase (se 3 (by rfl) ⟨131333, by rfl⟩ : syracuseStep 700445 = 262667) (by norm_num)
theorem B1749077 : Blo 610295 1749077 := bbase (se 8 (by rfl) ⟨10248, by rfl⟩ : syracuseStep 1749077 = 20497) (by norm_num)
theorem B929893 : Blo 610295 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B1159285 : Blo 610295 1159285 := bbase (se 5 (by rfl) ⟨54341, by rfl⟩ : syracuseStep 1159285 = 108683) (by norm_num)
theorem B1552517 : Blo 610295 1552517 := bbase (se 4 (by rfl) ⟨145548, by rfl⟩ : syracuseStep 1552517 = 291097) (by norm_num)
theorem B1159429 : Blo 610295 1159429 := bbase (se 4 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 1159429 = 217393) (by norm_num)
theorem B3092741 : Blo 610295 3092741 := bbase (se 4 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 3092741 = 579889) (by norm_num)
theorem B1552709 : Blo 610295 1552709 := bbase (se 4 (by rfl) ⟨145566, by rfl⟩ : syracuseStep 1552709 = 291133) (by norm_num)
theorem B1159589 : Blo 610295 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B1159733 : Blo 610295 1159733 := bbase (se 5 (by rfl) ⟨54362, by rfl⟩ : syracuseStep 1159733 = 108725) (by norm_num)
theorem B1553053 : Blo 610295 1553053 := bbase (se 3 (by rfl) ⟨291197, by rfl⟩ : syracuseStep 1553053 = 582395) (by norm_num)
theorem B733865 : Blo 610295 733865 := bbase (se 2 (by rfl) ⟨275199, by rfl⟩ : syracuseStep 733865 = 550399) (by norm_num)
theorem B766657 : Blo 610295 766657 := bbase (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) (by norm_num)
theorem B996085 : Blo 610295 996085 := bbase (se 5 (by rfl) ⟨46691, by rfl⟩ : syracuseStep 996085 = 93383) (by norm_num)
theorem B1553165 : Blo 610295 1553165 := bbase (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) (by norm_num)
theorem B1160021 : Blo 610295 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1553357 : Blo 610295 1553357 := bbase (se 3 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 1553357 = 582509) (by norm_num)
theorem B1160173 : Blo 610295 1160173 := bbase (se 3 (by rfl) ⟨217532, by rfl⟩ : syracuseStep 1160173 = 435065) (by norm_num)
theorem B1160477 : Blo 610295 1160477 := bbase (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) (by norm_num)
theorem B1553701 : Blo 610295 1553701 := bbase (se 4 (by rfl) ⟨145659, by rfl⟩ : syracuseStep 1553701 = 291319) (by norm_num)
theorem B734557 : Blo 610295 734557 := bbase (se 3 (by rfl) ⟨137729, by rfl⟩ : syracuseStep 734557 = 275459) (by norm_num)
theorem B1553813 : Blo 610295 1553813 := bbase (se 6 (by rfl) ⟨36417, by rfl⟩ : syracuseStep 1553813 = 72835) (by norm_num)
theorem B734653 : Blo 610295 734653 := bbase (se 3 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 734653 = 275495) (by norm_num)
theorem B3094037 : Blo 610295 3094037 := bbase (se 6 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 3094037 = 145033) (by norm_num)
theorem B1554005 : Blo 610295 1554005 := bbase (se 8 (by rfl) ⟨9105, by rfl⟩ : syracuseStep 1554005 = 18211) (by norm_num)
theorem B3487445 : Blo 610295 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B997085 : Blo 610295 997085 := bbase (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) (by norm_num)
theorem B1029901 : Blo 610295 1029901 := bbase (se 3 (by rfl) ⟨193106, by rfl⟩ : syracuseStep 1029901 = 386213) (by norm_num)
theorem B735037 : Blo 610295 735037 := bbase (se 3 (by rfl) ⟨137819, by rfl⟩ : syracuseStep 735037 = 275639) (by norm_num)
theorem B1029989 : Blo 610295 1029989 := bbase (se 4 (by rfl) ⟨96561, by rfl⟩ : syracuseStep 1029989 = 193123) (by norm_num)
theorem B1554349 : Blo 610295 1554349 := bbase (se 3 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 1554349 = 582881) (by norm_num)
theorem B1030117 : Blo 610295 1030117 := bbase (se 4 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 1030117 = 193147) (by norm_num)
theorem B1161229 : Blo 610295 1161229 := bbase (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) (by norm_num)
theorem B1554461 : Blo 610295 1554461 := bbase (se 3 (by rfl) ⟨291461, by rfl⟩ : syracuseStep 1554461 = 582923) (by norm_num)
theorem B1030205 : Blo 610295 1030205 := bbase (se 3 (by rfl) ⟨193163, by rfl⟩ : syracuseStep 1030205 = 386327) (by norm_num)
theorem B1161373 : Blo 610295 1161373 := bbase (se 3 (by rfl) ⟨217757, by rfl⟩ : syracuseStep 1161373 = 435515) (by norm_num)
theorem B1030333 : Blo 610295 1030333 := bbase (se 3 (by rfl) ⟨193187, by rfl⟩ : syracuseStep 1030333 = 386375) (by norm_num)
theorem B1554653 : Blo 610295 1554653 := bbase (se 3 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 1554653 = 582995) (by norm_num)
theorem B932077 : Blo 610295 932077 := bbase (se 3 (by rfl) ⟨174764, by rfl⟩ : syracuseStep 932077 = 349529) (by norm_num)
theorem B1030421 : Blo 610295 1030421 := bbase (se 6 (by rfl) ⟨24150, by rfl⟩ : syracuseStep 1030421 = 48301) (by norm_num)
theorem B1161533 : Blo 610295 1161533 := bbase (se 3 (by rfl) ⟨217787, by rfl⟩ : syracuseStep 1161533 = 435575) (by norm_num)
theorem B188627285 : Blo 610295 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B1030549 : Blo 610295 1030549 := bbase (se 6 (by rfl) ⟨24153, by rfl⟩ : syracuseStep 1030549 = 48307) (by norm_num)
theorem B1161677 : Blo 610295 1161677 := bbase (se 3 (by rfl) ⟨217814, by rfl⟩ : syracuseStep 1161677 = 435629) (by norm_num)
theorem B1030637 : Blo 610295 1030637 := bbase (se 3 (by rfl) ⟨193244, by rfl⟩ : syracuseStep 1030637 = 386489) (by norm_num)
theorem B1030765 : Blo 610295 1030765 := bbase (se 3 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 1030765 = 386537) (by norm_num)
theorem B1030853 : Blo 610295 1030853 := bbase (se 4 (by rfl) ⟨96642, by rfl⟩ : syracuseStep 1030853 = 193285) (by norm_num)
theorem B1161965 : Blo 610295 1161965 := bbase (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) (by norm_num)
theorem B3095333 : Blo 610295 3095333 := bbase (se 4 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 3095333 = 580375) (by norm_num)
theorem B1030981 : Blo 610295 1030981 := bbase (se 4 (by rfl) ⟨96654, by rfl⟩ : syracuseStep 1030981 = 193309) (by norm_num)
theorem B736085 : Blo 610295 736085 := bbase (se 9 (by rfl) ⟨2156, by rfl⟩ : syracuseStep 736085 = 4313) (by norm_num)
theorem B22362965 : Blo 610295 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B3488629 : Blo 610295 3488629 := bbase (se 5 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 3488629 = 327059) (by norm_num)
theorem B1162117 : Blo 610295 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B1031069 : Blo 610295 1031069 := bbase (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) (by norm_num)
theorem B1653749 : Blo 610295 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B1031197 : Blo 610295 1031197 := bbase (se 3 (by rfl) ⟨193349, by rfl⟩ : syracuseStep 1031197 = 386699) (by norm_num)
theorem B1031285 : Blo 610295 1031285 := bbase (se 5 (by rfl) ⟨48341, by rfl⟩ : syracuseStep 1031285 = 96683) (by norm_num)
theorem B736393 : Blo 610295 736393 := bbase (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) (by norm_num)
theorem B736421 : Blo 610295 736421 := bbase (se 4 (by rfl) ⟨69039, by rfl⟩ : syracuseStep 736421 = 138079) (by norm_num)
theorem B1162421 : Blo 610295 1162421 := bbase (se 5 (by rfl) ⟨54488, by rfl⟩ : syracuseStep 1162421 = 108977) (by norm_num)
theorem B1031413 : Blo 610295 1031413 := bbase (se 5 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 1031413 = 96695) (by norm_num)
theorem B1326365 : Blo 610295 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B1031501 : Blo 610295 1031501 := bbase (se 3 (by rfl) ⟨193406, by rfl⟩ : syracuseStep 1031501 = 386813) (by norm_num)
theorem B3915125 : Blo 610295 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B1031629 : Blo 610295 1031629 := bbase (se 3 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 1031629 = 386861) (by norm_num)
theorem B1031717 : Blo 610295 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B933445 : Blo 610295 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B736921 : Blo 610295 736921 := bbase (se 2 (by rfl) ⟨276345, by rfl⟩ : syracuseStep 736921 = 552691) (by norm_num)
theorem B1031845 : Blo 610295 1031845 := bbase (se 4 (by rfl) ⟨96735, by rfl⟩ : syracuseStep 1031845 = 193471) (by norm_num)
theorem B1031933 : Blo 610295 1031933 := bbase (se 3 (by rfl) ⟨193487, by rfl⟩ : syracuseStep 1031933 = 386975) (by norm_num)
theorem B1032061 : Blo 610295 1032061 := bbase (se 3 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 1032061 = 387023) (by norm_num)
theorem B638857 : Blo 610295 638857 := bbase (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) (by norm_num)
theorem B933781 : Blo 610295 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B1163173 : Blo 610295 1163173 := bbase (se 4 (by rfl) ⟨109047, by rfl⟩ : syracuseStep 1163173 = 218095) (by norm_num)
theorem B1032149 : Blo 610295 1032149 := bbase (se 7 (by rfl) ⟨12095, by rfl⟩ : syracuseStep 1032149 = 24191) (by norm_num)
theorem B5947445 : Blo 610295 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B3096629 : Blo 610295 3096629 := bbase (se 5 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 3096629 = 290309) (by norm_num)
theorem B1163317 : Blo 610295 1163317 := bbase (se 5 (by rfl) ⟨54530, by rfl⟩ : syracuseStep 1163317 = 109061) (by norm_num)
theorem B1032277 : Blo 610295 1032277 := bbase (se 8 (by rfl) ⟨6048, by rfl⟩ : syracuseStep 1032277 = 12097) (by norm_num)
theorem B1491029 : Blo 610295 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B1032365 : Blo 610295 1032365 := bbase (se 3 (by rfl) ⟨193568, by rfl⟩ : syracuseStep 1032365 = 387137) (by norm_num)
theorem B1163477 : Blo 610295 1163477 := bbase (se 7 (by rfl) ⟨13634, by rfl⟩ : syracuseStep 1163477 = 27269) (by norm_num)
theorem B1327333 : Blo 610295 1327333 := bbase (se 4 (by rfl) ⟨124437, by rfl⟩ : syracuseStep 1327333 = 248875) (by norm_num)
theorem B1032493 : Blo 610295 1032493 := bbase (se 3 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 1032493 = 387185) (by norm_num)
theorem B1163621 : Blo 610295 1163621 := bbase (se 4 (by rfl) ⟨109089, by rfl⟩ : syracuseStep 1163621 = 218179) (by norm_num)
theorem B1032581 : Blo 610295 1032581 := bbase (se 4 (by rfl) ⟨96804, by rfl⟩ : syracuseStep 1032581 = 193609) (by norm_num)
theorem B639389 : Blo 610295 639389 := bbase (se 3 (by rfl) ⟨119885, by rfl⟩ : syracuseStep 639389 = 239771) (by norm_num)
theorem B1032709 : Blo 610295 1032709 := bbase (se 4 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 1032709 = 193633) (by norm_num)
theorem B1032797 : Blo 610295 1032797 := bbase (se 3 (by rfl) ⟨193649, by rfl⟩ : syracuseStep 1032797 = 387299) (by norm_num)
theorem B1163909 : Blo 610295 1163909 := bbase (se 4 (by rfl) ⟨109116, by rfl⟩ : syracuseStep 1163909 = 218233) (by norm_num)
theorem B1491605 : Blo 610295 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B1032925 : Blo 610295 1032925 := bbase (se 3 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 1032925 = 387347) (by norm_num)
theorem B1164061 : Blo 610295 1164061 := bbase (se 3 (by rfl) ⟨218261, by rfl⟩ : syracuseStep 1164061 = 436523) (by norm_num)
theorem B1393453 : Blo 610295 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B1033013 : Blo 610295 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B3490613 : Blo 610295 3490613 := bbase (se 5 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 3490613 = 327245) (by norm_num)
theorem B1033141 : Blo 610295 1033141 := bbase (se 5 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 1033141 = 96857) (by norm_num)
theorem B1033229 : Blo 610295 1033229 := bbase (se 3 (by rfl) ⟨193730, by rfl⟩ : syracuseStep 1033229 = 387461) (by norm_num)
theorem B1164365 : Blo 610295 1164365 := bbase (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) (by norm_num)
theorem B1033357 : Blo 610295 1033357 := bbase (se 3 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 1033357 = 387509) (by norm_num)
theorem B1033445 : Blo 610295 1033445 := bbase (se 4 (by rfl) ⟨96885, by rfl⟩ : syracuseStep 1033445 = 193771) (by norm_num)
theorem B869629 : Blo 610295 869629 := bbase (se 3 (by rfl) ⟨163055, by rfl⟩ : syracuseStep 869629 = 326111) (by norm_num)
theorem B3097925 : Blo 610295 3097925 := bbase (se 4 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 3097925 = 580861) (by norm_num)
theorem B1033573 : Blo 610295 1033573 := bbase (se 4 (by rfl) ⟨96897, by rfl⟩ : syracuseStep 1033573 = 193795) (by norm_num)
theorem B1033661 : Blo 610295 1033661 := bbase (se 3 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 1033661 = 387623) (by norm_num)
theorem B1033789 : Blo 610295 1033789 := bbase (se 3 (by rfl) ⟨193835, by rfl⟩ : syracuseStep 1033789 = 387671) (by norm_num)
theorem B1033877 : Blo 610295 1033877 := bbase (se 6 (by rfl) ⟨24231, by rfl⟩ : syracuseStep 1033877 = 48463) (by norm_num)
theorem B3032821 : Blo 610295 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B1034005 : Blo 610295 1034005 := bbase (se 6 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 1034005 = 48469) (by norm_num)
theorem B1165117 : Blo 610295 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B870221 : Blo 610295 870221 := bbase (se 3 (by rfl) ⟨163166, by rfl⟩ : syracuseStep 870221 = 326333) (by norm_num)
theorem B1034093 : Blo 610295 1034093 := bbase (se 3 (by rfl) ⟨193892, by rfl⟩ : syracuseStep 1034093 = 387785) (by norm_num)
theorem B870301 : Blo 610295 870301 := bbase (se 3 (by rfl) ⟨163181, by rfl⟩ : syracuseStep 870301 = 326363) (by norm_num)
theorem B1394621 : Blo 610295 1394621 := bbase (se 3 (by rfl) ⟨261491, by rfl⟩ : syracuseStep 1394621 = 522983) (by norm_num)
theorem B1165261 : Blo 610295 1165261 := bbase (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) (by norm_num)
theorem B1034221 : Blo 610295 1034221 := bbase (se 3 (by rfl) ⟨193916, by rfl⟩ : syracuseStep 1034221 = 387833) (by norm_num)
theorem B870421 : Blo 610295 870421 := bbase (se 6 (by rfl) ⟨20400, by rfl⟩ : syracuseStep 870421 = 40801) (by norm_num)
theorem B4769813 : Blo 610295 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1034309 : Blo 610295 1034309 := bbase (se 4 (by rfl) ⟨96966, by rfl⟩ : syracuseStep 1034309 = 193933) (by norm_num)
theorem B1165421 : Blo 610295 1165421 := bbase (se 3 (by rfl) ⟨218516, by rfl⟩ : syracuseStep 1165421 = 437033) (by norm_num)
theorem B870517 : Blo 610295 870517 := bbase (se 5 (by rfl) ⟨40805, by rfl⟩ : syracuseStep 870517 = 81611) (by norm_num)
theorem B4638869 : Blo 610295 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B1034437 : Blo 610295 1034437 := bbase (se 4 (by rfl) ⟨96978, by rfl⟩ : syracuseStep 1034437 = 193957) (by norm_num)
theorem B2607349 : Blo 610295 2607349 := bbase (se 5 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 2607349 = 244439) (by norm_num)
theorem B1165565 : Blo 610295 1165565 := bbase (se 3 (by rfl) ⟨218543, by rfl⟩ : syracuseStep 1165565 = 437087) (by norm_num)
theorem B805141 : Blo 610295 805141 := bbase (se 6 (by rfl) ⟨18870, by rfl⟩ : syracuseStep 805141 = 37741) (by norm_num)
theorem B1034525 : Blo 610295 1034525 := bbase (se 3 (by rfl) ⟨193973, by rfl⟩ : syracuseStep 1034525 = 387947) (by norm_num)
theorem B1034653 : Blo 610295 1034653 := bbase (se 3 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 1034653 = 387995) (by norm_num)
theorem B772517 : Blo 610295 772517 := bbase (se 4 (by rfl) ⟨72423, by rfl⟩ : syracuseStep 772517 = 144847) (by norm_num)
theorem B5228981 : Blo 610295 5228981 := bbase (se 5 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 5228981 = 490217) (by norm_num)
theorem B772573 : Blo 610295 772573 := bbase (se 3 (by rfl) ⟨144857, by rfl⟩ : syracuseStep 772573 = 289715) (by norm_num)
theorem B1034741 : Blo 610295 1034741 := bbase (se 5 (by rfl) ⟨48503, by rfl⟩ : syracuseStep 1034741 = 97007) (by norm_num)
theorem B1165853 : Blo 610295 1165853 := bbase (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) (by norm_num)
theorem B772669 : Blo 610295 772669 := bbase (se 3 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 772669 = 289751) (by norm_num)
theorem B3099221 : Blo 610295 3099221 := bbase (se 8 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 3099221 = 36319) (by norm_num)
theorem B871013 : Blo 610295 871013 := bbase (se 4 (by rfl) ⟨81657, by rfl⟩ : syracuseStep 871013 = 163315) (by norm_num)
theorem B1034869 : Blo 610295 1034869 := bbase (se 5 (by rfl) ⟨48509, by rfl⟩ : syracuseStep 1034869 = 97019) (by norm_num)
theorem B1166005 : Blo 610295 1166005 := bbase (se 5 (by rfl) ⟨54656, by rfl⟩ : syracuseStep 1166005 = 109313) (by norm_num)
theorem B1034957 : Blo 610295 1034957 := bbase (se 3 (by rfl) ⟨194054, by rfl⟩ : syracuseStep 1034957 = 388109) (by norm_num)
theorem B772841 : Blo 610295 772841 := bbase (se 2 (by rfl) ⟨289815, by rfl⟩ : syracuseStep 772841 = 579631) (by norm_num)
theorem B772897 : Blo 610295 772897 := bbase (se 2 (by rfl) ⟨289836, by rfl⟩ : syracuseStep 772897 = 579673) (by norm_num)
theorem B1395533 : Blo 610295 1395533 := bbase (se 3 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 1395533 = 523325) (by norm_num)
theorem B1035085 : Blo 610295 1035085 := bbase (se 3 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 1035085 = 388157) (by norm_num)
theorem B772993 : Blo 610295 772993 := bbase (se 2 (by rfl) ⟨289872, by rfl⟩ : syracuseStep 772993 = 579745) (by norm_num)
theorem B1035173 : Blo 610295 1035173 := bbase (se 4 (by rfl) ⟨97047, by rfl⟩ : syracuseStep 1035173 = 194095) (by norm_num)
theorem B3492821 : Blo 610295 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B1657813 : Blo 610295 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B1035301 : Blo 610295 1035301 := bbase (se 4 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 1035301 = 194119) (by norm_num)
theorem B773165 : Blo 610295 773165 := bbase (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) (by norm_num)
theorem B773221 : Blo 610295 773221 := bbase (se 4 (by rfl) ⟨72489, by rfl⟩ : syracuseStep 773221 = 144979) (by norm_num)
theorem B1035389 : Blo 610295 1035389 := bbase (se 3 (by rfl) ⟨194135, by rfl⟩ : syracuseStep 1035389 = 388271) (by norm_num)
theorem B1100941 : Blo 610295 1100941 := bbase (se 3 (by rfl) ⟨206426, by rfl⟩ : syracuseStep 1100941 = 412853) (by norm_num)
theorem B871565 : Blo 610295 871565 := bbase (se 3 (by rfl) ⟨163418, by rfl⟩ : syracuseStep 871565 = 326837) (by norm_num)
theorem B773317 : Blo 610295 773317 := bbase (se 4 (by rfl) ⟨72498, by rfl⟩ : syracuseStep 773317 = 144997) (by norm_num)
theorem B1035517 : Blo 610295 1035517 := bbase (se 3 (by rfl) ⟨194159, by rfl⟩ : syracuseStep 1035517 = 388319) (by norm_num)
theorem B1035605 : Blo 610295 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B773489 : Blo 610295 773489 := bbase (se 2 (by rfl) ⟨290058, by rfl⟩ : syracuseStep 773489 = 580117) (by norm_num)
theorem B773545 : Blo 610295 773545 := bbase (se 2 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 773545 = 580159) (by norm_num)
theorem B1035733 : Blo 610295 1035733 := bbase (se 7 (by rfl) ⟨12137, by rfl⟩ : syracuseStep 1035733 = 24275) (by norm_num)
theorem B773641 : Blo 610295 773641 := bbase (se 2 (by rfl) ⟨290115, by rfl⟩ : syracuseStep 773641 = 580231) (by norm_num)
theorem B1035821 : Blo 610295 1035821 := bbase (se 3 (by rfl) ⟨194216, by rfl⟩ : syracuseStep 1035821 = 388433) (by norm_num)
theorem B1035949 : Blo 610295 1035949 := bbase (se 3 (by rfl) ⟨194240, by rfl⟩ : syracuseStep 1035949 = 388481) (by norm_num)
theorem B773813 : Blo 610295 773813 := bbase (se 5 (by rfl) ⟨36272, by rfl⟩ : syracuseStep 773813 = 72545) (by norm_num)
theorem B19910357 : Blo 610295 19910357 := bbase (se 7 (by rfl) ⟨233324, by rfl⟩ : syracuseStep 19910357 = 466649) (by norm_num)
theorem B1396445 : Blo 610295 1396445 := bbase (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) (by norm_num)
theorem B773869 : Blo 610295 773869 := bbase (se 3 (by rfl) ⟨145100, by rfl⟩ : syracuseStep 773869 = 290201) (by norm_num)
theorem B1036037 : Blo 610295 1036037 := bbase (se 4 (by rfl) ⟨97128, by rfl⟩ : syracuseStep 1036037 = 194257) (by norm_num)
theorem B773965 : Blo 610295 773965 := bbase (se 3 (by rfl) ⟨145118, by rfl⟩ : syracuseStep 773965 = 290237) (by norm_num)
theorem B3100517 : Blo 610295 3100517 := bbase (se 4 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 3100517 = 581347) (by norm_num)
theorem B872317 : Blo 610295 872317 := bbase (se 3 (by rfl) ⟨163559, by rfl⟩ : syracuseStep 872317 = 327119) (by norm_num)
theorem B1036165 : Blo 610295 1036165 := bbase (se 4 (by rfl) ⟨97140, by rfl⟩ : syracuseStep 1036165 = 194281) (by norm_num)
theorem B708545 : Blo 610295 708545 := bbase (se 2 (by rfl) ⟨265704, by rfl⟩ : syracuseStep 708545 = 531409) (by norm_num)
theorem B1036253 : Blo 610295 1036253 := bbase (se 3 (by rfl) ⟨194297, by rfl⟩ : syracuseStep 1036253 = 388595) (by norm_num)
theorem B774137 : Blo 610295 774137 := bbase (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) (by norm_num)
theorem B1101821 : Blo 610295 1101821 := bbase (se 3 (by rfl) ⟨206591, by rfl⟩ : syracuseStep 1101821 = 413183) (by norm_num)
theorem B774193 : Blo 610295 774193 := bbase (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) (by norm_num)
theorem B3723317 : Blo 610295 3723317 := bbase (se 5 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 3723317 = 349061) (by norm_num)
theorem B1036381 : Blo 610295 1036381 := bbase (se 3 (by rfl) ⟨194321, by rfl⟩ : syracuseStep 1036381 = 388643) (by norm_num)
theorem B774289 : Blo 610295 774289 := bbase (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) (by norm_num)
theorem B1036469 : Blo 610295 1036469 := bbase (se 5 (by rfl) ⟨48584, by rfl⟩ : syracuseStep 1036469 = 97169) (by norm_num)
theorem B1036597 : Blo 610295 1036597 := bbase (se 5 (by rfl) ⟨48590, by rfl⟩ : syracuseStep 1036597 = 97181) (by norm_num)
theorem B774461 : Blo 610295 774461 := bbase (se 3 (by rfl) ⟨145211, by rfl⟩ : syracuseStep 774461 = 290423) (by norm_num)
theorem B774517 : Blo 610295 774517 := bbase (se 5 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 774517 = 72611) (by norm_num)
theorem B774613 : Blo 610295 774613 := bbase (se 7 (by rfl) ⟨9077, by rfl⟩ : syracuseStep 774613 = 18155) (by norm_num)
theorem B774785 : Blo 610295 774785 := bbase (se 2 (by rfl) ⟨290544, by rfl⟩ : syracuseStep 774785 = 581089) (by norm_num)
theorem B873109 : Blo 610295 873109 := bbase (se 6 (by rfl) ⟨20463, by rfl⟩ : syracuseStep 873109 = 40927) (by norm_num)
theorem B774841 : Blo 610295 774841 := bbase (se 2 (by rfl) ⟨290565, by rfl⟩ : syracuseStep 774841 = 581131) (by norm_num)
theorem B7951061 : Blo 610295 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B1659653 : Blo 610295 1659653 := bbase (se 4 (by rfl) ⟨155592, by rfl⟩ : syracuseStep 1659653 = 311185) (by norm_num)
theorem B774937 : Blo 610295 774937 := bbase (se 2 (by rfl) ⟨290601, by rfl⟩ : syracuseStep 774937 = 581203) (by norm_num)
theorem B1856405 : Blo 610295 1856405 := bbase (se 6 (by rfl) ⟨43509, by rfl⟩ : syracuseStep 1856405 = 87019) (by norm_num)
theorem B807841 : Blo 610295 807841 := bbase (se 2 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 807841 = 605881) (by norm_num)
theorem B775109 : Blo 610295 775109 := bbase (se 4 (by rfl) ⟨72666, by rfl⟩ : syracuseStep 775109 = 145333) (by norm_num)
theorem B873445 : Blo 610295 873445 := bbase (se 4 (by rfl) ⟨81885, by rfl⟩ : syracuseStep 873445 = 163771) (by norm_num)
theorem B775165 : Blo 610295 775165 := bbase (se 3 (by rfl) ⟨145343, by rfl⟩ : syracuseStep 775165 = 290687) (by norm_num)
theorem B775261 : Blo 610295 775261 := bbase (se 3 (by rfl) ⟨145361, by rfl⟩ : syracuseStep 775261 = 290723) (by norm_num)
theorem B3101813 : Blo 610295 3101813 := bbase (se 5 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 3101813 = 290795) (by norm_num)
theorem B873661 : Blo 610295 873661 := bbase (se 3 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 873661 = 327623) (by norm_num)
theorem B775433 : Blo 610295 775433 := bbase (se 2 (by rfl) ⟨290787, by rfl⟩ : syracuseStep 775433 = 581575) (by norm_num)
theorem B2938133 : Blo 610295 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B775489 : Blo 610295 775489 := bbase (se 2 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 775489 = 581617) (by norm_num)
theorem B775585 : Blo 610295 775585 := bbase (se 2 (by rfl) ⟨290844, by rfl⟩ : syracuseStep 775585 = 581689) (by norm_num)
theorem B1955269 : Blo 610295 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B1955333 : Blo 610295 1955333 := bbase (se 4 (by rfl) ⟨183312, by rfl⟩ : syracuseStep 1955333 = 366625) (by norm_num)
theorem B874037 : Blo 610295 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B775757 : Blo 610295 775757 := bbase (se 3 (by rfl) ⟨145454, by rfl⟩ : syracuseStep 775757 = 290909) (by norm_num)
theorem B775813 : Blo 610295 775813 := bbase (se 4 (by rfl) ⟨72732, by rfl⟩ : syracuseStep 775813 = 145465) (by norm_num)
theorem B775909 : Blo 610295 775909 := bbase (se 4 (by rfl) ⟨72741, by rfl⟩ : syracuseStep 775909 = 145483) (by norm_num)
theorem B776081 : Blo 610295 776081 := bbase (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) (by norm_num)
theorem B2938805 : Blo 610295 2938805 := bbase (se 5 (by rfl) ⟨137756, by rfl⟩ : syracuseStep 2938805 = 275513) (by norm_num)
theorem B776137 : Blo 610295 776137 := bbase (se 2 (by rfl) ⟨291051, by rfl⟩ : syracuseStep 776137 = 582103) (by norm_num)
theorem B776233 : Blo 610295 776233 := bbase (se 2 (by rfl) ⟨291087, by rfl⟩ : syracuseStep 776233 = 582175) (by norm_num)
theorem B776405 : Blo 610295 776405 := bbase (se 7 (by rfl) ⟨9098, by rfl⟩ : syracuseStep 776405 = 18197) (by norm_num)
theorem B776461 : Blo 610295 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B776557 : Blo 610295 776557 := bbase (se 3 (by rfl) ⟨145604, by rfl⟩ : syracuseStep 776557 = 291209) (by norm_num)
theorem B1857925 : Blo 610295 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B3103109 : Blo 610295 3103109 := bbase (se 4 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 3103109 = 581833) (by norm_num)
theorem B776729 : Blo 610295 776729 := bbase (se 2 (by rfl) ⟨291273, by rfl⟩ : syracuseStep 776729 = 582547) (by norm_num)
theorem B1858085 : Blo 610295 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B776785 : Blo 610295 776785 := bbase (se 2 (by rfl) ⟨291294, by rfl⟩ : syracuseStep 776785 = 582589) (by norm_num)
theorem B3136133 : Blo 610295 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B1432205 : Blo 610295 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B776881 : Blo 610295 776881 := bbase (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) (by norm_num)
theorem B1399621 : Blo 610295 1399621 := bbase (se 4 (by rfl) ⟨131214, by rfl⟩ : syracuseStep 1399621 = 262429) (by norm_num)
theorem B777053 : Blo 610295 777053 := bbase (se 3 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 777053 = 291395) (by norm_num)
theorem B777109 : Blo 610295 777109 := bbase (se 6 (by rfl) ⟨18213, by rfl⟩ : syracuseStep 777109 = 36427) (by norm_num)
theorem B940997 : Blo 610295 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B777205 : Blo 610295 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B2612357 : Blo 610295 2612357 := bbase (se 4 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 2612357 = 489817) (by norm_num)
theorem B777377 : Blo 610295 777377 := bbase (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) (by norm_num)
theorem B1105093 : Blo 610295 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B777433 : Blo 610295 777433 := bbase (se 2 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 777433 = 583075) (by norm_num)
theorem B2612645 : Blo 610295 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B1990117 : Blo 610295 1990117 := bbase (se 4 (by rfl) ⟨186573, by rfl⟩ : syracuseStep 1990117 = 373147) (by norm_num)
theorem B1859093 : Blo 610295 1859093 := bbase (se 6 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 1859093 = 87145) (by norm_num)
theorem B3726965 : Blo 610295 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B1793669 : Blo 610295 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B3104405 : Blo 610295 3104405 := bbase (se 6 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 3104405 = 145519) (by norm_num)
theorem B1892165 : Blo 610295 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1105901 : Blo 610295 1105901 := bbase (se 3 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 1105901 = 414713) (by norm_num)
theorem B2318341 : Blo 610295 2318341 := bbase (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) (by norm_num)
theorem B1466461 : Blo 610295 1466461 := bbase (se 3 (by rfl) ⟨274961, by rfl⟩ : syracuseStep 1466461 = 549923) (by norm_num)
theorem B2613397 : Blo 610295 2613397 := bbase (se 6 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 2613397 = 122503) (by norm_num)
theorem B2318645 : Blo 610295 2318645 := bbase (se 5 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 2318645 = 217373) (by norm_num)
theorem B1958357 : Blo 610295 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B1466885 : Blo 610295 1466885 := bbase (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) (by norm_num)
theorem B3302005 : Blo 610295 3302005 := bbase (se 5 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 3302005 = 309563) (by norm_num)
theorem B1237717 : Blo 610295 1237717 := bbase (se 7 (by rfl) ⟨14504, by rfl⟩ : syracuseStep 1237717 = 29009) (by norm_num)
theorem B1237781 : Blo 610295 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B1467173 : Blo 610295 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B2614133 : Blo 610295 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B1303445 : Blo 610295 1303445 := bbase (se 6 (by rfl) ⟨30549, by rfl⟩ : syracuseStep 1303445 = 61099) (by norm_num)
theorem B3105701 : Blo 610295 3105701 := bbase (se 4 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 3105701 = 582319) (by norm_num)
theorem B1303589 : Blo 610295 1303589 := bbase (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) (by norm_num)
theorem B4187861 : Blo 610295 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B4646645 : Blo 610295 4646645 := bbase (se 5 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 4646645 = 435623) (by norm_num)
theorem B1304333 : Blo 610295 1304333 := bbase (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) (by norm_num)
theorem B1238885 : Blo 610295 1238885 := bbase (se 4 (by rfl) ⟨116145, by rfl⟩ : syracuseStep 1238885 = 232291) (by norm_num)
theorem B7858133 : Blo 610295 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B3106997 : Blo 610295 3106997 := bbase (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) (by norm_num)
theorem B1009925 : Blo 610295 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B5237045 : Blo 610295 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B7072085 : Blo 610295 7072085 := bbase (se 10 (by rfl) ⟨10359, by rfl⟩ : syracuseStep 7072085 = 20719) (by norm_num)
theorem B2320757 : Blo 610295 2320757 := bbase (se 5 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 2320757 = 217571) (by norm_num)
theorem B1239437 : Blo 610295 1239437 := bbase (se 3 (by rfl) ⟨232394, by rfl⟩ : syracuseStep 1239437 = 464789) (by norm_num)
theorem B1305085 : Blo 610295 1305085 := bbase (se 3 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 1305085 = 489407) (by norm_num)
theorem B1305229 : Blo 610295 1305229 := bbase (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) (by norm_num)
theorem B2321045 : Blo 610295 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B1305605 : Blo 610295 1305605 := bbase (se 4 (by rfl) ⟨122400, by rfl⟩ : syracuseStep 1305605 = 244801) (by norm_num)
theorem B7826453 : Blo 610295 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B978077 : Blo 610295 978077 := bbase (se 3 (by rfl) ⟨183389, by rfl⟩ : syracuseStep 978077 = 366779) (by norm_num)
theorem B1305973 : Blo 610295 1305973 := bbase (se 5 (by rfl) ⟨61217, by rfl⟩ : syracuseStep 1305973 = 122435) (by norm_num)
theorem B1174981 : Blo 610295 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B3108293 : Blo 610295 3108293 := bbase (se 4 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 3108293 = 582805) (by norm_num)
theorem B978461 : Blo 610295 978461 := bbase (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) (by norm_num)
theorem B2059829 : Blo 610295 2059829 := bbase (se 5 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 2059829 = 193109) (by norm_num)
theorem B978589 : Blo 610295 978589 := bbase (se 3 (by rfl) ⟨183485, by rfl⟩ : syracuseStep 978589 = 366971) (by norm_num)
theorem B2322229 : Blo 610295 2322229 := bbase (se 5 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 2322229 = 217709) (by norm_num)
theorem B1568621 : Blo 610295 1568621 := bbase (se 3 (by rfl) ⟨294116, by rfl⟩ : syracuseStep 1568621 = 588233) (by norm_num)
theorem B1470325 : Blo 610295 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B1699717 : Blo 610295 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B3927989 : Blo 610295 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B2060261 : Blo 610295 2060261 := bbase (se 4 (by rfl) ⟨193149, by rfl⟩ : syracuseStep 2060261 = 386299) (by norm_num)
theorem B2617429 : Blo 610295 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B2322533 : Blo 610295 2322533 := bbase (se 4 (by rfl) ⟨217737, by rfl⟩ : syracuseStep 2322533 = 435475) (by norm_num)
theorem B1241237 : Blo 610295 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B1962149 : Blo 610295 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B618725 : Blo 610295 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B1175789 : Blo 610295 1175789 := bbase (se 3 (by rfl) ⟨220460, by rfl⟩ : syracuseStep 1175789 = 440921) (by norm_num)
theorem B1241413 : Blo 610295 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B2060693 : Blo 610295 2060693 := bbase (se 6 (by rfl) ⟨48297, by rfl⟩ : syracuseStep 2060693 = 96595) (by norm_num)
theorem B1470997 : Blo 610295 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B651893 : Blo 610295 651893 := bbase (se 5 (by rfl) ⟨30557, by rfl⟩ : syracuseStep 651893 = 61115) (by norm_num)
theorem B979589 : Blo 610295 979589 := bbase (se 4 (by rfl) ⟨91836, by rfl⟩ : syracuseStep 979589 = 183673) (by norm_num)
theorem B1569461 : Blo 610295 1569461 := bbase (se 5 (by rfl) ⟨73568, by rfl⟩ : syracuseStep 1569461 = 147137) (by norm_num)
theorem B783049 : Blo 610295 783049 := bbase (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) (by norm_num)
theorem B3109589 : Blo 610295 3109589 := bbase (se 7 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 3109589 = 72881) (by norm_num)
theorem B1471229 : Blo 610295 1471229 := bbase (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) (by norm_num)
theorem B979717 : Blo 610295 979717 := bbase (se 4 (by rfl) ⟨91848, by rfl⟩ : syracuseStep 979717 = 183697) (by norm_num)
theorem B1766165 : Blo 610295 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B619321 : Blo 610295 619321 := bbase (se 2 (by rfl) ⟨232245, by rfl⟩ : syracuseStep 619321 = 464491) (by norm_num)
theorem B2061125 : Blo 610295 2061125 := bbase (se 4 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 2061125 = 386461) (by norm_num)
theorem B1307477 : Blo 610295 1307477 := bbase (se 9 (by rfl) ⟨3830, by rfl⟩ : syracuseStep 1307477 = 7661) (by norm_num)
theorem B5665621 : Blo 610295 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1471373 : Blo 610295 1471373 := bbase (se 3 (by rfl) ⟨275882, by rfl⟩ : syracuseStep 1471373 = 551765) (by norm_num)
theorem B1471421 : Blo 610295 1471421 := bbase (se 3 (by rfl) ⟨275891, by rfl⟩ : syracuseStep 1471421 = 551783) (by norm_num)
theorem B1307621 : Blo 610295 1307621 := bbase (se 4 (by rfl) ⟨122589, by rfl⟩ : syracuseStep 1307621 = 245179) (by norm_num)
theorem B1373165 : Blo 610295 1373165 := bbase (se 3 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 1373165 = 514937) (by norm_num)
theorem B1373237 : Blo 610295 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B1963061 : Blo 610295 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B2126965 : Blo 610295 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B1373309 : Blo 610295 1373309 := bbase (se 3 (by rfl) ⟨257495, by rfl⟩ : syracuseStep 1373309 = 514991) (by norm_num)
theorem B980101 : Blo 610295 980101 := bbase (se 4 (by rfl) ⟨91884, by rfl⟩ : syracuseStep 980101 = 183769) (by norm_num)
theorem B1373381 : Blo 610295 1373381 := bbase (se 4 (by rfl) ⟨128754, by rfl⟩ : syracuseStep 1373381 = 257509) (by norm_num)
theorem B1471709 : Blo 610295 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B2061557 : Blo 610295 2061557 := bbase (se 5 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 2061557 = 193271) (by norm_num)
theorem B1373453 : Blo 610295 1373453 := bbase (se 3 (by rfl) ⟨257522, by rfl⟩ : syracuseStep 1373453 = 515045) (by norm_num)
theorem B1307981 : Blo 610295 1307981 := bbase (se 3 (by rfl) ⟨245246, by rfl⟩ : syracuseStep 1307981 = 490493) (by norm_num)
theorem B1373525 : Blo 610295 1373525 := bbase (se 13 (by rfl) ⟨251, by rfl⟩ : syracuseStep 1373525 = 503) (by norm_num)
theorem B652645 : Blo 610295 652645 := bbase (se 4 (by rfl) ⟨61185, by rfl⟩ : syracuseStep 652645 = 122371) (by norm_num)
theorem B980357 : Blo 610295 980357 := bbase (se 4 (by rfl) ⟨91908, by rfl⟩ : syracuseStep 980357 = 183817) (by norm_num)
theorem B1373597 : Blo 610295 1373597 := bbase (se 3 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 1373597 = 515099) (by norm_num)
theorem B652717 : Blo 610295 652717 := bbase (se 3 (by rfl) ⟨122384, by rfl⟩ : syracuseStep 652717 = 244769) (by norm_num)
theorem B619957 : Blo 610295 619957 := bbase (se 5 (by rfl) ⟨29060, by rfl⟩ : syracuseStep 619957 = 58121) (by norm_num)
theorem B1373669 : Blo 610295 1373669 := bbase (se 4 (by rfl) ⟨128781, by rfl⟩ : syracuseStep 1373669 = 257563) (by norm_num)
theorem B1373741 : Blo 610295 1373741 := bbase (se 3 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 1373741 = 515153) (by norm_num)
theorem B652897 : Blo 610295 652897 := bbase (se 2 (by rfl) ⟨244836, by rfl⟩ : syracuseStep 652897 = 489673) (by norm_num)
theorem B783977 : Blo 610295 783977 := bbase (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) (by norm_num)
theorem B1373813 : Blo 610295 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B2061989 : Blo 610295 2061989 := bbase (se 4 (by rfl) ⟨193311, by rfl⟩ : syracuseStep 2061989 = 386623) (by norm_num)
theorem B1373885 : Blo 610295 1373885 := bbase (se 3 (by rfl) ⟨257603, by rfl⟩ : syracuseStep 1373885 = 515207) (by norm_num)
theorem B1373957 : Blo 610295 1373957 := bbase (se 4 (by rfl) ⟨128808, by rfl⟩ : syracuseStep 1373957 = 257617) (by norm_num)
theorem B1374029 : Blo 610295 1374029 := bbase (se 3 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 1374029 = 515261) (by norm_num)
theorem B1242965 : Blo 610295 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B1374101 : Blo 610295 1374101 := bbase (se 6 (by rfl) ⟨32205, by rfl⟩ : syracuseStep 1374101 = 64411) (by norm_num)
theorem B653261 : Blo 610295 653261 := bbase (se 3 (by rfl) ⟨122486, by rfl⟩ : syracuseStep 653261 = 244973) (by norm_num)
theorem B1374173 : Blo 610295 1374173 := bbase (se 3 (by rfl) ⟨257657, by rfl⟩ : syracuseStep 1374173 = 515315) (by norm_num)
theorem B915461 : Blo 610295 915461 := bbase (se 4 (by rfl) ⟨85824, by rfl⟩ : syracuseStep 915461 = 171649) (by norm_num)
theorem B915485 : Blo 610295 915485 := bbase (se 3 (by rfl) ⟨171653, by rfl⟩ : syracuseStep 915485 = 343307) (by norm_num)
theorem B653341 : Blo 610295 653341 := bbase (se 3 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 653341 = 245003) (by norm_num)
theorem B1374245 : Blo 610295 1374245 := bbase (se 4 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 1374245 = 257671) (by norm_num)
theorem B915509 : Blo 610295 915509 := bbase (se 5 (by rfl) ⟨42914, by rfl⟩ : syracuseStep 915509 = 85829) (by norm_num)
theorem B915533 : Blo 610295 915533 := bbase (se 3 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 915533 = 343325) (by norm_num)
theorem B2062421 : Blo 610295 2062421 := bbase (se 8 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 2062421 = 24169) (by norm_num)
theorem B915557 : Blo 610295 915557 := bbase (se 4 (by rfl) ⟨85833, by rfl⟩ : syracuseStep 915557 = 171667) (by norm_num)
theorem B1374317 : Blo 610295 1374317 := bbase (se 3 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 1374317 = 515369) (by norm_num)
theorem B915581 : Blo 610295 915581 := bbase (se 3 (by rfl) ⟨171671, by rfl⟩ : syracuseStep 915581 = 343343) (by norm_num)
theorem B915605 : Blo 610295 915605 := bbase (se 6 (by rfl) ⟨21459, by rfl⟩ : syracuseStep 915605 = 42919) (by norm_num)
theorem B8485013 : Blo 610295 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B653465 : Blo 610295 653465 := bbase (se 2 (by rfl) ⟨245049, by rfl⟩ : syracuseStep 653465 = 490099) (by norm_num)
theorem B2324645 : Blo 610295 2324645 := bbase (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) (by norm_num)
theorem B915629 : Blo 610295 915629 := bbase (se 3 (by rfl) ⟨171680, by rfl⟩ : syracuseStep 915629 = 343361) (by norm_num)
theorem B1374389 : Blo 610295 1374389 := bbase (se 5 (by rfl) ⟨64424, by rfl⟩ : syracuseStep 1374389 = 128849) (by norm_num)
theorem B915653 : Blo 610295 915653 := bbase (se 4 (by rfl) ⟨85842, by rfl⟩ : syracuseStep 915653 = 171685) (by norm_num)
theorem B1308869 : Blo 610295 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B915677 : Blo 610295 915677 := bbase (se 3 (by rfl) ⟨171689, by rfl⟩ : syracuseStep 915677 = 343379) (by norm_num)
theorem B981229 : Blo 610295 981229 := bbase (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) (by norm_num)
theorem B915701 : Blo 610295 915701 := bbase (se 5 (by rfl) ⟨42923, by rfl⟩ : syracuseStep 915701 = 85847) (by norm_num)
theorem B1374461 : Blo 610295 1374461 := bbase (se 3 (by rfl) ⟨257711, by rfl⟩ : syracuseStep 1374461 = 515423) (by norm_num)
theorem B882949 : Blo 610295 882949 := bbase (se 4 (by rfl) ⟨82776, by rfl⟩ : syracuseStep 882949 = 165553) (by norm_num)
theorem B915725 : Blo 610295 915725 := bbase (se 3 (by rfl) ⟨171698, by rfl⟩ : syracuseStep 915725 = 343397) (by norm_num)
theorem B620821 : Blo 610295 620821 := bbase (se 6 (by rfl) ⟨14550, by rfl⟩ : syracuseStep 620821 = 29101) (by norm_num)
theorem B915749 : Blo 610295 915749 := bbase (se 4 (by rfl) ⟨85851, by rfl⟩ : syracuseStep 915749 = 171703) (by norm_num)
theorem B915773 : Blo 610295 915773 := bbase (se 3 (by rfl) ⟨171707, by rfl⟩ : syracuseStep 915773 = 343415) (by norm_num)
theorem B1374533 : Blo 610295 1374533 := bbase (se 4 (by rfl) ⟨128862, by rfl⟩ : syracuseStep 1374533 = 257725) (by norm_num)
theorem B981325 : Blo 610295 981325 := bbase (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) (by norm_num)
theorem B915797 : Blo 610295 915797 := bbase (se 10 (by rfl) ⟨1341, by rfl⟩ : syracuseStep 915797 = 2683) (by norm_num)
theorem B915821 : Blo 610295 915821 := bbase (se 3 (by rfl) ⟨171716, by rfl⟩ : syracuseStep 915821 = 343433) (by norm_num)
theorem B1964405 : Blo 610295 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B3733877 : Blo 610295 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B915845 : Blo 610295 915845 := bbase (se 4 (by rfl) ⟨85860, by rfl⟩ : syracuseStep 915845 = 171721) (by norm_num)
theorem B1374605 : Blo 610295 1374605 := bbase (se 3 (by rfl) ⟨257738, by rfl⟩ : syracuseStep 1374605 = 515477) (by norm_num)
theorem B653717 : Blo 610295 653717 := bbase (se 6 (by rfl) ⟨15321, by rfl⟩ : syracuseStep 653717 = 30643) (by norm_num)
theorem B5896597 : Blo 610295 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B915869 : Blo 610295 915869 := bbase (se 3 (by rfl) ⟨171725, by rfl⟩ : syracuseStep 915869 = 343451) (by norm_num)
theorem B915893 : Blo 610295 915893 := bbase (se 5 (by rfl) ⟨42932, by rfl⟩ : syracuseStep 915893 = 85865) (by norm_num)
theorem B1309117 : Blo 610295 1309117 := bbase (se 3 (by rfl) ⟨245459, by rfl⟩ : syracuseStep 1309117 = 490919) (by norm_num)
theorem B2324933 : Blo 610295 2324933 := bbase (se 4 (by rfl) ⟨217962, by rfl⟩ : syracuseStep 2324933 = 435925) (by norm_num)
theorem B915917 : Blo 610295 915917 := bbase (se 3 (by rfl) ⟨171734, by rfl⟩ : syracuseStep 915917 = 343469) (by norm_num)
theorem B1374677 : Blo 610295 1374677 := bbase (se 7 (by rfl) ⟨16109, by rfl⟩ : syracuseStep 1374677 = 32219) (by norm_num)
theorem B915941 : Blo 610295 915941 := bbase (se 4 (by rfl) ⟨85869, by rfl⟩ : syracuseStep 915941 = 171739) (by norm_num)
theorem B981485 : Blo 610295 981485 := bbase (se 3 (by rfl) ⟨184028, by rfl⟩ : syracuseStep 981485 = 368057) (by norm_num)
theorem B915965 : Blo 610295 915965 := bbase (se 3 (by rfl) ⟨171743, by rfl⟩ : syracuseStep 915965 = 343487) (by norm_num)
theorem B2062853 : Blo 610295 2062853 := bbase (se 4 (by rfl) ⟨193392, by rfl⟩ : syracuseStep 2062853 = 386785) (by norm_num)
theorem B686605 : Blo 610295 686605 := bbase (se 3 (by rfl) ⟨128738, by rfl⟩ : syracuseStep 686605 = 257477) (by norm_num)
theorem B915989 : Blo 610295 915989 := bbase (se 6 (by rfl) ⟨21468, by rfl⟩ : syracuseStep 915989 = 42937) (by norm_num)
theorem B1374749 : Blo 610295 1374749 := bbase (se 3 (by rfl) ⟨257765, by rfl⟩ : syracuseStep 1374749 = 515531) (by norm_num)
theorem B916013 : Blo 610295 916013 := bbase (se 3 (by rfl) ⟨171752, by rfl⟩ : syracuseStep 916013 = 343505) (by norm_num)
theorem B686641 : Blo 610295 686641 := bbase (se 2 (by rfl) ⟨257490, by rfl⟩ : syracuseStep 686641 = 514981) (by norm_num)
theorem B916037 : Blo 610295 916037 := bbase (se 4 (by rfl) ⟨85878, by rfl⟩ : syracuseStep 916037 = 171757) (by norm_num)
theorem B686677 : Blo 610295 686677 := bbase (se 8 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 686677 = 8047) (by norm_num)
theorem B1342037 : Blo 610295 1342037 := bbase (se 8 (by rfl) ⟨7863, by rfl⟩ : syracuseStep 1342037 = 15727) (by norm_num)
theorem B916061 : Blo 610295 916061 := bbase (se 3 (by rfl) ⟨171761, by rfl⟩ : syracuseStep 916061 = 343523) (by norm_num)
theorem B1374821 : Blo 610295 1374821 := bbase (se 4 (by rfl) ⟨128889, by rfl⟩ : syracuseStep 1374821 = 257779) (by norm_num)
theorem B916085 : Blo 610295 916085 := bbase (se 5 (by rfl) ⟨42941, by rfl⟩ : syracuseStep 916085 = 85883) (by norm_num)
theorem B686713 : Blo 610295 686713 := bbase (se 2 (by rfl) ⟨257517, by rfl⟩ : syracuseStep 686713 = 515035) (by norm_num)
theorem B916109 : Blo 610295 916109 := bbase (se 3 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 916109 = 343541) (by norm_num)
theorem B686749 : Blo 610295 686749 := bbase (se 3 (by rfl) ⟨128765, by rfl⟩ : syracuseStep 686749 = 257531) (by norm_num)
theorem B916133 : Blo 610295 916133 := bbase (se 4 (by rfl) ⟨85887, by rfl⟩ : syracuseStep 916133 = 171775) (by norm_num)
theorem B1374893 : Blo 610295 1374893 := bbase (se 3 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 1374893 = 515585) (by norm_num)
theorem B916157 : Blo 610295 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B686785 : Blo 610295 686785 := bbase (se 2 (by rfl) ⟨257544, by rfl⟩ : syracuseStep 686785 = 515089) (by norm_num)
theorem B916181 : Blo 610295 916181 := bbase (se 7 (by rfl) ⟨10736, by rfl⟩ : syracuseStep 916181 = 21473) (by norm_num)
theorem B686821 : Blo 610295 686821 := bbase (se 4 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 686821 = 128779) (by norm_num)
theorem B916205 : Blo 610295 916205 := bbase (se 3 (by rfl) ⟨171788, by rfl⟩ : syracuseStep 916205 = 343577) (by norm_num)
theorem B1374965 : Blo 610295 1374965 := bbase (se 5 (by rfl) ⟨64451, by rfl⟩ : syracuseStep 1374965 = 128903) (by norm_num)
theorem B916229 : Blo 610295 916229 := bbase (se 4 (by rfl) ⟨85896, by rfl⟩ : syracuseStep 916229 = 171793) (by norm_num)
theorem B686857 : Blo 610295 686857 := bbase (se 2 (by rfl) ⟨257571, by rfl⟩ : syracuseStep 686857 = 515143) (by norm_num)
theorem B916253 : Blo 610295 916253 := bbase (se 3 (by rfl) ⟨171797, by rfl⟩ : syracuseStep 916253 = 343595) (by norm_num)
theorem B686893 : Blo 610295 686893 := bbase (se 3 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 686893 = 257585) (by norm_num)
theorem B916277 : Blo 610295 916277 := bbase (se 5 (by rfl) ⟨42950, by rfl⟩ : syracuseStep 916277 = 85901) (by norm_num)
theorem B1375037 : Blo 610295 1375037 := bbase (se 3 (by rfl) ⟨257819, by rfl⟩ : syracuseStep 1375037 = 515639) (by norm_num)
theorem B916301 : Blo 610295 916301 := bbase (se 3 (by rfl) ⟨171806, by rfl⟩ : syracuseStep 916301 = 343613) (by norm_num)
theorem B686929 : Blo 610295 686929 := bbase (se 2 (by rfl) ⟨257598, by rfl⟩ : syracuseStep 686929 = 515197) (by norm_num)
theorem B654161 : Blo 610295 654161 := bbase (se 2 (by rfl) ⟨245310, by rfl⟩ : syracuseStep 654161 = 490621) (by norm_num)
theorem B916325 : Blo 610295 916325 := bbase (se 4 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 916325 = 171811) (by norm_num)
theorem B686965 : Blo 610295 686965 := bbase (se 5 (by rfl) ⟨32201, by rfl⟩ : syracuseStep 686965 = 64403) (by norm_num)
theorem B916349 : Blo 610295 916349 := bbase (se 3 (by rfl) ⟨171815, by rfl⟩ : syracuseStep 916349 = 343631) (by norm_num)
theorem B621437 : Blo 610295 621437 := bbase (se 3 (by rfl) ⟨116519, by rfl⟩ : syracuseStep 621437 = 233039) (by norm_num)
theorem B1375109 : Blo 610295 1375109 := bbase (se 4 (by rfl) ⟨128916, by rfl⟩ : syracuseStep 1375109 = 257833) (by norm_num)
theorem B916373 : Blo 610295 916373 := bbase (se 6 (by rfl) ⟨21477, by rfl⟩ : syracuseStep 916373 = 42955) (by norm_num)
theorem B687001 : Blo 610295 687001 := bbase (se 2 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 687001 = 515251) (by norm_num)
theorem B916397 : Blo 610295 916397 := bbase (se 3 (by rfl) ⟨171824, by rfl⟩ : syracuseStep 916397 = 343649) (by norm_num)
theorem B2063285 : Blo 610295 2063285 := bbase (se 5 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 2063285 = 193433) (by norm_num)
theorem B1309621 : Blo 610295 1309621 := bbase (se 5 (by rfl) ⟨61388, by rfl⟩ : syracuseStep 1309621 = 122777) (by norm_num)
theorem B687037 : Blo 610295 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B916421 : Blo 610295 916421 := bbase (se 4 (by rfl) ⟨85914, by rfl⟩ : syracuseStep 916421 = 171829) (by norm_num)
theorem B1375181 : Blo 610295 1375181 := bbase (se 3 (by rfl) ⟨257846, by rfl⟩ : syracuseStep 1375181 = 515693) (by norm_num)
theorem B916445 : Blo 610295 916445 := bbase (se 3 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 916445 = 343667) (by norm_num)
theorem B687073 : Blo 610295 687073 := bbase (se 2 (by rfl) ⟨257652, by rfl⟩ : syracuseStep 687073 = 515305) (by norm_num)
theorem B1571813 : Blo 610295 1571813 := bbase (se 4 (by rfl) ⟨147357, by rfl⟩ : syracuseStep 1571813 = 294715) (by norm_num)
theorem B2948069 : Blo 610295 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B916469 : Blo 610295 916469 := bbase (se 5 (by rfl) ⟨42959, by rfl⟩ : syracuseStep 916469 = 85919) (by norm_num)
theorem B687109 : Blo 610295 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B2620421 : Blo 610295 2620421 := bbase (se 4 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 2620421 = 491329) (by norm_num)
theorem B916493 : Blo 610295 916493 := bbase (se 3 (by rfl) ⟨171842, by rfl⟩ : syracuseStep 916493 = 343685) (by norm_num)
theorem B1375253 : Blo 610295 1375253 := bbase (se 6 (by rfl) ⟨32232, by rfl⟩ : syracuseStep 1375253 = 64465) (by norm_num)
theorem B916517 : Blo 610295 916517 := bbase (se 4 (by rfl) ⟨85923, by rfl⟩ : syracuseStep 916517 = 171847) (by norm_num)
theorem B687145 : Blo 610295 687145 := bbase (se 2 (by rfl) ⟨257679, by rfl⟩ : syracuseStep 687145 = 515359) (by norm_num)
theorem B916541 : Blo 610295 916541 := bbase (se 3 (by rfl) ⟨171851, by rfl⟩ : syracuseStep 916541 = 343703) (by norm_num)
theorem B654409 : Blo 610295 654409 := bbase (se 2 (by rfl) ⟨245403, by rfl⟩ : syracuseStep 654409 = 490807) (by norm_num)
theorem B687181 : Blo 610295 687181 := bbase (se 3 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 687181 = 257693) (by norm_num)
theorem B916565 : Blo 610295 916565 := bbase (se 8 (by rfl) ⟨5370, by rfl⟩ : syracuseStep 916565 = 10741) (by norm_num)
theorem B1375325 : Blo 610295 1375325 := bbase (se 3 (by rfl) ⟨257873, by rfl⟩ : syracuseStep 1375325 = 515747) (by norm_num)
theorem B916589 : Blo 610295 916589 := bbase (se 3 (by rfl) ⟨171860, by rfl⟩ : syracuseStep 916589 = 343721) (by norm_num)
theorem B687217 : Blo 610295 687217 := bbase (se 2 (by rfl) ⟨257706, by rfl⟩ : syracuseStep 687217 = 515413) (by norm_num)
theorem B916613 : Blo 610295 916613 := bbase (se 4 (by rfl) ⟨85932, by rfl⟩ : syracuseStep 916613 = 171865) (by norm_num)
theorem B621713 : Blo 610295 621713 := bbase (se 2 (by rfl) ⟨233142, by rfl⟩ : syracuseStep 621713 = 466285) (by norm_num)
theorem B687253 : Blo 610295 687253 := bbase (se 6 (by rfl) ⟨16107, by rfl⟩ : syracuseStep 687253 = 32215) (by norm_num)
theorem B916637 : Blo 610295 916637 := bbase (se 3 (by rfl) ⟨171869, by rfl⟩ : syracuseStep 916637 = 343739) (by norm_num)
theorem B1375397 : Blo 610295 1375397 := bbase (se 4 (by rfl) ⟨128943, by rfl⟩ : syracuseStep 1375397 = 257887) (by norm_num)
theorem B1244333 : Blo 610295 1244333 := bbase (se 3 (by rfl) ⟨233312, by rfl⟩ : syracuseStep 1244333 = 466625) (by norm_num)
theorem B916661 : Blo 610295 916661 := bbase (se 5 (by rfl) ⟨42968, by rfl⟩ : syracuseStep 916661 = 85937) (by norm_num)
theorem B687289 : Blo 610295 687289 := bbase (se 2 (by rfl) ⟨257733, by rfl⟩ : syracuseStep 687289 = 515467) (by norm_num)
theorem B916685 : Blo 610295 916685 := bbase (se 3 (by rfl) ⟨171878, by rfl⟩ : syracuseStep 916685 = 343757) (by norm_num)
theorem B687325 : Blo 610295 687325 := bbase (se 3 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 687325 = 257747) (by norm_num)
theorem B916709 : Blo 610295 916709 := bbase (se 4 (by rfl) ⟨85941, by rfl⟩ : syracuseStep 916709 = 171883) (by norm_num)
theorem B2489573 : Blo 610295 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B1375469 : Blo 610295 1375469 := bbase (se 3 (by rfl) ⟨257900, by rfl⟩ : syracuseStep 1375469 = 515801) (by norm_num)
theorem B916733 : Blo 610295 916733 := bbase (se 3 (by rfl) ⟨171887, by rfl⟩ : syracuseStep 916733 = 343775) (by norm_num)
theorem B687361 : Blo 610295 687361 := bbase (se 2 (by rfl) ⟨257760, by rfl⟩ : syracuseStep 687361 = 515521) (by norm_num)
theorem B916757 : Blo 610295 916757 := bbase (se 6 (by rfl) ⟨21486, by rfl⟩ : syracuseStep 916757 = 42973) (by norm_num)
theorem B687397 : Blo 610295 687397 := bbase (se 4 (by rfl) ⟨64443, by rfl⟩ : syracuseStep 687397 = 128887) (by norm_num)
theorem B916781 : Blo 610295 916781 := bbase (se 3 (by rfl) ⟨171896, by rfl⟩ : syracuseStep 916781 = 343793) (by norm_num)
theorem B1375541 : Blo 610295 1375541 := bbase (se 5 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 1375541 = 128957) (by norm_num)
theorem B916805 : Blo 610295 916805 := bbase (se 4 (by rfl) ⟨85950, by rfl⟩ : syracuseStep 916805 = 171901) (by norm_num)
theorem B687433 : Blo 610295 687433 := bbase (se 2 (by rfl) ⟨257787, by rfl⟩ : syracuseStep 687433 = 515575) (by norm_num)
theorem B7142741 : Blo 610295 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B916829 : Blo 610295 916829 := bbase (se 3 (by rfl) ⟨171905, by rfl⟩ : syracuseStep 916829 = 343811) (by norm_num)
theorem B2063717 : Blo 610295 2063717 := bbase (se 4 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 2063717 = 386947) (by norm_num)
theorem B2948453 : Blo 610295 2948453 := bbase (se 4 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 2948453 = 552835) (by norm_num)
theorem B687469 : Blo 610295 687469 := bbase (se 3 (by rfl) ⟨128900, by rfl⟩ : syracuseStep 687469 = 257801) (by norm_num)
theorem B916853 : Blo 610295 916853 := bbase (se 5 (by rfl) ⟨42977, by rfl⟩ : syracuseStep 916853 = 85955) (by norm_num)
theorem B1375613 : Blo 610295 1375613 := bbase (se 3 (by rfl) ⟨257927, by rfl⟩ : syracuseStep 1375613 = 515855) (by norm_num)
theorem B916877 : Blo 610295 916877 := bbase (se 3 (by rfl) ⟨171914, by rfl⟩ : syracuseStep 916877 = 343829) (by norm_num)
theorem B687505 : Blo 610295 687505 := bbase (se 2 (by rfl) ⟨257814, by rfl⟩ : syracuseStep 687505 = 515629) (by norm_num)
theorem B916901 : Blo 610295 916901 := bbase (se 4 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 916901 = 171919) (by norm_num)
theorem B687541 : Blo 610295 687541 := bbase (se 5 (by rfl) ⟨32228, by rfl⟩ : syracuseStep 687541 = 64457) (by norm_num)
theorem B916925 : Blo 610295 916925 := bbase (se 3 (by rfl) ⟨171923, by rfl⟩ : syracuseStep 916925 = 343847) (by norm_num)
theorem B1375685 : Blo 610295 1375685 := bbase (se 4 (by rfl) ⟨128970, by rfl⟩ : syracuseStep 1375685 = 257941) (by norm_num)
theorem B916949 : Blo 610295 916949 := bbase (se 7 (by rfl) ⟨10745, by rfl⟩ : syracuseStep 916949 = 21491) (by norm_num)
theorem B687577 : Blo 610295 687577 := bbase (se 2 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 687577 = 515683) (by norm_num)
theorem B916973 : Blo 610295 916973 := bbase (se 3 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 916973 = 343865) (by norm_num)
theorem B687613 : Blo 610295 687613 := bbase (se 3 (by rfl) ⟨128927, by rfl⟩ : syracuseStep 687613 = 257855) (by norm_num)
theorem B916997 : Blo 610295 916997 := bbase (se 4 (by rfl) ⟨85968, by rfl⟩ : syracuseStep 916997 = 171937) (by norm_num)
theorem B654853 : Blo 610295 654853 := bbase (se 4 (by rfl) ⟨61392, by rfl⟩ : syracuseStep 654853 = 122785) (by norm_num)
theorem B1375757 : Blo 610295 1375757 := bbase (se 3 (by rfl) ⟨257954, by rfl⟩ : syracuseStep 1375757 = 515909) (by norm_num)
theorem B917021 : Blo 610295 917021 := bbase (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) (by norm_num)
theorem B687649 : Blo 610295 687649 := bbase (se 2 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 687649 = 515737) (by norm_num)
theorem B917045 : Blo 610295 917045 := bbase (se 5 (by rfl) ⟨42986, by rfl⟩ : syracuseStep 917045 = 85973) (by norm_num)
theorem B654913 : Blo 610295 654913 := bbase (se 2 (by rfl) ⟨245592, by rfl⟩ : syracuseStep 654913 = 491185) (by norm_num)
theorem B687685 : Blo 610295 687685 := bbase (se 4 (by rfl) ⟨64470, by rfl⟩ : syracuseStep 687685 = 128941) (by norm_num)
theorem B917069 : Blo 610295 917069 := bbase (se 3 (by rfl) ⟨171950, by rfl⟩ : syracuseStep 917069 = 343901) (by norm_num)
theorem B1375829 : Blo 610295 1375829 := bbase (se 8 (by rfl) ⟨8061, by rfl⟩ : syracuseStep 1375829 = 16123) (by norm_num)
theorem B982613 : Blo 610295 982613 := bbase (se 8 (by rfl) ⟨5757, by rfl⟩ : syracuseStep 982613 = 11515) (by norm_num)
theorem B1474141 : Blo 610295 1474141 := bbase (se 3 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 1474141 = 552803) (by norm_num)
theorem B917093 : Blo 610295 917093 := bbase (se 4 (by rfl) ⟨85977, by rfl⟩ : syracuseStep 917093 = 171955) (by norm_num)
theorem B2326117 : Blo 610295 2326117 := bbase (se 4 (by rfl) ⟨218073, by rfl⟩ : syracuseStep 2326117 = 436147) (by norm_num)
theorem B687721 : Blo 610295 687721 := bbase (se 2 (by rfl) ⟨257895, by rfl⟩ : syracuseStep 687721 = 515791) (by norm_num)
theorem B917117 : Blo 610295 917117 := bbase (se 3 (by rfl) ⟨171959, by rfl⟩ : syracuseStep 917117 = 343919) (by norm_num)
theorem B2981509 : Blo 610295 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B687757 : Blo 610295 687757 := bbase (se 3 (by rfl) ⟨128954, by rfl⟩ : syracuseStep 687757 = 257909) (by norm_num)
theorem B917141 : Blo 610295 917141 := bbase (se 6 (by rfl) ⟨21495, by rfl⟩ : syracuseStep 917141 = 42991) (by norm_num)
theorem B1375901 : Blo 610295 1375901 := bbase (se 3 (by rfl) ⟨257981, by rfl⟩ : syracuseStep 1375901 = 515963) (by norm_num)
theorem B917165 : Blo 610295 917165 := bbase (se 3 (by rfl) ⟨171968, by rfl⟩ : syracuseStep 917165 = 343937) (by norm_num)
theorem B1244845 : Blo 610295 1244845 := bbase (se 3 (by rfl) ⟨233408, by rfl⟩ : syracuseStep 1244845 = 466817) (by norm_num)
theorem B687793 : Blo 610295 687793 := bbase (se 2 (by rfl) ⟨257922, by rfl⟩ : syracuseStep 687793 = 515845) (by norm_num)
theorem B917189 : Blo 610295 917189 := bbase (se 4 (by rfl) ⟨85986, by rfl⟩ : syracuseStep 917189 = 171973) (by norm_num)
theorem B687829 : Blo 610295 687829 := bbase (se 7 (by rfl) ⟨8060, by rfl⟩ : syracuseStep 687829 = 16121) (by norm_num)
theorem B3931861 : Blo 610295 3931861 := bbase (se 7 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 3931861 = 92153) (by norm_num)
theorem B917213 : Blo 610295 917213 := bbase (se 3 (by rfl) ⟨171977, by rfl⟩ : syracuseStep 917213 = 343955) (by norm_num)
theorem B1375973 : Blo 610295 1375973 := bbase (se 4 (by rfl) ⟨128997, by rfl⟩ : syracuseStep 1375973 = 257995) (by norm_num)
theorem B917237 : Blo 610295 917237 := bbase (se 5 (by rfl) ⟨42995, by rfl⟩ : syracuseStep 917237 = 85991) (by norm_num)
theorem B1244917 : Blo 610295 1244917 := bbase (se 5 (by rfl) ⟨58355, by rfl⟩ : syracuseStep 1244917 = 116711) (by norm_num)
theorem B687865 : Blo 610295 687865 := bbase (se 2 (by rfl) ⟨257949, by rfl⟩ : syracuseStep 687865 = 515899) (by norm_num)
theorem B1572605 : Blo 610295 1572605 := bbase (se 3 (by rfl) ⟨294863, by rfl⟩ : syracuseStep 1572605 = 589727) (by norm_num)
theorem B1965829 : Blo 610295 1965829 := bbase (se 4 (by rfl) ⟨184296, by rfl⟩ : syracuseStep 1965829 = 368593) (by norm_num)
theorem B917261 : Blo 610295 917261 := bbase (se 3 (by rfl) ⟨171986, by rfl⟩ : syracuseStep 917261 = 343973) (by norm_num)
theorem B2064149 : Blo 610295 2064149 := bbase (se 6 (by rfl) ⟨48378, by rfl⟩ : syracuseStep 2064149 = 96757) (by norm_num)
theorem B687901 : Blo 610295 687901 := bbase (se 3 (by rfl) ⟨128981, by rfl⟩ : syracuseStep 687901 = 257963) (by norm_num)
theorem B917285 : Blo 610295 917285 := bbase (se 4 (by rfl) ⟨85995, by rfl⟩ : syracuseStep 917285 = 171991) (by norm_num)
theorem B1376045 : Blo 610295 1376045 := bbase (se 3 (by rfl) ⟨258008, by rfl⟩ : syracuseStep 1376045 = 516017) (by norm_num)
theorem B1310509 : Blo 610295 1310509 := bbase (se 3 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 1310509 = 491441) (by norm_num)
theorem B917309 : Blo 610295 917309 := bbase (se 3 (by rfl) ⟨171995, by rfl⟩ : syracuseStep 917309 = 343991) (by norm_num)
theorem B1212221 : Blo 610295 1212221 := bbase (se 3 (by rfl) ⟨227291, by rfl⟩ : syracuseStep 1212221 = 454583) (by norm_num)
theorem B687937 : Blo 610295 687937 := bbase (se 2 (by rfl) ⟨257976, by rfl⟩ : syracuseStep 687937 = 515953) (by norm_num)
theorem B917333 : Blo 610295 917333 := bbase (se 9 (by rfl) ⟨2687, by rfl⟩ : syracuseStep 917333 = 5375) (by norm_num)
theorem B687973 : Blo 610295 687973 := bbase (se 4 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 687973 = 128995) (by norm_num)
theorem B917357 : Blo 610295 917357 := bbase (se 3 (by rfl) ⟨172004, by rfl⟩ : syracuseStep 917357 = 344009) (by norm_num)
theorem B1376117 : Blo 610295 1376117 := bbase (se 5 (by rfl) ⟨64505, by rfl⟩ : syracuseStep 1376117 = 129011) (by norm_num)
theorem B655229 : Blo 610295 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B917381 : Blo 610295 917381 := bbase (se 4 (by rfl) ⟨86004, by rfl⟩ : syracuseStep 917381 = 172009) (by norm_num)
theorem B688009 : Blo 610295 688009 := bbase (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) (by norm_num)
theorem B2326421 : Blo 610295 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B917405 : Blo 610295 917405 := bbase (se 3 (by rfl) ⟨172013, by rfl⟩ : syracuseStep 917405 = 344027) (by norm_num)
theorem B688045 : Blo 610295 688045 := bbase (se 3 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 688045 = 258017) (by norm_num)
theorem B917429 : Blo 610295 917429 := bbase (se 5 (by rfl) ⟨43004, by rfl⟩ : syracuseStep 917429 = 86009) (by norm_num)
theorem B1376189 : Blo 610295 1376189 := bbase (se 3 (by rfl) ⟨258035, by rfl⟩ : syracuseStep 1376189 = 516071) (by norm_num)
theorem B917453 : Blo 610295 917453 := bbase (se 3 (by rfl) ⟨172022, by rfl⟩ : syracuseStep 917453 = 344045) (by norm_num)
theorem B688081 : Blo 610295 688081 := bbase (se 2 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 688081 = 516061) (by norm_num)
theorem B917477 : Blo 610295 917477 := bbase (se 4 (by rfl) ⟨86013, by rfl⟩ : syracuseStep 917477 = 172027) (by norm_num)
theorem B688117 : Blo 610295 688117 := bbase (se 5 (by rfl) ⟨32255, by rfl⟩ : syracuseStep 688117 = 64511) (by norm_num)
theorem B2621429 : Blo 610295 2621429 := bbase (se 5 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 2621429 = 245759) (by norm_num)
theorem B917501 : Blo 610295 917501 := bbase (se 3 (by rfl) ⟨172031, by rfl⟩ : syracuseStep 917501 = 344063) (by norm_num)
theorem B917507 : Blo 610295 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B917537 : Blo 610295 917537 := bstep (se 2 (by rfl) ⟨344076, by rfl⟩ : syracuseStep 917537 = 688153) B688153
theorem B3964963 : Blo 610295 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B2064419 : Blo 610295 2064419 := bstep (se 1 (by rfl) ⟨1548314, by rfl⟩ : syracuseStep 2064419 = 3096629) B3096629
theorem B917555 : Blo 610295 917555 := bstep (se 1 (by rfl) ⟨688166, by rfl⟩ : syracuseStep 917555 = 1376333) B1376333
theorem B1867853 : Blo 610295 1867853 := bstep (se 3 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 1867853 = 700445) B700445
theorem B917585 : Blo 610295 917585 := bstep (se 2 (by rfl) ⟨344094, by rfl⟩ : syracuseStep 917585 = 688189) B688189
theorem B917603 : Blo 610295 917603 := bstep (se 1 (by rfl) ⟨688202, by rfl⟩ : syracuseStep 917603 = 1376405) B1376405
theorem B1376369 : Blo 610295 1376369 := bstep (se 2 (by rfl) ⟨516138, by rfl⟩ : syracuseStep 1376369 = 1032277) B1032277
theorem B1310833 : Blo 610295 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B688243 : Blo 610295 688243 := bstep (se 1 (by rfl) ⟨516182, by rfl⟩ : syracuseStep 688243 = 1032365) B1032365
theorem B786547 : Blo 610295 786547 := bstep (se 1 (by rfl) ⟨589910, by rfl⟩ : syracuseStep 786547 = 1179821) B1179821
theorem B917633 : Blo 610295 917633 := bstep (se 2 (by rfl) ⟨344112, by rfl⟩ : syracuseStep 917633 = 688225) B688225
theorem B1376387 : Blo 610295 1376387 := bstep (se 1 (by rfl) ⟨1032290, by rfl⟩ : syracuseStep 1376387 = 2064581) B2064581
theorem B983171 : Blo 610295 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B917651 : Blo 610295 917651 := bstep (se 1 (by rfl) ⟨688238, by rfl⟩ : syracuseStep 917651 = 1376477) B1376477
theorem B917681 : Blo 610295 917681 := bstep (se 2 (by rfl) ⟨344130, by rfl⟩ : syracuseStep 917681 = 688261) B688261
theorem B917699 : Blo 610295 917699 := bstep (se 1 (by rfl) ⟨688274, by rfl⟩ : syracuseStep 917699 = 1376549) B1376549
theorem B917729 : Blo 610295 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B917747 : Blo 610295 917747 := bstep (se 1 (by rfl) ⟨688310, by rfl⟩ : syracuseStep 917747 = 1376621) B1376621
theorem B688387 : Blo 610295 688387 := bstep (se 1 (by rfl) ⟨516290, by rfl⟩ : syracuseStep 688387 = 1032581) B1032581
theorem B917777 : Blo 610295 917777 := bstep (se 2 (by rfl) ⟨344166, by rfl⟩ : syracuseStep 917777 = 688333) B688333
theorem B917795 : Blo 610295 917795 := bstep (se 1 (by rfl) ⟨688346, by rfl⟩ : syracuseStep 917795 = 1376693) B1376693
theorem B2064689 : Blo 610295 2064689 := bstep (se 2 (by rfl) ⟨774258, by rfl⟩ : syracuseStep 2064689 = 1548517) B1548517
theorem B1769777 : Blo 610295 1769777 := bstep (se 2 (by rfl) ⟨663666, by rfl⟩ : syracuseStep 1769777 = 1327333) B1327333
theorem B917825 : Blo 610295 917825 := bstep (se 2 (by rfl) ⟨344184, by rfl⟩ : syracuseStep 917825 = 688369) B688369
theorem B917843 : Blo 610295 917843 := bstep (se 1 (by rfl) ⟨688382, by rfl⟩ : syracuseStep 917843 = 1376765) B1376765
theorem B917873 : Blo 610295 917873 := bstep (se 2 (by rfl) ⟨344202, by rfl⟩ : syracuseStep 917873 = 688405) B688405
theorem B917891 : Blo 610295 917891 := bstep (se 1 (by rfl) ⟨688418, by rfl⟩ : syracuseStep 917891 = 1376837) B1376837
theorem B1376657 : Blo 610295 1376657 := bstep (se 2 (by rfl) ⟨516246, by rfl⟩ : syracuseStep 1376657 = 1032493) B1032493
theorem B688531 : Blo 610295 688531 := bstep (se 1 (by rfl) ⟨516398, by rfl⟩ : syracuseStep 688531 = 1032797) B1032797
theorem B917921 : Blo 610295 917921 := bstep (se 2 (by rfl) ⟨344220, by rfl⟩ : syracuseStep 917921 = 688441) B688441
theorem B1376675 : Blo 610295 1376675 := bstep (se 1 (by rfl) ⟨1032506, by rfl⟩ : syracuseStep 1376675 = 2065013) B2065013
theorem B917939 : Blo 610295 917939 := bstep (se 1 (by rfl) ⟨688454, by rfl⟩ : syracuseStep 917939 = 1376909) B1376909
theorem B917969 : Blo 610295 917969 := bstep (se 2 (by rfl) ⟨344238, by rfl⟩ : syracuseStep 917969 = 688477) B688477
theorem B917987 : Blo 610295 917987 := bstep (se 1 (by rfl) ⟨688490, by rfl⟩ : syracuseStep 917987 = 1376981) B1376981
theorem B918017 : Blo 610295 918017 := bstep (se 2 (by rfl) ⟨344256, by rfl⟩ : syracuseStep 918017 = 688513) B688513
theorem B1966609 : Blo 610295 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B918035 : Blo 610295 918035 := bstep (se 1 (by rfl) ⟨688526, by rfl⟩ : syracuseStep 918035 = 1377053) B1377053
theorem B688675 : Blo 610295 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B2327075 : Blo 610295 2327075 := bstep (se 1 (by rfl) ⟨1745306, by rfl⟩ : syracuseStep 2327075 = 3490613) B3490613
theorem B918065 : Blo 610295 918065 := bstep (se 2 (by rfl) ⟨344274, by rfl⟩ : syracuseStep 918065 = 688549) B688549
theorem B2327089 : Blo 610295 2327089 := bstep (se 2 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 2327089 = 1745317) B1745317
theorem B918083 : Blo 610295 918083 := bstep (se 1 (by rfl) ⟨688562, by rfl⟩ : syracuseStep 918083 = 1377125) B1377125
theorem B918113 : Blo 610295 918113 := bstep (se 2 (by rfl) ⟨344292, by rfl⟩ : syracuseStep 918113 = 688585) B688585
theorem B918131 : Blo 610295 918131 := bstep (se 1 (by rfl) ⟨688598, by rfl⟩ : syracuseStep 918131 = 1377197) B1377197
theorem B918161 : Blo 610295 918161 := bstep (se 2 (by rfl) ⟨344310, by rfl⟩ : syracuseStep 918161 = 688621) B688621
theorem B918179 : Blo 610295 918179 := bstep (se 1 (by rfl) ⟨688634, by rfl⟩ : syracuseStep 918179 = 1377269) B1377269
theorem B1376945 : Blo 610295 1376945 := bstep (se 2 (by rfl) ⟨516354, by rfl⟩ : syracuseStep 1376945 = 1032709) B1032709
theorem B688819 : Blo 610295 688819 := bstep (se 1 (by rfl) ⟨516614, by rfl⟩ : syracuseStep 688819 = 1033229) B1033229
theorem B918209 : Blo 610295 918209 := bstep (se 2 (by rfl) ⟨344328, by rfl⟩ : syracuseStep 918209 = 688657) B688657
theorem B1376963 : Blo 610295 1376963 := bstep (se 1 (by rfl) ⟨1032722, by rfl⟩ : syracuseStep 1376963 = 2065445) B2065445
theorem B918227 : Blo 610295 918227 := bstep (se 1 (by rfl) ⟨688670, by rfl⟩ : syracuseStep 918227 = 1377341) B1377341
theorem B918257 : Blo 610295 918257 := bstep (se 2 (by rfl) ⟨344346, by rfl⟩ : syracuseStep 918257 = 688693) B688693
theorem B918275 : Blo 610295 918275 := bstep (se 1 (by rfl) ⟨688706, by rfl⟩ : syracuseStep 918275 = 1377413) B1377413
theorem B3539717 : Blo 610295 3539717 := bstep (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) B663697
theorem B918305 : Blo 610295 918305 := bstep (se 2 (by rfl) ⟨344364, by rfl⟩ : syracuseStep 918305 = 688729) B688729
theorem B983843 : Blo 610295 983843 := bstep (se 1 (by rfl) ⟨737882, by rfl⟩ : syracuseStep 983843 = 1475765) B1475765
theorem B918323 : Blo 610295 918323 := bstep (se 1 (by rfl) ⟨688742, by rfl⟩ : syracuseStep 918323 = 1377485) B1377485
theorem B688963 : Blo 610295 688963 := bstep (se 1 (by rfl) ⟨516722, by rfl⟩ : syracuseStep 688963 = 1033445) B1033445
theorem B2065229 : Blo 610295 2065229 := bstep (se 3 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 2065229 = 774461) B774461
theorem B918353 : Blo 610295 918353 := bstep (se 2 (by rfl) ⟨344382, by rfl⟩ : syracuseStep 918353 = 688765) B688765
theorem B918371 : Blo 610295 918371 := bstep (se 1 (by rfl) ⟨688778, by rfl⟩ : syracuseStep 918371 = 1377557) B1377557
theorem B918401 : Blo 610295 918401 := bstep (se 2 (by rfl) ⟨344400, by rfl⟩ : syracuseStep 918401 = 688801) B688801
theorem B2065283 : Blo 610295 2065283 := bstep (se 1 (by rfl) ⟨1548962, by rfl⟩ : syracuseStep 2065283 = 3097925) B3097925
theorem B918419 : Blo 610295 918419 := bstep (se 1 (by rfl) ⟨688814, by rfl⟩ : syracuseStep 918419 = 1377629) B1377629
theorem B918449 : Blo 610295 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B918467 : Blo 610295 918467 := bstep (se 1 (by rfl) ⟨688850, by rfl⟩ : syracuseStep 918467 = 1377701) B1377701
theorem B1377233 : Blo 610295 1377233 := bstep (se 2 (by rfl) ⟨516462, by rfl⟩ : syracuseStep 1377233 = 1032925) B1032925
theorem B689107 : Blo 610295 689107 := bstep (se 1 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 689107 = 1033661) B1033661
theorem B918497 : Blo 610295 918497 := bstep (se 2 (by rfl) ⟨344436, by rfl⟩ : syracuseStep 918497 = 688873) B688873
theorem B1377251 : Blo 610295 1377251 := bstep (se 1 (by rfl) ⟨1032938, by rfl⟩ : syracuseStep 1377251 = 2065877) B2065877
theorem B918515 : Blo 610295 918515 := bstep (se 1 (by rfl) ⟨688886, by rfl⟩ : syracuseStep 918515 = 1377773) B1377773
theorem B918545 : Blo 610295 918545 := bstep (se 2 (by rfl) ⟨344454, by rfl⟩ : syracuseStep 918545 = 688909) B688909
theorem B918563 : Blo 610295 918563 := bstep (se 1 (by rfl) ⟨688922, by rfl⟩ : syracuseStep 918563 = 1377845) B1377845
theorem B918593 : Blo 610295 918593 := bstep (se 2 (by rfl) ⟨344472, by rfl⟩ : syracuseStep 918593 = 688945) B688945
theorem B918611 : Blo 610295 918611 := bstep (se 1 (by rfl) ⟨688958, by rfl⟩ : syracuseStep 918611 = 1377917) B1377917
theorem B689251 : Blo 610295 689251 := bstep (se 1 (by rfl) ⟨516938, by rfl⟩ : syracuseStep 689251 = 1033877) B1033877
theorem B918641 : Blo 610295 918641 := bstep (se 2 (by rfl) ⟨344490, by rfl⟩ : syracuseStep 918641 = 688981) B688981
theorem B918659 : Blo 610295 918659 := bstep (se 1 (by rfl) ⟨688994, by rfl⟩ : syracuseStep 918659 = 1377989) B1377989
theorem B2065553 : Blo 610295 2065553 := bstep (se 2 (by rfl) ⟨774582, by rfl⟩ : syracuseStep 2065553 = 1549165) B1549165
theorem B918689 : Blo 610295 918689 := bstep (se 2 (by rfl) ⟨344508, by rfl⟩ : syracuseStep 918689 = 689017) B689017
theorem B918707 : Blo 610295 918707 := bstep (se 1 (by rfl) ⟨689030, by rfl⟩ : syracuseStep 918707 = 1378061) B1378061
theorem B2098381 : Blo 610295 2098381 := bstep (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) B786893
theorem B918737 : Blo 610295 918737 := bstep (se 2 (by rfl) ⟨344526, by rfl⟩ : syracuseStep 918737 = 689053) B689053
theorem B918755 : Blo 610295 918755 := bstep (se 1 (by rfl) ⟨689066, by rfl⟩ : syracuseStep 918755 = 1378133) B1378133
theorem B1377521 : Blo 610295 1377521 := bstep (se 2 (by rfl) ⟨516570, by rfl⟩ : syracuseStep 1377521 = 1033141) B1033141
theorem B689395 : Blo 610295 689395 := bstep (se 1 (by rfl) ⟨517046, by rfl⟩ : syracuseStep 689395 = 1034093) B1034093
theorem B918785 : Blo 610295 918785 := bstep (se 2 (by rfl) ⟨344544, by rfl⟩ : syracuseStep 918785 = 689089) B689089
theorem B1377539 : Blo 610295 1377539 := bstep (se 1 (by rfl) ⟨1033154, by rfl⟩ : syracuseStep 1377539 = 2066309) B2066309
theorem B918803 : Blo 610295 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B918833 : Blo 610295 918833 := bstep (se 2 (by rfl) ⟨344562, by rfl⟩ : syracuseStep 918833 = 689125) B689125
theorem B918851 : Blo 610295 918851 := bstep (se 1 (by rfl) ⟨689138, by rfl⟩ : syracuseStep 918851 = 1378277) B1378277
theorem B1574225 : Blo 610295 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B918881 : Blo 610295 918881 := bstep (se 2 (by rfl) ⟨344580, by rfl⟩ : syracuseStep 918881 = 689161) B689161
theorem B918899 : Blo 610295 918899 := bstep (se 1 (by rfl) ⟨689174, by rfl⟩ : syracuseStep 918899 = 1378349) B1378349
theorem B689539 : Blo 610295 689539 := bstep (se 1 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 689539 = 1034309) B1034309
theorem B918929 : Blo 610295 918929 := bstep (se 2 (by rfl) ⟨344598, by rfl⟩ : syracuseStep 918929 = 689197) B689197
theorem B918947 : Blo 610295 918947 := bstep (se 1 (by rfl) ⟨689210, by rfl⟩ : syracuseStep 918947 = 1378421) B1378421
theorem B918977 : Blo 610295 918977 := bstep (se 2 (by rfl) ⟨344616, by rfl⟩ : syracuseStep 918977 = 689233) B689233
theorem B4294085 : Blo 610295 4294085 := bstep (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) B805141
theorem B918995 : Blo 610295 918995 := bstep (se 1 (by rfl) ⟨689246, by rfl⟩ : syracuseStep 918995 = 1378493) B1378493
theorem B919025 : Blo 610295 919025 := bstep (se 2 (by rfl) ⟨344634, by rfl⟩ : syracuseStep 919025 = 689269) B689269
theorem B919043 : Blo 610295 919043 := bstep (se 1 (by rfl) ⟨689282, by rfl⟩ : syracuseStep 919043 = 1378565) B1378565
theorem B1377809 : Blo 610295 1377809 := bstep (se 2 (by rfl) ⟨516678, by rfl⟩ : syracuseStep 1377809 = 1033357) B1033357
theorem B689683 : Blo 610295 689683 := bstep (se 1 (by rfl) ⟨517262, by rfl⟩ : syracuseStep 689683 = 1034525) B1034525
theorem B919073 : Blo 610295 919073 := bstep (se 2 (by rfl) ⟨344652, by rfl⟩ : syracuseStep 919073 = 689305) B689305
theorem B1377827 : Blo 610295 1377827 := bstep (se 1 (by rfl) ⟨1033370, by rfl⟩ : syracuseStep 1377827 = 2066741) B2066741
theorem B919091 : Blo 610295 919091 := bstep (se 1 (by rfl) ⟨689318, by rfl⟩ : syracuseStep 919091 = 1378637) B1378637
theorem B919121 : Blo 610295 919121 := bstep (se 2 (by rfl) ⟨344670, by rfl⟩ : syracuseStep 919121 = 689341) B689341
theorem B919139 : Blo 610295 919139 := bstep (se 1 (by rfl) ⟨689354, by rfl⟩ : syracuseStep 919139 = 1378709) B1378709
theorem B919169 : Blo 610295 919169 := bstep (se 2 (by rfl) ⟨344688, by rfl⟩ : syracuseStep 919169 = 689377) B689377
theorem B1738381 : Blo 610295 1738381 := bstep (se 3 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 1738381 = 651893) B651893
theorem B1672849 : Blo 610295 1672849 := bstep (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) B1254637
theorem B919187 : Blo 610295 919187 := bstep (se 1 (by rfl) ⟨689390, by rfl⟩ : syracuseStep 919187 = 1378781) B1378781
theorem B689827 : Blo 610295 689827 := bstep (se 1 (by rfl) ⟨517370, by rfl⟩ : syracuseStep 689827 = 1034741) B1034741
theorem B2066093 : Blo 610295 2066093 := bstep (se 3 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 2066093 = 774785) B774785
theorem B919217 : Blo 610295 919217 := bstep (se 2 (by rfl) ⟨344706, by rfl⟩ : syracuseStep 919217 = 689413) B689413
theorem B919235 : Blo 610295 919235 := bstep (se 1 (by rfl) ⟨689426, by rfl⟩ : syracuseStep 919235 = 1378853) B1378853
theorem B6620869 : Blo 610295 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B919265 : Blo 610295 919265 := bstep (se 2 (by rfl) ⟨344724, by rfl⟩ : syracuseStep 919265 = 689449) B689449
theorem B2066147 : Blo 610295 2066147 := bstep (se 1 (by rfl) ⟨1549610, by rfl⟩ : syracuseStep 2066147 = 3099221) B3099221
theorem B919283 : Blo 610295 919283 := bstep (se 1 (by rfl) ⟨689462, by rfl⟩ : syracuseStep 919283 = 1378925) B1378925
theorem B919313 : Blo 610295 919313 := bstep (se 2 (by rfl) ⟨344742, by rfl⟩ : syracuseStep 919313 = 689485) B689485
theorem B919331 : Blo 610295 919331 := bstep (se 1 (by rfl) ⟨689498, by rfl⟩ : syracuseStep 919331 = 1378997) B1378997
theorem B1378097 : Blo 610295 1378097 := bstep (se 2 (by rfl) ⟨516786, by rfl⟩ : syracuseStep 1378097 = 1033573) B1033573
theorem B689971 : Blo 610295 689971 := bstep (se 1 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 689971 = 1034957) B1034957
theorem B919361 : Blo 610295 919361 := bstep (se 2 (by rfl) ⟨344760, by rfl⟩ : syracuseStep 919361 = 689521) B689521
theorem B1378115 : Blo 610295 1378115 := bstep (se 1 (by rfl) ⟨1033586, by rfl⟩ : syracuseStep 1378115 = 2067173) B2067173
theorem B919379 : Blo 610295 919379 := bstep (se 1 (by rfl) ⟨689534, by rfl⟩ : syracuseStep 919379 = 1379069) B1379069
theorem B919409 : Blo 610295 919409 := bstep (se 2 (by rfl) ⟨344778, by rfl⟩ : syracuseStep 919409 = 689557) B689557
theorem B919427 : Blo 610295 919427 := bstep (se 1 (by rfl) ⟨689570, by rfl⟩ : syracuseStep 919427 = 1379141) B1379141
theorem B21202829 : Blo 610295 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B919457 : Blo 610295 919457 := bstep (se 2 (by rfl) ⟨344796, by rfl⟩ : syracuseStep 919457 = 689593) B689593
theorem B919475 : Blo 610295 919475 := bstep (se 1 (by rfl) ⟨689606, by rfl⟩ : syracuseStep 919475 = 1379213) B1379213
theorem B690115 : Blo 610295 690115 := bstep (se 1 (by rfl) ⟨517586, by rfl⟩ : syracuseStep 690115 = 1035173) B1035173
theorem B919505 : Blo 610295 919505 := bstep (se 2 (by rfl) ⟨344814, by rfl⟩ : syracuseStep 919505 = 689629) B689629
theorem B919523 : Blo 610295 919523 := bstep (se 1 (by rfl) ⟨689642, by rfl⟩ : syracuseStep 919523 = 1379285) B1379285
theorem B2328547 : Blo 610295 2328547 := bstep (se 1 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 2328547 = 3492821) B3492821
theorem B2066417 : Blo 610295 2066417 := bstep (se 2 (by rfl) ⟨774906, by rfl⟩ : syracuseStep 2066417 = 1549813) B1549813
theorem B919553 : Blo 610295 919553 := bstep (se 2 (by rfl) ⟨344832, by rfl⟩ : syracuseStep 919553 = 689665) B689665
theorem B919571 : Blo 610295 919571 := bstep (se 1 (by rfl) ⟨689678, by rfl⟩ : syracuseStep 919571 = 1379357) B1379357
theorem B919601 : Blo 610295 919601 := bstep (se 2 (by rfl) ⟨344850, by rfl⟩ : syracuseStep 919601 = 689701) B689701
theorem B919619 : Blo 610295 919619 := bstep (se 1 (by rfl) ⟨689714, by rfl⟩ : syracuseStep 919619 = 1379429) B1379429
theorem B1378385 : Blo 610295 1378385 := bstep (se 2 (by rfl) ⟨516894, by rfl⟩ : syracuseStep 1378385 = 1033789) B1033789
theorem B690259 : Blo 610295 690259 := bstep (se 1 (by rfl) ⟨517694, by rfl⟩ : syracuseStep 690259 = 1035389) B1035389
theorem B919649 : Blo 610295 919649 := bstep (se 2 (by rfl) ⟨344868, by rfl⟩ : syracuseStep 919649 = 689737) B689737
theorem B1378403 : Blo 610295 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B919667 : Blo 610295 919667 := bstep (se 1 (by rfl) ⟨689750, by rfl⟩ : syracuseStep 919667 = 1379501) B1379501
theorem B919697 : Blo 610295 919697 := bstep (se 2 (by rfl) ⟨344886, by rfl⟩ : syracuseStep 919697 = 689773) B689773
theorem B919715 : Blo 610295 919715 := bstep (se 1 (by rfl) ⟨689786, by rfl⟩ : syracuseStep 919715 = 1379573) B1379573
theorem B919745 : Blo 610295 919745 := bstep (se 2 (by rfl) ⟨344904, by rfl⟩ : syracuseStep 919745 = 689809) B689809
theorem B919763 : Blo 610295 919763 := bstep (se 1 (by rfl) ⟨689822, by rfl⟩ : syracuseStep 919763 = 1379645) B1379645
theorem B690403 : Blo 610295 690403 := bstep (se 1 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 690403 = 1035605) B1035605
theorem B919793 : Blo 610295 919793 := bstep (se 2 (by rfl) ⟨344922, by rfl⟩ : syracuseStep 919793 = 689845) B689845
theorem B919811 : Blo 610295 919811 := bstep (se 1 (by rfl) ⟨689858, by rfl⟩ : syracuseStep 919811 = 1379717) B1379717
theorem B919841 : Blo 610295 919841 := bstep (se 2 (by rfl) ⟨344940, by rfl⟩ : syracuseStep 919841 = 689881) B689881
theorem B919859 : Blo 610295 919859 := bstep (se 1 (by rfl) ⟨689894, by rfl⟩ : syracuseStep 919859 = 1379789) B1379789
theorem B919889 : Blo 610295 919889 := bstep (se 2 (by rfl) ⟨344958, by rfl⟩ : syracuseStep 919889 = 689917) B689917
theorem B919907 : Blo 610295 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B1378673 : Blo 610295 1378673 := bstep (se 2 (by rfl) ⟨517002, by rfl⟩ : syracuseStep 1378673 = 1034005) B1034005
theorem B690547 : Blo 610295 690547 := bstep (se 1 (by rfl) ⟨517910, by rfl⟩ : syracuseStep 690547 = 1035821) B1035821
theorem B919937 : Blo 610295 919937 := bstep (se 2 (by rfl) ⟨344976, by rfl⟩ : syracuseStep 919937 = 689953) B689953
theorem B1116547 : Blo 610295 1116547 := bstep (se 1 (by rfl) ⟨837410, by rfl⟩ : syracuseStep 1116547 = 1674821) B1674821
theorem B1378691 : Blo 610295 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B919955 : Blo 610295 919955 := bstep (se 1 (by rfl) ⟨689966, by rfl⟩ : syracuseStep 919955 = 1379933) B1379933
theorem B919985 : Blo 610295 919985 := bstep (se 2 (by rfl) ⟨344994, by rfl⟩ : syracuseStep 919985 = 689989) B689989
theorem B920003 : Blo 610295 920003 := bstep (se 1 (by rfl) ⟨690002, by rfl⟩ : syracuseStep 920003 = 1380005) B1380005
theorem B920033 : Blo 610295 920033 := bstep (se 2 (by rfl) ⟨345012, by rfl⟩ : syracuseStep 920033 = 690025) B690025
theorem B13273571 : Blo 610295 13273571 := bstep (se 1 (by rfl) ⟨9955178, by rfl⟩ : syracuseStep 13273571 = 19910357) B19910357
theorem B920051 : Blo 610295 920051 := bstep (se 1 (by rfl) ⟨690038, by rfl⟩ : syracuseStep 920051 = 1380077) B1380077
theorem B690691 : Blo 610295 690691 := bstep (se 1 (by rfl) ⟨518018, by rfl⟩ : syracuseStep 690691 = 1036037) B1036037
theorem B2066957 : Blo 610295 2066957 := bstep (se 3 (by rfl) ⟨387554, by rfl⟩ : syracuseStep 2066957 = 775109) B775109
theorem B920081 : Blo 610295 920081 := bstep (se 2 (by rfl) ⟨345030, by rfl⟩ : syracuseStep 920081 = 690061) B690061
theorem B920099 : Blo 610295 920099 := bstep (se 1 (by rfl) ⟨690074, by rfl⟩ : syracuseStep 920099 = 1380149) B1380149
theorem B920129 : Blo 610295 920129 := bstep (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) B690097
theorem B2067011 : Blo 610295 2067011 := bstep (se 1 (by rfl) ⟨1550258, by rfl⟩ : syracuseStep 2067011 = 3100517) B3100517
theorem B920147 : Blo 610295 920147 := bstep (se 1 (by rfl) ⟨690110, by rfl⟩ : syracuseStep 920147 = 1380221) B1380221
theorem B920177 : Blo 610295 920177 := bstep (se 2 (by rfl) ⟨345066, by rfl⟩ : syracuseStep 920177 = 690133) B690133
theorem B920195 : Blo 610295 920195 := bstep (se 1 (by rfl) ⟨690146, by rfl⟩ : syracuseStep 920195 = 1380293) B1380293
theorem B1378961 : Blo 610295 1378961 := bstep (se 2 (by rfl) ⟨517110, by rfl⟩ : syracuseStep 1378961 = 1034221) B1034221
theorem B690835 : Blo 610295 690835 := bstep (se 1 (by rfl) ⟨518126, by rfl⟩ : syracuseStep 690835 = 1036253) B1036253
theorem B920225 : Blo 610295 920225 := bstep (se 2 (by rfl) ⟨345084, by rfl⟩ : syracuseStep 920225 = 690169) B690169
theorem B1378979 : Blo 610295 1378979 := bstep (se 1 (by rfl) ⟨1034234, by rfl⟩ : syracuseStep 1378979 = 2068469) B2068469
theorem B920243 : Blo 610295 920243 := bstep (se 1 (by rfl) ⟨690182, by rfl⟩ : syracuseStep 920243 = 1380365) B1380365
theorem B920273 : Blo 610295 920273 := bstep (se 2 (by rfl) ⟨345102, by rfl⟩ : syracuseStep 920273 = 690205) B690205
theorem B920291 : Blo 610295 920291 := bstep (se 1 (by rfl) ⟨690218, by rfl⟩ : syracuseStep 920291 = 1380437) B1380437
theorem B920321 : Blo 610295 920321 := bstep (se 2 (by rfl) ⟨345120, by rfl⟩ : syracuseStep 920321 = 690241) B690241
theorem B920339 : Blo 610295 920339 := bstep (se 1 (by rfl) ⟨690254, by rfl⟩ : syracuseStep 920339 = 1380509) B1380509
theorem B690979 : Blo 610295 690979 := bstep (se 1 (by rfl) ⟨518234, by rfl⟩ : syracuseStep 690979 = 1036469) B1036469
theorem B920369 : Blo 610295 920369 := bstep (se 2 (by rfl) ⟨345138, by rfl⟩ : syracuseStep 920369 = 690277) B690277
theorem B920387 : Blo 610295 920387 := bstep (se 1 (by rfl) ⟨690290, by rfl⟩ : syracuseStep 920387 = 1380581) B1380581
theorem B2067281 : Blo 610295 2067281 := bstep (se 2 (by rfl) ⟨775230, by rfl⟩ : syracuseStep 2067281 = 1550461) B1550461
theorem B920417 : Blo 610295 920417 := bstep (se 2 (by rfl) ⟨345156, by rfl⟩ : syracuseStep 920417 = 690313) B690313
theorem B920435 : Blo 610295 920435 := bstep (se 1 (by rfl) ⟨690326, by rfl⟩ : syracuseStep 920435 = 1380653) B1380653
theorem B920465 : Blo 610295 920465 := bstep (se 2 (by rfl) ⟨345174, by rfl⟩ : syracuseStep 920465 = 690349) B690349
theorem B920483 : Blo 610295 920483 := bstep (se 1 (by rfl) ⟨690362, by rfl⟩ : syracuseStep 920483 = 1380725) B1380725
theorem B1379249 : Blo 610295 1379249 := bstep (se 2 (by rfl) ⟨517218, by rfl⟩ : syracuseStep 1379249 = 1034437) B1034437
theorem B920513 : Blo 610295 920513 := bstep (se 2 (by rfl) ⟨345192, by rfl⟩ : syracuseStep 920513 = 690385) B690385
theorem B1379267 : Blo 610295 1379267 := bstep (se 1 (by rfl) ⟨1034450, by rfl⟩ : syracuseStep 1379267 = 2068901) B2068901
theorem B920531 : Blo 610295 920531 := bstep (se 1 (by rfl) ⟨690398, by rfl⟩ : syracuseStep 920531 = 1380797) B1380797
theorem B3476465 : Blo 610295 3476465 := bstep (se 2 (by rfl) ⟨1303674, by rfl⟩ : syracuseStep 3476465 = 2607349) B2607349
theorem B920561 : Blo 610295 920561 := bstep (se 2 (by rfl) ⟨345210, by rfl⟩ : syracuseStep 920561 = 690421) B690421
theorem B920579 : Blo 610295 920579 := bstep (se 1 (by rfl) ⟨690434, by rfl⟩ : syracuseStep 920579 = 1380869) B1380869
theorem B920609 : Blo 610295 920609 := bstep (se 2 (by rfl) ⟨345228, by rfl⟩ : syracuseStep 920609 = 690457) B690457
theorem B920627 : Blo 610295 920627 := bstep (se 1 (by rfl) ⟨690470, by rfl⟩ : syracuseStep 920627 = 1380941) B1380941
theorem B920657 : Blo 610295 920657 := bstep (se 2 (by rfl) ⟨345246, by rfl⟩ : syracuseStep 920657 = 690493) B690493
theorem B920675 : Blo 610295 920675 := bstep (se 1 (by rfl) ⟨690506, by rfl⟩ : syracuseStep 920675 = 1381013) B1381013
theorem B920705 : Blo 610295 920705 := bstep (se 2 (by rfl) ⟨345264, by rfl⟩ : syracuseStep 920705 = 690529) B690529
theorem B920723 : Blo 610295 920723 := bstep (se 1 (by rfl) ⟨690542, by rfl⟩ : syracuseStep 920723 = 1381085) B1381085
theorem B920753 : Blo 610295 920753 := bstep (se 2 (by rfl) ⟨345282, by rfl⟩ : syracuseStep 920753 = 690565) B690565
theorem B920771 : Blo 610295 920771 := bstep (se 1 (by rfl) ⟨690578, by rfl⟩ : syracuseStep 920771 = 1381157) B1381157
theorem B1379537 : Blo 610295 1379537 := bstep (se 2 (by rfl) ⟨517326, by rfl⟩ : syracuseStep 1379537 = 1034653) B1034653
theorem B920801 : Blo 610295 920801 := bstep (se 2 (by rfl) ⟨345300, by rfl⟩ : syracuseStep 920801 = 690601) B690601
theorem B1379555 : Blo 610295 1379555 := bstep (se 1 (by rfl) ⟨1034666, by rfl⟩ : syracuseStep 1379555 = 2069333) B2069333
theorem B920819 : Blo 610295 920819 := bstep (se 1 (by rfl) ⟨690614, by rfl⟩ : syracuseStep 920819 = 1381229) B1381229
theorem B920849 : Blo 610295 920849 := bstep (se 2 (by rfl) ⟨345318, by rfl⟩ : syracuseStep 920849 = 690637) B690637
theorem B920867 : Blo 610295 920867 := bstep (se 1 (by rfl) ⟨690650, by rfl⟩ : syracuseStep 920867 = 1381301) B1381301
theorem B920897 : Blo 610295 920897 := bstep (se 2 (by rfl) ⟨345336, by rfl⟩ : syracuseStep 920897 = 690673) B690673
theorem B1740113 : Blo 610295 1740113 := bstep (se 2 (by rfl) ⟨652542, by rfl⟩ : syracuseStep 1740113 = 1305085) B1305085
theorem B920915 : Blo 610295 920915 := bstep (se 1 (by rfl) ⟨690686, by rfl⟩ : syracuseStep 920915 = 1381373) B1381373
theorem B2067821 : Blo 610295 2067821 := bstep (se 3 (by rfl) ⟨387716, by rfl⟩ : syracuseStep 2067821 = 775433) B775433
theorem B920945 : Blo 610295 920945 := bstep (se 2 (by rfl) ⟨345354, by rfl⟩ : syracuseStep 920945 = 690709) B690709
theorem B920963 : Blo 610295 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B920993 : Blo 610295 920993 := bstep (se 2 (by rfl) ⟨345372, by rfl⟩ : syracuseStep 920993 = 690745) B690745
theorem B2067875 : Blo 610295 2067875 := bstep (se 1 (by rfl) ⟨1550906, by rfl⟩ : syracuseStep 2067875 = 3101813) B3101813
theorem B921011 : Blo 610295 921011 := bstep (se 1 (by rfl) ⟨690758, by rfl⟩ : syracuseStep 921011 = 1381517) B1381517
theorem B921041 : Blo 610295 921041 := bstep (se 2 (by rfl) ⟨345390, by rfl⟩ : syracuseStep 921041 = 690781) B690781
theorem B921059 : Blo 610295 921059 := bstep (se 1 (by rfl) ⟨690794, by rfl⟩ : syracuseStep 921059 = 1381589) B1381589
theorem B1379825 : Blo 610295 1379825 := bstep (se 2 (by rfl) ⟨517434, by rfl⟩ : syracuseStep 1379825 = 1034869) B1034869
theorem B921089 : Blo 610295 921089 := bstep (se 2 (by rfl) ⟨345408, by rfl⟩ : syracuseStep 921089 = 690817) B690817
theorem B1379843 : Blo 610295 1379843 := bstep (se 1 (by rfl) ⟨1034882, by rfl⟩ : syracuseStep 1379843 = 2069765) B2069765
theorem B5246477 : Blo 610295 5246477 := bstep (se 3 (by rfl) ⟨983714, by rfl⟩ : syracuseStep 5246477 = 1967429) B1967429
theorem B1740305 : Blo 610295 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B921107 : Blo 610295 921107 := bstep (se 1 (by rfl) ⟨690830, by rfl⟩ : syracuseStep 921107 = 1381661) B1381661
theorem B921137 : Blo 610295 921137 := bstep (se 2 (by rfl) ⟨345426, by rfl⟩ : syracuseStep 921137 = 690853) B690853
theorem B921155 : Blo 610295 921155 := bstep (se 1 (by rfl) ⟨690866, by rfl⟩ : syracuseStep 921155 = 1381733) B1381733
theorem B921185 : Blo 610295 921185 := bstep (se 2 (by rfl) ⟨345444, by rfl⟩ : syracuseStep 921185 = 690889) B690889
theorem B921203 : Blo 610295 921203 := bstep (se 1 (by rfl) ⟨690902, by rfl⟩ : syracuseStep 921203 = 1381805) B1381805
theorem B921233 : Blo 610295 921233 := bstep (se 2 (by rfl) ⟨345462, by rfl⟩ : syracuseStep 921233 = 690925) B690925
theorem B921251 : Blo 610295 921251 := bstep (se 1 (by rfl) ⟨690938, by rfl⟩ : syracuseStep 921251 = 1381877) B1381877
theorem B2068145 : Blo 610295 2068145 := bstep (se 2 (by rfl) ⟨775554, by rfl⟩ : syracuseStep 2068145 = 1551109) B1551109
theorem B921281 : Blo 610295 921281 := bstep (se 2 (by rfl) ⟨345480, by rfl⟩ : syracuseStep 921281 = 690961) B690961
theorem B921299 : Blo 610295 921299 := bstep (se 1 (by rfl) ⟨690974, by rfl⟩ : syracuseStep 921299 = 1381949) B1381949
theorem B921329 : Blo 610295 921329 := bstep (se 2 (by rfl) ⟨345498, by rfl⟩ : syracuseStep 921329 = 690997) B690997
theorem B921347 : Blo 610295 921347 := bstep (se 1 (by rfl) ⟨691010, by rfl⟩ : syracuseStep 921347 = 1382021) B1382021
theorem B1380113 : Blo 610295 1380113 := bstep (se 2 (by rfl) ⟨517542, by rfl⟩ : syracuseStep 1380113 = 1035085) B1035085
theorem B921377 : Blo 610295 921377 := bstep (se 2 (by rfl) ⟨345516, by rfl⟩ : syracuseStep 921377 = 691033) B691033
theorem B1380131 : Blo 610295 1380131 := bstep (se 1 (by rfl) ⟨1035098, by rfl⟩ : syracuseStep 1380131 = 2070197) B2070197
theorem B921395 : Blo 610295 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B921425 : Blo 610295 921425 := bstep (se 2 (by rfl) ⟨345534, by rfl⟩ : syracuseStep 921425 = 691069) B691069
theorem B921443 : Blo 610295 921443 := bstep (se 1 (by rfl) ⟨691082, by rfl⟩ : syracuseStep 921443 = 1382165) B1382165
theorem B8359793 : Blo 610295 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B1380401 : Blo 610295 1380401 := bstep (se 2 (by rfl) ⟨517650, by rfl⟩ : syracuseStep 1380401 = 1035301) B1035301
theorem B1380419 : Blo 610295 1380419 := bstep (se 1 (by rfl) ⟨1035314, by rfl⟩ : syracuseStep 1380419 = 2070629) B2070629
theorem B2330765 : Blo 610295 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B2068685 : Blo 610295 2068685 := bstep (se 3 (by rfl) ⟨387878, by rfl⟩ : syracuseStep 2068685 = 775757) B775757
theorem B2101457 : Blo 610295 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B2068739 : Blo 610295 2068739 := bstep (se 1 (by rfl) ⟨1551554, by rfl⟩ : syracuseStep 2068739 = 3103109) B3103109
theorem B1380689 : Blo 610295 1380689 := bstep (se 2 (by rfl) ⟨517758, by rfl⟩ : syracuseStep 1380689 = 1035517) B1035517
theorem B1380707 : Blo 610295 1380707 := bstep (se 1 (by rfl) ⟨1035530, by rfl⟩ : syracuseStep 1380707 = 2071061) B2071061
theorem B3477923 : Blo 610295 3477923 := bstep (se 1 (by rfl) ⟨2608442, by rfl⟩ : syracuseStep 3477923 = 5216885) B5216885
theorem B1741297 : Blo 610295 1741297 := bstep (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) B1305973
theorem B2069009 : Blo 610295 2069009 := bstep (se 2 (by rfl) ⟨775878, by rfl⟩ : syracuseStep 2069009 = 1551757) B1551757
theorem B1380977 : Blo 610295 1380977 := bstep (se 2 (by rfl) ⟨517866, by rfl⟩ : syracuseStep 1380977 = 1035733) B1035733
theorem B1380995 : Blo 610295 1380995 := bstep (se 1 (by rfl) ⟨1035746, by rfl⟩ : syracuseStep 1380995 = 2071493) B2071493
theorem B1741571 : Blo 610295 1741571 := bstep (se 1 (by rfl) ⟨1306178, by rfl⟩ : syracuseStep 1741571 = 2612357) B2612357
theorem B1381265 : Blo 610295 1381265 := bstep (se 2 (by rfl) ⟨517974, by rfl⟩ : syracuseStep 1381265 = 1035949) B1035949
theorem B1381283 : Blo 610295 1381283 := bstep (se 1 (by rfl) ⟨1035962, by rfl⟩ : syracuseStep 1381283 = 2071925) B2071925
theorem B1741763 : Blo 610295 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B2069549 : Blo 610295 2069549 := bstep (se 3 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 2069549 = 776081) B776081
theorem B2069603 : Blo 610295 2069603 := bstep (se 1 (by rfl) ⟨1552202, by rfl⟩ : syracuseStep 2069603 = 3104405) B3104405
theorem B2266289 : Blo 610295 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B1381553 : Blo 610295 1381553 := bstep (se 2 (by rfl) ⟨518082, by rfl⟩ : syracuseStep 1381553 = 1036165) B1036165
theorem B1381571 : Blo 610295 1381571 := bstep (se 1 (by rfl) ⟨1036178, by rfl⟩ : syracuseStep 1381571 = 2072357) B2072357
theorem B1742029 : Blo 610295 1742029 := bstep (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) B653261
theorem B2069873 : Blo 610295 2069873 := bstep (se 2 (by rfl) ⟨776202, by rfl⟩ : syracuseStep 2069873 = 1552405) B1552405
theorem B12719501 : Blo 610295 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1381841 : Blo 610295 1381841 := bstep (se 2 (by rfl) ⟨518190, by rfl⟩ : syracuseStep 1381841 = 1036381) B1036381
theorem B1381859 : Blo 610295 1381859 := bstep (se 1 (by rfl) ⟨1036394, by rfl⟩ : syracuseStep 1381859 = 2072789) B2072789
theorem B1545713 : Blo 610295 1545713 := bstep (se 2 (by rfl) ⟨579642, by rfl⟩ : syracuseStep 1545713 = 1159285) B1159285
theorem B1545763 : Blo 610295 1545763 := bstep (se 1 (by rfl) ⟨1159322, by rfl⟩ : syracuseStep 1545763 = 2318645) B2318645
theorem B1545905 : Blo 610295 1545905 := bstep (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) B1159429
theorem B1742573 : Blo 610295 1742573 := bstep (se 3 (by rfl) ⟨326732, by rfl⟩ : syracuseStep 1742573 = 653465) B653465
theorem B1382129 : Blo 610295 1382129 := bstep (se 2 (by rfl) ⟨518298, by rfl⟩ : syracuseStep 1382129 = 1036597) B1036597
theorem B1382147 : Blo 610295 1382147 := bstep (se 1 (by rfl) ⟨1036610, by rfl⟩ : syracuseStep 1382147 = 2073221) B2073221
theorem B2070413 : Blo 610295 2070413 := bstep (se 3 (by rfl) ⟨388202, by rfl⟩ : syracuseStep 2070413 = 776405) B776405
theorem B1742755 : Blo 610295 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B2070467 : Blo 610295 2070467 := bstep (se 1 (by rfl) ⟨1552850, by rfl⟩ : syracuseStep 2070467 = 3105701) B3105701
theorem B5871685 : Blo 610295 5871685 := bstep (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) B1100941
theorem B10623089 : Blo 610295 10623089 := bstep (se 2 (by rfl) ⟨3983658, by rfl⟩ : syracuseStep 10623089 = 7967317) B7967317
theorem B2070737 : Blo 610295 2070737 := bstep (se 2 (by rfl) ⟨776526, by rfl⟩ : syracuseStep 2070737 = 1553053) B1553053
theorem B6953201 : Blo 610295 6953201 := bstep (se 2 (by rfl) ⟨2607450, by rfl⟩ : syracuseStep 6953201 = 5214901) B5214901
theorem B1022209 : Blo 610295 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B1743245 : Blo 610295 1743245 := bstep (se 3 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 1743245 = 653717) B653717
theorem B825761 : Blo 610295 825761 := bstep (se 2 (by rfl) ⟨309660, by rfl⟩ : syracuseStep 825761 = 619321) B619321
theorem B2791907 : Blo 610295 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B8854069 : Blo 610295 8854069 := bstep (se 5 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 8854069 = 830069) B830069
theorem B825923 : Blo 610295 825923 := bstep (se 1 (by rfl) ⟨619442, by rfl⟩ : syracuseStep 825923 = 1238885) B1238885
theorem B4725317 : Blo 610295 4725317 := bstep (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) B885997
theorem B1546897 : Blo 610295 1546897 := bstep (se 2 (by rfl) ⟨580086, by rfl⟩ : syracuseStep 1546897 = 1160173) B1160173
theorem B2071277 : Blo 610295 2071277 := bstep (se 3 (by rfl) ⟨388364, by rfl⟩ : syracuseStep 2071277 = 776729) B776729
theorem B2071331 : Blo 610295 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B15276853 : Blo 610295 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B1547171 : Blo 610295 1547171 := bstep (se 1 (by rfl) ⟨1160378, by rfl⟩ : syracuseStep 1547171 = 2320757) B2320757
theorem B826291 : Blo 610295 826291 := bstep (se 1 (by rfl) ⟨619718, by rfl⟩ : syracuseStep 826291 = 1239437) B1239437
theorem B2071601 : Blo 610295 2071601 := bstep (se 2 (by rfl) ⟨776850, by rfl⟩ : syracuseStep 2071601 = 1553701) B1553701
theorem B1547363 : Blo 610295 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B5217635 : Blo 610295 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B1744429 : Blo 610295 1744429 := bstep (se 3 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 1744429 = 654161) B654161
theorem B3481157 : Blo 610295 3481157 := bstep (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) B652717
theorem B2072141 : Blo 610295 2072141 := bstep (se 3 (by rfl) ⟨388526, by rfl⟩ : syracuseStep 2072141 = 777053) B777053
theorem B2072195 : Blo 610295 2072195 := bstep (se 1 (by rfl) ⟨1554146, by rfl⟩ : syracuseStep 2072195 = 3108293) B3108293
theorem B2072465 : Blo 610295 2072465 := bstep (se 2 (by rfl) ⟨777174, by rfl⟩ : syracuseStep 2072465 = 1554349) B1554349
theorem B3481613 : Blo 610295 3481613 := bstep (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) B1305605
theorem B1548305 : Blo 610295 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B1548355 : Blo 610295 1548355 := bstep (se 1 (by rfl) ⟨1161266, by rfl⟩ : syracuseStep 1548355 = 2322533) B2322533
theorem B827491 : Blo 610295 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B1548497 : Blo 610295 1548497 := bstep (se 2 (by rfl) ⟨580686, by rfl⟩ : syracuseStep 1548497 = 1161373) B1161373
theorem B827761 : Blo 610295 827761 := bstep (se 2 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 827761 = 620821) B620821
theorem B2073005 : Blo 610295 2073005 := bstep (se 3 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 2073005 = 777377) B777377
theorem B3318221 : Blo 610295 3318221 := bstep (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) B1244333
theorem B2073059 : Blo 610295 2073059 := bstep (se 1 (by rfl) ⟨1554794, by rfl⟩ : syracuseStep 2073059 = 3109589) B3109589
theorem B1745489 : Blo 610295 1745489 := bstep (se 2 (by rfl) ⟨654558, by rfl⟩ : syracuseStep 1745489 = 1309117) B1309117
theorem B15901381 : Blo 610295 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B664723 : Blo 610295 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B1549489 : Blo 610295 1549489 := bstep (se 2 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 1549489 = 1162117) B1162117
theorem B828643 : Blo 610295 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B1746161 : Blo 610295 1746161 := bstep (se 2 (by rfl) ⟨654810, by rfl⟩ : syracuseStep 1746161 = 1309621) B1309621
theorem B2204941 : Blo 610295 2204941 := bstep (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) B826853
theorem B6628661 : Blo 610295 6628661 := bstep (se 5 (by rfl) ⟨310718, by rfl⟩ : syracuseStep 6628661 = 621437) B621437
theorem B1549763 : Blo 610295 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B1549955 : Blo 610295 1549955 := bstep (se 1 (by rfl) ⟨1162466, by rfl⟩ : syracuseStep 1549955 = 2324933) B2324933
theorem B894691 : Blo 610295 894691 := bstep (se 1 (by rfl) ⟨671018, by rfl⟩ : syracuseStep 894691 = 1342037) B1342037
theorem B1746947 : Blo 610295 1746947 := bstep (se 1 (by rfl) ⟨1310210, by rfl⟩ : syracuseStep 1746947 = 2620421) B2620421
theorem B4761827 : Blo 610295 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B1747277 : Blo 610295 1747277 := bstep (se 3 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 1747277 = 655229) B655229
theorem B1747345 : Blo 610295 1747345 := bstep (se 2 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 1747345 = 1310509) B1310509
theorem B1550897 : Blo 610295 1550897 := bstep (se 2 (by rfl) ⟨581586, by rfl⟩ : syracuseStep 1550897 = 1163173) B1163173
theorem B1550947 : Blo 610295 1550947 := bstep (se 1 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 1550947 = 2326421) B2326421
theorem B1747619 : Blo 610295 1747619 := bstep (se 1 (by rfl) ⟨1310714, by rfl⟩ : syracuseStep 1747619 = 2621429) B2621429
theorem B3091121 : Blo 610295 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B928433 : Blo 610295 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B1551089 : Blo 610295 1551089 := bstep (se 2 (by rfl) ⟨581658, by rfl⟩ : syracuseStep 1551089 = 1163317) B1163317
theorem B3484529 : Blo 610295 3484529 := bstep (se 2 (by rfl) ⟨1306698, by rfl⟩ : syracuseStep 3484529 = 2613397) B2613397
theorem B994403 : Blo 610295 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B1649933 : Blo 610295 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B3911075 : Blo 610295 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B1748461 : Blo 610295 1748461 := bstep (se 3 (by rfl) ⟨327836, by rfl⟩ : syracuseStep 1748461 = 655673) B655673
theorem B4402673 : Blo 610295 4402673 := bstep (se 2 (by rfl) ⟨1651002, by rfl⟩ : syracuseStep 4402673 = 3302005) B3302005
theorem B15904309 : Blo 610295 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B1650289 : Blo 610295 1650289 := bstep (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) B1237717
theorem B1748621 : Blo 610295 1748621 := bstep (se 3 (by rfl) ⟨327866, by rfl⟩ : syracuseStep 1748621 = 655733) B655733
theorem B1552081 : Blo 610295 1552081 := bstep (se 2 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 1552081 = 1164061) B1164061
theorem B1748803 : Blo 610295 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B929747 : Blo 610295 929747 := bstep (se 1 (by rfl) ⟨697310, by rfl⟩ : syracuseStep 929747 = 1394621) B1394621
theorem B1552355 : Blo 610295 1552355 := bstep (se 1 (by rfl) ⟨1164266, by rfl⟩ : syracuseStep 1552355 = 2328533) B2328533
theorem B3092579 : Blo 610295 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B1552547 : Blo 610295 1552547 := bstep (se 1 (by rfl) ⟨1164410, by rfl⟩ : syracuseStep 1552547 = 2328821) B2328821
theorem B3485987 : Blo 610295 3485987 := bstep (se 1 (by rfl) ⟨2614490, by rfl⟩ : syracuseStep 3485987 = 5228981) B5228981
theorem B1159505 : Blo 610295 1159505 := bstep (se 2 (by rfl) ⟨434814, by rfl⟩ : syracuseStep 1159505 = 869629) B869629
theorem B930355 : Blo 610295 930355 := bstep (se 1 (by rfl) ⟨697766, by rfl⟩ : syracuseStep 930355 = 1395533) B1395533
theorem B3912461 : Blo 610295 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B2798435 : Blo 610295 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B3093389 : Blo 610295 3093389 := bstep (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) B1160021
theorem B1553489 : Blo 610295 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B1553539 : Blo 610295 1553539 := bstep (se 1 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 1553539 = 2330309) B2330309
theorem B1160401 : Blo 610295 1160401 := bstep (se 2 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 1160401 = 870301) B870301
theorem B3486989 : Blo 610295 3486989 := bstep (se 3 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 3486989 = 1307621) B1307621
theorem B1553681 : Blo 610295 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B25212181 : Blo 610295 25212181 := bstep (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) B1181821
theorem B1160561 : Blo 610295 1160561 := bstep (se 2 (by rfl) ⟨435210, by rfl⟩ : syracuseStep 1160561 = 870421) B870421
theorem B1160963 : Blo 610295 1160963 := bstep (se 1 (by rfl) ⟨870722, by rfl⟩ : syracuseStep 1160963 = 1741445) B1741445
theorem B1029955 : Blo 610295 1029955 := bstep (se 1 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 1029955 = 1544933) B1544933
theorem B1030097 : Blo 610295 1030097 := bstep (se 2 (by rfl) ⟨386286, by rfl⟩ : syracuseStep 1030097 = 772573) B772573
theorem B1030225 : Blo 610295 1030225 := bstep (se 2 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 1030225 = 772669) B772669
theorem B1030259 : Blo 610295 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B1554673 : Blo 610295 1554673 := bstep (se 2 (by rfl) ⟨583002, by rfl⟩ : syracuseStep 1554673 = 1166005) B1166005
theorem B1030387 : Blo 610295 1030387 := bstep (se 1 (by rfl) ⟨772790, by rfl⟩ : syracuseStep 1030387 = 1545581) B1545581
theorem B1030529 : Blo 610295 1030529 := bstep (se 2 (by rfl) ⟨386448, by rfl⟩ : syracuseStep 1030529 = 772897) B772897
theorem B1030657 : Blo 610295 1030657 := bstep (se 2 (by rfl) ⟨386496, by rfl⟩ : syracuseStep 1030657 = 772993) B772993
theorem B1030691 : Blo 610295 1030691 := bstep (se 1 (by rfl) ⟨773018, by rfl⟩ : syracuseStep 1030691 = 1546037) B1546037
theorem B2210417 : Blo 610295 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B1161859 : Blo 610295 1161859 := bstep (se 1 (by rfl) ⟨871394, by rfl⟩ : syracuseStep 1161859 = 1742789) B1742789
theorem B1030819 : Blo 610295 1030819 := bstep (se 1 (by rfl) ⟨773114, by rfl⟩ : syracuseStep 1030819 = 1546229) B1546229
theorem B1162019 : Blo 610295 1162019 := bstep (se 1 (by rfl) ⟨871514, by rfl⟩ : syracuseStep 1162019 = 1743029) B1743029
theorem B1030961 : Blo 610295 1030961 := bstep (se 2 (by rfl) ⟨386610, by rfl⟩ : syracuseStep 1030961 = 773221) B773221
theorem B1031089 : Blo 610295 1031089 := bstep (se 2 (by rfl) ⟨386658, by rfl⟩ : syracuseStep 1031089 = 773317) B773317
theorem B1031123 : Blo 610295 1031123 := bstep (se 1 (by rfl) ⟨773342, by rfl⟩ : syracuseStep 1031123 = 1546685) B1546685
theorem B1031251 : Blo 610295 1031251 := bstep (se 1 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 1031251 = 1546877) B1546877
theorem B1031393 : Blo 610295 1031393 := bstep (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) B773545
theorem B1031521 : Blo 610295 1031521 := bstep (se 2 (by rfl) ⟨386820, by rfl⟩ : syracuseStep 1031521 = 773641) B773641
theorem B1031555 : Blo 610295 1031555 := bstep (se 1 (by rfl) ⟨773666, by rfl⟩ : syracuseStep 1031555 = 1547333) B1547333
theorem B1031683 : Blo 610295 1031683 := bstep (se 1 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 1031683 = 1547525) B1547525
theorem B1031825 : Blo 610295 1031825 := bstep (se 2 (by rfl) ⟨386934, by rfl⟩ : syracuseStep 1031825 = 773869) B773869
theorem B3096305 : Blo 610295 3096305 := bstep (se 2 (by rfl) ⟨1161114, by rfl⟩ : syracuseStep 3096305 = 2322229) B2322229
theorem B1031953 : Blo 610295 1031953 := bstep (se 2 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 1031953 = 773965) B773965
theorem B1031987 : Blo 610295 1031987 := bstep (se 1 (by rfl) ⟨773990, by rfl⟩ : syracuseStep 1031987 = 1547981) B1547981
theorem B1163089 : Blo 610295 1163089 := bstep (se 2 (by rfl) ⟨436158, by rfl⟩ : syracuseStep 1163089 = 872317) B872317
theorem B1032115 : Blo 610295 1032115 := bstep (se 1 (by rfl) ⟨774086, by rfl⟩ : syracuseStep 1032115 = 1548173) B1548173
theorem B737267 : Blo 610295 737267 := bstep (se 1 (by rfl) ⟨552950, by rfl⟩ : syracuseStep 737267 = 1105901) B1105901
theorem B1032257 : Blo 610295 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B3489905 : Blo 610295 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B1032385 : Blo 610295 1032385 := bstep (se 2 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 1032385 = 774289) B774289
theorem B1032419 : Blo 610295 1032419 := bstep (se 1 (by rfl) ⟨774314, by rfl⟩ : syracuseStep 1032419 = 1548629) B1548629
theorem B1032547 : Blo 610295 1032547 := bstep (se 1 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 1032547 = 1548821) B1548821
theorem B1032689 : Blo 610295 1032689 := bstep (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) B774517
theorem B868963 : Blo 610295 868963 := bstep (se 1 (by rfl) ⟨651722, by rfl⟩ : syracuseStep 868963 = 1303445) B1303445
theorem B1032817 : Blo 610295 1032817 := bstep (se 2 (by rfl) ⟨387306, by rfl⟩ : syracuseStep 1032817 = 774613) B774613
theorem B1032851 : Blo 610295 1032851 := bstep (se 1 (by rfl) ⟨774638, by rfl⟩ : syracuseStep 1032851 = 1549277) B1549277
theorem B869059 : Blo 610295 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B4637411 : Blo 610295 4637411 := bstep (se 1 (by rfl) ⟨3478058, by rfl⟩ : syracuseStep 4637411 = 6956117) B6956117
theorem B1032979 : Blo 610295 1032979 := bstep (se 1 (by rfl) ⟨774734, by rfl⟩ : syracuseStep 1032979 = 1549469) B1549469
theorem B1164145 : Blo 610295 1164145 := bstep (se 2 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 1164145 = 873109) B873109
theorem B1033121 : Blo 610295 1033121 := bstep (se 2 (by rfl) ⟨387420, by rfl⟩ : syracuseStep 1033121 = 774841) B774841
theorem B1328113 : Blo 610295 1328113 := bstep (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) B996085
theorem B1033249 : Blo 610295 1033249 := bstep (se 2 (by rfl) ⟨387468, by rfl⟩ : syracuseStep 1033249 = 774937) B774937
theorem B1033283 : Blo 610295 1033283 := bstep (se 1 (by rfl) ⟨774962, by rfl⟩ : syracuseStep 1033283 = 1549925) B1549925
theorem B7554161 : Blo 610295 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B3097763 : Blo 610295 3097763 := bstep (se 1 (by rfl) ⟨2323322, by rfl⟩ : syracuseStep 3097763 = 4646645) B4646645
theorem B869555 : Blo 610295 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B1033411 : Blo 610295 1033411 := bstep (se 1 (by rfl) ⟨775058, by rfl⟩ : syracuseStep 1033411 = 1550117) B1550117
theorem B27280597 : Blo 610295 27280597 := bstep (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) B639389
theorem B1164547 : Blo 610295 1164547 := bstep (se 1 (by rfl) ⟨873410, by rfl⟩ : syracuseStep 1164547 = 1746821) B1746821
theorem B15680789 : Blo 610295 15680789 := bstep (se 6 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 15680789 = 735037) B735037
theorem B1164593 : Blo 610295 1164593 := bstep (se 2 (by rfl) ⟨436722, by rfl⟩ : syracuseStep 1164593 = 873445) B873445
theorem B1033553 : Blo 610295 1033553 := bstep (se 2 (by rfl) ⟨387582, by rfl⟩ : syracuseStep 1033553 = 775165) B775165
theorem B1033681 : Blo 610295 1033681 := bstep (se 2 (by rfl) ⟨387630, by rfl⟩ : syracuseStep 1033681 = 775261) B775261
theorem B2835953 : Blo 610295 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B1033715 : Blo 610295 1033715 := bstep (se 1 (by rfl) ⟨775286, by rfl⟩ : syracuseStep 1033715 = 1550573) B1550573
theorem B673283 : Blo 610295 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B3491363 : Blo 610295 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B4408901 : Blo 610295 4408901 := bstep (se 4 (by rfl) ⟨413334, by rfl⟩ : syracuseStep 4408901 = 826669) B826669
theorem B1164881 : Blo 610295 1164881 := bstep (se 2 (by rfl) ⟨436830, by rfl⟩ : syracuseStep 1164881 = 873661) B873661
theorem B1033843 : Blo 610295 1033843 := bstep (se 1 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 1033843 = 1550765) B1550765
theorem B1033985 : Blo 610295 1033985 := bstep (se 2 (by rfl) ⟨387744, by rfl⟩ : syracuseStep 1033985 = 775489) B775489
theorem B870193 : Blo 610295 870193 := bstep (se 2 (by rfl) ⟨326322, by rfl⟩ : syracuseStep 870193 = 652645) B652645
theorem B1034113 : Blo 610295 1034113 := bstep (se 2 (by rfl) ⟨387792, by rfl⟩ : syracuseStep 1034113 = 775585) B775585
theorem B1034147 : Blo 610295 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B2607025 : Blo 610295 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B3098573 : Blo 610295 3098573 := bstep (se 3 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 3098573 = 1161965) B1161965
theorem B1034275 : Blo 610295 1034275 := bstep (se 1 (by rfl) ⟨775706, by rfl⟩ : syracuseStep 1034275 = 1551413) B1551413
theorem B870529 : Blo 610295 870529 := bstep (se 2 (by rfl) ⟨326448, by rfl⟩ : syracuseStep 870529 = 652897) B652897
theorem B1034417 : Blo 610295 1034417 := bstep (se 2 (by rfl) ⟨387906, by rfl⟩ : syracuseStep 1034417 = 775813) B775813
theorem B2935075 : Blo 610295 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B1165603 : Blo 610295 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B1034545 : Blo 610295 1034545 := bstep (se 2 (by rfl) ⟨387954, by rfl⟩ : syracuseStep 1034545 = 775909) B775909
theorem B1034579 : Blo 610295 1034579 := bstep (se 1 (by rfl) ⟨775934, by rfl⟩ : syracuseStep 1034579 = 1551869) B1551869
theorem B1034707 : Blo 610295 1034707 := bstep (se 1 (by rfl) ⟨776030, by rfl⟩ : syracuseStep 1034707 = 1552061) B1552061
theorem B2509325 : Blo 610295 2509325 := bstep (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) B940997
theorem B1034849 : Blo 610295 1034849 := bstep (se 2 (by rfl) ⟨388068, by rfl⟩ : syracuseStep 1034849 = 776137) B776137
theorem B871121 : Blo 610295 871121 := bstep (se 2 (by rfl) ⟨326670, by rfl⟩ : syracuseStep 871121 = 653341) B653341
theorem B1034977 : Blo 610295 1034977 := bstep (se 2 (by rfl) ⟨388116, by rfl⟩ : syracuseStep 1034977 = 776233) B776233
theorem B1166051 : Blo 610295 1166051 := bstep (se 1 (by rfl) ⟨874538, by rfl⟩ : syracuseStep 1166051 = 1749077) B1749077
theorem B1035011 : Blo 610295 1035011 := bstep (se 1 (by rfl) ⟨776258, by rfl⟩ : syracuseStep 1035011 = 1552517) B1552517
theorem B1035139 : Blo 610295 1035139 := bstep (se 1 (by rfl) ⟨776354, by rfl⟩ : syracuseStep 1035139 = 1552709) B1552709
theorem B773059 : Blo 610295 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B1035281 : Blo 610295 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B773155 : Blo 610295 773155 := bstep (se 1 (by rfl) ⟨579866, by rfl⟩ : syracuseStep 773155 = 1159733) B1159733
theorem B1657901 : Blo 610295 1657901 := bstep (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) B621713
theorem B1035409 : Blo 610295 1035409 := bstep (se 2 (by rfl) ⟨388278, by rfl⟩ : syracuseStep 1035409 = 776557) B776557
theorem B2477233 : Blo 610295 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B1035443 : Blo 610295 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B871651 : Blo 610295 871651 := bstep (se 1 (by rfl) ⟨653738, by rfl⟩ : syracuseStep 871651 = 1307477) B1307477
theorem B6638861 : Blo 610295 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B1035571 : Blo 610295 1035571 := bstep (se 1 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 1035571 = 1553357) B1553357
theorem B1035713 : Blo 610295 1035713 := bstep (se 2 (by rfl) ⟨388392, by rfl⟩ : syracuseStep 1035713 = 776785) B776785
theorem B773651 : Blo 610295 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B871987 : Blo 610295 871987 := bstep (se 1 (by rfl) ⟨653990, by rfl⟩ : syracuseStep 871987 = 1307981) B1307981
theorem B1035841 : Blo 610295 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B1035875 : Blo 610295 1035875 := bstep (se 1 (by rfl) ⟨776906, by rfl⟩ : syracuseStep 1035875 = 1553813) B1553813
theorem B1036003 : Blo 610295 1036003 := bstep (se 1 (by rfl) ⟨777002, by rfl⟩ : syracuseStep 1036003 = 1554005) B1554005
theorem B1036145 : Blo 610295 1036145 := bstep (se 2 (by rfl) ⟨388554, by rfl⟩ : syracuseStep 1036145 = 777109) B777109
theorem B16175045 : Blo 610295 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1036273 : Blo 610295 1036273 := bstep (se 2 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 1036273 = 777205) B777205
theorem B610307 : Blo 610295 610307 := bstep (se 1 (by rfl) ⟨457730, by rfl⟩ : syracuseStep 610307 = 915461) B915461
theorem B610323 : Blo 610295 610323 := bstep (se 1 (by rfl) ⟨457742, by rfl⟩ : syracuseStep 610323 = 915485) B915485
theorem B1036307 : Blo 610295 1036307 := bstep (se 1 (by rfl) ⟨777230, by rfl⟩ : syracuseStep 1036307 = 1554461) B1554461
theorem B610339 : Blo 610295 610339 := bstep (se 1 (by rfl) ⟨457754, by rfl⟩ : syracuseStep 610339 = 915509) B915509
theorem B610355 : Blo 610295 610355 := bstep (se 1 (by rfl) ⟨457766, by rfl⟩ : syracuseStep 610355 = 915533) B915533
theorem B610371 : Blo 610295 610371 := bstep (se 1 (by rfl) ⟨457778, by rfl⟩ : syracuseStep 610371 = 915557) B915557
theorem B610387 : Blo 610295 610387 := bstep (se 1 (by rfl) ⟨457790, by rfl⟩ : syracuseStep 610387 = 915581) B915581
theorem B872545 : Blo 610295 872545 := bstep (se 2 (by rfl) ⟨327204, by rfl⟩ : syracuseStep 872545 = 654409) B654409
theorem B610403 : Blo 610295 610403 := bstep (se 1 (by rfl) ⟨457802, by rfl⟩ : syracuseStep 610403 = 915605) B915605
theorem B5656675 : Blo 610295 5656675 := bstep (se 1 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 5656675 = 8485013) B8485013
theorem B1101937 : Blo 610295 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B610419 : Blo 610295 610419 := bstep (se 1 (by rfl) ⟨457814, by rfl⟩ : syracuseStep 610419 = 915629) B915629
theorem B610435 : Blo 610295 610435 := bstep (se 1 (by rfl) ⟨457826, by rfl⟩ : syracuseStep 610435 = 915653) B915653
theorem B872579 : Blo 610295 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B610451 : Blo 610295 610451 := bstep (se 1 (by rfl) ⟨457838, by rfl⟩ : syracuseStep 610451 = 915677) B915677
theorem B1036435 : Blo 610295 1036435 := bstep (se 1 (by rfl) ⟨777326, by rfl⟩ : syracuseStep 1036435 = 1554653) B1554653
theorem B610467 : Blo 610295 610467 := bstep (se 1 (by rfl) ⟨457850, by rfl⟩ : syracuseStep 610467 = 915701) B915701
theorem B610483 : Blo 610295 610483 := bstep (se 1 (by rfl) ⟨457862, by rfl⟩ : syracuseStep 610483 = 915725) B915725
theorem B610499 : Blo 610295 610499 := bstep (se 1 (by rfl) ⟨457874, by rfl⟩ : syracuseStep 610499 = 915749) B915749
theorem B610515 : Blo 610295 610515 := bstep (se 1 (by rfl) ⟨457886, by rfl⟩ : syracuseStep 610515 = 915773) B915773
theorem B774355 : Blo 610295 774355 := bstep (se 1 (by rfl) ⟨580766, by rfl⟩ : syracuseStep 774355 = 1161533) B1161533
theorem B610531 : Blo 610295 610531 := bstep (se 1 (by rfl) ⟨457898, by rfl⟩ : syracuseStep 610531 = 915797) B915797
theorem B125751523 : Blo 610295 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B2937073 : Blo 610295 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B610547 : Blo 610295 610547 := bstep (se 1 (by rfl) ⟨457910, by rfl⟩ : syracuseStep 610547 = 915821) B915821
theorem B610563 : Blo 610295 610563 := bstep (se 1 (by rfl) ⟨457922, by rfl⟩ : syracuseStep 610563 = 915845) B915845
theorem B610579 : Blo 610295 610579 := bstep (se 1 (by rfl) ⟨457934, by rfl⟩ : syracuseStep 610579 = 915869) B915869
theorem B1036577 : Blo 610295 1036577 := bstep (se 2 (by rfl) ⟨388716, by rfl⟩ : syracuseStep 1036577 = 777433) B777433
theorem B610595 : Blo 610295 610595 := bstep (se 1 (by rfl) ⟨457946, by rfl⟩ : syracuseStep 610595 = 915893) B915893
theorem B610611 : Blo 610295 610611 := bstep (se 1 (by rfl) ⟨457958, by rfl⟩ : syracuseStep 610611 = 915917) B915917
theorem B774451 : Blo 610295 774451 := bstep (se 1 (by rfl) ⟨580838, by rfl⟩ : syracuseStep 774451 = 1161677) B1161677
theorem B610627 : Blo 610295 610627 := bstep (se 1 (by rfl) ⟨457970, by rfl⟩ : syracuseStep 610627 = 915941) B915941
theorem B610643 : Blo 610295 610643 := bstep (se 1 (by rfl) ⟨457982, by rfl⟩ : syracuseStep 610643 = 915965) B915965
theorem B610659 : Blo 610295 610659 := bstep (se 1 (by rfl) ⟨457994, by rfl⟩ : syracuseStep 610659 = 915989) B915989
theorem B610675 : Blo 610295 610675 := bstep (se 1 (by rfl) ⟨458006, by rfl⟩ : syracuseStep 610675 = 916013) B916013
theorem B610691 : Blo 610295 610691 := bstep (se 1 (by rfl) ⟨458018, by rfl⟩ : syracuseStep 610691 = 916037) B916037
theorem B610707 : Blo 610295 610707 := bstep (se 1 (by rfl) ⟨458030, by rfl⟩ : syracuseStep 610707 = 916061) B916061
theorem B610723 : Blo 610295 610723 := bstep (se 1 (by rfl) ⟨458042, by rfl⟩ : syracuseStep 610723 = 916085) B916085
theorem B610739 : Blo 610295 610739 := bstep (se 1 (by rfl) ⟨458054, by rfl⟩ : syracuseStep 610739 = 916109) B916109
theorem B610755 : Blo 610295 610755 := bstep (se 1 (by rfl) ⟨458066, by rfl⟩ : syracuseStep 610755 = 916133) B916133
theorem B610771 : Blo 610295 610771 := bstep (se 1 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 610771 = 916157) B916157
theorem B610787 : Blo 610295 610787 := bstep (se 1 (by rfl) ⟨458090, by rfl⟩ : syracuseStep 610787 = 916181) B916181
theorem B610803 : Blo 610295 610803 := bstep (se 1 (by rfl) ⟨458102, by rfl⟩ : syracuseStep 610803 = 916205) B916205
theorem B610819 : Blo 610295 610819 := bstep (se 1 (by rfl) ⟨458114, by rfl⟩ : syracuseStep 610819 = 916229) B916229
theorem B610835 : Blo 610295 610835 := bstep (se 1 (by rfl) ⟨458126, by rfl⟩ : syracuseStep 610835 = 916253) B916253
theorem B610851 : Blo 610295 610851 := bstep (se 1 (by rfl) ⟨458138, by rfl⟩ : syracuseStep 610851 = 916277) B916277
theorem B610867 : Blo 610295 610867 := bstep (se 1 (by rfl) ⟨458150, by rfl⟩ : syracuseStep 610867 = 916301) B916301
theorem B610883 : Blo 610295 610883 := bstep (se 1 (by rfl) ⟨458162, by rfl⟩ : syracuseStep 610883 = 916325) B916325
theorem B3723853 : Blo 610295 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B610899 : Blo 610295 610899 := bstep (se 1 (by rfl) ⟨458174, by rfl⟩ : syracuseStep 610899 = 916349) B916349
theorem B610915 : Blo 610295 610915 := bstep (se 1 (by rfl) ⟨458186, by rfl⟩ : syracuseStep 610915 = 916373) B916373
theorem B610931 : Blo 610295 610931 := bstep (se 1 (by rfl) ⟨458198, by rfl⟩ : syracuseStep 610931 = 916397) B916397
theorem B610947 : Blo 610295 610947 := bstep (se 1 (by rfl) ⟨458210, by rfl⟩ : syracuseStep 610947 = 916421) B916421
theorem B610963 : Blo 610295 610963 := bstep (se 1 (by rfl) ⟨458222, by rfl⟩ : syracuseStep 610963 = 916445) B916445
theorem B610979 : Blo 610295 610979 := bstep (se 1 (by rfl) ⟨458234, by rfl⟩ : syracuseStep 610979 = 916469) B916469
theorem B1102499 : Blo 610295 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B873137 : Blo 610295 873137 := bstep (se 2 (by rfl) ⟨327426, by rfl⟩ : syracuseStep 873137 = 654853) B654853
theorem B610995 : Blo 610295 610995 := bstep (se 1 (by rfl) ⟨458246, by rfl⟩ : syracuseStep 610995 = 916493) B916493
theorem B611011 : Blo 610295 611011 := bstep (se 1 (by rfl) ⟨458258, by rfl⟩ : syracuseStep 611011 = 916517) B916517
theorem B611027 : Blo 610295 611027 := bstep (se 1 (by rfl) ⟨458270, by rfl⟩ : syracuseStep 611027 = 916541) B916541
theorem B611043 : Blo 610295 611043 := bstep (se 1 (by rfl) ⟨458282, by rfl⟩ : syracuseStep 611043 = 916565) B916565
theorem B611059 : Blo 610295 611059 := bstep (se 1 (by rfl) ⟨458294, by rfl⟩ : syracuseStep 611059 = 916589) B916589
theorem B873217 : Blo 610295 873217 := bstep (se 2 (by rfl) ⟨327456, by rfl⟩ : syracuseStep 873217 = 654913) B654913
theorem B611075 : Blo 610295 611075 := bstep (se 1 (by rfl) ⟨458306, by rfl⟩ : syracuseStep 611075 = 916613) B916613
theorem B611091 : Blo 610295 611091 := bstep (se 1 (by rfl) ⟨458318, by rfl⟩ : syracuseStep 611091 = 916637) B916637
theorem B611107 : Blo 610295 611107 := bstep (se 1 (by rfl) ⟨458330, by rfl⟩ : syracuseStep 611107 = 916661) B916661
theorem B774947 : Blo 610295 774947 := bstep (se 1 (by rfl) ⟨581210, by rfl⟩ : syracuseStep 774947 = 1162421) B1162421
theorem B3101489 : Blo 610295 3101489 := bstep (se 2 (by rfl) ⟨1163058, by rfl⟩ : syracuseStep 3101489 = 2326117) B2326117
theorem B611123 : Blo 610295 611123 := bstep (se 1 (by rfl) ⟨458342, by rfl⟩ : syracuseStep 611123 = 916685) B916685
theorem B611139 : Blo 610295 611139 := bstep (se 1 (by rfl) ⟨458354, by rfl⟩ : syracuseStep 611139 = 916709) B916709
theorem B611155 : Blo 610295 611155 := bstep (se 1 (by rfl) ⟨458366, by rfl⟩ : syracuseStep 611155 = 916733) B916733
theorem B611171 : Blo 610295 611171 := bstep (se 1 (by rfl) ⟨458378, by rfl⟩ : syracuseStep 611171 = 916757) B916757
theorem B611187 : Blo 610295 611187 := bstep (se 1 (by rfl) ⟨458390, by rfl⟩ : syracuseStep 611187 = 916781) B916781
theorem B611203 : Blo 610295 611203 := bstep (se 1 (by rfl) ⟨458402, by rfl⟩ : syracuseStep 611203 = 916805) B916805
theorem B1659793 : Blo 610295 1659793 := bstep (se 2 (by rfl) ⟨622422, by rfl⟩ : syracuseStep 1659793 = 1244845) B1244845
theorem B611219 : Blo 610295 611219 := bstep (se 1 (by rfl) ⟨458414, by rfl⟩ : syracuseStep 611219 = 916829) B916829
theorem B2610083 : Blo 610295 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B611235 : Blo 610295 611235 := bstep (se 1 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 611235 = 916853) B916853
theorem B611251 : Blo 610295 611251 := bstep (se 1 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 611251 = 916877) B916877
theorem B611267 : Blo 610295 611267 := bstep (se 1 (by rfl) ⟨458450, by rfl⟩ : syracuseStep 611267 = 916901) B916901
theorem B611283 : Blo 610295 611283 := bstep (se 1 (by rfl) ⟨458462, by rfl⟩ : syracuseStep 611283 = 916925) B916925
theorem B611299 : Blo 610295 611299 := bstep (se 1 (by rfl) ⟨458474, by rfl⟩ : syracuseStep 611299 = 916949) B916949
theorem B1659889 : Blo 610295 1659889 := bstep (se 2 (by rfl) ⟨622458, by rfl⟩ : syracuseStep 1659889 = 1244917) B1244917
theorem B611315 : Blo 610295 611315 := bstep (se 1 (by rfl) ⟨458486, by rfl⟩ : syracuseStep 611315 = 916973) B916973
theorem B611331 : Blo 610295 611331 := bstep (se 1 (by rfl) ⟨458498, by rfl⟩ : syracuseStep 611331 = 916997) B916997
theorem B611347 : Blo 610295 611347 := bstep (se 1 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 611347 = 917021) B917021
theorem B611363 : Blo 610295 611363 := bstep (se 1 (by rfl) ⟨458522, by rfl⟩ : syracuseStep 611363 = 917045) B917045
theorem B611379 : Blo 610295 611379 := bstep (se 1 (by rfl) ⟨458534, by rfl⟩ : syracuseStep 611379 = 917069) B917069
theorem B611395 : Blo 610295 611395 := bstep (se 1 (by rfl) ⟨458546, by rfl⟩ : syracuseStep 611395 = 917093) B917093
theorem B611411 : Blo 610295 611411 := bstep (se 1 (by rfl) ⟨458558, by rfl⟩ : syracuseStep 611411 = 917117) B917117
theorem B611427 : Blo 610295 611427 := bstep (se 1 (by rfl) ⟨458570, by rfl⟩ : syracuseStep 611427 = 917141) B917141
theorem B611443 : Blo 610295 611443 := bstep (se 1 (by rfl) ⟨458582, by rfl⟩ : syracuseStep 611443 = 917165) B917165
theorem B611459 : Blo 610295 611459 := bstep (se 1 (by rfl) ⟨458594, by rfl⟩ : syracuseStep 611459 = 917189) B917189
theorem B611475 : Blo 610295 611475 := bstep (se 1 (by rfl) ⟨458606, by rfl⟩ : syracuseStep 611475 = 917213) B917213
theorem B611491 : Blo 610295 611491 := bstep (se 1 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 611491 = 917237) B917237
theorem B1889453 : Blo 610295 1889453 := bstep (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) B708545
theorem B611507 : Blo 610295 611507 := bstep (se 1 (by rfl) ⟨458630, by rfl⟩ : syracuseStep 611507 = 917261) B917261
theorem B611523 : Blo 610295 611523 := bstep (se 1 (by rfl) ⟨458642, by rfl⟩ : syracuseStep 611523 = 917285) B917285
theorem B611539 : Blo 610295 611539 := bstep (se 1 (by rfl) ⟨458654, by rfl⟩ : syracuseStep 611539 = 917309) B917309
theorem B808147 : Blo 610295 808147 := bstep (se 1 (by rfl) ⟨606110, by rfl⟩ : syracuseStep 808147 = 1212221) B1212221
theorem B611555 : Blo 610295 611555 := bstep (se 1 (by rfl) ⟨458666, by rfl⟩ : syracuseStep 611555 = 917333) B917333
theorem B611571 : Blo 610295 611571 := bstep (se 1 (by rfl) ⟨458678, by rfl⟩ : syracuseStep 611571 = 917357) B917357
theorem B611587 : Blo 610295 611587 := bstep (se 1 (by rfl) ⟨458690, by rfl⟩ : syracuseStep 611587 = 917381) B917381
theorem B611603 : Blo 610295 611603 := bstep (se 1 (by rfl) ⟨458702, by rfl⟩ : syracuseStep 611603 = 917405) B917405
theorem B611619 : Blo 610295 611619 := bstep (se 1 (by rfl) ⟨458714, by rfl⟩ : syracuseStep 611619 = 917429) B917429
theorem B611635 : Blo 610295 611635 := bstep (se 1 (by rfl) ⟨458726, by rfl⟩ : syracuseStep 611635 = 917453) B917453
theorem B611651 : Blo 610295 611651 := bstep (se 1 (by rfl) ⟨458738, by rfl⟩ : syracuseStep 611651 = 917477) B917477
theorem B2938189 : Blo 610295 2938189 := bstep (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) B1101821
theorem B611667 : Blo 610295 611667 := bstep (se 1 (by rfl) ⟨458750, by rfl⟩ : syracuseStep 611667 = 917501) B917501
theorem B611683 : Blo 610295 611683 := bstep (se 1 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 611683 = 917525) B917525
theorem B611699 : Blo 610295 611699 := bstep (se 1 (by rfl) ⟨458774, by rfl⟩ : syracuseStep 611699 = 917549) B917549
theorem B611715 : Blo 610295 611715 := bstep (se 1 (by rfl) ⟨458786, by rfl⟩ : syracuseStep 611715 = 917573) B917573
theorem B611731 : Blo 610295 611731 := bstep (se 1 (by rfl) ⟨458798, by rfl⟩ : syracuseStep 611731 = 917597) B917597
theorem B611747 : Blo 610295 611747 := bstep (se 1 (by rfl) ⟨458810, by rfl⟩ : syracuseStep 611747 = 917621) B917621
theorem B611763 : Blo 610295 611763 := bstep (se 1 (by rfl) ⟨458822, by rfl⟩ : syracuseStep 611763 = 917645) B917645
theorem B611779 : Blo 610295 611779 := bstep (se 1 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 611779 = 917669) B917669
theorem B1955281 : Blo 610295 1955281 := bstep (se 2 (by rfl) ⟨733230, by rfl⟩ : syracuseStep 1955281 = 1466461) B1466461
theorem B611795 : Blo 610295 611795 := bstep (se 1 (by rfl) ⟨458846, by rfl⟩ : syracuseStep 611795 = 917693) B917693
theorem B611811 : Blo 610295 611811 := bstep (se 1 (by rfl) ⟨458858, by rfl⟩ : syracuseStep 611811 = 917717) B917717
theorem B775651 : Blo 610295 775651 := bstep (se 1 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 775651 = 1163477) B1163477
theorem B611827 : Blo 610295 611827 := bstep (se 1 (by rfl) ⟨458870, by rfl⟩ : syracuseStep 611827 = 917741) B917741
theorem B611843 : Blo 610295 611843 := bstep (se 1 (by rfl) ⟨458882, by rfl⟩ : syracuseStep 611843 = 917765) B917765
theorem B611859 : Blo 610295 611859 := bstep (se 1 (by rfl) ⟨458894, by rfl⟩ : syracuseStep 611859 = 917789) B917789
theorem B874003 : Blo 610295 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B611875 : Blo 610295 611875 := bstep (se 1 (by rfl) ⟨458906, by rfl⟩ : syracuseStep 611875 = 917813) B917813
theorem B611891 : Blo 610295 611891 := bstep (se 1 (by rfl) ⟨458918, by rfl⟩ : syracuseStep 611891 = 917837) B917837
theorem B611907 : Blo 610295 611907 := bstep (se 1 (by rfl) ⟨458930, by rfl⟩ : syracuseStep 611907 = 917861) B917861
theorem B775747 : Blo 610295 775747 := bstep (se 1 (by rfl) ⟨581810, by rfl⟩ : syracuseStep 775747 = 1163621) B1163621
theorem B611923 : Blo 610295 611923 := bstep (se 1 (by rfl) ⟨458942, by rfl⟩ : syracuseStep 611923 = 917885) B917885
theorem B611939 : Blo 610295 611939 := bstep (se 1 (by rfl) ⟨458954, by rfl⟩ : syracuseStep 611939 = 917909) B917909
theorem B1103473 : Blo 610295 1103473 := bstep (se 2 (by rfl) ⟨413802, by rfl⟩ : syracuseStep 1103473 = 827605) B827605
theorem B611955 : Blo 610295 611955 := bstep (se 1 (by rfl) ⟨458966, by rfl⟩ : syracuseStep 611955 = 917933) B917933
theorem B611971 : Blo 610295 611971 := bstep (se 1 (by rfl) ⟨458978, by rfl⟩ : syracuseStep 611971 = 917957) B917957
theorem B611987 : Blo 610295 611987 := bstep (se 1 (by rfl) ⟨458990, by rfl⟩ : syracuseStep 611987 = 917981) B917981
theorem B612003 : Blo 610295 612003 := bstep (se 1 (by rfl) ⟨459002, by rfl⟩ : syracuseStep 612003 = 918005) B918005
theorem B1103537 : Blo 610295 1103537 := bstep (se 2 (by rfl) ⟨413826, by rfl⟩ : syracuseStep 1103537 = 827653) B827653
theorem B612019 : Blo 610295 612019 := bstep (se 1 (by rfl) ⟨459014, by rfl⟩ : syracuseStep 612019 = 918029) B918029
theorem B612035 : Blo 610295 612035 := bstep (se 1 (by rfl) ⟨459026, by rfl⟩ : syracuseStep 612035 = 918053) B918053
theorem B612051 : Blo 610295 612051 := bstep (se 1 (by rfl) ⟨459038, by rfl⟩ : syracuseStep 612051 = 918077) B918077
theorem B612067 : Blo 610295 612067 := bstep (se 1 (by rfl) ⟨459050, by rfl⟩ : syracuseStep 612067 = 918101) B918101
theorem B612083 : Blo 610295 612083 := bstep (se 1 (by rfl) ⟨459062, by rfl⟩ : syracuseStep 612083 = 918125) B918125
theorem B612099 : Blo 610295 612099 := bstep (se 1 (by rfl) ⟨459074, by rfl⟩ : syracuseStep 612099 = 918149) B918149
theorem B5232397 : Blo 610295 5232397 := bstep (se 3 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 5232397 = 1962149) B1962149
theorem B612115 : Blo 610295 612115 := bstep (se 1 (by rfl) ⟨459086, by rfl⟩ : syracuseStep 612115 = 918173) B918173
theorem B612131 : Blo 610295 612131 := bstep (se 1 (by rfl) ⟨459098, by rfl⟩ : syracuseStep 612131 = 918197) B918197
theorem B612147 : Blo 610295 612147 := bstep (se 1 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 612147 = 918221) B918221
theorem B612163 : Blo 610295 612163 := bstep (se 1 (by rfl) ⟨459122, by rfl⟩ : syracuseStep 612163 = 918245) B918245
theorem B612179 : Blo 610295 612179 := bstep (se 1 (by rfl) ⟨459134, by rfl⟩ : syracuseStep 612179 = 918269) B918269
theorem B612195 : Blo 610295 612195 := bstep (se 1 (by rfl) ⟨459146, by rfl⟩ : syracuseStep 612195 = 918293) B918293
theorem B612211 : Blo 610295 612211 := bstep (se 1 (by rfl) ⟨459158, by rfl⟩ : syracuseStep 612211 = 918317) B918317
theorem B612227 : Blo 610295 612227 := bstep (se 1 (by rfl) ⟨459170, by rfl⟩ : syracuseStep 612227 = 918341) B918341
theorem B612243 : Blo 610295 612243 := bstep (se 1 (by rfl) ⟨459182, by rfl⟩ : syracuseStep 612243 = 918365) B918365
theorem B612259 : Blo 610295 612259 := bstep (se 1 (by rfl) ⟨459194, by rfl⟩ : syracuseStep 612259 = 918389) B918389
theorem B612275 : Blo 610295 612275 := bstep (se 1 (by rfl) ⟨459206, by rfl⟩ : syracuseStep 612275 = 918413) B918413
theorem B612291 : Blo 610295 612291 := bstep (se 1 (by rfl) ⟨459218, by rfl⟩ : syracuseStep 612291 = 918437) B918437
theorem B4642757 : Blo 610295 4642757 := bstep (se 4 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 4642757 = 870517) B870517
theorem B612307 : Blo 610295 612307 := bstep (se 1 (by rfl) ⟨459230, by rfl⟩ : syracuseStep 612307 = 918461) B918461
theorem B612323 : Blo 610295 612323 := bstep (se 1 (by rfl) ⟨459242, by rfl⟩ : syracuseStep 612323 = 918485) B918485
theorem B874481 : Blo 610295 874481 := bstep (se 2 (by rfl) ⟨327930, by rfl⟩ : syracuseStep 874481 = 655861) B655861
theorem B612339 : Blo 610295 612339 := bstep (se 1 (by rfl) ⟨459254, by rfl⟩ : syracuseStep 612339 = 918509) B918509
theorem B612355 : Blo 610295 612355 := bstep (se 1 (by rfl) ⟨459266, by rfl⟩ : syracuseStep 612355 = 918533) B918533
theorem B612371 : Blo 610295 612371 := bstep (se 1 (by rfl) ⟨459278, by rfl⟩ : syracuseStep 612371 = 918557) B918557
theorem B612387 : Blo 610295 612387 := bstep (se 1 (by rfl) ⟨459290, by rfl⟩ : syracuseStep 612387 = 918581) B918581
theorem B612403 : Blo 610295 612403 := bstep (se 1 (by rfl) ⟨459302, by rfl⟩ : syracuseStep 612403 = 918605) B918605
theorem B776243 : Blo 610295 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B612419 : Blo 610295 612419 := bstep (se 1 (by rfl) ⟨459314, by rfl⟩ : syracuseStep 612419 = 918629) B918629
theorem B612435 : Blo 610295 612435 := bstep (se 1 (by rfl) ⟨459326, by rfl⟩ : syracuseStep 612435 = 918653) B918653
theorem B612451 : Blo 610295 612451 := bstep (se 1 (by rfl) ⟨459338, by rfl⟩ : syracuseStep 612451 = 918677) B918677
theorem B874595 : Blo 610295 874595 := bstep (se 1 (by rfl) ⟨655946, by rfl⟩ : syracuseStep 874595 = 1311893) B1311893
theorem B612467 : Blo 610295 612467 := bstep (se 1 (by rfl) ⟨459350, by rfl⟩ : syracuseStep 612467 = 918701) B918701
theorem B612483 : Blo 610295 612483 := bstep (se 1 (by rfl) ⟨459362, by rfl⟩ : syracuseStep 612483 = 918725) B918725
theorem B612499 : Blo 610295 612499 := bstep (se 1 (by rfl) ⟨459374, by rfl⟩ : syracuseStep 612499 = 918749) B918749
theorem B612515 : Blo 610295 612515 := bstep (se 1 (by rfl) ⟨459386, by rfl⟩ : syracuseStep 612515 = 918773) B918773
theorem B612531 : Blo 610295 612531 := bstep (se 1 (by rfl) ⟨459398, by rfl⟩ : syracuseStep 612531 = 918797) B918797
theorem B612547 : Blo 610295 612547 := bstep (se 1 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 612547 = 918821) B918821
theorem B3725509 : Blo 610295 3725509 := bstep (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) B698533
theorem B612563 : Blo 610295 612563 := bstep (se 1 (by rfl) ⟨459422, by rfl⟩ : syracuseStep 612563 = 918845) B918845
theorem B612579 : Blo 610295 612579 := bstep (se 1 (by rfl) ⟨459434, by rfl⟩ : syracuseStep 612579 = 918869) B918869
theorem B3102947 : Blo 610295 3102947 := bstep (se 1 (by rfl) ⟨2327210, by rfl⟩ : syracuseStep 3102947 = 4654421) B4654421
theorem B612595 : Blo 610295 612595 := bstep (se 1 (by rfl) ⟨459446, by rfl⟩ : syracuseStep 612595 = 918893) B918893
theorem B612611 : Blo 610295 612611 := bstep (se 1 (by rfl) ⟨459458, by rfl⟩ : syracuseStep 612611 = 918917) B918917
theorem B612627 : Blo 610295 612627 := bstep (se 1 (by rfl) ⟨459470, by rfl⟩ : syracuseStep 612627 = 918941) B918941
theorem B612643 : Blo 610295 612643 := bstep (se 1 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 612643 = 918965) B918965
theorem B612659 : Blo 610295 612659 := bstep (se 1 (by rfl) ⟨459494, by rfl⟩ : syracuseStep 612659 = 918989) B918989
theorem B612675 : Blo 610295 612675 := bstep (se 1 (by rfl) ⟨459506, by rfl⟩ : syracuseStep 612675 = 919013) B919013
theorem B612691 : Blo 610295 612691 := bstep (se 1 (by rfl) ⟨459518, by rfl⟩ : syracuseStep 612691 = 919037) B919037
theorem B612707 : Blo 610295 612707 := bstep (se 1 (by rfl) ⟨459530, by rfl⟩ : syracuseStep 612707 = 919061) B919061
theorem B612723 : Blo 610295 612723 := bstep (se 1 (by rfl) ⟨459542, by rfl⟩ : syracuseStep 612723 = 919085) B919085
theorem B612739 : Blo 610295 612739 := bstep (se 1 (by rfl) ⟨459554, by rfl⟩ : syracuseStep 612739 = 919109) B919109
theorem B1857937 : Blo 610295 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B612755 : Blo 610295 612755 := bstep (se 1 (by rfl) ⟨459566, by rfl⟩ : syracuseStep 612755 = 919133) B919133
theorem B612771 : Blo 610295 612771 := bstep (se 1 (by rfl) ⟨459578, by rfl⟩ : syracuseStep 612771 = 919157) B919157
theorem B612787 : Blo 610295 612787 := bstep (se 1 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 612787 = 919181) B919181
theorem B612803 : Blo 610295 612803 := bstep (se 1 (by rfl) ⟨459602, by rfl⟩ : syracuseStep 612803 = 919205) B919205
theorem B612819 : Blo 610295 612819 := bstep (se 1 (by rfl) ⟨459614, by rfl⟩ : syracuseStep 612819 = 919229) B919229
theorem B612835 : Blo 610295 612835 := bstep (se 1 (by rfl) ⟨459626, by rfl⟩ : syracuseStep 612835 = 919253) B919253
theorem B612851 : Blo 610295 612851 := bstep (se 1 (by rfl) ⟨459638, by rfl⟩ : syracuseStep 612851 = 919277) B919277
theorem B612867 : Blo 610295 612867 := bstep (se 1 (by rfl) ⟨459650, by rfl⟩ : syracuseStep 612867 = 919301) B919301
theorem B612883 : Blo 610295 612883 := bstep (se 1 (by rfl) ⟨459662, by rfl⟩ : syracuseStep 612883 = 919325) B919325
theorem B612899 : Blo 610295 612899 := bstep (se 1 (by rfl) ⟨459674, by rfl⟩ : syracuseStep 612899 = 919349) B919349
theorem B612915 : Blo 610295 612915 := bstep (se 1 (by rfl) ⟨459686, by rfl⟩ : syracuseStep 612915 = 919373) B919373
theorem B612931 : Blo 610295 612931 := bstep (se 1 (by rfl) ⟨459698, by rfl⟩ : syracuseStep 612931 = 919397) B919397
theorem B612947 : Blo 610295 612947 := bstep (se 1 (by rfl) ⟨459710, by rfl⟩ : syracuseStep 612947 = 919421) B919421
theorem B612963 : Blo 610295 612963 := bstep (se 1 (by rfl) ⟨459722, by rfl⟩ : syracuseStep 612963 = 919445) B919445
theorem B612979 : Blo 610295 612979 := bstep (se 1 (by rfl) ⟨459734, by rfl⟩ : syracuseStep 612979 = 919469) B919469
theorem B612995 : Blo 610295 612995 := bstep (se 1 (by rfl) ⟨459746, by rfl⟩ : syracuseStep 612995 = 919493) B919493
theorem B613011 : Blo 610295 613011 := bstep (se 1 (by rfl) ⟨459758, by rfl⟩ : syracuseStep 613011 = 919517) B919517
theorem B613027 : Blo 610295 613027 := bstep (se 1 (by rfl) ⟨459770, by rfl⟩ : syracuseStep 613027 = 919541) B919541
theorem B613043 : Blo 610295 613043 := bstep (se 1 (by rfl) ⟨459782, by rfl⟩ : syracuseStep 613043 = 919565) B919565
theorem B613059 : Blo 610295 613059 := bstep (se 1 (by rfl) ⟨459794, by rfl⟩ : syracuseStep 613059 = 919589) B919589
theorem B613075 : Blo 610295 613075 := bstep (se 1 (by rfl) ⟨459806, by rfl⟩ : syracuseStep 613075 = 919613) B919613
theorem B613091 : Blo 610295 613091 := bstep (se 1 (by rfl) ⟨459818, by rfl⟩ : syracuseStep 613091 = 919637) B919637
theorem B613107 : Blo 610295 613107 := bstep (se 1 (by rfl) ⟨459830, by rfl⟩ : syracuseStep 613107 = 919661) B919661
theorem B776947 : Blo 610295 776947 := bstep (se 1 (by rfl) ⟨582710, by rfl⟩ : syracuseStep 776947 = 1165421) B1165421
theorem B613123 : Blo 610295 613123 := bstep (se 1 (by rfl) ⟨459842, by rfl⟩ : syracuseStep 613123 = 919685) B919685
theorem B613139 : Blo 610295 613139 := bstep (se 1 (by rfl) ⟨459854, by rfl⟩ : syracuseStep 613139 = 919709) B919709
theorem B613155 : Blo 610295 613155 := bstep (se 1 (by rfl) ⟨459866, by rfl⟩ : syracuseStep 613155 = 919733) B919733
theorem B613171 : Blo 610295 613171 := bstep (se 1 (by rfl) ⟨459878, by rfl⟩ : syracuseStep 613171 = 919757) B919757
theorem B613187 : Blo 610295 613187 := bstep (se 1 (by rfl) ⟨459890, by rfl⟩ : syracuseStep 613187 = 919781) B919781
theorem B613203 : Blo 610295 613203 := bstep (se 1 (by rfl) ⟨459902, by rfl⟩ : syracuseStep 613203 = 919805) B919805
theorem B777043 : Blo 610295 777043 := bstep (se 1 (by rfl) ⟨582782, by rfl⟩ : syracuseStep 777043 = 1165565) B1165565
theorem B613219 : Blo 610295 613219 := bstep (se 1 (by rfl) ⟨459914, by rfl⟩ : syracuseStep 613219 = 919829) B919829
theorem B613235 : Blo 610295 613235 := bstep (se 1 (by rfl) ⟨459926, by rfl⟩ : syracuseStep 613235 = 919853) B919853
theorem B613251 : Blo 610295 613251 := bstep (se 1 (by rfl) ⟨459938, by rfl⟩ : syracuseStep 613251 = 919877) B919877
theorem B613267 : Blo 610295 613267 := bstep (se 1 (by rfl) ⟨459950, by rfl⟩ : syracuseStep 613267 = 919901) B919901
theorem B613283 : Blo 610295 613283 := bstep (se 1 (by rfl) ⟨459962, by rfl⟩ : syracuseStep 613283 = 919925) B919925
theorem B613299 : Blo 610295 613299 := bstep (se 1 (by rfl) ⟨459974, by rfl⟩ : syracuseStep 613299 = 919949) B919949
theorem B613315 : Blo 610295 613315 := bstep (se 1 (by rfl) ⟨459986, by rfl⟩ : syracuseStep 613315 = 919973) B919973
theorem B613331 : Blo 610295 613331 := bstep (se 1 (by rfl) ⟨459998, by rfl⟩ : syracuseStep 613331 = 919997) B919997
theorem B613347 : Blo 610295 613347 := bstep (se 1 (by rfl) ⟨460010, by rfl⟩ : syracuseStep 613347 = 920021) B920021
theorem B613363 : Blo 610295 613363 := bstep (se 1 (by rfl) ⟨460022, by rfl⟩ : syracuseStep 613363 = 920045) B920045
theorem B613379 : Blo 610295 613379 := bstep (se 1 (by rfl) ⟨460034, by rfl⟩ : syracuseStep 613379 = 920069) B920069
theorem B3103757 : Blo 610295 3103757 := bstep (se 3 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 3103757 = 1163909) B1163909
theorem B613395 : Blo 610295 613395 := bstep (se 1 (by rfl) ⟨460046, by rfl⟩ : syracuseStep 613395 = 920093) B920093
theorem B613411 : Blo 610295 613411 := bstep (se 1 (by rfl) ⟨460058, by rfl⟩ : syracuseStep 613411 = 920117) B920117
theorem B613427 : Blo 610295 613427 := bstep (se 1 (by rfl) ⟨460070, by rfl⟩ : syracuseStep 613427 = 920141) B920141
theorem B7855157 : Blo 610295 7855157 := bstep (se 5 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 7855157 = 736421) B736421
theorem B613443 : Blo 610295 613443 := bstep (se 1 (by rfl) ⟨460082, by rfl⟩ : syracuseStep 613443 = 920165) B920165
theorem B5233733 : Blo 610295 5233733 := bstep (se 4 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 5233733 = 981325) B981325
theorem B613459 : Blo 610295 613459 := bstep (se 1 (by rfl) ⟨460094, by rfl⟩ : syracuseStep 613459 = 920189) B920189
theorem B613475 : Blo 610295 613475 := bstep (se 1 (by rfl) ⟨460106, by rfl⟩ : syracuseStep 613475 = 920213) B920213
theorem B1956973 : Blo 610295 1956973 := bstep (se 3 (by rfl) ⟨366932, by rfl⟩ : syracuseStep 1956973 = 733865) B733865
theorem B613491 : Blo 610295 613491 := bstep (se 1 (by rfl) ⟨460118, by rfl⟩ : syracuseStep 613491 = 920237) B920237
theorem B613507 : Blo 610295 613507 := bstep (se 1 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 613507 = 920261) B920261
theorem B613523 : Blo 610295 613523 := bstep (se 1 (by rfl) ⟨460142, by rfl⟩ : syracuseStep 613523 = 920285) B920285
theorem B613539 : Blo 610295 613539 := bstep (se 1 (by rfl) ⟨460154, by rfl⟩ : syracuseStep 613539 = 920309) B920309
theorem B613555 : Blo 610295 613555 := bstep (se 1 (by rfl) ⟨460166, by rfl⟩ : syracuseStep 613555 = 920333) B920333
theorem B613571 : Blo 610295 613571 := bstep (se 1 (by rfl) ⟨460178, by rfl⟩ : syracuseStep 613571 = 920357) B920357
theorem B613587 : Blo 610295 613587 := bstep (se 1 (by rfl) ⟨460190, by rfl⟩ : syracuseStep 613587 = 920381) B920381
theorem B613603 : Blo 610295 613603 := bstep (se 1 (by rfl) ⟨460202, by rfl⟩ : syracuseStep 613603 = 920405) B920405
theorem B613619 : Blo 610295 613619 := bstep (se 1 (by rfl) ⟨460214, by rfl⟩ : syracuseStep 613619 = 920429) B920429
theorem B613635 : Blo 610295 613635 := bstep (se 1 (by rfl) ⟨460226, by rfl⟩ : syracuseStep 613635 = 920453) B920453
theorem B613651 : Blo 610295 613651 := bstep (se 1 (by rfl) ⟨460238, by rfl⟩ : syracuseStep 613651 = 920477) B920477
theorem B613667 : Blo 610295 613667 := bstep (se 1 (by rfl) ⟨460250, by rfl⟩ : syracuseStep 613667 = 920501) B920501
theorem B613683 : Blo 610295 613683 := bstep (se 1 (by rfl) ⟨460262, by rfl⟩ : syracuseStep 613683 = 920525) B920525
theorem B613699 : Blo 610295 613699 := bstep (se 1 (by rfl) ⟨460274, by rfl⟩ : syracuseStep 613699 = 920549) B920549
theorem B613715 : Blo 610295 613715 := bstep (se 1 (by rfl) ⟨460286, by rfl⟩ : syracuseStep 613715 = 920573) B920573
theorem B613731 : Blo 610295 613731 := bstep (se 1 (by rfl) ⟨460298, by rfl⟩ : syracuseStep 613731 = 920597) B920597
theorem B613747 : Blo 610295 613747 := bstep (se 1 (by rfl) ⟨460310, by rfl⟩ : syracuseStep 613747 = 920621) B920621
theorem B613763 : Blo 610295 613763 := bstep (se 1 (by rfl) ⟨460322, by rfl⟩ : syracuseStep 613763 = 920645) B920645
theorem B3300749 : Blo 610295 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B4709773 : Blo 610295 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B613779 : Blo 610295 613779 := bstep (se 1 (by rfl) ⟨460334, by rfl⟩ : syracuseStep 613779 = 920669) B920669
theorem B613795 : Blo 610295 613795 := bstep (se 1 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 613795 = 920693) B920693
theorem B613811 : Blo 610295 613811 := bstep (se 1 (by rfl) ⟨460358, by rfl⟩ : syracuseStep 613811 = 920717) B920717
theorem B613827 : Blo 610295 613827 := bstep (se 1 (by rfl) ⟨460370, by rfl⟩ : syracuseStep 613827 = 920741) B920741
theorem B613843 : Blo 610295 613843 := bstep (se 1 (by rfl) ⟨460382, by rfl⟩ : syracuseStep 613843 = 920765) B920765
theorem B613859 : Blo 610295 613859 := bstep (se 1 (by rfl) ⟨460394, by rfl⟩ : syracuseStep 613859 = 920789) B920789
theorem B613875 : Blo 610295 613875 := bstep (se 1 (by rfl) ⟨460406, by rfl⟩ : syracuseStep 613875 = 920813) B920813
theorem B613891 : Blo 610295 613891 := bstep (se 1 (by rfl) ⟨460418, by rfl⟩ : syracuseStep 613891 = 920837) B920837
theorem B613907 : Blo 610295 613907 := bstep (se 1 (by rfl) ⟨460430, by rfl⟩ : syracuseStep 613907 = 920861) B920861
theorem B613923 : Blo 610295 613923 := bstep (se 1 (by rfl) ⟨460442, by rfl⟩ : syracuseStep 613923 = 920885) B920885
theorem B613939 : Blo 610295 613939 := bstep (se 1 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 613939 = 920909) B920909
theorem B613955 : Blo 610295 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B613971 : Blo 610295 613971 := bstep (se 1 (by rfl) ⟨460478, by rfl⟩ : syracuseStep 613971 = 920957) B920957
theorem B613987 : Blo 610295 613987 := bstep (se 1 (by rfl) ⟨460490, by rfl⟩ : syracuseStep 613987 = 920981) B920981
theorem B614003 : Blo 610295 614003 := bstep (se 1 (by rfl) ⟨460502, by rfl⟩ : syracuseStep 614003 = 921005) B921005
theorem B614019 : Blo 610295 614019 := bstep (se 1 (by rfl) ⟨460514, by rfl⟩ : syracuseStep 614019 = 921029) B921029
theorem B614035 : Blo 610295 614035 := bstep (se 1 (by rfl) ⟨460526, by rfl⟩ : syracuseStep 614035 = 921053) B921053
theorem B614051 : Blo 610295 614051 := bstep (se 1 (by rfl) ⟨460538, by rfl⟩ : syracuseStep 614051 = 921077) B921077
theorem B614067 : Blo 610295 614067 := bstep (se 1 (by rfl) ⟨460550, by rfl⟩ : syracuseStep 614067 = 921101) B921101
theorem B614083 : Blo 610295 614083 := bstep (se 1 (by rfl) ⟨460562, by rfl⟩ : syracuseStep 614083 = 921125) B921125
theorem B614099 : Blo 610295 614099 := bstep (se 1 (by rfl) ⟨460574, by rfl⟩ : syracuseStep 614099 = 921149) B921149
theorem B614115 : Blo 610295 614115 := bstep (se 1 (by rfl) ⟨460586, by rfl⟩ : syracuseStep 614115 = 921173) B921173
theorem B614131 : Blo 610295 614131 := bstep (se 1 (by rfl) ⟨460598, by rfl⟩ : syracuseStep 614131 = 921197) B921197
theorem B614147 : Blo 610295 614147 := bstep (se 1 (by rfl) ⟨460610, by rfl⟩ : syracuseStep 614147 = 921221) B921221
theorem B614163 : Blo 610295 614163 := bstep (se 1 (by rfl) ⟨460622, by rfl⟩ : syracuseStep 614163 = 921245) B921245
theorem B614179 : Blo 610295 614179 := bstep (se 1 (by rfl) ⟨460634, by rfl⟩ : syracuseStep 614179 = 921269) B921269
theorem B2318129 : Blo 610295 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B2416433 : Blo 610295 2416433 := bstep (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) B1812325
theorem B614195 : Blo 610295 614195 := bstep (se 1 (by rfl) ⟨460646, by rfl⟩ : syracuseStep 614195 = 921293) B921293
theorem B614211 : Blo 610295 614211 := bstep (se 1 (by rfl) ⟨460658, by rfl⟩ : syracuseStep 614211 = 921317) B921317
theorem B614227 : Blo 610295 614227 := bstep (se 1 (by rfl) ⟨460670, by rfl⟩ : syracuseStep 614227 = 921341) B921341
theorem B614243 : Blo 610295 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B614259 : Blo 610295 614259 := bstep (se 1 (by rfl) ⟨460694, by rfl⟩ : syracuseStep 614259 = 921389) B921389
theorem B614275 : Blo 610295 614275 := bstep (se 1 (by rfl) ⟨460706, by rfl⟩ : syracuseStep 614275 = 921413) B921413
theorem B614291 : Blo 610295 614291 := bstep (se 1 (by rfl) ⟨460718, by rfl⟩ : syracuseStep 614291 = 921437) B921437
theorem B2482211 : Blo 610295 2482211 := bstep (se 1 (by rfl) ⟨1861658, by rfl⟩ : syracuseStep 2482211 = 3723317) B3723317
theorem B1106435 : Blo 610295 1106435 := bstep (se 1 (by rfl) ⟨829826, by rfl⟩ : syracuseStep 1106435 = 1659653) B1659653
theorem B3924557 : Blo 610295 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B1237603 : Blo 610295 1237603 := bstep (se 1 (by rfl) ⟨928202, by rfl⟩ : syracuseStep 1237603 = 1856405) B1856405
theorem B1958755 : Blo 610295 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B1303555 : Blo 610295 1303555 := bstep (se 1 (by rfl) ⟨977666, by rfl⟩ : syracuseStep 1303555 = 1955333) B1955333
theorem B2614285 : Blo 610295 2614285 := bstep (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) B980357
theorem B2319587 : Blo 610295 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B1467683 : Blo 610295 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B1959203 : Blo 610295 1959203 := bstep (se 1 (by rfl) ⟨1469402, by rfl⟩ : syracuseStep 1959203 = 2938805) B2938805
theorem B2090605 : Blo 610295 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B1238723 : Blo 610295 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B2090755 : Blo 610295 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B3106673 : Blo 610295 3106673 := bstep (se 2 (by rfl) ⟨1165002, by rfl⟩ : syracuseStep 3106673 = 2330005) B2330005
theorem B1566641 : Blo 610295 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B2320589 : Blo 610295 2320589 := bstep (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) B870221
theorem B1304785 : Blo 610295 1304785 := bstep (se 2 (by rfl) ⟨489294, by rfl⟩ : syracuseStep 1304785 = 978589) B978589
theorem B15952099 : Blo 610295 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B1239395 : Blo 610295 1239395 := bstep (se 1 (by rfl) ⟨929546, by rfl⟩ : syracuseStep 1239395 = 1859093) B1859093
theorem B2484643 : Blo 610295 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B1960433 : Blo 610295 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B7432717 : Blo 610295 7432717 := bstep (se 3 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 7432717 = 2787269) B2787269
theorem B1239857 : Blo 610295 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B1305571 : Blo 610295 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B977923 : Blo 610295 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B1862851 : Blo 610295 1862851 := bstep (se 1 (by rfl) ⟨1397138, by rfl⟩ : syracuseStep 1862851 = 2794277) B2794277
theorem B3108131 : Blo 610295 3108131 := bstep (se 1 (by rfl) ⟨2331098, by rfl⟩ : syracuseStep 3108131 = 4662197) B4662197
theorem B1961329 : Blo 610295 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B2649677 : Blo 610295 2649677 := bstep (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) B993629
theorem B1044065 : Blo 610295 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B4648589 : Blo 610295 4648589 := bstep (se 3 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 4648589 = 1743221) B1743221
theorem B1306289 : Blo 610295 1306289 := bstep (se 2 (by rfl) ⟨489858, by rfl⟩ : syracuseStep 1306289 = 979717) B979717
theorem B5893829 : Blo 610295 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B2060045 : Blo 610295 2060045 := bstep (se 3 (by rfl) ⟨386258, by rfl⟩ : syracuseStep 2060045 = 772517) B772517
theorem B5598989 : Blo 610295 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B2060099 : Blo 610295 2060099 := bstep (se 1 (by rfl) ⟨1545074, by rfl⟩ : syracuseStep 2060099 = 3090149) B3090149
theorem B1077121 : Blo 610295 1077121 := bstep (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) B807841
theorem B5238755 : Blo 610295 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B19132469 : Blo 610295 19132469 := bstep (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) B1793669
theorem B3108941 : Blo 610295 3108941 := bstep (se 3 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 3108941 = 1165853) B1165853
theorem B2060369 : Blo 610295 2060369 := bstep (se 2 (by rfl) ⟨772638, by rfl⟩ : syracuseStep 2060369 = 1545277) B1545277
theorem B4419683 : Blo 610295 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B1306801 : Blo 610295 1306801 := bstep (se 2 (by rfl) ⟨490050, by rfl⟩ : syracuseStep 1306801 = 980101) B980101
theorem B4714723 : Blo 610295 4714723 := bstep (se 1 (by rfl) ⟨3536042, by rfl⟩ : syracuseStep 4714723 = 7072085) B7072085
theorem B2322701 : Blo 610295 2322701 := bstep (se 3 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 2322701 = 871013) B871013
theorem B1765805 : Blo 610295 1765805 := bstep (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) B662177
theorem B979409 : Blo 610295 979409 := bstep (se 2 (by rfl) ⟨367278, by rfl⟩ : syracuseStep 979409 = 734557) B734557
theorem B16740917 : Blo 610295 16740917 := bstep (se 5 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 16740917 = 1569461) B1569461
theorem B979537 : Blo 610295 979537 := bstep (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) B734653
theorem B2060909 : Blo 610295 2060909 := bstep (se 3 (by rfl) ⟨386420, by rfl⟩ : syracuseStep 2060909 = 772841) B772841
theorem B2060963 : Blo 610295 2060963 := bstep (se 1 (by rfl) ⟨1545722, by rfl⟩ : syracuseStep 2060963 = 3091445) B3091445
theorem B881425 : Blo 610295 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B652051 : Blo 610295 652051 := bstep (se 1 (by rfl) ⟨489038, by rfl⟩ : syracuseStep 652051 = 978077) B978077
theorem B1962893 : Blo 610295 1962893 := bstep (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) B736085
theorem B2061233 : Blo 610295 2061233 := bstep (se 2 (by rfl) ⟨772962, by rfl⟩ : syracuseStep 2061233 = 1545925) B1545925
theorem B3306437 : Blo 610295 3306437 := bstep (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) B619957
theorem B1471459 : Blo 610295 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B1373201 : Blo 610295 1373201 := bstep (se 2 (by rfl) ⟨514950, by rfl⟩ : syracuseStep 1373201 = 1029901) B1029901
theorem B652307 : Blo 610295 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B1373219 : Blo 610295 1373219 := bstep (se 1 (by rfl) ⟨1029914, by rfl⟩ : syracuseStep 1373219 = 2059829) B2059829
theorem B2323505 : Blo 610295 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B1471555 : Blo 610295 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B1045747 : Blo 610295 1045747 := bstep (se 1 (by rfl) ⟨784310, by rfl⟩ : syracuseStep 1045747 = 1568621) B1568621
theorem B2618659 : Blo 610295 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B1373489 : Blo 610295 1373489 := bstep (se 2 (by rfl) ⟨515058, by rfl⟩ : syracuseStep 1373489 = 1030117) B1030117
theorem B1373507 : Blo 610295 1373507 := bstep (se 1 (by rfl) ⟨1030130, by rfl⟩ : syracuseStep 1373507 = 2060261) B2060261
theorem B2061773 : Blo 610295 2061773 := bstep (se 3 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 2061773 = 773165) B773165
theorem B783859 : Blo 610295 783859 := bstep (se 1 (by rfl) ⟨587894, by rfl⟩ : syracuseStep 783859 = 1175789) B1175789
theorem B2061827 : Blo 610295 2061827 := bstep (se 1 (by rfl) ⟨1546370, by rfl⟩ : syracuseStep 2061827 = 3092741) B3092741
theorem B1373777 : Blo 610295 1373777 := bstep (se 2 (by rfl) ⟨515166, by rfl⟩ : syracuseStep 1373777 = 1030333) B1030333
theorem B1373795 : Blo 610295 1373795 := bstep (se 1 (by rfl) ⟨1030346, by rfl⟩ : syracuseStep 1373795 = 2060693) B2060693
theorem B1308305 : Blo 610295 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B1242769 : Blo 610295 1242769 := bstep (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) B932077
theorem B1177265 : Blo 610295 1177265 := bstep (se 2 (by rfl) ⟨441474, by rfl⟩ : syracuseStep 1177265 = 882949) B882949
theorem B2324173 : Blo 610295 2324173 := bstep (se 3 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 2324173 = 871565) B871565
theorem B653059 : Blo 610295 653059 := bstep (se 1 (by rfl) ⟨489794, by rfl⟩ : syracuseStep 653059 = 979589) B979589
theorem B2062097 : Blo 610295 2062097 := bstep (se 2 (by rfl) ⟨773286, by rfl⟩ : syracuseStep 2062097 = 1546573) B1546573
theorem B980819 : Blo 610295 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B1374065 : Blo 610295 1374065 := bstep (se 2 (by rfl) ⟨515274, by rfl⟩ : syracuseStep 1374065 = 1030549) B1030549
theorem B7862129 : Blo 610295 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B1374083 : Blo 610295 1374083 := bstep (se 1 (by rfl) ⟨1030562, by rfl⟩ : syracuseStep 1374083 = 2061125) B2061125
theorem B29718413 : Blo 610295 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B980915 : Blo 610295 980915 := bstep (se 1 (by rfl) ⟨735686, by rfl⟩ : syracuseStep 980915 = 1471373) B1471373
theorem B980947 : Blo 610295 980947 := bstep (se 1 (by rfl) ⟨735710, by rfl⟩ : syracuseStep 980947 = 1471421) B1471421
theorem B915443 : Blo 610295 915443 := bstep (se 1 (by rfl) ⟨686582, by rfl⟩ : syracuseStep 915443 = 1373165) B1373165
theorem B915473 : Blo 610295 915473 := bstep (se 2 (by rfl) ⟨343302, by rfl⟩ : syracuseStep 915473 = 686605) B686605
theorem B915491 : Blo 610295 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B1308707 : Blo 610295 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B20183093 : Blo 610295 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B915521 : Blo 610295 915521 := bstep (se 2 (by rfl) ⟨343320, by rfl⟩ : syracuseStep 915521 = 686641) B686641
theorem B915539 : Blo 610295 915539 := bstep (se 1 (by rfl) ⟨686654, by rfl⟩ : syracuseStep 915539 = 1373309) B1373309
theorem B915569 : Blo 610295 915569 := bstep (se 2 (by rfl) ⟨343338, by rfl⟩ : syracuseStep 915569 = 686677) B686677
theorem B915587 : Blo 610295 915587 := bstep (se 1 (by rfl) ⟨686690, by rfl⟩ : syracuseStep 915587 = 1373381) B1373381
theorem B3930245 : Blo 610295 3930245 := bstep (se 4 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 3930245 = 736921) B736921
theorem B1374353 : Blo 610295 1374353 := bstep (se 2 (by rfl) ⟨515382, by rfl⟩ : syracuseStep 1374353 = 1030765) B1030765
theorem B915617 : Blo 610295 915617 := bstep (se 2 (by rfl) ⟨343356, by rfl⟩ : syracuseStep 915617 = 686713) B686713
theorem B1374371 : Blo 610295 1374371 := bstep (se 1 (by rfl) ⟨1030778, by rfl⟩ : syracuseStep 1374371 = 2061557) B2061557
theorem B915635 : Blo 610295 915635 := bstep (se 1 (by rfl) ⟨686726, by rfl⟩ : syracuseStep 915635 = 1373453) B1373453
theorem B915665 : Blo 610295 915665 := bstep (se 2 (by rfl) ⟨343374, by rfl⟩ : syracuseStep 915665 = 686749) B686749
theorem B915683 : Blo 610295 915683 := bstep (se 1 (by rfl) ⟨686762, by rfl⟩ : syracuseStep 915683 = 1373525) B1373525
theorem B915713 : Blo 610295 915713 := bstep (se 2 (by rfl) ⟨343392, by rfl⟩ : syracuseStep 915713 = 686785) B686785
theorem B915731 : Blo 610295 915731 := bstep (se 1 (by rfl) ⟨686798, by rfl⟩ : syracuseStep 915731 = 1373597) B1373597
theorem B2062637 : Blo 610295 2062637 := bstep (se 3 (by rfl) ⟨386744, by rfl⟩ : syracuseStep 2062637 = 773489) B773489
theorem B915761 : Blo 610295 915761 := bstep (se 2 (by rfl) ⟨343410, by rfl⟩ : syracuseStep 915761 = 686821) B686821
theorem B915779 : Blo 610295 915779 := bstep (se 1 (by rfl) ⟨686834, by rfl⟩ : syracuseStep 915779 = 1373669) B1373669
theorem B915809 : Blo 610295 915809 := bstep (se 2 (by rfl) ⟨343428, by rfl⟩ : syracuseStep 915809 = 686857) B686857
theorem B2062691 : Blo 610295 2062691 := bstep (se 1 (by rfl) ⟨1547018, by rfl⟩ : syracuseStep 2062691 = 3094037) B3094037
theorem B915827 : Blo 610295 915827 := bstep (se 1 (by rfl) ⟨686870, by rfl⟩ : syracuseStep 915827 = 1373741) B1373741
theorem B915857 : Blo 610295 915857 := bstep (se 2 (by rfl) ⟨343446, by rfl⟩ : syracuseStep 915857 = 686893) B686893
theorem B915875 : Blo 610295 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B1374641 : Blo 610295 1374641 := bstep (se 2 (by rfl) ⟨515490, by rfl⟩ : syracuseStep 1374641 = 1030981) B1030981
theorem B1866161 : Blo 610295 1866161 := bstep (se 2 (by rfl) ⟨699810, by rfl⟩ : syracuseStep 1866161 = 1399621) B1399621
theorem B915905 : Blo 610295 915905 := bstep (se 2 (by rfl) ⟨343464, by rfl⟩ : syracuseStep 915905 = 686929) B686929
theorem B1374659 : Blo 610295 1374659 := bstep (se 1 (by rfl) ⟨1030994, by rfl⟩ : syracuseStep 1374659 = 2061989) B2061989
theorem B915923 : Blo 610295 915923 := bstep (se 1 (by rfl) ⟨686942, by rfl⟩ : syracuseStep 915923 = 1373885) B1373885
theorem B2324963 : Blo 610295 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B915953 : Blo 610295 915953 := bstep (se 2 (by rfl) ⟨343482, by rfl⟩ : syracuseStep 915953 = 686965) B686965
theorem B4651505 : Blo 610295 4651505 := bstep (se 2 (by rfl) ⟨1744314, by rfl⟩ : syracuseStep 4651505 = 3488629) B3488629
theorem B915971 : Blo 610295 915971 := bstep (se 1 (by rfl) ⟨686978, by rfl⟩ : syracuseStep 915971 = 1373957) B1373957
theorem B916001 : Blo 610295 916001 := bstep (se 2 (by rfl) ⟨343500, by rfl⟩ : syracuseStep 916001 = 687001) B687001
theorem B916019 : Blo 610295 916019 := bstep (se 1 (by rfl) ⟨687014, by rfl⟩ : syracuseStep 916019 = 1374029) B1374029
theorem B686659 : Blo 610295 686659 := bstep (se 1 (by rfl) ⟨514994, by rfl⟩ : syracuseStep 686659 = 1029989) B1029989
theorem B916049 : Blo 610295 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B916067 : Blo 610295 916067 := bstep (se 1 (by rfl) ⟨687050, by rfl⟩ : syracuseStep 916067 = 1374101) B1374101
theorem B2062961 : Blo 610295 2062961 := bstep (se 2 (by rfl) ⟨773610, by rfl⟩ : syracuseStep 2062961 = 1547221) B1547221
theorem B916097 : Blo 610295 916097 := bstep (se 2 (by rfl) ⟨343536, by rfl⟩ : syracuseStep 916097 = 687073) B687073
theorem B916115 : Blo 610295 916115 := bstep (se 1 (by rfl) ⟨687086, by rfl⟩ : syracuseStep 916115 = 1374173) B1374173
theorem B916145 : Blo 610295 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B916163 : Blo 610295 916163 := bstep (se 1 (by rfl) ⟨687122, by rfl⟩ : syracuseStep 916163 = 1374245) B1374245
theorem B1374929 : Blo 610295 1374929 := bstep (se 2 (by rfl) ⟨515598, by rfl⟩ : syracuseStep 1374929 = 1031197) B1031197
theorem B686803 : Blo 610295 686803 := bstep (se 1 (by rfl) ⟨515102, by rfl⟩ : syracuseStep 686803 = 1030205) B1030205
theorem B916193 : Blo 610295 916193 := bstep (se 2 (by rfl) ⟨343572, by rfl⟩ : syracuseStep 916193 = 687145) B687145
theorem B1374947 : Blo 610295 1374947 := bstep (se 1 (by rfl) ⟨1031210, by rfl⟩ : syracuseStep 1374947 = 2062421) B2062421
theorem B916211 : Blo 610295 916211 := bstep (se 1 (by rfl) ⟨687158, by rfl⟩ : syracuseStep 916211 = 1374317) B1374317
theorem B916241 : Blo 610295 916241 := bstep (se 2 (by rfl) ⟨343590, by rfl⟩ : syracuseStep 916241 = 687181) B687181
theorem B916259 : Blo 610295 916259 := bstep (se 1 (by rfl) ⟨687194, by rfl⟩ : syracuseStep 916259 = 1374389) B1374389
theorem B916289 : Blo 610295 916289 := bstep (se 2 (by rfl) ⟨343608, by rfl⟩ : syracuseStep 916289 = 687217) B687217
theorem B916307 : Blo 610295 916307 := bstep (se 1 (by rfl) ⟨687230, by rfl⟩ : syracuseStep 916307 = 1374461) B1374461
theorem B981857 : Blo 610295 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B686947 : Blo 610295 686947 := bstep (se 1 (by rfl) ⟨515210, by rfl⟩ : syracuseStep 686947 = 1030421) B1030421
theorem B1768301 : Blo 610295 1768301 := bstep (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) B663113
theorem B916337 : Blo 610295 916337 := bstep (se 2 (by rfl) ⟨343626, by rfl⟩ : syracuseStep 916337 = 687253) B687253
theorem B916355 : Blo 610295 916355 := bstep (se 1 (by rfl) ⟨687266, by rfl⟩ : syracuseStep 916355 = 1374533) B1374533
theorem B916385 : Blo 610295 916385 := bstep (se 2 (by rfl) ⟨343644, by rfl⟩ : syracuseStep 916385 = 687289) B687289
theorem B1309603 : Blo 610295 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B2489251 : Blo 610295 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B916403 : Blo 610295 916403 := bstep (se 1 (by rfl) ⟨687302, by rfl⟩ : syracuseStep 916403 = 1374605) B1374605
theorem B916433 : Blo 610295 916433 := bstep (se 2 (by rfl) ⟨343662, by rfl⟩ : syracuseStep 916433 = 687325) B687325
theorem B916451 : Blo 610295 916451 := bstep (se 1 (by rfl) ⟨687338, by rfl⟩ : syracuseStep 916451 = 1374677) B1374677
theorem B1375217 : Blo 610295 1375217 := bstep (se 2 (by rfl) ⟨515706, by rfl⟩ : syracuseStep 1375217 = 1031413) B1031413
theorem B687091 : Blo 610295 687091 := bstep (se 1 (by rfl) ⟨515318, by rfl⟩ : syracuseStep 687091 = 1030637) B1030637
theorem B654323 : Blo 610295 654323 := bstep (se 1 (by rfl) ⟨490742, by rfl⟩ : syracuseStep 654323 = 981485) B981485
theorem B916481 : Blo 610295 916481 := bstep (se 2 (by rfl) ⟨343680, by rfl⟩ : syracuseStep 916481 = 687361) B687361
theorem B1375235 : Blo 610295 1375235 := bstep (se 1 (by rfl) ⟨1031426, by rfl⟩ : syracuseStep 1375235 = 2062853) B2062853
theorem B916499 : Blo 610295 916499 := bstep (se 1 (by rfl) ⟨687374, by rfl⟩ : syracuseStep 916499 = 1374749) B1374749
theorem B916529 : Blo 610295 916529 := bstep (se 2 (by rfl) ⟨343698, by rfl⟩ : syracuseStep 916529 = 687397) B687397
theorem B916547 : Blo 610295 916547 := bstep (se 1 (by rfl) ⟨687410, by rfl⟩ : syracuseStep 916547 = 1374821) B1374821
theorem B916577 : Blo 610295 916577 := bstep (se 2 (by rfl) ⟨343716, by rfl⟩ : syracuseStep 916577 = 687433) B687433
theorem B2325617 : Blo 610295 2325617 := bstep (se 2 (by rfl) ⟨872106, by rfl⟩ : syracuseStep 2325617 = 1744213) B1744213
theorem B916595 : Blo 610295 916595 := bstep (se 1 (by rfl) ⟨687446, by rfl⟩ : syracuseStep 916595 = 1374893) B1374893
theorem B687235 : Blo 610295 687235 := bstep (se 1 (by rfl) ⟨515426, by rfl⟩ : syracuseStep 687235 = 1030853) B1030853
theorem B2063501 : Blo 610295 2063501 := bstep (se 3 (by rfl) ⟨386906, by rfl⟩ : syracuseStep 2063501 = 773813) B773813
theorem B916625 : Blo 610295 916625 := bstep (se 2 (by rfl) ⟨343734, by rfl⟩ : syracuseStep 916625 = 687469) B687469
theorem B916643 : Blo 610295 916643 := bstep (se 1 (by rfl) ⟨687482, by rfl⟩ : syracuseStep 916643 = 1374965) B1374965
theorem B916673 : Blo 610295 916673 := bstep (se 2 (by rfl) ⟨343752, by rfl⟩ : syracuseStep 916673 = 687505) B687505
theorem B2063555 : Blo 610295 2063555 := bstep (se 1 (by rfl) ⟨1547666, by rfl⟩ : syracuseStep 2063555 = 3095333) B3095333
theorem B916691 : Blo 610295 916691 := bstep (se 1 (by rfl) ⟨687518, by rfl⟩ : syracuseStep 916691 = 1375037) B1375037
theorem B14908643 : Blo 610295 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B916721 : Blo 610295 916721 := bstep (se 2 (by rfl) ⟨343770, by rfl⟩ : syracuseStep 916721 = 687541) B687541
theorem B916739 : Blo 610295 916739 := bstep (se 1 (by rfl) ⟨687554, by rfl⟩ : syracuseStep 916739 = 1375109) B1375109
theorem B1375505 : Blo 610295 1375505 := bstep (se 2 (by rfl) ⟨515814, by rfl⟩ : syracuseStep 1375505 = 1031629) B1031629
theorem B687379 : Blo 610295 687379 := bstep (se 1 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 687379 = 1031069) B1031069
theorem B916769 : Blo 610295 916769 := bstep (se 2 (by rfl) ⟨343788, by rfl⟩ : syracuseStep 916769 = 687577) B687577
theorem B1375523 : Blo 610295 1375523 := bstep (se 1 (by rfl) ⟨1031642, by rfl⟩ : syracuseStep 1375523 = 2063285) B2063285
theorem B2653489 : Blo 610295 2653489 := bstep (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) B1990117
theorem B916787 : Blo 610295 916787 := bstep (se 1 (by rfl) ⟨687590, by rfl⟩ : syracuseStep 916787 = 1375181) B1375181
theorem B1047875 : Blo 610295 1047875 := bstep (se 1 (by rfl) ⟨785906, by rfl⟩ : syracuseStep 1047875 = 1571813) B1571813
theorem B1965379 : Blo 610295 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B916817 : Blo 610295 916817 := bstep (se 2 (by rfl) ⟨343806, by rfl⟩ : syracuseStep 916817 = 687613) B687613
theorem B916835 : Blo 610295 916835 := bstep (se 1 (by rfl) ⟨687626, by rfl⟩ : syracuseStep 916835 = 1375253) B1375253
theorem B4423025 : Blo 610295 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B916865 : Blo 610295 916865 := bstep (se 2 (by rfl) ⟨343824, by rfl⟩ : syracuseStep 916865 = 687649) B687649
theorem B916883 : Blo 610295 916883 := bstep (se 1 (by rfl) ⟨687662, by rfl⟩ : syracuseStep 916883 = 1375325) B1375325
theorem B687523 : Blo 610295 687523 := bstep (se 1 (by rfl) ⟨515642, by rfl⟩ : syracuseStep 687523 = 1031285) B1031285
theorem B916913 : Blo 610295 916913 := bstep (se 2 (by rfl) ⟨343842, by rfl⟩ : syracuseStep 916913 = 687685) B687685
theorem B1244593 : Blo 610295 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B916931 : Blo 610295 916931 := bstep (se 1 (by rfl) ⟨687698, by rfl⟩ : syracuseStep 916931 = 1375397) B1375397
theorem B2063825 : Blo 610295 2063825 := bstep (se 2 (by rfl) ⟨773934, by rfl⟩ : syracuseStep 2063825 = 1547869) B1547869
theorem B1965521 : Blo 610295 1965521 := bstep (se 2 (by rfl) ⟨737070, by rfl⟩ : syracuseStep 1965521 = 1474141) B1474141
theorem B916961 : Blo 610295 916961 := bstep (se 2 (by rfl) ⟨343860, by rfl⟩ : syracuseStep 916961 = 687721) B687721
theorem B916979 : Blo 610295 916979 := bstep (se 1 (by rfl) ⟨687734, by rfl⟩ : syracuseStep 916979 = 1375469) B1375469
theorem B917009 : Blo 610295 917009 := bstep (se 2 (by rfl) ⟨343878, by rfl⟩ : syracuseStep 917009 = 687757) B687757
theorem B884243 : Blo 610295 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B917027 : Blo 610295 917027 := bstep (se 1 (by rfl) ⟨687770, by rfl⟩ : syracuseStep 917027 = 1375541) B1375541
theorem B1375793 : Blo 610295 1375793 := bstep (se 2 (by rfl) ⟨515922, by rfl⟩ : syracuseStep 1375793 = 1031845) B1031845
theorem B687667 : Blo 610295 687667 := bstep (se 1 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 687667 = 1031501) B1031501
theorem B917057 : Blo 610295 917057 := bstep (se 2 (by rfl) ⟨343896, by rfl⟩ : syracuseStep 917057 = 687793) B687793
theorem B1375811 : Blo 610295 1375811 := bstep (se 1 (by rfl) ⟨1031858, by rfl⟩ : syracuseStep 1375811 = 2063717) B2063717
theorem B1965635 : Blo 610295 1965635 := bstep (se 1 (by rfl) ⟨1474226, by rfl⟩ : syracuseStep 1965635 = 2948453) B2948453
theorem B917075 : Blo 610295 917075 := bstep (se 1 (by rfl) ⟨687806, by rfl⟩ : syracuseStep 917075 = 1375613) B1375613
theorem B917105 : Blo 610295 917105 := bstep (se 2 (by rfl) ⟨343914, by rfl⟩ : syracuseStep 917105 = 687829) B687829
theorem B5242481 : Blo 610295 5242481 := bstep (se 2 (by rfl) ⟨1965930, by rfl⟩ : syracuseStep 5242481 = 3931861) B3931861
theorem B917123 : Blo 610295 917123 := bstep (se 1 (by rfl) ⟨687842, by rfl⟩ : syracuseStep 917123 = 1375685) B1375685
theorem B917153 : Blo 610295 917153 := bstep (se 2 (by rfl) ⟨343932, by rfl⟩ : syracuseStep 917153 = 687865) B687865
theorem B2621105 : Blo 610295 2621105 := bstep (se 2 (by rfl) ⟨982914, by rfl⟩ : syracuseStep 2621105 = 1965829) B1965829
theorem B917171 : Blo 610295 917171 := bstep (se 1 (by rfl) ⟨687878, by rfl⟩ : syracuseStep 917171 = 1375757) B1375757
theorem B687811 : Blo 610295 687811 := bstep (se 1 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 687811 = 1031717) B1031717
theorem B917201 : Blo 610295 917201 := bstep (se 2 (by rfl) ⟨343950, by rfl⟩ : syracuseStep 917201 = 687901) B687901
theorem B917219 : Blo 610295 917219 := bstep (se 1 (by rfl) ⟨687914, by rfl⟩ : syracuseStep 917219 = 1375829) B1375829
theorem B655075 : Blo 610295 655075 := bstep (se 1 (by rfl) ⟨491306, by rfl⟩ : syracuseStep 655075 = 982613) B982613
theorem B917249 : Blo 610295 917249 := bstep (se 2 (by rfl) ⟨343968, by rfl⟩ : syracuseStep 917249 = 687937) B687937
theorem B917267 : Blo 610295 917267 := bstep (se 1 (by rfl) ⟨687950, by rfl⟩ : syracuseStep 917267 = 1375901) B1375901
theorem B917297 : Blo 610295 917297 := bstep (se 2 (by rfl) ⟨343986, by rfl⟩ : syracuseStep 917297 = 687973) B687973
theorem B917315 : Blo 610295 917315 := bstep (se 1 (by rfl) ⟨687986, by rfl⟩ : syracuseStep 917315 = 1375973) B1375973
theorem B1376081 : Blo 610295 1376081 := bstep (se 2 (by rfl) ⟨516030, by rfl⟩ : syracuseStep 1376081 = 1032061) B1032061
theorem B687955 : Blo 610295 687955 := bstep (se 1 (by rfl) ⟨515966, by rfl⟩ : syracuseStep 687955 = 1031933) B1031933
theorem B1048403 : Blo 610295 1048403 := bstep (se 1 (by rfl) ⟨786302, by rfl⟩ : syracuseStep 1048403 = 1572605) B1572605
theorem B917345 : Blo 610295 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B851809 : Blo 610295 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B1376099 : Blo 610295 1376099 := bstep (se 1 (by rfl) ⟨1032074, by rfl⟩ : syracuseStep 1376099 = 2064149) B2064149
theorem B1245041 : Blo 610295 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B917363 : Blo 610295 917363 := bstep (se 1 (by rfl) ⟨688022, by rfl⟩ : syracuseStep 917363 = 1376045) B1376045
theorem B917393 : Blo 610295 917393 := bstep (se 2 (by rfl) ⟨344022, by rfl⟩ : syracuseStep 917393 = 688045) B688045
theorem B917411 : Blo 610295 917411 := bstep (se 1 (by rfl) ⟨688058, by rfl⟩ : syracuseStep 917411 = 1376117) B1376117
theorem B917441 : Blo 610295 917441 := bstep (se 2 (by rfl) ⟨344040, by rfl⟩ : syracuseStep 917441 = 688081) B688081
theorem B917459 : Blo 610295 917459 := bstep (se 1 (by rfl) ⟨688094, by rfl⟩ : syracuseStep 917459 = 1376189) B1376189
theorem B688099 : Blo 610295 688099 := bstep (se 1 (by rfl) ⟨516074, by rfl⟩ : syracuseStep 688099 = 1032149) B1032149
theorem B2064365 : Blo 610295 2064365 := bstep (se 3 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 2064365 = 774137) B774137
theorem B917489 : Blo 610295 917489 := bstep (se 2 (by rfl) ⟨344058, by rfl⟩ : syracuseStep 917489 = 688117) B688117
theorem B1376279 : Blo 610295 1376279 := bstep (se 1 (by rfl) ⟨1032209, by rfl⟩ : syracuseStep 1376279 = 2064419) B2064419
theorem B688171 : Blo 610295 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B1245235 : Blo 610295 1245235 := bstep (se 1 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 1245235 = 1867853) B1867853
theorem B917579 : Blo 610295 917579 := bstep (se 1 (by rfl) ⟨688184, by rfl⟩ : syracuseStep 917579 = 1376369) B1376369
theorem B2326603 : Blo 610295 2326603 := bstep (se 1 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 2326603 = 3489905) B3489905
theorem B917591 : Blo 610295 917591 := bstep (se 1 (by rfl) ⟨688193, by rfl⟩ : syracuseStep 917591 = 1376387) B1376387
theorem B655447 : Blo 610295 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B2064473 : Blo 610295 2064473 := bstep (se 2 (by rfl) ⟨774177, by rfl⟩ : syracuseStep 2064473 = 1548355) B1548355
theorem B6619229 : Blo 610295 6619229 := bstep (se 3 (by rfl) ⟨1241105, by rfl⟩ : syracuseStep 6619229 = 2482211) B2482211
theorem B688279 : Blo 610295 688279 := bstep (se 1 (by rfl) ⟨516209, by rfl⟩ : syracuseStep 688279 = 1032419) B1032419
theorem B917657 : Blo 610295 917657 := bstep (se 2 (by rfl) ⟨344121, by rfl⟩ : syracuseStep 917657 = 688243) B688243
theorem B1376459 : Blo 610295 1376459 := bstep (se 1 (by rfl) ⟨1032344, by rfl⟩ : syracuseStep 1376459 = 2064689) B2064689
theorem B1179851 : Blo 610295 1179851 := bstep (se 1 (by rfl) ⟨884888, by rfl⟩ : syracuseStep 1179851 = 1769777) B1769777
theorem B1376513 : Blo 610295 1376513 := bstep (se 2 (by rfl) ⟨516192, by rfl⟩ : syracuseStep 1376513 = 1032385) B1032385
theorem B917771 : Blo 610295 917771 := bstep (se 1 (by rfl) ⟨688328, by rfl⟩ : syracuseStep 917771 = 1376657) B1376657
theorem B917783 : Blo 610295 917783 := bstep (se 1 (by rfl) ⟨688337, by rfl⟩ : syracuseStep 917783 = 1376675) B1376675
theorem B688459 : Blo 610295 688459 := bstep (se 1 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 688459 = 1032689) B1032689
theorem B917849 : Blo 610295 917849 := bstep (se 2 (by rfl) ⟨344193, by rfl⟩ : syracuseStep 917849 = 688387) B688387
theorem B2326877 : Blo 610295 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B688567 : Blo 610295 688567 := bstep (se 1 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 688567 = 1032851) B1032851
theorem B917963 : Blo 610295 917963 := bstep (se 1 (by rfl) ⟨688472, by rfl⟩ : syracuseStep 917963 = 1376945) B1376945
theorem B917975 : Blo 610295 917975 := bstep (se 1 (by rfl) ⟨688481, by rfl⟩ : syracuseStep 917975 = 1376963) B1376963
theorem B1376729 : Blo 610295 1376729 := bstep (se 2 (by rfl) ⟨516273, by rfl⟩ : syracuseStep 1376729 = 1032547) B1032547
theorem B2359811 : Blo 610295 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B655895 : Blo 610295 655895 := bstep (se 1 (by rfl) ⟨491921, by rfl⟩ : syracuseStep 655895 = 983843) B983843
theorem B918041 : Blo 610295 918041 := bstep (se 2 (by rfl) ⟨344265, by rfl⟩ : syracuseStep 918041 = 688531) B688531
theorem B1376819 : Blo 610295 1376819 := bstep (se 1 (by rfl) ⟨1032614, by rfl⟩ : syracuseStep 1376819 = 2065229) B2065229
theorem B1376855 : Blo 610295 1376855 := bstep (se 1 (by rfl) ⟨1032641, by rfl⟩ : syracuseStep 1376855 = 2065283) B2065283
theorem B4194917 : Blo 610295 4194917 := bstep (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) B786547
theorem B688747 : Blo 610295 688747 := bstep (se 1 (by rfl) ⟨516560, by rfl⟩ : syracuseStep 688747 = 1033121) B1033121
theorem B918155 : Blo 610295 918155 := bstep (se 1 (by rfl) ⟨688616, by rfl⟩ : syracuseStep 918155 = 1377233) B1377233
theorem B918167 : Blo 610295 918167 := bstep (se 1 (by rfl) ⟨688625, by rfl⟩ : syracuseStep 918167 = 1377251) B1377251
theorem B2622145 : Blo 610295 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B688855 : Blo 610295 688855 := bstep (se 1 (by rfl) ⟨516641, by rfl⟩ : syracuseStep 688855 = 1033283) B1033283
theorem B918233 : Blo 610295 918233 := bstep (se 2 (by rfl) ⟨344337, by rfl⟩ : syracuseStep 918233 = 688675) B688675
theorem B1377035 : Blo 610295 1377035 := bstep (se 1 (by rfl) ⟨1032776, by rfl⟩ : syracuseStep 1377035 = 2065553) B2065553
theorem B2065175 : Blo 610295 2065175 := bstep (se 1 (by rfl) ⟨1548881, by rfl⟩ : syracuseStep 2065175 = 3097763) B3097763
theorem B1377089 : Blo 610295 1377089 := bstep (se 2 (by rfl) ⟨516408, by rfl⟩ : syracuseStep 1377089 = 1032817) B1032817
theorem B918347 : Blo 610295 918347 := bstep (se 1 (by rfl) ⟨688760, by rfl⟩ : syracuseStep 918347 = 1377521) B1377521
theorem B918359 : Blo 610295 918359 := bstep (se 1 (by rfl) ⟨688769, by rfl⟩ : syracuseStep 918359 = 1377539) B1377539
theorem B10453859 : Blo 610295 10453859 := bstep (se 1 (by rfl) ⟨7840394, by rfl⟩ : syracuseStep 10453859 = 15680789) B15680789
theorem B689035 : Blo 610295 689035 := bstep (se 1 (by rfl) ⟨516776, by rfl⟩ : syracuseStep 689035 = 1033553) B1033553
theorem B1049483 : Blo 610295 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B918425 : Blo 610295 918425 := bstep (se 2 (by rfl) ⟨344409, by rfl⟩ : syracuseStep 918425 = 688819) B688819
theorem B21201841 : Blo 610295 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B689143 : Blo 610295 689143 := bstep (se 1 (by rfl) ⟨516857, by rfl⟩ : syracuseStep 689143 = 1033715) B1033715
theorem B918539 : Blo 610295 918539 := bstep (se 1 (by rfl) ⟨688904, by rfl⟩ : syracuseStep 918539 = 1377809) B1377809
theorem B918551 : Blo 610295 918551 := bstep (se 1 (by rfl) ⟨688913, by rfl⟩ : syracuseStep 918551 = 1377827) B1377827
theorem B2327575 : Blo 610295 2327575 := bstep (se 1 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 2327575 = 3491363) B3491363
theorem B1377305 : Blo 610295 1377305 := bstep (se 2 (by rfl) ⟨516489, by rfl⟩ : syracuseStep 1377305 = 1032979) B1032979
theorem B918617 : Blo 610295 918617 := bstep (se 2 (by rfl) ⟨344481, by rfl⟩ : syracuseStep 918617 = 688963) B688963
theorem B1377395 : Blo 610295 1377395 := bstep (se 1 (by rfl) ⟨1033046, by rfl⟩ : syracuseStep 1377395 = 2066093) B2066093
theorem B1377431 : Blo 610295 1377431 := bstep (se 1 (by rfl) ⟨1033073, by rfl⟩ : syracuseStep 1377431 = 2066147) B2066147
theorem B689323 : Blo 610295 689323 := bstep (se 1 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 689323 = 1033985) B1033985
theorem B918731 : Blo 610295 918731 := bstep (se 1 (by rfl) ⟨689048, by rfl⟩ : syracuseStep 918731 = 1378097) B1378097
theorem B918743 : Blo 610295 918743 := bstep (se 1 (by rfl) ⟨689057, by rfl⟩ : syracuseStep 918743 = 1378115) B1378115
theorem B689431 : Blo 610295 689431 := bstep (se 1 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 689431 = 1034147) B1034147
theorem B918809 : Blo 610295 918809 := bstep (se 2 (by rfl) ⟨344553, by rfl⟩ : syracuseStep 918809 = 689107) B689107
theorem B2065715 : Blo 610295 2065715 := bstep (se 1 (by rfl) ⟨1549286, by rfl⟩ : syracuseStep 2065715 = 3098573) B3098573
theorem B1770817 : Blo 610295 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B1377611 : Blo 610295 1377611 := bstep (se 1 (by rfl) ⟨1033208, by rfl⟩ : syracuseStep 1377611 = 2066417) B2066417
theorem B1738073 : Blo 610295 1738073 := bstep (se 2 (by rfl) ⟨651777, by rfl⟩ : syracuseStep 1738073 = 1303555) B1303555
theorem B1377665 : Blo 610295 1377665 := bstep (se 2 (by rfl) ⟨516624, by rfl⟩ : syracuseStep 1377665 = 1033249) B1033249
theorem B918923 : Blo 610295 918923 := bstep (se 1 (by rfl) ⟨689192, by rfl⟩ : syracuseStep 918923 = 1378385) B1378385
theorem B918935 : Blo 610295 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B689611 : Blo 610295 689611 := bstep (se 1 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 689611 = 1034417) B1034417
theorem B919001 : Blo 610295 919001 := bstep (se 2 (by rfl) ⟨344625, by rfl⟩ : syracuseStep 919001 = 689251) B689251
theorem B689719 : Blo 610295 689719 := bstep (se 1 (by rfl) ⟨517289, by rfl⟩ : syracuseStep 689719 = 1034579) B1034579
theorem B2065985 : Blo 610295 2065985 := bstep (se 2 (by rfl) ⟨774744, by rfl⟩ : syracuseStep 2065985 = 1549489) B1549489
theorem B919115 : Blo 610295 919115 := bstep (se 1 (by rfl) ⟨689336, by rfl⟩ : syracuseStep 919115 = 1378673) B1378673
theorem B919127 : Blo 610295 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B1377881 : Blo 610295 1377881 := bstep (se 2 (by rfl) ⟨516705, by rfl⟩ : syracuseStep 1377881 = 1033411) B1033411
theorem B36374129 : Blo 610295 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B8849047 : Blo 610295 8849047 := bstep (se 1 (by rfl) ⟨6636785, by rfl⟩ : syracuseStep 8849047 = 13273571) B13273571
theorem B919193 : Blo 610295 919193 := bstep (se 2 (by rfl) ⟨344697, by rfl⟩ : syracuseStep 919193 = 689395) B689395
theorem B1672883 : Blo 610295 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B1377971 : Blo 610295 1377971 := bstep (se 1 (by rfl) ⟨1033478, by rfl⟩ : syracuseStep 1377971 = 2066957) B2066957
theorem B1378007 : Blo 610295 1378007 := bstep (se 1 (by rfl) ⟨1033505, by rfl⟩ : syracuseStep 1378007 = 2067011) B2067011
theorem B689899 : Blo 610295 689899 := bstep (se 1 (by rfl) ⟨517424, by rfl⟩ : syracuseStep 689899 = 1034849) B1034849
theorem B919307 : Blo 610295 919307 := bstep (se 1 (by rfl) ⟨689480, by rfl⟩ : syracuseStep 919307 = 1378961) B1378961
theorem B919319 : Blo 610295 919319 := bstep (se 1 (by rfl) ⟨689489, by rfl⟩ : syracuseStep 919319 = 1378979) B1378979
theorem B2328365 : Blo 610295 2328365 := bstep (se 3 (by rfl) ⟨436568, by rfl⟩ : syracuseStep 2328365 = 873137) B873137
theorem B690007 : Blo 610295 690007 := bstep (se 1 (by rfl) ⟨517505, by rfl⟩ : syracuseStep 690007 = 1035011) B1035011
theorem B919385 : Blo 610295 919385 := bstep (se 2 (by rfl) ⟨344769, by rfl⟩ : syracuseStep 919385 = 689539) B689539
theorem B1378187 : Blo 610295 1378187 := bstep (se 1 (by rfl) ⟨1033640, by rfl⟩ : syracuseStep 1378187 = 2067281) B2067281
theorem B1378241 : Blo 610295 1378241 := bstep (se 2 (by rfl) ⟨516840, by rfl⟩ : syracuseStep 1378241 = 1033681) B1033681
theorem B919499 : Blo 610295 919499 := bstep (se 1 (by rfl) ⟨689624, by rfl⟩ : syracuseStep 919499 = 1379249) B1379249
theorem B919511 : Blo 610295 919511 := bstep (se 1 (by rfl) ⟨689633, by rfl⟩ : syracuseStep 919511 = 1379267) B1379267
theorem B690187 : Blo 610295 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B919577 : Blo 610295 919577 := bstep (se 2 (by rfl) ⟨344841, by rfl⟩ : syracuseStep 919577 = 689683) B689683
theorem B2066525 : Blo 610295 2066525 := bstep (se 3 (by rfl) ⟨387473, by rfl⟩ : syracuseStep 2066525 = 774947) B774947
theorem B690295 : Blo 610295 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B919691 : Blo 610295 919691 := bstep (se 1 (by rfl) ⟨689768, by rfl⟩ : syracuseStep 919691 = 1379537) B1379537
theorem B2787473 : Blo 610295 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B919703 : Blo 610295 919703 := bstep (se 1 (by rfl) ⟨689777, by rfl⟩ : syracuseStep 919703 = 1379555) B1379555
theorem B1378457 : Blo 610295 1378457 := bstep (se 2 (by rfl) ⟨516921, by rfl⟩ : syracuseStep 1378457 = 1033843) B1033843
theorem B2230465 : Blo 610295 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B919769 : Blo 610295 919769 := bstep (se 2 (by rfl) ⟨344913, by rfl⟩ : syracuseStep 919769 = 689827) B689827
theorem B1378547 : Blo 610295 1378547 := bstep (se 1 (by rfl) ⟨1033910, by rfl⟩ : syracuseStep 1378547 = 2067821) B2067821
theorem B1378583 : Blo 610295 1378583 := bstep (se 1 (by rfl) ⟨1033937, by rfl⟩ : syracuseStep 1378583 = 2067875) B2067875
theorem B690475 : Blo 610295 690475 := bstep (se 1 (by rfl) ⟨517856, by rfl⟩ : syracuseStep 690475 = 1035713) B1035713
theorem B919883 : Blo 610295 919883 := bstep (se 1 (by rfl) ⟨689912, by rfl⟩ : syracuseStep 919883 = 1379825) B1379825
theorem B919895 : Blo 610295 919895 := bstep (se 1 (by rfl) ⟨689921, by rfl⟩ : syracuseStep 919895 = 1379843) B1379843
theorem B690583 : Blo 610295 690583 := bstep (se 1 (by rfl) ⟨517937, by rfl⟩ : syracuseStep 690583 = 1035875) B1035875
theorem B919961 : Blo 610295 919961 := bstep (se 2 (by rfl) ⟨344985, by rfl⟩ : syracuseStep 919961 = 689971) B689971
theorem B1378763 : Blo 610295 1378763 := bstep (se 1 (by rfl) ⟨1034072, by rfl⟩ : syracuseStep 1378763 = 2068145) B2068145
theorem B1378817 : Blo 610295 1378817 := bstep (se 2 (by rfl) ⟨517056, by rfl⟩ : syracuseStep 1378817 = 1034113) B1034113
theorem B920075 : Blo 610295 920075 := bstep (se 1 (by rfl) ⟨690056, by rfl⟩ : syracuseStep 920075 = 1380113) B1380113
theorem B920087 : Blo 610295 920087 := bstep (se 1 (by rfl) ⟨690065, by rfl⟩ : syracuseStep 920087 = 1380131) B1380131
theorem B3476033 : Blo 610295 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B5573195 : Blo 610295 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B690763 : Blo 610295 690763 := bstep (se 1 (by rfl) ⟨518072, by rfl⟩ : syracuseStep 690763 = 1036145) B1036145
theorem B920153 : Blo 610295 920153 := bstep (se 2 (by rfl) ⟨345057, by rfl⟩ : syracuseStep 920153 = 690115) B690115
theorem B10783363 : Blo 610295 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B690871 : Blo 610295 690871 := bstep (se 1 (by rfl) ⟨518153, by rfl⟩ : syracuseStep 690871 = 1036307) B1036307
theorem B920267 : Blo 610295 920267 := bstep (se 1 (by rfl) ⟨690200, by rfl⟩ : syracuseStep 920267 = 1380401) B1380401
theorem B920279 : Blo 610295 920279 := bstep (se 1 (by rfl) ⟨690209, by rfl⟩ : syracuseStep 920279 = 1380419) B1380419
theorem B1379033 : Blo 610295 1379033 := bstep (se 2 (by rfl) ⟨517137, by rfl⟩ : syracuseStep 1379033 = 1034275) B1034275
theorem B1739485 : Blo 610295 1739485 := bstep (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) B652307
theorem B920345 : Blo 610295 920345 := bstep (se 2 (by rfl) ⟨345129, by rfl⟩ : syracuseStep 920345 = 690259) B690259
theorem B1379123 : Blo 610295 1379123 := bstep (se 1 (by rfl) ⟨1034342, by rfl⟩ : syracuseStep 1379123 = 2068685) B2068685
theorem B1379159 : Blo 610295 1379159 := bstep (se 1 (by rfl) ⟨1034369, by rfl⟩ : syracuseStep 1379159 = 2068739) B2068739
theorem B691051 : Blo 610295 691051 := bstep (se 1 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 691051 = 1036577) B1036577
theorem B920459 : Blo 610295 920459 := bstep (se 1 (by rfl) ⟨690344, by rfl⟩ : syracuseStep 920459 = 1380689) B1380689
theorem B920471 : Blo 610295 920471 := bstep (se 1 (by rfl) ⟨690353, by rfl⟩ : syracuseStep 920471 = 1380707) B1380707
theorem B1739713 : Blo 610295 1739713 := bstep (se 2 (by rfl) ⟨652392, by rfl⟩ : syracuseStep 1739713 = 1304785) B1304785
theorem B920537 : Blo 610295 920537 := bstep (se 2 (by rfl) ⟨345201, by rfl⟩ : syracuseStep 920537 = 690403) B690403
theorem B21269465 : Blo 610295 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B1379339 : Blo 610295 1379339 := bstep (se 1 (by rfl) ⟨1034504, by rfl⟩ : syracuseStep 1379339 = 2069009) B2069009
theorem B1379393 : Blo 610295 1379393 := bstep (se 2 (by rfl) ⟨517272, by rfl⟩ : syracuseStep 1379393 = 1034545) B1034545
theorem B920651 : Blo 610295 920651 := bstep (se 1 (by rfl) ⟨690488, by rfl⟩ : syracuseStep 920651 = 1380977) B1380977
theorem B920663 : Blo 610295 920663 := bstep (se 1 (by rfl) ⟨690497, by rfl⟩ : syracuseStep 920663 = 1380995) B1380995
theorem B920729 : Blo 610295 920729 := bstep (se 2 (by rfl) ⟨345273, by rfl⟩ : syracuseStep 920729 = 690547) B690547
theorem B2329793 : Blo 610295 2329793 := bstep (se 2 (by rfl) ⟨873672, by rfl⟩ : syracuseStep 2329793 = 1747345) B1747345
theorem B2067659 : Blo 610295 2067659 := bstep (se 1 (by rfl) ⟨1550744, by rfl⟩ : syracuseStep 2067659 = 3101489) B3101489
theorem B3312857 : Blo 610295 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B920843 : Blo 610295 920843 := bstep (se 1 (by rfl) ⟨690632, by rfl⟩ : syracuseStep 920843 = 1381265) B1381265
theorem B1740055 : Blo 610295 1740055 := bstep (se 1 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 1740055 = 2610083) B2610083
theorem B920855 : Blo 610295 920855 := bstep (se 1 (by rfl) ⟨690641, by rfl⟩ : syracuseStep 920855 = 1381283) B1381283
theorem B1379609 : Blo 610295 1379609 := bstep (se 2 (by rfl) ⟨517353, by rfl⟩ : syracuseStep 1379609 = 1034707) B1034707
theorem B920921 : Blo 610295 920921 := bstep (se 2 (by rfl) ⟨345345, by rfl⟩ : syracuseStep 920921 = 690691) B690691
theorem B1379699 : Blo 610295 1379699 := bstep (se 1 (by rfl) ⟨1034774, by rfl⟩ : syracuseStep 1379699 = 2069549) B2069549
theorem B1379735 : Blo 610295 1379735 := bstep (se 1 (by rfl) ⟨1034801, by rfl⟩ : syracuseStep 1379735 = 2069603) B2069603
theorem B1510859 : Blo 610295 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B921035 : Blo 610295 921035 := bstep (se 1 (by rfl) ⟨690776, by rfl⟩ : syracuseStep 921035 = 1381553) B1381553
theorem B921047 : Blo 610295 921047 := bstep (se 1 (by rfl) ⟨690785, by rfl⟩ : syracuseStep 921047 = 1381571) B1381571
theorem B2067929 : Blo 610295 2067929 := bstep (se 2 (by rfl) ⟨775473, by rfl⟩ : syracuseStep 2067929 = 1550947) B1550947
theorem B921113 : Blo 610295 921113 := bstep (se 2 (by rfl) ⟨345417, by rfl⟩ : syracuseStep 921113 = 690835) B690835
theorem B1379915 : Blo 610295 1379915 := bstep (se 1 (by rfl) ⟨1034936, by rfl⟩ : syracuseStep 1379915 = 2069873) B2069873
theorem B1379969 : Blo 610295 1379969 := bstep (se 2 (by rfl) ⟨517488, by rfl⟩ : syracuseStep 1379969 = 1034977) B1034977
theorem B921227 : Blo 610295 921227 := bstep (se 1 (by rfl) ⟨690920, by rfl⟩ : syracuseStep 921227 = 1381841) B1381841
theorem B921239 : Blo 610295 921239 := bstep (se 1 (by rfl) ⟨690929, by rfl⟩ : syracuseStep 921239 = 1381859) B1381859
theorem B921305 : Blo 610295 921305 := bstep (se 2 (by rfl) ⟨345489, by rfl⟩ : syracuseStep 921305 = 690979) B690979
theorem B921419 : Blo 610295 921419 := bstep (se 1 (by rfl) ⟨691064, by rfl⟩ : syracuseStep 921419 = 1382129) B1382129
theorem B921431 : Blo 610295 921431 := bstep (se 1 (by rfl) ⟨691073, by rfl⟩ : syracuseStep 921431 = 1382147) B1382147
theorem B1380185 : Blo 610295 1380185 := bstep (se 2 (by rfl) ⟨517569, by rfl⟩ : syracuseStep 1380185 = 1035139) B1035139
theorem B1380275 : Blo 610295 1380275 := bstep (se 1 (by rfl) ⟨1035206, by rfl⟩ : syracuseStep 1380275 = 2070413) B2070413
theorem B1380311 : Blo 610295 1380311 := bstep (se 1 (by rfl) ⟨1035233, by rfl⟩ : syracuseStep 1380311 = 2070467) B2070467
theorem B1740761 : Blo 610295 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B7082059 : Blo 610295 7082059 := bstep (se 1 (by rfl) ⟨5311544, by rfl⟩ : syracuseStep 7082059 = 10623089) B10623089
theorem B1380491 : Blo 610295 1380491 := bstep (se 1 (by rfl) ⟨1035368, by rfl⟩ : syracuseStep 1380491 = 2070737) B2070737
theorem B2068631 : Blo 610295 2068631 := bstep (se 1 (by rfl) ⟨1551473, by rfl⟩ : syracuseStep 2068631 = 3102947) B3102947
theorem B1380545 : Blo 610295 1380545 := bstep (se 2 (by rfl) ⟨517704, by rfl⟩ : syracuseStep 1380545 = 1035409) B1035409
theorem B3150211 : Blo 610295 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B1380761 : Blo 610295 1380761 := bstep (se 2 (by rfl) ⟨517785, by rfl⟩ : syracuseStep 1380761 = 1035571) B1035571
theorem B1380851 : Blo 610295 1380851 := bstep (se 1 (by rfl) ⟨1035638, by rfl⟩ : syracuseStep 1380851 = 2071277) B2071277
theorem B1380887 : Blo 610295 1380887 := bstep (se 1 (by rfl) ⟨1035665, by rfl⟩ : syracuseStep 1380887 = 2071331) B2071331
theorem B2331281 : Blo 610295 2331281 := bstep (se 2 (by rfl) ⟨874230, by rfl⟩ : syracuseStep 2331281 = 1748461) B1748461
theorem B2069171 : Blo 610295 2069171 := bstep (se 1 (by rfl) ⟨1551878, by rfl⟩ : syracuseStep 2069171 = 3103757) B3103757
theorem B1381067 : Blo 610295 1381067 := bstep (se 1 (by rfl) ⟨1035800, by rfl⟩ : syracuseStep 1381067 = 2071601) B2071601
theorem B21205745 : Blo 610295 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B1381121 : Blo 610295 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B2200385 : Blo 610295 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B3478423 : Blo 610295 3478423 := bstep (se 1 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 3478423 = 5217635) B5217635
theorem B2200499 : Blo 610295 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B2069441 : Blo 610295 2069441 := bstep (se 2 (by rfl) ⟨776040, by rfl⟩ : syracuseStep 2069441 = 1552081) B1552081
theorem B1381337 : Blo 610295 1381337 := bstep (se 2 (by rfl) ⟨518001, by rfl⟩ : syracuseStep 1381337 = 1036003) B1036003
theorem B1381427 : Blo 610295 1381427 := bstep (se 1 (by rfl) ⟨1036070, by rfl⟩ : syracuseStep 1381427 = 2072141) B2072141
theorem B1381463 : Blo 610295 1381463 := bstep (se 1 (by rfl) ⟨1036097, by rfl⟩ : syracuseStep 1381463 = 2072195) B2072195
theorem B2331737 : Blo 610295 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B1545419 : Blo 610295 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B1381643 : Blo 610295 1381643 := bstep (se 1 (by rfl) ⟨1036232, by rfl⟩ : syracuseStep 1381643 = 2072465) B2072465
theorem B2331949 : Blo 610295 2331949 := bstep (se 3 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 2331949 = 874481) B874481
theorem B1381697 : Blo 610295 1381697 := bstep (se 2 (by rfl) ⟨518136, by rfl⟩ : syracuseStep 1381697 = 1036273) B1036273
theorem B7542233 : Blo 610295 7542233 := bstep (se 2 (by rfl) ⟨2828337, by rfl⟩ : syracuseStep 7542233 = 5656675) B5656675
theorem B2069981 : Blo 610295 2069981 := bstep (se 3 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 2069981 = 776243) B776243
theorem B1381913 : Blo 610295 1381913 := bstep (se 2 (by rfl) ⟨518217, by rfl⟩ : syracuseStep 1381913 = 1036435) B1036435
theorem B1742401 : Blo 610295 1742401 := bstep (se 2 (by rfl) ⟨653400, by rfl⟩ : syracuseStep 1742401 = 1306801) B1306801
theorem B2332253 : Blo 610295 2332253 := bstep (se 3 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 2332253 = 874595) B874595
theorem B1382003 : Blo 610295 1382003 := bstep (se 1 (by rfl) ⟨1036502, by rfl⟩ : syracuseStep 1382003 = 2073005) B2073005
theorem B1382039 : Blo 610295 1382039 := bstep (se 1 (by rfl) ⟨1036529, by rfl⟩ : syracuseStep 1382039 = 2073059) B2073059
theorem B3545189 : Blo 610295 3545189 := bstep (se 4 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 3545189 = 664723) B664723
theorem B1546391 : Blo 610295 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B13211909 : Blo 610295 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B2202029 : Blo 610295 2202029 := bstep (se 3 (by rfl) ⟨412880, by rfl⟩ : syracuseStep 2202029 = 825761) B825761
theorem B825815 : Blo 610295 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2071115 : Blo 610295 2071115 := bstep (se 1 (by rfl) ⟨1553336, by rfl⟩ : syracuseStep 2071115 = 3106673) B3106673
theorem B1547059 : Blo 610295 1547059 := bstep (se 1 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 1547059 = 2320589) B2320589
theorem B2071385 : Blo 610295 2071385 := bstep (se 2 (by rfl) ⟨776769, by rfl⟩ : syracuseStep 2071385 = 1553539) B1553539
theorem B2202461 : Blo 610295 2202461 := bstep (se 3 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 2202461 = 825923) B825923
theorem B1547201 : Blo 610295 1547201 := bstep (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) B1160401
theorem B826571 : Blo 610295 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B2072087 : Blo 610295 2072087 := bstep (se 1 (by rfl) ⟨1554065, by rfl⟩ : syracuseStep 2072087 = 3108131) B3108131
theorem B696043 : Blo 610295 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B12754979 : Blo 610295 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B2072627 : Blo 610295 2072627 := bstep (se 1 (by rfl) ⟨1554470, by rfl⟩ : syracuseStep 2072627 = 3108941) B3108941
theorem B1548467 : Blo 610295 1548467 := bstep (se 1 (by rfl) ⟨1161350, by rfl⟩ : syracuseStep 1548467 = 2322701) B2322701
theorem B2072897 : Blo 610295 2072897 := bstep (se 2 (by rfl) ⟨777336, by rfl⟩ : syracuseStep 2072897 = 1554673) B1554673
theorem B2204291 : Blo 610295 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B1549003 : Blo 610295 1549003 := bstep (se 1 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 1549003 = 2323505) B2323505
theorem B17703629 : Blo 610295 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B11805425 : Blo 610295 11805425 := bstep (se 2 (by rfl) ⟨4427034, by rfl⟩ : syracuseStep 11805425 = 8854069) B8854069
theorem B1549145 : Blo 610295 1549145 := bstep (se 2 (by rfl) ⟨580929, by rfl⟩ : syracuseStep 1549145 = 1161859) B1161859
theorem B2794333 : Blo 610295 2794333 := bstep (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) B1047875
theorem B1746137 : Blo 610295 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B3319001 : Blo 610295 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B11150693 : Blo 610295 11150693 := bstep (se 4 (by rfl) ⟨1045377, by rfl⟩ : syracuseStep 11150693 = 2090755) B2090755
theorem B1549975 : Blo 610295 1549975 := bstep (se 1 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 1549975 = 2324963) B2324963
theorem B1550411 : Blo 610295 1550411 := bstep (se 1 (by rfl) ⟨1162808, by rfl⟩ : syracuseStep 1550411 = 2325617) B2325617
theorem B9939095 : Blo 610295 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B1550785 : Blo 610295 1550785 := bstep (se 2 (by rfl) ⟨581544, by rfl⟩ : syracuseStep 1550785 = 1163089) B1163089
theorem B1747403 : Blo 610295 1747403 := bstep (se 1 (by rfl) ⟨1310552, by rfl⟩ : syracuseStep 1747403 = 2621105) B2621105
theorem B698935 : Blo 610295 698935 := bstep (se 1 (by rfl) ⟨524201, by rfl⟩ : syracuseStep 698935 = 1048403) B1048403
theorem B830027 : Blo 610295 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B5286617 : Blo 610295 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B1551383 : Blo 610295 1551383 := bstep (se 1 (by rfl) ⟨1163537, by rfl⟩ : syracuseStep 1551383 = 2327075) B2327075
theorem B3091607 : Blo 610295 3091607 := bstep (se 1 (by rfl) ⟨2318705, by rfl⟩ : syracuseStep 3091607 = 4637411) B4637411
theorem B6991109 : Blo 610295 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B1158617 : Blo 610295 1158617 := bstep (se 2 (by rfl) ⟨434481, by rfl⟩ : syracuseStep 1158617 = 868963) B868963
theorem B1650137 : Blo 610295 1650137 := bstep (se 2 (by rfl) ⟨618801, by rfl⟩ : syracuseStep 1650137 = 1237603) B1237603
theorem B1552193 : Blo 610295 1552193 := bstep (se 2 (by rfl) ⟨582072, by rfl⟩ : syracuseStep 1552193 = 1164145) B1164145
theorem B14135219 : Blo 610295 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B5451781 : Blo 610295 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B3485713 : Blo 610295 3485713 := bstep (se 2 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 3485713 = 2614285) B2614285
theorem B2797841 : Blo 610295 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B1552729 : Blo 610295 1552729 := bstep (se 2 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 1552729 = 1164547) B1164547
theorem B1160075 : Blo 610295 1160075 := bstep (se 1 (by rfl) ⟨870056, by rfl⟩ : syracuseStep 1160075 = 1740113) B1740113
theorem B1160257 : Blo 610295 1160257 := bstep (se 2 (by rfl) ⟨435096, by rfl⟩ : syracuseStep 1160257 = 870193) B870193
theorem B1553843 : Blo 610295 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1160705 : Blo 610295 1160705 := bstep (se 2 (by rfl) ⟨435264, by rfl⟩ : syracuseStep 1160705 = 870529) B870529
theorem B4961893 : Blo 610295 4961893 := bstep (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) B930355
theorem B3913433 : Blo 610295 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B1554137 : Blo 610295 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B734999 : Blo 610295 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B1161047 : Blo 610295 1161047 := bstep (se 1 (by rfl) ⟨870785, by rfl⟩ : syracuseStep 1161047 = 1741571) B1741571
theorem B9910289 : Blo 610295 9910289 := bstep (se 2 (by rfl) ⟨3716358, by rfl⟩ : syracuseStep 9910289 = 7432717) B7432717
theorem B1030475 : Blo 610295 1030475 := bstep (se 1 (by rfl) ⟨772856, by rfl⟩ : syracuseStep 1030475 = 1545713) B1545713
theorem B4634981 : Blo 610295 4634981 := bstep (se 4 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 4634981 = 869059) B869059
theorem B1030603 : Blo 610295 1030603 := bstep (se 1 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 1030603 = 1545905) B1545905
theorem B735691 : Blo 610295 735691 := bstep (se 1 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 735691 = 1103537) B1103537
theorem B1161715 : Blo 610295 1161715 := bstep (se 1 (by rfl) ⟨871286, by rfl⟩ : syracuseStep 1161715 = 1742573) B1742573
theorem B11450893 : Blo 610295 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B1030745 : Blo 610295 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B3095171 : Blo 610295 3095171 := bstep (se 1 (by rfl) ⟨2321378, by rfl⟩ : syracuseStep 3095171 = 4642757) B4642757
theorem B1030873 : Blo 610295 1030873 := bstep (se 2 (by rfl) ⟨386577, by rfl⟩ : syracuseStep 1030873 = 773155) B773155
theorem B4635467 : Blo 610295 4635467 := bstep (se 1 (by rfl) ⟨3476600, by rfl⟩ : syracuseStep 4635467 = 6953201) B6953201
theorem B1162163 : Blo 610295 1162163 := bstep (se 1 (by rfl) ⟨871622, by rfl⟩ : syracuseStep 1162163 = 1743245) B1743245
theorem B81476549 : Blo 610295 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1162201 : Blo 610295 1162201 := bstep (se 2 (by rfl) ⟨435825, by rfl⟩ : syracuseStep 1162201 = 871651) B871651
theorem B1031447 : Blo 610295 1031447 := bstep (se 1 (by rfl) ⟨773585, by rfl⟩ : syracuseStep 1031447 = 1547171) B1547171
theorem B3489155 : Blo 610295 3489155 := bstep (se 1 (by rfl) ⟨2616866, by rfl⟩ : syracuseStep 3489155 = 5233733) B5233733
theorem B1031575 : Blo 610295 1031575 := bstep (se 1 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 1031575 = 1547363) B1547363
theorem B1162649 : Blo 610295 1162649 := bstep (se 2 (by rfl) ⟨435993, by rfl⟩ : syracuseStep 1162649 = 871987) B871987
theorem B1032203 : Blo 610295 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B1163393 : Blo 610295 1163393 := bstep (se 2 (by rfl) ⟨436272, by rfl⟩ : syracuseStep 1163393 = 872545) B872545
theorem B1032331 : Blo 610295 1032331 := bstep (se 1 (by rfl) ⟨774248, by rfl⟩ : syracuseStep 1032331 = 1548497) B1548497
theorem B1032473 : Blo 610295 1032473 := bstep (se 2 (by rfl) ⟨387177, by rfl⟩ : syracuseStep 1032473 = 774355) B774355
theorem B2212147 : Blo 610295 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B3916097 : Blo 610295 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B737623 : Blo 610295 737623 := bstep (se 1 (by rfl) ⟨553217, by rfl⟩ : syracuseStep 737623 = 1106435) B1106435
theorem B1163659 : Blo 610295 1163659 := bstep (se 1 (by rfl) ⟨872744, by rfl⟩ : syracuseStep 1163659 = 1745489) B1745489
theorem B1032601 : Blo 610295 1032601 := bstep (se 2 (by rfl) ⟨387225, by rfl⟩ : syracuseStep 1032601 = 774451) B774451
theorem B4965137 : Blo 610295 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B1164107 : Blo 610295 1164107 := bstep (se 1 (by rfl) ⟨873080, by rfl⟩ : syracuseStep 1164107 = 1746161) B1746161
theorem B1033175 : Blo 610295 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B1164289 : Blo 610295 1164289 := bstep (se 2 (by rfl) ⟨436608, by rfl⟩ : syracuseStep 1164289 = 873217) B873217
theorem B869401 : Blo 610295 869401 := bstep (se 2 (by rfl) ⟨326025, by rfl⟩ : syracuseStep 869401 = 652051) B652051
theorem B9290821 : Blo 610295 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B1033303 : Blo 610295 1033303 := bstep (se 1 (by rfl) ⟨774977, by rfl⟩ : syracuseStep 1033303 = 1549955) B1549955
theorem B4310117 : Blo 610295 4310117 := bstep (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) B808147
theorem B2213057 : Blo 610295 2213057 := bstep (se 2 (by rfl) ⟨829896, by rfl⟩ : syracuseStep 2213057 = 1659793) B1659793
theorem B2213185 : Blo 610295 2213185 := bstep (se 2 (by rfl) ⟨829944, by rfl⟩ : syracuseStep 2213185 = 1659889) B1659889
theorem B1164631 : Blo 610295 1164631 := bstep (se 1 (by rfl) ⟨873473, by rfl⟩ : syracuseStep 1164631 = 1746947) B1746947
theorem B1164851 : Blo 610295 1164851 := bstep (se 1 (by rfl) ⟨873638, by rfl⟩ : syracuseStep 1164851 = 1747277) B1747277
theorem B1394329 : Blo 610295 1394329 := bstep (se 2 (by rfl) ⟨522873, by rfl⟩ : syracuseStep 1394329 = 1045747) B1045747
theorem B1033931 : Blo 610295 1033931 := bstep (se 1 (by rfl) ⟨775448, by rfl⟩ : syracuseStep 1033931 = 1550897) B1550897
theorem B3491545 : Blo 610295 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B3917585 : Blo 610295 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B1165079 : Blo 610295 1165079 := bstep (se 1 (by rfl) ⟨873809, by rfl⟩ : syracuseStep 1165079 = 1747619) B1747619
theorem B2475821 : Blo 610295 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B1034059 : Blo 610295 1034059 := bstep (se 1 (by rfl) ⟨775544, by rfl⟩ : syracuseStep 1034059 = 1551089) B1551089
theorem B2607041 : Blo 610295 2607041 := bstep (se 2 (by rfl) ⟨977640, by rfl⟩ : syracuseStep 2607041 = 1955281) B1955281
theorem B1034201 : Blo 610295 1034201 := bstep (se 2 (by rfl) ⟨387825, by rfl⟩ : syracuseStep 1034201 = 775651) B775651
theorem B1165337 : Blo 610295 1165337 := bstep (se 2 (by rfl) ⟨437001, by rfl⟩ : syracuseStep 1165337 = 874003) B874003
theorem B1034329 : Blo 610295 1034329 := bstep (se 2 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 1034329 = 775747) B775747
theorem B1099955 : Blo 610295 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B1657025 : Blo 610295 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B3098897 : Blo 610295 3098897 := bstep (se 2 (by rfl) ⟨1162086, by rfl⟩ : syracuseStep 3098897 = 2324173) B2324173
theorem B2607383 : Blo 610295 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B2935115 : Blo 610295 2935115 := bstep (se 1 (by rfl) ⟨2201336, by rfl⟩ : syracuseStep 2935115 = 4402673) B4402673
theorem B870745 : Blo 610295 870745 := bstep (se 2 (by rfl) ⟨326529, by rfl⟩ : syracuseStep 870745 = 653059) B653059
theorem B3099059 : Blo 610295 3099059 := bstep (se 1 (by rfl) ⟨2324294, by rfl⟩ : syracuseStep 3099059 = 4648589) B4648589
theorem B1165747 : Blo 610295 1165747 := bstep (se 1 (by rfl) ⟨874310, by rfl⟩ : syracuseStep 1165747 = 1748621) B1748621
theorem B870859 : Blo 610295 870859 := bstep (se 1 (by rfl) ⟨653144, by rfl⟩ : syracuseStep 870859 = 1306289) B1306289
theorem B3492503 : Blo 610295 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B1034903 : Blo 610295 1034903 := bstep (se 1 (by rfl) ⟨776177, by rfl⟩ : syracuseStep 1034903 = 1552355) B1552355
theorem B1035031 : Blo 610295 1035031 := bstep (se 1 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 1035031 = 1552547) B1552547
theorem B773003 : Blo 610295 773003 := bstep (se 1 (by rfl) ⟨579752, by rfl⟩ : syracuseStep 773003 = 1159505) B1159505
theorem B4967345 : Blo 610295 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B11160611 : Blo 610295 11160611 := bstep (se 1 (by rfl) ⟨8370458, by rfl⟩ : syracuseStep 11160611 = 16740917) B16740917
theorem B2608307 : Blo 610295 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B2477249 : Blo 610295 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B1035659 : Blo 610295 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B1035787 : Blo 610295 1035787 := bstep (se 1 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 1035787 = 1553681) B1553681
theorem B773707 : Blo 610295 773707 := bstep (se 1 (by rfl) ⟨580280, by rfl⟩ : syracuseStep 773707 = 1160561) B1160561
theorem B1035929 : Blo 610295 1035929 := bstep (se 2 (by rfl) ⟨388473, by rfl⟩ : syracuseStep 1035929 = 776947) B776947
theorem B35311301 : Blo 610295 35311301 := bstep (se 4 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 35311301 = 6620869) B6620869
theorem B872203 : Blo 610295 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B1036057 : Blo 610295 1036057 := bstep (se 2 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 1036057 = 777043) B777043
theorem B773975 : Blo 610295 773975 := bstep (se 1 (by rfl) ⟨580481, by rfl⟩ : syracuseStep 773975 = 1160963) B1160963
theorem B4771685 : Blo 610295 4771685 := bstep (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) B894691
theorem B1101721 : Blo 610295 1101721 := bstep (se 2 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 1101721 = 826291) B826291
theorem B19812275 : Blo 610295 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B610295 : Blo 610295 610295 := bstep (se 1 (by rfl) ⟨457721, by rfl⟩ : syracuseStep 610295 = 915443) B915443
theorem B610315 : Blo 610295 610315 := bstep (se 1 (by rfl) ⟨457736, by rfl⟩ : syracuseStep 610315 = 915473) B915473
theorem B610327 : Blo 610295 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B872471 : Blo 610295 872471 := bstep (se 1 (by rfl) ⟨654353, by rfl⟩ : syracuseStep 872471 = 1308707) B1308707
theorem B13455395 : Blo 610295 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B610347 : Blo 610295 610347 := bstep (se 1 (by rfl) ⟨457760, by rfl⟩ : syracuseStep 610347 = 915521) B915521
theorem B4640813 : Blo 610295 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B610359 : Blo 610295 610359 := bstep (se 1 (by rfl) ⟨457769, by rfl⟩ : syracuseStep 610359 = 915539) B915539
theorem B610379 : Blo 610295 610379 := bstep (se 1 (by rfl) ⟨457784, by rfl⟩ : syracuseStep 610379 = 915569) B915569
theorem B610391 : Blo 610295 610391 := bstep (se 1 (by rfl) ⟨457793, by rfl⟩ : syracuseStep 610391 = 915587) B915587
theorem B610411 : Blo 610295 610411 := bstep (se 1 (by rfl) ⟨457808, by rfl⟩ : syracuseStep 610411 = 915617) B915617
theorem B610423 : Blo 610295 610423 := bstep (se 1 (by rfl) ⟨457817, by rfl⟩ : syracuseStep 610423 = 915635) B915635
theorem B610443 : Blo 610295 610443 := bstep (se 1 (by rfl) ⟨457832, by rfl⟩ : syracuseStep 610443 = 915665) B915665
theorem B2609297 : Blo 610295 2609297 := bstep (se 2 (by rfl) ⟨978486, by rfl⟩ : syracuseStep 2609297 = 1956973) B1956973
theorem B610455 : Blo 610295 610455 := bstep (se 1 (by rfl) ⟨457841, by rfl⟩ : syracuseStep 610455 = 915683) B915683
theorem B610475 : Blo 610295 610475 := bstep (se 1 (by rfl) ⟨457856, by rfl⟩ : syracuseStep 610475 = 915713) B915713
theorem B610487 : Blo 610295 610487 := bstep (se 1 (by rfl) ⟨457865, by rfl⟩ : syracuseStep 610487 = 915731) B915731
theorem B610507 : Blo 610295 610507 := bstep (se 1 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 610507 = 915761) B915761
theorem B7065805 : Blo 610295 7065805 := bstep (se 3 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 7065805 = 2649677) B2649677
theorem B610519 : Blo 610295 610519 := bstep (se 1 (by rfl) ⟨457889, by rfl⟩ : syracuseStep 610519 = 915779) B915779
theorem B610539 : Blo 610295 610539 := bstep (se 1 (by rfl) ⟨457904, by rfl⟩ : syracuseStep 610539 = 915809) B915809
theorem B610551 : Blo 610295 610551 := bstep (se 1 (by rfl) ⟨457913, by rfl⟩ : syracuseStep 610551 = 915827) B915827
theorem B610571 : Blo 610295 610571 := bstep (se 1 (by rfl) ⟨457928, by rfl⟩ : syracuseStep 610571 = 915857) B915857
theorem B610583 : Blo 610295 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B610603 : Blo 610295 610603 := bstep (se 1 (by rfl) ⟨457952, by rfl⟩ : syracuseStep 610603 = 915905) B915905
theorem B610615 : Blo 610295 610615 := bstep (se 1 (by rfl) ⟨457961, by rfl⟩ : syracuseStep 610615 = 915923) B915923
theorem B610635 : Blo 610295 610635 := bstep (se 1 (by rfl) ⟨457976, by rfl⟩ : syracuseStep 610635 = 915953) B915953
theorem B3101003 : Blo 610295 3101003 := bstep (se 1 (by rfl) ⟨2325752, by rfl⟩ : syracuseStep 3101003 = 4651505) B4651505
theorem B610647 : Blo 610295 610647 := bstep (se 1 (by rfl) ⟨457985, by rfl⟩ : syracuseStep 610647 = 915971) B915971
theorem B610667 : Blo 610295 610667 := bstep (se 1 (by rfl) ⟨458000, by rfl⟩ : syracuseStep 610667 = 916001) B916001
theorem B610679 : Blo 610295 610679 := bstep (se 1 (by rfl) ⟨458009, by rfl⟩ : syracuseStep 610679 = 916019) B916019
theorem B610699 : Blo 610295 610699 := bstep (se 1 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 610699 = 916049) B916049
theorem B610711 : Blo 610295 610711 := bstep (se 1 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 610711 = 916067) B916067
theorem B610731 : Blo 610295 610731 := bstep (se 1 (by rfl) ⟨458048, by rfl⟩ : syracuseStep 610731 = 916097) B916097
theorem B610743 : Blo 610295 610743 := bstep (se 1 (by rfl) ⟨458057, by rfl⟩ : syracuseStep 610743 = 916115) B916115
theorem B610763 : Blo 610295 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B610775 : Blo 610295 610775 := bstep (se 1 (by rfl) ⟨458081, by rfl⟩ : syracuseStep 610775 = 916163) B916163
theorem B610795 : Blo 610295 610795 := bstep (se 1 (by rfl) ⟨458096, by rfl⟩ : syracuseStep 610795 = 916193) B916193
theorem B610807 : Blo 610295 610807 := bstep (se 1 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 610807 = 916211) B916211
theorem B610827 : Blo 610295 610827 := bstep (se 1 (by rfl) ⟨458120, by rfl⟩ : syracuseStep 610827 = 916241) B916241
theorem B6279697 : Blo 610295 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B610839 : Blo 610295 610839 := bstep (se 1 (by rfl) ⟨458129, by rfl⟩ : syracuseStep 610839 = 916259) B916259
theorem B774679 : Blo 610295 774679 := bstep (se 1 (by rfl) ⟨581009, by rfl⟩ : syracuseStep 774679 = 1162019) B1162019
theorem B610859 : Blo 610295 610859 := bstep (se 1 (by rfl) ⟨458144, by rfl⟩ : syracuseStep 610859 = 916289) B916289
theorem B610871 : Blo 610295 610871 := bstep (se 1 (by rfl) ⟨458153, by rfl⟩ : syracuseStep 610871 = 916307) B916307
theorem B1659457 : Blo 610295 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B610891 : Blo 610295 610891 := bstep (se 1 (by rfl) ⟨458168, by rfl⟩ : syracuseStep 610891 = 916337) B916337
theorem B610903 : Blo 610295 610903 := bstep (se 1 (by rfl) ⟨458177, by rfl⟩ : syracuseStep 610903 = 916355) B916355
theorem B610923 : Blo 610295 610923 := bstep (se 1 (by rfl) ⟨458192, by rfl⟩ : syracuseStep 610923 = 916385) B916385
theorem B610935 : Blo 610295 610935 := bstep (se 1 (by rfl) ⟨458201, by rfl⟩ : syracuseStep 610935 = 916403) B916403
theorem B610955 : Blo 610295 610955 := bstep (se 1 (by rfl) ⟨458216, by rfl⟩ : syracuseStep 610955 = 916433) B916433
theorem B610967 : Blo 610295 610967 := bstep (se 1 (by rfl) ⟨458225, by rfl⟩ : syracuseStep 610967 = 916451) B916451
theorem B610987 : Blo 610295 610987 := bstep (se 1 (by rfl) ⟨458240, by rfl⟩ : syracuseStep 610987 = 916481) B916481
theorem B610999 : Blo 610295 610999 := bstep (se 1 (by rfl) ⟨458249, by rfl⟩ : syracuseStep 610999 = 916499) B916499
theorem B611019 : Blo 610295 611019 := bstep (se 1 (by rfl) ⟨458264, by rfl⟩ : syracuseStep 611019 = 916529) B916529
theorem B611031 : Blo 610295 611031 := bstep (se 1 (by rfl) ⟨458273, by rfl⟩ : syracuseStep 611031 = 916547) B916547
theorem B611051 : Blo 610295 611051 := bstep (se 1 (by rfl) ⟨458288, by rfl⟩ : syracuseStep 611051 = 916577) B916577
theorem B611063 : Blo 610295 611063 := bstep (se 1 (by rfl) ⟨458297, by rfl⟩ : syracuseStep 611063 = 916595) B916595
theorem B611083 : Blo 610295 611083 := bstep (se 1 (by rfl) ⟨458312, by rfl⟩ : syracuseStep 611083 = 916625) B916625
theorem B611095 : Blo 610295 611095 := bstep (se 1 (by rfl) ⟨458321, by rfl⟩ : syracuseStep 611095 = 916643) B916643
theorem B611115 : Blo 610295 611115 := bstep (se 1 (by rfl) ⟨458336, by rfl⟩ : syracuseStep 611115 = 916673) B916673
theorem B6443821 : Blo 610295 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B611127 : Blo 610295 611127 := bstep (se 1 (by rfl) ⟨458345, by rfl⟩ : syracuseStep 611127 = 916691) B916691
theorem B611147 : Blo 610295 611147 := bstep (se 1 (by rfl) ⟨458360, by rfl⟩ : syracuseStep 611147 = 916721) B916721
theorem B611159 : Blo 610295 611159 := bstep (se 1 (by rfl) ⟨458369, by rfl⟩ : syracuseStep 611159 = 916739) B916739
theorem B611179 : Blo 610295 611179 := bstep (se 1 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 611179 = 916769) B916769
theorem B611191 : Blo 610295 611191 := bstep (se 1 (by rfl) ⟨458393, by rfl⟩ : syracuseStep 611191 = 916787) B916787
theorem B611211 : Blo 610295 611211 := bstep (se 1 (by rfl) ⟨458408, by rfl⟩ : syracuseStep 611211 = 916817) B916817
theorem B611223 : Blo 610295 611223 := bstep (se 1 (by rfl) ⟨458417, by rfl⟩ : syracuseStep 611223 = 916835) B916835
theorem B611243 : Blo 610295 611243 := bstep (se 1 (by rfl) ⟨458432, by rfl⟩ : syracuseStep 611243 = 916865) B916865
theorem B611255 : Blo 610295 611255 := bstep (se 1 (by rfl) ⟨458441, by rfl⟩ : syracuseStep 611255 = 916883) B916883
theorem B611275 : Blo 610295 611275 := bstep (se 1 (by rfl) ⟨458456, by rfl⟩ : syracuseStep 611275 = 916913) B916913
theorem B611287 : Blo 610295 611287 := bstep (se 1 (by rfl) ⟨458465, by rfl⟩ : syracuseStep 611287 = 916931) B916931
theorem B873433 : Blo 610295 873433 := bstep (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) B655075
theorem B611307 : Blo 610295 611307 := bstep (se 1 (by rfl) ⟨458480, by rfl⟩ : syracuseStep 611307 = 916961) B916961
theorem B611319 : Blo 610295 611319 := bstep (se 1 (by rfl) ⟨458489, by rfl⟩ : syracuseStep 611319 = 916979) B916979
theorem B611339 : Blo 610295 611339 := bstep (se 1 (by rfl) ⟨458504, by rfl⟩ : syracuseStep 611339 = 917009) B917009
theorem B611351 : Blo 610295 611351 := bstep (se 1 (by rfl) ⟨458513, by rfl⟩ : syracuseStep 611351 = 917027) B917027
theorem B611371 : Blo 610295 611371 := bstep (se 1 (by rfl) ⟨458528, by rfl⟩ : syracuseStep 611371 = 917057) B917057
theorem B611383 : Blo 610295 611383 := bstep (se 1 (by rfl) ⟨458537, by rfl⟩ : syracuseStep 611383 = 917075) B917075
theorem B611403 : Blo 610295 611403 := bstep (se 1 (by rfl) ⟨458552, by rfl⟩ : syracuseStep 611403 = 917105) B917105
theorem B3494987 : Blo 610295 3494987 := bstep (se 1 (by rfl) ⟨2621240, by rfl⟩ : syracuseStep 3494987 = 5242481) B5242481
theorem B611415 : Blo 610295 611415 := bstep (se 1 (by rfl) ⟨458561, by rfl⟩ : syracuseStep 611415 = 917123) B917123
theorem B611435 : Blo 610295 611435 := bstep (se 1 (by rfl) ⟨458576, by rfl⟩ : syracuseStep 611435 = 917153) B917153
theorem B611447 : Blo 610295 611447 := bstep (se 1 (by rfl) ⟨458585, by rfl⟩ : syracuseStep 611447 = 917171) B917171
theorem B1135745 : Blo 610295 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B611467 : Blo 610295 611467 := bstep (se 1 (by rfl) ⟨458600, by rfl⟩ : syracuseStep 611467 = 917201) B917201
theorem B611479 : Blo 610295 611479 := bstep (se 1 (by rfl) ⟨458609, by rfl⟩ : syracuseStep 611479 = 917219) B917219
theorem B611499 : Blo 610295 611499 := bstep (se 1 (by rfl) ⟨458624, by rfl⟩ : syracuseStep 611499 = 917249) B917249
theorem B611511 : Blo 610295 611511 := bstep (se 1 (by rfl) ⟨458633, by rfl⟩ : syracuseStep 611511 = 917267) B917267
theorem B611531 : Blo 610295 611531 := bstep (se 1 (by rfl) ⟨458648, by rfl⟩ : syracuseStep 611531 = 917297) B917297
theorem B611543 : Blo 610295 611543 := bstep (se 1 (by rfl) ⟨458657, by rfl⟩ : syracuseStep 611543 = 917315) B917315
theorem B611563 : Blo 610295 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B611575 : Blo 610295 611575 := bstep (se 1 (by rfl) ⟨458681, by rfl⟩ : syracuseStep 611575 = 917363) B917363
theorem B611595 : Blo 610295 611595 := bstep (se 1 (by rfl) ⟨458696, by rfl⟩ : syracuseStep 611595 = 917393) B917393
theorem B611607 : Blo 610295 611607 := bstep (se 1 (by rfl) ⟨458705, by rfl⟩ : syracuseStep 611607 = 917411) B917411
theorem B611627 : Blo 610295 611627 := bstep (se 1 (by rfl) ⟨458720, by rfl⟩ : syracuseStep 611627 = 917441) B917441
theorem B611639 : Blo 610295 611639 := bstep (se 1 (by rfl) ⟨458729, by rfl⟩ : syracuseStep 611639 = 917459) B917459
theorem B611659 : Blo 610295 611659 := bstep (se 1 (by rfl) ⟨458744, by rfl⟩ : syracuseStep 611659 = 917489) B917489
theorem B611671 : Blo 610295 611671 := bstep (se 1 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 611671 = 917507) B917507
theorem B611691 : Blo 610295 611691 := bstep (se 1 (by rfl) ⟨458768, by rfl⟩ : syracuseStep 611691 = 917537) B917537
theorem B611703 : Blo 610295 611703 := bstep (se 1 (by rfl) ⟨458777, by rfl⟩ : syracuseStep 611703 = 917555) B917555
theorem B611723 : Blo 610295 611723 := bstep (se 1 (by rfl) ⟨458792, by rfl⟩ : syracuseStep 611723 = 917585) B917585
theorem B611735 : Blo 610295 611735 := bstep (se 1 (by rfl) ⟨458801, by rfl⟩ : syracuseStep 611735 = 917603) B917603
theorem B611755 : Blo 610295 611755 := bstep (se 1 (by rfl) ⟨458816, by rfl⟩ : syracuseStep 611755 = 917633) B917633
theorem B611767 : Blo 610295 611767 := bstep (se 1 (by rfl) ⟨458825, by rfl⟩ : syracuseStep 611767 = 917651) B917651
theorem B611787 : Blo 610295 611787 := bstep (se 1 (by rfl) ⟨458840, by rfl⟩ : syracuseStep 611787 = 917681) B917681
theorem B611799 : Blo 610295 611799 := bstep (se 1 (by rfl) ⟨458849, by rfl⟩ : syracuseStep 611799 = 917699) B917699
theorem B1103321 : Blo 610295 1103321 := bstep (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) B827491
theorem B611819 : Blo 610295 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B611831 : Blo 610295 611831 := bstep (se 1 (by rfl) ⟨458873, by rfl⟩ : syracuseStep 611831 = 917747) B917747
theorem B611851 : Blo 610295 611851 := bstep (se 1 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 611851 = 917777) B917777
theorem B611863 : Blo 610295 611863 := bstep (se 1 (by rfl) ⟨458897, by rfl⟩ : syracuseStep 611863 = 917795) B917795
theorem B611883 : Blo 610295 611883 := bstep (se 1 (by rfl) ⟨458912, by rfl⟩ : syracuseStep 611883 = 917825) B917825
theorem B611895 : Blo 610295 611895 := bstep (se 1 (by rfl) ⟨458921, by rfl⟩ : syracuseStep 611895 = 917843) B917843
theorem B611915 : Blo 610295 611915 := bstep (se 1 (by rfl) ⟨458936, by rfl⟩ : syracuseStep 611915 = 917873) B917873
theorem B611927 : Blo 610295 611927 := bstep (se 1 (by rfl) ⟨458945, by rfl⟩ : syracuseStep 611927 = 917891) B917891
theorem B611947 : Blo 610295 611947 := bstep (se 1 (by rfl) ⟨458960, by rfl⟩ : syracuseStep 611947 = 917921) B917921
theorem B611959 : Blo 610295 611959 := bstep (se 1 (by rfl) ⟨458969, by rfl⟩ : syracuseStep 611959 = 917939) B917939
theorem B611979 : Blo 610295 611979 := bstep (se 1 (by rfl) ⟨458984, by rfl⟩ : syracuseStep 611979 = 917969) B917969
theorem B611991 : Blo 610295 611991 := bstep (se 1 (by rfl) ⟨458993, by rfl⟩ : syracuseStep 611991 = 917987) B917987
theorem B612011 : Blo 610295 612011 := bstep (se 1 (by rfl) ⟨459008, by rfl⟩ : syracuseStep 612011 = 918017) B918017
theorem B612023 : Blo 610295 612023 := bstep (se 1 (by rfl) ⟨459017, by rfl⟩ : syracuseStep 612023 = 918035) B918035
theorem B612043 : Blo 610295 612043 := bstep (se 1 (by rfl) ⟨459032, by rfl⟩ : syracuseStep 612043 = 918065) B918065
theorem B612055 : Blo 610295 612055 := bstep (se 1 (by rfl) ⟨459041, by rfl⟩ : syracuseStep 612055 = 918083) B918083
theorem B612075 : Blo 610295 612075 := bstep (se 1 (by rfl) ⟨459056, by rfl⟩ : syracuseStep 612075 = 918113) B918113
theorem B612087 : Blo 610295 612087 := bstep (se 1 (by rfl) ⟨459065, by rfl⟩ : syracuseStep 612087 = 918131) B918131
theorem B612107 : Blo 610295 612107 := bstep (se 1 (by rfl) ⟨459080, by rfl⟩ : syracuseStep 612107 = 918161) B918161
theorem B612119 : Blo 610295 612119 := bstep (se 1 (by rfl) ⟨459089, by rfl⟩ : syracuseStep 612119 = 918179) B918179
theorem B612139 : Blo 610295 612139 := bstep (se 1 (by rfl) ⟨459104, by rfl⟩ : syracuseStep 612139 = 918209) B918209
theorem B612151 : Blo 610295 612151 := bstep (se 1 (by rfl) ⟨459113, by rfl⟩ : syracuseStep 612151 = 918227) B918227
theorem B1103681 : Blo 610295 1103681 := bstep (se 2 (by rfl) ⟨413880, by rfl⟩ : syracuseStep 1103681 = 827761) B827761
theorem B612171 : Blo 610295 612171 := bstep (se 1 (by rfl) ⟨459128, by rfl⟩ : syracuseStep 612171 = 918257) B918257
theorem B612183 : Blo 610295 612183 := bstep (se 1 (by rfl) ⟨459137, by rfl⟩ : syracuseStep 612183 = 918275) B918275
theorem B612203 : Blo 610295 612203 := bstep (se 1 (by rfl) ⟨459152, by rfl⟩ : syracuseStep 612203 = 918305) B918305
theorem B612215 : Blo 610295 612215 := bstep (se 1 (by rfl) ⟨459161, by rfl⟩ : syracuseStep 612215 = 918323) B918323
theorem B612235 : Blo 610295 612235 := bstep (se 1 (by rfl) ⟨459176, by rfl⟩ : syracuseStep 612235 = 918353) B918353
theorem B612247 : Blo 610295 612247 := bstep (se 1 (by rfl) ⟨459185, by rfl⟩ : syracuseStep 612247 = 918371) B918371
theorem B612267 : Blo 610295 612267 := bstep (se 1 (by rfl) ⟨459200, by rfl⟩ : syracuseStep 612267 = 918401) B918401
theorem B612279 : Blo 610295 612279 := bstep (se 1 (by rfl) ⟨459209, by rfl⟩ : syracuseStep 612279 = 918419) B918419
theorem B612299 : Blo 610295 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B612311 : Blo 610295 612311 := bstep (se 1 (by rfl) ⟨459233, by rfl⟩ : syracuseStep 612311 = 918467) B918467
theorem B612331 : Blo 610295 612331 := bstep (se 1 (by rfl) ⟨459248, by rfl⟩ : syracuseStep 612331 = 918497) B918497
theorem B612343 : Blo 610295 612343 := bstep (se 1 (by rfl) ⟨459257, by rfl⟩ : syracuseStep 612343 = 918515) B918515
theorem B612363 : Blo 610295 612363 := bstep (se 1 (by rfl) ⟨459272, by rfl⟩ : syracuseStep 612363 = 918545) B918545
theorem B612375 : Blo 610295 612375 := bstep (se 1 (by rfl) ⟨459281, by rfl⟩ : syracuseStep 612375 = 918563) B918563
theorem B612395 : Blo 610295 612395 := bstep (se 1 (by rfl) ⟨459296, by rfl⟩ : syracuseStep 612395 = 918593) B918593
theorem B612407 : Blo 610295 612407 := bstep (se 1 (by rfl) ⟨459305, by rfl⟩ : syracuseStep 612407 = 918611) B918611
theorem B3102785 : Blo 610295 3102785 := bstep (se 2 (by rfl) ⟨1163544, by rfl⟩ : syracuseStep 3102785 = 2327089) B2327089
theorem B612427 : Blo 610295 612427 := bstep (se 1 (by rfl) ⟨459320, by rfl⟩ : syracuseStep 612427 = 918641) B918641
theorem B5036107 : Blo 610295 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B612439 : Blo 610295 612439 := bstep (se 1 (by rfl) ⟨459329, by rfl⟩ : syracuseStep 612439 = 918659) B918659
theorem B612459 : Blo 610295 612459 := bstep (se 1 (by rfl) ⟨459344, by rfl⟩ : syracuseStep 612459 = 918689) B918689
theorem B612471 : Blo 610295 612471 := bstep (se 1 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 612471 = 918707) B918707
theorem B612491 : Blo 610295 612491 := bstep (se 1 (by rfl) ⟨459368, by rfl⟩ : syracuseStep 612491 = 918737) B918737
theorem B612503 : Blo 610295 612503 := bstep (se 1 (by rfl) ⟨459377, by rfl⟩ : syracuseStep 612503 = 918755) B918755
theorem B612523 : Blo 610295 612523 := bstep (se 1 (by rfl) ⟨459392, by rfl⟩ : syracuseStep 612523 = 918785) B918785
theorem B612535 : Blo 610295 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B612555 : Blo 610295 612555 := bstep (se 1 (by rfl) ⟨459416, by rfl⟩ : syracuseStep 612555 = 918833) B918833
theorem B776395 : Blo 610295 776395 := bstep (se 1 (by rfl) ⟨582296, by rfl⟩ : syracuseStep 776395 = 1164593) B1164593
theorem B612567 : Blo 610295 612567 := bstep (se 1 (by rfl) ⟨459425, by rfl⟩ : syracuseStep 612567 = 918851) B918851
theorem B612587 : Blo 610295 612587 := bstep (se 1 (by rfl) ⟨459440, by rfl⟩ : syracuseStep 612587 = 918881) B918881
theorem B612599 : Blo 610295 612599 := bstep (se 1 (by rfl) ⟨459449, by rfl⟩ : syracuseStep 612599 = 918899) B918899
theorem B612619 : Blo 610295 612619 := bstep (se 1 (by rfl) ⟨459464, by rfl⟩ : syracuseStep 612619 = 918929) B918929
theorem B612631 : Blo 610295 612631 := bstep (se 1 (by rfl) ⟨459473, by rfl⟩ : syracuseStep 612631 = 918947) B918947
theorem B612651 : Blo 610295 612651 := bstep (se 1 (by rfl) ⟨459488, by rfl⟩ : syracuseStep 612651 = 918977) B918977
theorem B612663 : Blo 610295 612663 := bstep (se 1 (by rfl) ⟨459497, by rfl⟩ : syracuseStep 612663 = 918995) B918995
theorem B612683 : Blo 610295 612683 := bstep (se 1 (by rfl) ⟨459512, by rfl⟩ : syracuseStep 612683 = 919025) B919025
theorem B1890635 : Blo 610295 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B612695 : Blo 610295 612695 := bstep (se 1 (by rfl) ⟨459521, by rfl⟩ : syracuseStep 612695 = 919043) B919043
theorem B612715 : Blo 610295 612715 := bstep (se 1 (by rfl) ⟨459536, by rfl⟩ : syracuseStep 612715 = 919073) B919073
theorem B612727 : Blo 610295 612727 := bstep (se 1 (by rfl) ⟨459545, by rfl⟩ : syracuseStep 612727 = 919091) B919091
theorem B2939267 : Blo 610295 2939267 := bstep (se 1 (by rfl) ⟨2204450, by rfl⟩ : syracuseStep 2939267 = 4408901) B4408901
theorem B612747 : Blo 610295 612747 := bstep (se 1 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 612747 = 919121) B919121
theorem B612759 : Blo 610295 612759 := bstep (se 1 (by rfl) ⟨459569, by rfl⟩ : syracuseStep 612759 = 919139) B919139
theorem B612779 : Blo 610295 612779 := bstep (se 1 (by rfl) ⟨459584, by rfl⟩ : syracuseStep 612779 = 919169) B919169
theorem B612791 : Blo 610295 612791 := bstep (se 1 (by rfl) ⟨459593, by rfl⟩ : syracuseStep 612791 = 919187) B919187
theorem B612811 : Blo 610295 612811 := bstep (se 1 (by rfl) ⟨459608, by rfl⟩ : syracuseStep 612811 = 919217) B919217
theorem B4708813 : Blo 610295 4708813 := bstep (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) B1765805
theorem B612823 : Blo 610295 612823 := bstep (se 1 (by rfl) ⟨459617, by rfl⟩ : syracuseStep 612823 = 919235) B919235
theorem B2611673 : Blo 610295 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B612843 : Blo 610295 612843 := bstep (se 1 (by rfl) ⟨459632, by rfl⟩ : syracuseStep 612843 = 919265) B919265
theorem B612855 : Blo 610295 612855 := bstep (se 1 (by rfl) ⟨459641, by rfl⟩ : syracuseStep 612855 = 919283) B919283
theorem B612875 : Blo 610295 612875 := bstep (se 1 (by rfl) ⟨459656, by rfl⟩ : syracuseStep 612875 = 919313) B919313
theorem B612887 : Blo 610295 612887 := bstep (se 1 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 612887 = 919331) B919331
theorem B612907 : Blo 610295 612907 := bstep (se 1 (by rfl) ⟨459680, by rfl⟩ : syracuseStep 612907 = 919361) B919361
theorem B2611757 : Blo 610295 2611757 := bstep (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) B979409
theorem B612919 : Blo 610295 612919 := bstep (se 1 (by rfl) ⟨459689, by rfl⟩ : syracuseStep 612919 = 919379) B919379
theorem B612939 : Blo 610295 612939 := bstep (se 1 (by rfl) ⟨459704, by rfl⟩ : syracuseStep 612939 = 919409) B919409
theorem B612951 : Blo 610295 612951 := bstep (se 1 (by rfl) ⟨459713, by rfl⟩ : syracuseStep 612951 = 919427) B919427
theorem B612971 : Blo 610295 612971 := bstep (se 1 (by rfl) ⟨459728, by rfl⟩ : syracuseStep 612971 = 919457) B919457
theorem B612983 : Blo 610295 612983 := bstep (se 1 (by rfl) ⟨459737, by rfl⟩ : syracuseStep 612983 = 919475) B919475
theorem B613003 : Blo 610295 613003 := bstep (se 1 (by rfl) ⟨459752, by rfl⟩ : syracuseStep 613003 = 919505) B919505
theorem B613015 : Blo 610295 613015 := bstep (se 1 (by rfl) ⟨459761, by rfl⟩ : syracuseStep 613015 = 919523) B919523
theorem B613035 : Blo 610295 613035 := bstep (se 1 (by rfl) ⟨459776, by rfl⟩ : syracuseStep 613035 = 919553) B919553
theorem B613047 : Blo 610295 613047 := bstep (se 1 (by rfl) ⟨459785, by rfl⟩ : syracuseStep 613047 = 919571) B919571
theorem B613067 : Blo 610295 613067 := bstep (se 1 (by rfl) ⟨459800, by rfl⟩ : syracuseStep 613067 = 919601) B919601
theorem B613079 : Blo 610295 613079 := bstep (se 1 (by rfl) ⟨459809, by rfl⟩ : syracuseStep 613079 = 919619) B919619
theorem B613099 : Blo 610295 613099 := bstep (se 1 (by rfl) ⟨459824, by rfl⟩ : syracuseStep 613099 = 919649) B919649
theorem B613111 : Blo 610295 613111 := bstep (se 1 (by rfl) ⟨459833, by rfl⟩ : syracuseStep 613111 = 919667) B919667
theorem B613131 : Blo 610295 613131 := bstep (se 1 (by rfl) ⟨459848, by rfl⟩ : syracuseStep 613131 = 919697) B919697
theorem B613143 : Blo 610295 613143 := bstep (se 1 (by rfl) ⟨459857, by rfl⟩ : syracuseStep 613143 = 919715) B919715
theorem B613163 : Blo 610295 613163 := bstep (se 1 (by rfl) ⟨459872, by rfl⟩ : syracuseStep 613163 = 919745) B919745
theorem B613175 : Blo 610295 613175 := bstep (se 1 (by rfl) ⟨459881, by rfl⟩ : syracuseStep 613175 = 919763) B919763
theorem B613195 : Blo 610295 613195 := bstep (se 1 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 613195 = 919793) B919793
theorem B613207 : Blo 610295 613207 := bstep (se 1 (by rfl) ⟨459905, by rfl⟩ : syracuseStep 613207 = 919811) B919811
theorem B613227 : Blo 610295 613227 := bstep (se 1 (by rfl) ⟨459920, by rfl⟩ : syracuseStep 613227 = 919841) B919841
theorem B613239 : Blo 610295 613239 := bstep (se 1 (by rfl) ⟨459929, by rfl⟩ : syracuseStep 613239 = 919859) B919859
theorem B613259 : Blo 610295 613259 := bstep (se 1 (by rfl) ⟨459944, by rfl⟩ : syracuseStep 613259 = 919889) B919889
theorem B613271 : Blo 610295 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B613291 : Blo 610295 613291 := bstep (se 1 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 613291 = 919937) B919937
theorem B613303 : Blo 610295 613303 := bstep (se 1 (by rfl) ⟨459977, by rfl⟩ : syracuseStep 613303 = 919955) B919955
theorem B613323 : Blo 610295 613323 := bstep (se 1 (by rfl) ⟨459992, by rfl⟩ : syracuseStep 613323 = 919985) B919985
theorem B613335 : Blo 610295 613335 := bstep (se 1 (by rfl) ⟨460001, by rfl⟩ : syracuseStep 613335 = 920003) B920003
theorem B1104857 : Blo 610295 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B613355 : Blo 610295 613355 := bstep (se 1 (by rfl) ⟨460016, by rfl⟩ : syracuseStep 613355 = 920033) B920033
theorem B613367 : Blo 610295 613367 := bstep (se 1 (by rfl) ⟨460025, by rfl⟩ : syracuseStep 613367 = 920051) B920051
theorem B613387 : Blo 610295 613387 := bstep (se 1 (by rfl) ⟨460040, by rfl⟩ : syracuseStep 613387 = 920081) B920081
theorem B2939921 : Blo 610295 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B613399 : Blo 610295 613399 := bstep (se 1 (by rfl) ⟨460049, by rfl⟩ : syracuseStep 613399 = 920099) B920099
theorem B613419 : Blo 610295 613419 := bstep (se 1 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 613419 = 920129) B920129
theorem B613431 : Blo 610295 613431 := bstep (se 1 (by rfl) ⟨460073, by rfl⟩ : syracuseStep 613431 = 920147) B920147
theorem B613451 : Blo 610295 613451 := bstep (se 1 (by rfl) ⟨460088, by rfl⟩ : syracuseStep 613451 = 920177) B920177
theorem B613463 : Blo 610295 613463 := bstep (se 1 (by rfl) ⟨460097, by rfl⟩ : syracuseStep 613463 = 920195) B920195
theorem B613483 : Blo 610295 613483 := bstep (se 1 (by rfl) ⟨460112, by rfl⟩ : syracuseStep 613483 = 920225) B920225
theorem B613495 : Blo 610295 613495 := bstep (se 1 (by rfl) ⟨460121, by rfl⟩ : syracuseStep 613495 = 920243) B920243
theorem B613515 : Blo 610295 613515 := bstep (se 1 (by rfl) ⟨460136, by rfl⟩ : syracuseStep 613515 = 920273) B920273
theorem B613527 : Blo 610295 613527 := bstep (se 1 (by rfl) ⟨460145, by rfl⟩ : syracuseStep 613527 = 920291) B920291
theorem B777367 : Blo 610295 777367 := bstep (se 1 (by rfl) ⟨583025, by rfl⟩ : syracuseStep 777367 = 1166051) B1166051
theorem B613547 : Blo 610295 613547 := bstep (se 1 (by rfl) ⟨460160, by rfl⟩ : syracuseStep 613547 = 920321) B920321
theorem B613559 : Blo 610295 613559 := bstep (se 1 (by rfl) ⟨460169, by rfl⟩ : syracuseStep 613559 = 920339) B920339
theorem B613579 : Blo 610295 613579 := bstep (se 1 (by rfl) ⟨460184, by rfl⟩ : syracuseStep 613579 = 920369) B920369
theorem B613591 : Blo 610295 613591 := bstep (se 1 (by rfl) ⟨460193, by rfl⟩ : syracuseStep 613591 = 920387) B920387
theorem B613611 : Blo 610295 613611 := bstep (se 1 (by rfl) ⟨460208, by rfl⟩ : syracuseStep 613611 = 920417) B920417
theorem B613623 : Blo 610295 613623 := bstep (se 1 (by rfl) ⟨460217, by rfl⟩ : syracuseStep 613623 = 920435) B920435
theorem B613643 : Blo 610295 613643 := bstep (se 1 (by rfl) ⟨460232, by rfl⟩ : syracuseStep 613643 = 920465) B920465
theorem B613655 : Blo 610295 613655 := bstep (se 1 (by rfl) ⟨460241, by rfl⟩ : syracuseStep 613655 = 920483) B920483
theorem B613675 : Blo 610295 613675 := bstep (se 1 (by rfl) ⟨460256, by rfl⟩ : syracuseStep 613675 = 920513) B920513
theorem B613687 : Blo 610295 613687 := bstep (se 1 (by rfl) ⟨460265, by rfl⟩ : syracuseStep 613687 = 920531) B920531
theorem B2317643 : Blo 610295 2317643 := bstep (se 1 (by rfl) ⟨1738232, by rfl⟩ : syracuseStep 2317643 = 3476465) B3476465
theorem B613707 : Blo 610295 613707 := bstep (se 1 (by rfl) ⟨460280, by rfl⟩ : syracuseStep 613707 = 920561) B920561
theorem B613719 : Blo 610295 613719 := bstep (se 1 (by rfl) ⟨460289, by rfl⟩ : syracuseStep 613719 = 920579) B920579
theorem B5954917 : Blo 610295 5954917 := bstep (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) B1116547
theorem B613739 : Blo 610295 613739 := bstep (se 1 (by rfl) ⟨460304, by rfl⟩ : syracuseStep 613739 = 920609) B920609
theorem B1105267 : Blo 610295 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B613751 : Blo 610295 613751 := bstep (se 1 (by rfl) ⟨460313, by rfl⟩ : syracuseStep 613751 = 920627) B920627
theorem B613771 : Blo 610295 613771 := bstep (se 1 (by rfl) ⟨460328, by rfl⟩ : syracuseStep 613771 = 920657) B920657
theorem B613783 : Blo 610295 613783 := bstep (se 1 (by rfl) ⟨460337, by rfl⟩ : syracuseStep 613783 = 920675) B920675
theorem B613803 : Blo 610295 613803 := bstep (se 1 (by rfl) ⟨460352, by rfl⟩ : syracuseStep 613803 = 920705) B920705
theorem B613815 : Blo 610295 613815 := bstep (se 1 (by rfl) ⟨460361, by rfl⟩ : syracuseStep 613815 = 920723) B920723
theorem B613835 : Blo 610295 613835 := bstep (se 1 (by rfl) ⟨460376, by rfl⟩ : syracuseStep 613835 = 920753) B920753
theorem B613847 : Blo 610295 613847 := bstep (se 1 (by rfl) ⟨460385, by rfl⟩ : syracuseStep 613847 = 920771) B920771
theorem B613867 : Blo 610295 613867 := bstep (se 1 (by rfl) ⟨460400, by rfl⟩ : syracuseStep 613867 = 920801) B920801
theorem B613879 : Blo 610295 613879 := bstep (se 1 (by rfl) ⟨460409, by rfl⟩ : syracuseStep 613879 = 920819) B920819
theorem B613899 : Blo 610295 613899 := bstep (se 1 (by rfl) ⟨460424, by rfl⟩ : syracuseStep 613899 = 920849) B920849
theorem B2317841 : Blo 610295 2317841 := bstep (se 2 (by rfl) ⟨869190, by rfl⟩ : syracuseStep 2317841 = 1738381) B1738381
theorem B613911 : Blo 610295 613911 := bstep (se 1 (by rfl) ⟨460433, by rfl⟩ : syracuseStep 613911 = 920867) B920867
theorem B613931 : Blo 610295 613931 := bstep (se 1 (by rfl) ⟨460448, by rfl⟩ : syracuseStep 613931 = 920897) B920897
theorem B613943 : Blo 610295 613943 := bstep (se 1 (by rfl) ⟨460457, by rfl⟩ : syracuseStep 613943 = 920915) B920915
theorem B613963 : Blo 610295 613963 := bstep (se 1 (by rfl) ⟨460472, by rfl⟩ : syracuseStep 613963 = 920945) B920945
theorem B613975 : Blo 610295 613975 := bstep (se 1 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 613975 = 920963) B920963
theorem B7462493 : Blo 610295 7462493 := bstep (se 3 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 7462493 = 2798435) B2798435
theorem B613995 : Blo 610295 613995 := bstep (se 1 (by rfl) ⟨460496, by rfl⟩ : syracuseStep 613995 = 920993) B920993
theorem B614007 : Blo 610295 614007 := bstep (se 1 (by rfl) ⟨460505, by rfl⟩ : syracuseStep 614007 = 921011) B921011
theorem B614027 : Blo 610295 614027 := bstep (se 1 (by rfl) ⟨460520, by rfl⟩ : syracuseStep 614027 = 921041) B921041
theorem B614039 : Blo 610295 614039 := bstep (se 1 (by rfl) ⟨460529, by rfl⟩ : syracuseStep 614039 = 921059) B921059
theorem B614059 : Blo 610295 614059 := bstep (se 1 (by rfl) ⟨460544, by rfl⟩ : syracuseStep 614059 = 921089) B921089
theorem B3497651 : Blo 610295 3497651 := bstep (se 1 (by rfl) ⟨2623238, by rfl⟩ : syracuseStep 3497651 = 5246477) B5246477
theorem B614071 : Blo 610295 614071 := bstep (se 1 (by rfl) ⟨460553, by rfl⟩ : syracuseStep 614071 = 921107) B921107
theorem B614091 : Blo 610295 614091 := bstep (se 1 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 614091 = 921137) B921137
theorem B5234381 : Blo 610295 5234381 := bstep (se 3 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 5234381 = 1962893) B1962893
theorem B614103 : Blo 610295 614103 := bstep (se 1 (by rfl) ⟨460577, by rfl⟩ : syracuseStep 614103 = 921155) B921155
theorem B614123 : Blo 610295 614123 := bstep (se 1 (by rfl) ⟨460592, by rfl⟩ : syracuseStep 614123 = 921185) B921185
theorem B614135 : Blo 610295 614135 := bstep (se 1 (by rfl) ⟨460601, by rfl⟩ : syracuseStep 614135 = 921203) B921203
theorem B614155 : Blo 610295 614155 := bstep (se 1 (by rfl) ⟨460616, by rfl⟩ : syracuseStep 614155 = 921233) B921233
theorem B614167 : Blo 610295 614167 := bstep (se 1 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 614167 = 921251) B921251
theorem B614187 : Blo 610295 614187 := bstep (se 1 (by rfl) ⟨460640, by rfl⟩ : syracuseStep 614187 = 921281) B921281
theorem B614199 : Blo 610295 614199 := bstep (se 1 (by rfl) ⟨460649, by rfl⟩ : syracuseStep 614199 = 921299) B921299
theorem B614219 : Blo 610295 614219 := bstep (se 1 (by rfl) ⟨460664, by rfl⟩ : syracuseStep 614219 = 921329) B921329
theorem B614231 : Blo 610295 614231 := bstep (se 1 (by rfl) ⟨460673, by rfl⟩ : syracuseStep 614231 = 921347) B921347
theorem B4644701 : Blo 610295 4644701 := bstep (se 3 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 4644701 = 1741763) B1741763
theorem B614251 : Blo 610295 614251 := bstep (se 1 (by rfl) ⟨460688, by rfl⟩ : syracuseStep 614251 = 921377) B921377
theorem B614263 : Blo 610295 614263 := bstep (se 1 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 614263 = 921395) B921395
theorem B614283 : Blo 610295 614283 := bstep (se 1 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 614283 = 921425) B921425
theorem B614295 : Blo 610295 614295 := bstep (se 1 (by rfl) ⟨460721, by rfl⟩ : syracuseStep 614295 = 921443) B921443
theorem B3104729 : Blo 610295 3104729 := bstep (se 2 (by rfl) ⟨1164273, by rfl⟩ : syracuseStep 3104729 = 2328547) B2328547
theorem B1400971 : Blo 610295 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B2318615 : Blo 610295 2318615 := bstep (se 1 (by rfl) ⟨1738961, by rfl⟩ : syracuseStep 2318615 = 3477923) B3477923
theorem B5038541 : Blo 610295 5038541 := bstep (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) B1889453
theorem B2318813 : Blo 610295 2318813 := bstep (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) B869555
theorem B8479667 : Blo 610295 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B1303897 : Blo 610295 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B1795421 : Blo 610295 1795421 := bstep (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) B673283
theorem B3106349 : Blo 610295 3106349 := bstep (se 3 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 3106349 = 1164881) B1164881
theorem B2483801 : Blo 610295 2483801 := bstep (se 2 (by rfl) ⟨931425, by rfl⟩ : syracuseStep 2483801 = 1862851) B1862851
theorem B1861271 : Blo 610295 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B3139373 : Blo 610295 3139373 := bstep (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) B1177265
theorem B2615105 : Blo 610295 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B5236771 : Blo 610295 5236771 := bstep (se 1 (by rfl) ⟨3927578, by rfl⟩ : syracuseStep 5236771 = 7855157) B7855157
theorem B2320771 : Blo 610295 2320771 := bstep (se 1 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 2320771 = 3481157) B3481157
theorem B2615773 : Blo 610295 2615773 := bstep (se 3 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 2615773 = 980915) B980915
theorem B1436161 : Blo 610295 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B2321075 : Blo 610295 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B1469249 : Blo 610295 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B167668697 : Blo 610295 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B6286297 : Blo 610295 6286297 := bstep (se 2 (by rfl) ⟨2357361, by rfl⟩ : syracuseStep 6286297 = 4714723) B4714723
theorem B2616371 : Blo 610295 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B2321729 : Blo 610295 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B1306049 : Blo 610295 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B978455 : Blo 610295 978455 := bstep (se 1 (by rfl) ⟨733841, by rfl⟩ : syracuseStep 978455 = 1467683) B1467683
theorem B1306135 : Blo 610295 1306135 := bstep (se 1 (by rfl) ⟨979601, by rfl⟩ : syracuseStep 1306135 = 1959203) B1959203
theorem B4419107 : Blo 610295 4419107 := bstep (se 1 (by rfl) ⟨3314330, by rfl⟩ : syracuseStep 4419107 = 6628661) B6628661
theorem B3305053 : Blo 610295 3305053 := bstep (se 3 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 3305053 = 1239395) B1239395
theorem B1175233 : Blo 610295 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B1044427 : Blo 610295 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B1961945 : Blo 610295 1961945 := bstep (se 2 (by rfl) ⟨735729, by rfl⟩ : syracuseStep 1961945 = 1471459) B1471459
theorem B1962073 : Blo 610295 1962073 := bstep (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) B1471555
theorem B3174551 : Blo 610295 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B14151941 : Blo 610295 14151941 := bstep (se 4 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 14151941 = 2653489) B2653489
theorem B1306955 : Blo 610295 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B33616241 : Blo 610295 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B2060747 : Blo 610295 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B2322989 : Blo 610295 2322989 := bstep (se 3 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 2322989 = 871121) B871121
theorem B2323019 : Blo 610295 2323019 := bstep (se 1 (by rfl) ⟨1742264, by rfl⟩ : syracuseStep 2323019 = 3484529) B3484529
theorem B1045145 : Blo 610295 1045145 := bstep (se 2 (by rfl) ⟨391929, by rfl⟩ : syracuseStep 1045145 = 783859) B783859
theorem B2061017 : Blo 610295 2061017 := bstep (se 2 (by rfl) ⟨772881, by rfl⟩ : syracuseStep 2061017 = 1545763) B1545763
theorem B1471297 : Blo 610295 1471297 := bstep (se 2 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 1471297 = 1103473) B1103473
theorem B6976529 : Blo 610295 6976529 := bstep (se 2 (by rfl) ⟨2616198, by rfl⟩ : syracuseStep 6976529 = 5232397) B5232397
theorem B1373273 : Blo 610295 1373273 := bstep (se 2 (by rfl) ⟨514977, by rfl⟩ : syracuseStep 1373273 = 1029955) B1029955
theorem B3929219 : Blo 610295 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B1373363 : Blo 610295 1373363 := bstep (se 1 (by rfl) ⟨1030022, by rfl⟩ : syracuseStep 1373363 = 2060045) B2060045
theorem B3732659 : Blo 610295 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B1373399 : Blo 610295 1373399 := bstep (se 1 (by rfl) ⟨1030049, by rfl⟩ : syracuseStep 1373399 = 2060099) B2060099
theorem B2323673 : Blo 610295 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B1307929 : Blo 610295 1307929 := bstep (se 2 (by rfl) ⟨490473, by rfl⟩ : syracuseStep 1307929 = 980947) B980947
theorem B619831 : Blo 610295 619831 := bstep (se 1 (by rfl) ⟨464873, by rfl⟩ : syracuseStep 619831 = 929747) B929747
theorem B1373579 : Blo 610295 1373579 := bstep (se 1 (by rfl) ⟨1030184, by rfl⟩ : syracuseStep 1373579 = 2060369) B2060369
theorem B2061719 : Blo 610295 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B2946455 : Blo 610295 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B7828913 : Blo 610295 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B1373633 : Blo 610295 1373633 := bstep (se 2 (by rfl) ⟨515112, by rfl⟩ : syracuseStep 1373633 = 1030225) B1030225
theorem B2323991 : Blo 610295 2323991 := bstep (se 1 (by rfl) ⟨1742993, by rfl⟩ : syracuseStep 2323991 = 3485987) B3485987
theorem B2651741 : Blo 610295 2651741 := bstep (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) B994403
theorem B1373849 : Blo 610295 1373849 := bstep (se 2 (by rfl) ⟨515193, by rfl⟩ : syracuseStep 1373849 = 1030387) B1030387
theorem B1373939 : Blo 610295 1373939 := bstep (se 1 (by rfl) ⟨1030454, by rfl⟩ : syracuseStep 1373939 = 2060909) B2060909
theorem B1373975 : Blo 610295 1373975 := bstep (se 1 (by rfl) ⟨1030481, by rfl⟩ : syracuseStep 1373975 = 2060963) B2060963
theorem B2062259 : Blo 610295 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B1374155 : Blo 610295 1374155 := bstep (se 1 (by rfl) ⟨1030616, by rfl⟩ : syracuseStep 1374155 = 2061233) B2061233
theorem B1374209 : Blo 610295 1374209 := bstep (se 2 (by rfl) ⟨515328, by rfl⟩ : syracuseStep 1374209 = 1030657) B1030657
theorem B915467 : Blo 610295 915467 := bstep (se 1 (by rfl) ⟨686600, by rfl⟩ : syracuseStep 915467 = 1373201) B1373201
theorem B915479 : Blo 610295 915479 := bstep (se 1 (by rfl) ⟨686609, by rfl⟩ : syracuseStep 915479 = 1373219) B1373219
theorem B915545 : Blo 610295 915545 := bstep (se 2 (by rfl) ⟨343329, by rfl⟩ : syracuseStep 915545 = 686659) B686659
theorem B2324659 : Blo 610295 2324659 := bstep (se 1 (by rfl) ⟨1743494, by rfl⟩ : syracuseStep 2324659 = 3486989) B3486989
theorem B2062529 : Blo 610295 2062529 := bstep (se 2 (by rfl) ⟨773448, by rfl⟩ : syracuseStep 2062529 = 1546897) B1546897
theorem B915659 : Blo 610295 915659 := bstep (se 1 (by rfl) ⟨686744, by rfl⟩ : syracuseStep 915659 = 1373489) B1373489
theorem B915671 : Blo 610295 915671 := bstep (se 1 (by rfl) ⟨686753, by rfl⟩ : syracuseStep 915671 = 1373507) B1373507
theorem B1374425 : Blo 610295 1374425 := bstep (se 2 (by rfl) ⟨515409, by rfl⟩ : syracuseStep 1374425 = 1030819) B1030819
theorem B915737 : Blo 610295 915737 := bstep (se 2 (by rfl) ⟨343401, by rfl⟩ : syracuseStep 915737 = 686803) B686803
theorem B11794733 : Blo 610295 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B1374515 : Blo 610295 1374515 := bstep (se 1 (by rfl) ⟨1030886, by rfl⟩ : syracuseStep 1374515 = 2061773) B2061773
theorem B1374551 : Blo 610295 1374551 := bstep (se 1 (by rfl) ⟨1030913, by rfl⟩ : syracuseStep 1374551 = 2061827) B2061827
theorem B915851 : Blo 610295 915851 := bstep (se 1 (by rfl) ⟨686888, by rfl⟩ : syracuseStep 915851 = 1373777) B1373777
theorem B915863 : Blo 610295 915863 := bstep (se 1 (by rfl) ⟨686897, by rfl⟩ : syracuseStep 915863 = 1373795) B1373795
theorem B915929 : Blo 610295 915929 := bstep (se 2 (by rfl) ⟨343473, by rfl⟩ : syracuseStep 915929 = 686947) B686947
theorem B1374731 : Blo 610295 1374731 := bstep (se 1 (by rfl) ⟨1031048, by rfl⟩ : syracuseStep 1374731 = 2062097) B2062097
theorem B653879 : Blo 610295 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B1374785 : Blo 610295 1374785 := bstep (se 2 (by rfl) ⟨515544, by rfl⟩ : syracuseStep 1374785 = 1031089) B1031089
theorem B916043 : Blo 610295 916043 := bstep (se 1 (by rfl) ⟨687032, by rfl⟩ : syracuseStep 916043 = 1374065) B1374065
theorem B5241419 : Blo 610295 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B916055 : Blo 610295 916055 := bstep (se 1 (by rfl) ⟨687041, by rfl⟩ : syracuseStep 916055 = 1374083) B1374083
theorem B686731 : Blo 610295 686731 := bstep (se 1 (by rfl) ⟨515048, by rfl⟩ : syracuseStep 686731 = 1030097) B1030097
theorem B916121 : Blo 610295 916121 := bstep (se 2 (by rfl) ⟨343545, by rfl⟩ : syracuseStep 916121 = 687091) B687091
theorem B2063069 : Blo 610295 2063069 := bstep (se 3 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 2063069 = 773651) B773651
theorem B2357981 : Blo 610295 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B686839 : Blo 610295 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B2620163 : Blo 610295 2620163 := bstep (se 1 (by rfl) ⟨1965122, by rfl⟩ : syracuseStep 2620163 = 3930245) B3930245
theorem B916235 : Blo 610295 916235 := bstep (se 1 (by rfl) ⟨687176, by rfl⟩ : syracuseStep 916235 = 1374353) B1374353
theorem B916247 : Blo 610295 916247 := bstep (se 1 (by rfl) ⟨687185, by rfl⟩ : syracuseStep 916247 = 1374371) B1374371
theorem B1375001 : Blo 610295 1375001 := bstep (se 2 (by rfl) ⟨515625, by rfl⟩ : syracuseStep 1375001 = 1031251) B1031251
theorem B916313 : Blo 610295 916313 := bstep (se 2 (by rfl) ⟨343617, by rfl⟩ : syracuseStep 916313 = 687235) B687235
theorem B1375091 : Blo 610295 1375091 := bstep (se 1 (by rfl) ⟨1031318, by rfl⟩ : syracuseStep 1375091 = 2062637) B2062637
theorem B1375127 : Blo 610295 1375127 := bstep (se 1 (by rfl) ⟨1031345, by rfl⟩ : syracuseStep 1375127 = 2062691) B2062691
theorem B687019 : Blo 610295 687019 := bstep (se 1 (by rfl) ⟨515264, by rfl⟩ : syracuseStep 687019 = 1030529) B1030529
theorem B916427 : Blo 610295 916427 := bstep (se 1 (by rfl) ⟨687320, by rfl⟩ : syracuseStep 916427 = 1374641) B1374641
theorem B1244107 : Blo 610295 1244107 := bstep (se 1 (by rfl) ⟨933080, by rfl⟩ : syracuseStep 1244107 = 1866161) B1866161
theorem B916439 : Blo 610295 916439 := bstep (se 1 (by rfl) ⟨687329, by rfl⟩ : syracuseStep 916439 = 1374659) B1374659
theorem B687127 : Blo 610295 687127 := bstep (se 1 (by rfl) ⟨515345, by rfl⟩ : syracuseStep 687127 = 1030691) B1030691
theorem B916505 : Blo 610295 916505 := bstep (se 2 (by rfl) ⟨343689, by rfl⟩ : syracuseStep 916505 = 687379) B687379
theorem B1375307 : Blo 610295 1375307 := bstep (se 1 (by rfl) ⟨1031480, by rfl⟩ : syracuseStep 1375307 = 2062961) B2062961
theorem B1473611 : Blo 610295 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B2620505 : Blo 610295 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B1375361 : Blo 610295 1375361 := bstep (se 2 (by rfl) ⟨515760, by rfl⟩ : syracuseStep 1375361 = 1031521) B1031521
theorem B916619 : Blo 610295 916619 := bstep (se 1 (by rfl) ⟨687464, by rfl⟩ : syracuseStep 916619 = 1374929) B1374929
theorem B916631 : Blo 610295 916631 := bstep (se 1 (by rfl) ⟨687473, by rfl⟩ : syracuseStep 916631 = 1374947) B1374947
theorem B687307 : Blo 610295 687307 := bstep (se 1 (by rfl) ⟨515480, by rfl⟩ : syracuseStep 687307 = 1030961) B1030961
theorem B916697 : Blo 610295 916697 := bstep (se 2 (by rfl) ⟨343761, by rfl⟩ : syracuseStep 916697 = 687523) B687523
theorem B654571 : Blo 610295 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B1178867 : Blo 610295 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B687415 : Blo 610295 687415 := bstep (se 1 (by rfl) ⟨515561, by rfl⟩ : syracuseStep 687415 = 1031123) B1031123
theorem B916811 : Blo 610295 916811 := bstep (se 1 (by rfl) ⟨687608, by rfl⟩ : syracuseStep 916811 = 1375217) B1375217
theorem B916823 : Blo 610295 916823 := bstep (se 1 (by rfl) ⟨687617, by rfl⟩ : syracuseStep 916823 = 1375235) B1375235
theorem B1375577 : Blo 610295 1375577 := bstep (se 2 (by rfl) ⟨515841, by rfl⟩ : syracuseStep 1375577 = 1031683) B1031683
theorem B2325905 : Blo 610295 2325905 := bstep (se 2 (by rfl) ⟨872214, by rfl⟩ : syracuseStep 2325905 = 1744429) B1744429
theorem B916889 : Blo 610295 916889 := bstep (se 2 (by rfl) ⟨343833, by rfl⟩ : syracuseStep 916889 = 687667) B687667
theorem B1375667 : Blo 610295 1375667 := bstep (se 1 (by rfl) ⟨1031750, by rfl⟩ : syracuseStep 1375667 = 2063501) B2063501
theorem B1375703 : Blo 610295 1375703 := bstep (se 1 (by rfl) ⟨1031777, by rfl⟩ : syracuseStep 1375703 = 2063555) B2063555
theorem B687595 : Blo 610295 687595 := bstep (se 1 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 687595 = 1031393) B1031393
theorem B917003 : Blo 610295 917003 := bstep (se 1 (by rfl) ⟨687752, by rfl⟩ : syracuseStep 917003 = 1375505) B1375505
theorem B917015 : Blo 610295 917015 := bstep (se 1 (by rfl) ⟨687761, by rfl⟩ : syracuseStep 917015 = 1375523) B1375523
theorem B687703 : Blo 610295 687703 := bstep (se 1 (by rfl) ⟨515777, by rfl⟩ : syracuseStep 687703 = 1031555) B1031555
theorem B917081 : Blo 610295 917081 := bstep (se 2 (by rfl) ⟨343905, by rfl⟩ : syracuseStep 917081 = 687811) B687811
theorem B1375883 : Blo 610295 1375883 := bstep (se 1 (by rfl) ⟨1031912, by rfl⟩ : syracuseStep 1375883 = 2063825) B2063825
theorem B1310347 : Blo 610295 1310347 := bstep (se 1 (by rfl) ⟨982760, by rfl⟩ : syracuseStep 1310347 = 1965521) B1965521
theorem B1375937 : Blo 610295 1375937 := bstep (se 2 (by rfl) ⟨515976, by rfl⟩ : syracuseStep 1375937 = 1031953) B1031953
theorem B917195 : Blo 610295 917195 := bstep (se 1 (by rfl) ⟨687896, by rfl⟩ : syracuseStep 917195 = 1375793) B1375793
theorem B917207 : Blo 610295 917207 := bstep (se 1 (by rfl) ⟨687905, by rfl⟩ : syracuseStep 917207 = 1375811) B1375811
theorem B1310423 : Blo 610295 1310423 := bstep (se 1 (by rfl) ⟨982817, by rfl⟩ : syracuseStep 1310423 = 1965635) B1965635
theorem B687883 : Blo 610295 687883 := bstep (se 1 (by rfl) ⟨515912, by rfl⟩ : syracuseStep 687883 = 1031825) B1031825
theorem B917273 : Blo 610295 917273 := bstep (se 2 (by rfl) ⟨343977, by rfl⟩ : syracuseStep 917273 = 687955) B687955
theorem B2064203 : Blo 610295 2064203 := bstep (se 1 (by rfl) ⟨1548152, by rfl⟩ : syracuseStep 2064203 = 3096305) B3096305
theorem B6979445 : Blo 610295 6979445 := bstep (se 5 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 6979445 = 654323) B654323
theorem B687991 : Blo 610295 687991 := bstep (se 1 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 687991 = 1031987) B1031987
theorem B917387 : Blo 610295 917387 := bstep (se 1 (by rfl) ⟨688040, by rfl⟩ : syracuseStep 917387 = 1376081) B1376081
theorem B917399 : Blo 610295 917399 := bstep (se 1 (by rfl) ⟨688049, by rfl⟩ : syracuseStep 917399 = 1376099) B1376099
theorem B1376153 : Blo 610295 1376153 := bstep (se 2 (by rfl) ⟨516057, by rfl⟩ : syracuseStep 1376153 = 1032115) B1032115
theorem B917465 : Blo 610295 917465 := bstep (se 2 (by rfl) ⟨344049, by rfl⟩ : syracuseStep 917465 = 688099) B688099
theorem B1966045 : Blo 610295 1966045 := bstep (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) B737267
theorem B1376243 : Blo 610295 1376243 := bstep (se 1 (by rfl) ⟨1032182, by rfl⟩ : syracuseStep 1376243 = 2064365) B2064365
theorem B688135 : Blo 610295 688135 := bstep (se 1 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 688135 = 1032203) B1032203
theorem B917519 : Blo 610295 917519 := bstep (se 1 (by rfl) ⟨688139, by rfl⟩ : syracuseStep 917519 = 1376279) B1376279
theorem B917561 : Blo 610295 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B1376315 : Blo 610295 1376315 := bstep (se 1 (by rfl) ⟨1032236, by rfl⟩ : syracuseStep 1376315 = 2064473) B2064473
theorem B2326589 : Blo 610295 2326589 := bstep (se 3 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 2326589 = 872471) B872471
theorem B917639 : Blo 610295 917639 := bstep (se 1 (by rfl) ⟨688229, by rfl⟩ : syracuseStep 917639 = 1376459) B1376459
theorem B917675 : Blo 610295 917675 := bstep (se 1 (by rfl) ⟨688256, by rfl⟩ : syracuseStep 917675 = 1376513) B1376513
theorem B1376441 : Blo 610295 1376441 := bstep (se 2 (by rfl) ⟨516165, by rfl⟩ : syracuseStep 1376441 = 1032331) B1032331
theorem B688315 : Blo 610295 688315 := bstep (se 1 (by rfl) ⟨516236, by rfl⟩ : syracuseStep 688315 = 1032473) B1032473
theorem B1867961 : Blo 610295 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B917705 : Blo 610295 917705 := bstep (se 2 (by rfl) ⟨344139, by rfl⟩ : syracuseStep 917705 = 688279) B688279
theorem B917819 : Blo 610295 917819 := bstep (se 1 (by rfl) ⟨688364, by rfl⟩ : syracuseStep 917819 = 1376729) B1376729
theorem B917879 : Blo 610295 917879 := bstep (se 1 (by rfl) ⟨688409, by rfl⟩ : syracuseStep 917879 = 1376819) B1376819
theorem B917903 : Blo 610295 917903 := bstep (se 1 (by rfl) ⟨688427, by rfl⟩ : syracuseStep 917903 = 1376855) B1376855
theorem B2949529 : Blo 610295 2949529 := bstep (se 2 (by rfl) ⟨1106073, by rfl⟩ : syracuseStep 2949529 = 2212147) B2212147
theorem B917945 : Blo 610295 917945 := bstep (se 2 (by rfl) ⟨344229, by rfl⟩ : syracuseStep 917945 = 688459) B688459
theorem B983497 : Blo 610295 983497 := bstep (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) B737623
theorem B918023 : Blo 610295 918023 := bstep (se 1 (by rfl) ⟨688517, by rfl⟩ : syracuseStep 918023 = 1377035) B1377035
theorem B3310091 : Blo 610295 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B1376783 : Blo 610295 1376783 := bstep (se 1 (by rfl) ⟨1032587, by rfl⟩ : syracuseStep 1376783 = 2065175) B2065175
theorem B1376801 : Blo 610295 1376801 := bstep (se 2 (by rfl) ⟨516300, by rfl⟩ : syracuseStep 1376801 = 1032601) B1032601
theorem B918059 : Blo 610295 918059 := bstep (se 1 (by rfl) ⟨688544, by rfl⟩ : syracuseStep 918059 = 1377089) B1377089
theorem B918089 : Blo 610295 918089 := bstep (se 2 (by rfl) ⟨344283, by rfl⟩ : syracuseStep 918089 = 688567) B688567
theorem B688783 : Blo 610295 688783 := bstep (se 1 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 688783 = 1033175) B1033175
theorem B918203 : Blo 610295 918203 := bstep (se 1 (by rfl) ⟨688652, by rfl⟩ : syracuseStep 918203 = 1377305) B1377305
theorem B918263 : Blo 610295 918263 := bstep (se 1 (by rfl) ⟨688697, by rfl⟩ : syracuseStep 918263 = 1377395) B1377395
theorem B918287 : Blo 610295 918287 := bstep (se 1 (by rfl) ⟨688715, by rfl⟩ : syracuseStep 918287 = 1377431) B1377431
theorem B1475371 : Blo 610295 1475371 := bstep (se 1 (by rfl) ⟨1106528, by rfl⟩ : syracuseStep 1475371 = 2213057) B2213057
theorem B918329 : Blo 610295 918329 := bstep (se 2 (by rfl) ⟨344373, by rfl⟩ : syracuseStep 918329 = 688747) B688747
theorem B1377143 : Blo 610295 1377143 := bstep (se 1 (by rfl) ⟨1032857, by rfl⟩ : syracuseStep 1377143 = 2065715) B2065715
theorem B918407 : Blo 610295 918407 := bstep (se 1 (by rfl) ⟨688805, by rfl⟩ : syracuseStep 918407 = 1377611) B1377611
theorem B918443 : Blo 610295 918443 := bstep (se 1 (by rfl) ⟨688832, by rfl⟩ : syracuseStep 918443 = 1377665) B1377665
theorem B2065337 : Blo 610295 2065337 := bstep (se 2 (by rfl) ⟨774501, by rfl⟩ : syracuseStep 2065337 = 1549003) B1549003
theorem B918473 : Blo 610295 918473 := bstep (se 2 (by rfl) ⟨344427, by rfl⟩ : syracuseStep 918473 = 688855) B688855
theorem B1377323 : Blo 610295 1377323 := bstep (se 1 (by rfl) ⟨1032992, by rfl⟩ : syracuseStep 1377323 = 2065985) B2065985
theorem B37815349 : Blo 610295 37815349 := bstep (se 5 (by rfl) ⟨1772594, by rfl⟩ : syracuseStep 37815349 = 3545189) B3545189
theorem B918587 : Blo 610295 918587 := bstep (se 1 (by rfl) ⟨688940, by rfl⟩ : syracuseStep 918587 = 1377881) B1377881
theorem B24249419 : Blo 610295 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B1115255 : Blo 610295 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B918647 : Blo 610295 918647 := bstep (se 1 (by rfl) ⟨688985, by rfl⟩ : syracuseStep 918647 = 1377971) B1377971
theorem B689287 : Blo 610295 689287 := bstep (se 1 (by rfl) ⟨516965, by rfl⟩ : syracuseStep 689287 = 1033931) B1033931
theorem B918671 : Blo 610295 918671 := bstep (se 1 (by rfl) ⟨689003, by rfl⟩ : syracuseStep 918671 = 1378007) B1378007
theorem B918713 : Blo 610295 918713 := bstep (se 2 (by rfl) ⟨344517, by rfl⟩ : syracuseStep 918713 = 689035) B689035
theorem B918791 : Blo 610295 918791 := bstep (se 1 (by rfl) ⟨689093, by rfl⟩ : syracuseStep 918791 = 1378187) B1378187
theorem B1738027 : Blo 610295 1738027 := bstep (se 1 (by rfl) ⟨1303520, by rfl⟩ : syracuseStep 1738027 = 2607041) B2607041
theorem B918827 : Blo 610295 918827 := bstep (se 1 (by rfl) ⟨689120, by rfl⟩ : syracuseStep 918827 = 1378241) B1378241
theorem B689467 : Blo 610295 689467 := bstep (se 1 (by rfl) ⟨517100, by rfl⟩ : syracuseStep 689467 = 1034201) B1034201
theorem B918857 : Blo 610295 918857 := bstep (se 2 (by rfl) ⟨344571, by rfl⟩ : syracuseStep 918857 = 689143) B689143
theorem B6292829 : Blo 610295 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B1377683 : Blo 610295 1377683 := bstep (se 1 (by rfl) ⟨1033262, by rfl⟩ : syracuseStep 1377683 = 2066525) B2066525
theorem B12387761 : Blo 610295 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B918971 : Blo 610295 918971 := bstep (se 1 (by rfl) ⟨689228, by rfl⟩ : syracuseStep 918971 = 1378457) B1378457
theorem B1377737 : Blo 610295 1377737 := bstep (se 2 (by rfl) ⟨516651, by rfl⟩ : syracuseStep 1377737 = 1033303) B1033303
theorem B919031 : Blo 610295 919031 := bstep (se 1 (by rfl) ⟨689273, by rfl⟩ : syracuseStep 919031 = 1378547) B1378547
theorem B2065931 : Blo 610295 2065931 := bstep (se 1 (by rfl) ⟨1549448, by rfl⟩ : syracuseStep 2065931 = 3098897) B3098897
theorem B1738255 : Blo 610295 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B919055 : Blo 610295 919055 := bstep (se 1 (by rfl) ⟨689291, by rfl⟩ : syracuseStep 919055 = 1378583) B1378583
theorem B919097 : Blo 610295 919097 := bstep (se 2 (by rfl) ⟨344661, by rfl⟩ : syracuseStep 919097 = 689323) B689323
theorem B2066039 : Blo 610295 2066039 := bstep (se 1 (by rfl) ⟨1549529, by rfl⟩ : syracuseStep 2066039 = 3099059) B3099059
theorem B919175 : Blo 610295 919175 := bstep (se 1 (by rfl) ⟨689381, by rfl⟩ : syracuseStep 919175 = 1378763) B1378763
theorem B919211 : Blo 610295 919211 := bstep (se 1 (by rfl) ⟨689408, by rfl⟩ : syracuseStep 919211 = 1378817) B1378817
theorem B919241 : Blo 610295 919241 := bstep (se 2 (by rfl) ⟨344715, by rfl⟩ : syracuseStep 919241 = 689431) B689431
theorem B2361089 : Blo 610295 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B2950913 : Blo 610295 2950913 := bstep (se 2 (by rfl) ⟨1106592, by rfl⟩ : syracuseStep 2950913 = 2213185) B2213185
theorem B2328335 : Blo 610295 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B689935 : Blo 610295 689935 := bstep (se 1 (by rfl) ⟨517451, by rfl⟩ : syracuseStep 689935 = 1034903) B1034903
theorem B1738529 : Blo 610295 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B919355 : Blo 610295 919355 := bstep (se 1 (by rfl) ⟨689516, by rfl⟩ : syracuseStep 919355 = 1379033) B1379033
theorem B919415 : Blo 610295 919415 := bstep (se 1 (by rfl) ⟨689561, by rfl⟩ : syracuseStep 919415 = 1379123) B1379123
theorem B919439 : Blo 610295 919439 := bstep (se 1 (by rfl) ⟨689579, by rfl⟩ : syracuseStep 919439 = 1379159) B1379159
theorem B919481 : Blo 610295 919481 := bstep (se 2 (by rfl) ⟨344805, by rfl⟩ : syracuseStep 919481 = 689611) B689611
theorem B3311563 : Blo 610295 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B919559 : Blo 610295 919559 := bstep (se 1 (by rfl) ⟨689669, by rfl⟩ : syracuseStep 919559 = 1379339) B1379339
theorem B7440407 : Blo 610295 7440407 := bstep (se 1 (by rfl) ⟨5580305, by rfl⟩ : syracuseStep 7440407 = 11160611) B11160611
theorem B919595 : Blo 610295 919595 := bstep (se 1 (by rfl) ⟨689696, by rfl⟩ : syracuseStep 919595 = 1379393) B1379393
theorem B919625 : Blo 610295 919625 := bstep (se 2 (by rfl) ⟨344859, by rfl⟩ : syracuseStep 919625 = 689719) B689719
theorem B12585077 : Blo 610295 12585077 := bstep (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) B1179851
theorem B1738871 : Blo 610295 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B1378439 : Blo 610295 1378439 := bstep (se 1 (by rfl) ⟨1033829, by rfl⟩ : syracuseStep 1378439 = 2067659) B2067659
theorem B919739 : Blo 610295 919739 := bstep (se 1 (by rfl) ⟨689804, by rfl⟩ : syracuseStep 919739 = 1379609) B1379609
theorem B2066633 : Blo 610295 2066633 := bstep (se 2 (by rfl) ⟨774987, by rfl⟩ : syracuseStep 2066633 = 1549975) B1549975
theorem B11798729 : Blo 610295 11798729 := bstep (se 2 (by rfl) ⟨4424523, by rfl⟩ : syracuseStep 11798729 = 8849047) B8849047
theorem B919799 : Blo 610295 919799 := bstep (se 1 (by rfl) ⟨689849, by rfl⟩ : syracuseStep 919799 = 1379699) B1379699
theorem B690439 : Blo 610295 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B919823 : Blo 610295 919823 := bstep (se 1 (by rfl) ⟨689867, by rfl⟩ : syracuseStep 919823 = 1379735) B1379735
theorem B4655393 : Blo 610295 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B919865 : Blo 610295 919865 := bstep (se 2 (by rfl) ⟨344949, by rfl⟩ : syracuseStep 919865 = 689899) B689899
theorem B1378619 : Blo 610295 1378619 := bstep (se 1 (by rfl) ⟨1033964, by rfl⟩ : syracuseStep 1378619 = 2067929) B2067929
theorem B919943 : Blo 610295 919943 := bstep (se 1 (by rfl) ⟨689957, by rfl⟩ : syracuseStep 919943 = 1379915) B1379915
theorem B919979 : Blo 610295 919979 := bstep (se 1 (by rfl) ⟨689984, by rfl⟩ : syracuseStep 919979 = 1379969) B1379969
theorem B1378745 : Blo 610295 1378745 := bstep (se 2 (by rfl) ⟨517029, by rfl⟩ : syracuseStep 1378745 = 1034059) B1034059
theorem B690619 : Blo 610295 690619 := bstep (se 1 (by rfl) ⟨517964, by rfl⟩ : syracuseStep 690619 = 1035929) B1035929
theorem B920009 : Blo 610295 920009 := bstep (se 2 (by rfl) ⟨345003, by rfl⟩ : syracuseStep 920009 = 690007) B690007
theorem B920123 : Blo 610295 920123 := bstep (se 1 (by rfl) ⟨690092, by rfl⟩ : syracuseStep 920123 = 1380185) B1380185
theorem B3181123 : Blo 610295 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B13208183 : Blo 610295 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B920183 : Blo 610295 920183 := bstep (se 1 (by rfl) ⟨690137, by rfl⟩ : syracuseStep 920183 = 1380275) B1380275
theorem B920207 : Blo 610295 920207 := bstep (se 1 (by rfl) ⟨690155, by rfl⟩ : syracuseStep 920207 = 1380311) B1380311
theorem B920249 : Blo 610295 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B6982361 : Blo 610295 6982361 := bstep (se 2 (by rfl) ⟨2618385, by rfl⟩ : syracuseStep 6982361 = 5236771) B5236771
theorem B920327 : Blo 610295 920327 := bstep (se 1 (by rfl) ⟨690245, by rfl⟩ : syracuseStep 920327 = 1380491) B1380491
theorem B1739531 : Blo 610295 1739531 := bstep (se 1 (by rfl) ⟨1304648, by rfl⟩ : syracuseStep 1739531 = 2609297) B2609297
theorem B1379087 : Blo 610295 1379087 := bstep (se 1 (by rfl) ⟨1034315, by rfl⟩ : syracuseStep 1379087 = 2068631) B2068631
theorem B1379105 : Blo 610295 1379105 := bstep (se 2 (by rfl) ⟨517164, by rfl⟩ : syracuseStep 1379105 = 1034329) B1034329
theorem B920363 : Blo 610295 920363 := bstep (se 1 (by rfl) ⟨690272, by rfl⟩ : syracuseStep 920363 = 1380545) B1380545
theorem B920393 : Blo 610295 920393 := bstep (se 2 (by rfl) ⟨345147, by rfl⟩ : syracuseStep 920393 = 690295) B690295
theorem B2067335 : Blo 610295 2067335 := bstep (se 1 (by rfl) ⟨1550501, by rfl⟩ : syracuseStep 2067335 = 3101003) B3101003
theorem B920507 : Blo 610295 920507 := bstep (se 1 (by rfl) ⟨690380, by rfl⟩ : syracuseStep 920507 = 1380761) B1380761
theorem B920567 : Blo 610295 920567 := bstep (se 1 (by rfl) ⟨690425, by rfl⟩ : syracuseStep 920567 = 1380851) B1380851
theorem B920591 : Blo 610295 920591 := bstep (se 1 (by rfl) ⟨690443, by rfl⟩ : syracuseStep 920591 = 1380887) B1380887
theorem B920633 : Blo 610295 920633 := bstep (se 2 (by rfl) ⟨345237, by rfl⟩ : syracuseStep 920633 = 690475) B690475
theorem B1379447 : Blo 610295 1379447 := bstep (se 1 (by rfl) ⟨1034585, by rfl⟩ : syracuseStep 1379447 = 2069171) B2069171
theorem B920711 : Blo 610295 920711 := bstep (se 1 (by rfl) ⟨690533, by rfl⟩ : syracuseStep 920711 = 1381067) B1381067
theorem B920747 : Blo 610295 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B920777 : Blo 610295 920777 := bstep (se 2 (by rfl) ⟨345291, by rfl⟩ : syracuseStep 920777 = 690583) B690583
theorem B4656365 : Blo 610295 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B2067713 : Blo 610295 2067713 := bstep (se 2 (by rfl) ⟨775392, by rfl⟩ : syracuseStep 2067713 = 1550785) B1550785
theorem B1379627 : Blo 610295 1379627 := bstep (se 1 (by rfl) ⟨1034720, by rfl⟩ : syracuseStep 1379627 = 2069441) B2069441
theorem B920891 : Blo 610295 920891 := bstep (se 1 (by rfl) ⟨690668, by rfl⟩ : syracuseStep 920891 = 1381337) B1381337
theorem B920951 : Blo 610295 920951 := bstep (se 1 (by rfl) ⟨690713, by rfl⟩ : syracuseStep 920951 = 1381427) B1381427
theorem B2329991 : Blo 610295 2329991 := bstep (se 1 (by rfl) ⟨1747493, by rfl⟩ : syracuseStep 2329991 = 3494987) B3494987
theorem B920975 : Blo 610295 920975 := bstep (se 1 (by rfl) ⟨690731, by rfl⟩ : syracuseStep 920975 = 1381463) B1381463
theorem B921017 : Blo 610295 921017 := bstep (se 2 (by rfl) ⟨345381, by rfl⟩ : syracuseStep 921017 = 690763) B690763
theorem B921095 : Blo 610295 921095 := bstep (se 1 (by rfl) ⟨690821, by rfl⟩ : syracuseStep 921095 = 1381643) B1381643
theorem B921131 : Blo 610295 921131 := bstep (se 1 (by rfl) ⟨690848, by rfl⟩ : syracuseStep 921131 = 1381697) B1381697
theorem B921161 : Blo 610295 921161 := bstep (se 2 (by rfl) ⟨345435, by rfl⟩ : syracuseStep 921161 = 690871) B690871
theorem B1379987 : Blo 610295 1379987 := bstep (se 1 (by rfl) ⟨1034990, by rfl⟩ : syracuseStep 1379987 = 2069981) B2069981
theorem B921275 : Blo 610295 921275 := bstep (se 1 (by rfl) ⟨690956, by rfl⟩ : syracuseStep 921275 = 1381913) B1381913
theorem B1380041 : Blo 610295 1380041 := bstep (se 2 (by rfl) ⟨517515, by rfl⟩ : syracuseStep 1380041 = 1035031) B1035031
theorem B921335 : Blo 610295 921335 := bstep (se 1 (by rfl) ⟨691001, by rfl⟩ : syracuseStep 921335 = 1382003) B1382003
theorem B921359 : Blo 610295 921359 := bstep (se 1 (by rfl) ⟨691019, by rfl⟩ : syracuseStep 921359 = 1382039) B1382039
theorem B921401 : Blo 610295 921401 := bstep (se 2 (by rfl) ⟨345525, by rfl⟩ : syracuseStep 921401 = 691051) B691051
theorem B2068523 : Blo 610295 2068523 := bstep (se 1 (by rfl) ⟨1551392, by rfl⟩ : syracuseStep 2068523 = 3102785) B3102785
theorem B1741115 : Blo 610295 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B1741171 : Blo 610295 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B1380743 : Blo 610295 1380743 := bstep (se 1 (by rfl) ⟨1035557, by rfl⟩ : syracuseStep 1380743 = 2071115) B2071115
theorem B1380923 : Blo 610295 1380923 := bstep (se 1 (by rfl) ⟨1035692, by rfl⟩ : syracuseStep 1380923 = 2071385) B2071385
theorem B1381049 : Blo 610295 1381049 := bstep (se 2 (by rfl) ⟨517893, by rfl⟩ : syracuseStep 1381049 = 1035787) B1035787
theorem B1741513 : Blo 610295 1741513 := bstep (se 2 (by rfl) ⟨653067, by rfl⟩ : syracuseStep 1741513 = 1306135) B1306135
theorem B1545095 : Blo 610295 1545095 := bstep (se 1 (by rfl) ⟨1158821, by rfl⟩ : syracuseStep 1545095 = 2317643) B2317643
theorem B1545227 : Blo 610295 1545227 := bstep (se 1 (by rfl) ⟨1158920, by rfl⟩ : syracuseStep 1545227 = 2317841) B2317841
theorem B1381391 : Blo 610295 1381391 := bstep (se 1 (by rfl) ⟨1036043, by rfl⟩ : syracuseStep 1381391 = 2072087) B2072087
theorem B1381409 : Blo 610295 1381409 := bstep (se 2 (by rfl) ⟨518028, by rfl⟩ : syracuseStep 1381409 = 1036057) B1036057
theorem B2331767 : Blo 610295 2331767 := bstep (se 1 (by rfl) ⟨1748825, by rfl⟩ : syracuseStep 2331767 = 3497651) B3497651
theorem B4658309 : Blo 610295 4658309 := bstep (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) B873433
theorem B2069819 : Blo 610295 2069819 := bstep (se 1 (by rfl) ⟨1552364, by rfl⟩ : syracuseStep 2069819 = 3104729) B3104729
theorem B1381751 : Blo 610295 1381751 := bstep (se 1 (by rfl) ⟨1036313, by rfl⟩ : syracuseStep 1381751 = 2072627) B2072627
theorem B9442745 : Blo 610295 9442745 := bstep (se 2 (by rfl) ⟨3541029, by rfl⟩ : syracuseStep 9442745 = 7082059) B7082059
theorem B1545743 : Blo 610295 1545743 := bstep (se 1 (by rfl) ⟨1159307, by rfl⟩ : syracuseStep 1545743 = 2318615) B2318615
theorem B1381931 : Blo 610295 1381931 := bstep (se 1 (by rfl) ⟨1036448, by rfl⟩ : syracuseStep 1381931 = 2072897) B2072897
theorem B1545875 : Blo 610295 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B2070305 : Blo 610295 2070305 := bstep (se 2 (by rfl) ⟨776364, by rfl⟩ : syracuseStep 2070305 = 1552729) B1552729
theorem B11802419 : Blo 610295 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B7870283 : Blo 610295 7870283 := bstep (se 1 (by rfl) ⟨5902712, by rfl⟩ : syracuseStep 7870283 = 11805425) B11805425
theorem B4200281 : Blo 610295 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B2070899 : Blo 610295 2070899 := bstep (se 1 (by rfl) ⟨1553174, by rfl⟩ : syracuseStep 2070899 = 3106349) B3106349
theorem B8591761 : Blo 610295 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B2202173 : Blo 610295 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1547009 : Blo 610295 1547009 := bstep (se 2 (by rfl) ⟨580128, by rfl⟩ : syracuseStep 1547009 = 1160257) B1160257
theorem B6626063 : Blo 610295 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B1743677 : Blo 610295 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B1743905 : Blo 610295 1743905 := bstep (se 2 (by rfl) ⟨653964, by rfl⟩ : syracuseStep 1743905 = 1307929) B1307929
theorem B1547383 : Blo 610295 1547383 := bstep (se 1 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 1547383 = 2321075) B2321075
theorem B111779131 : Blo 610295 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B1744247 : Blo 610295 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B4660739 : Blo 610295 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B1547819 : Blo 610295 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B1548659 : Blo 610295 1548659 := bstep (se 1 (by rfl) ⟨1161494, by rfl⟩ : syracuseStep 1548659 = 2322989) B2322989
theorem B1548679 : Blo 610295 1548679 := bstep (se 1 (by rfl) ⟨1161509, by rfl⟩ : syracuseStep 1548679 = 2323019) B2323019
theorem B696763 : Blo 610295 696763 := bstep (se 1 (by rfl) ⟨522572, by rfl⟩ : syracuseStep 696763 = 1045145) B1045145
theorem B2204189 : Blo 610295 2204189 := bstep (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) B826571
theorem B1548953 : Blo 610295 1548953 := bstep (se 2 (by rfl) ⟨580857, by rfl⟩ : syracuseStep 1548953 = 1161715) B1161715
theorem B1549115 : Blo 610295 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B5219275 : Blo 610295 5219275 := bstep (se 1 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 5219275 = 7828913) B7828913
theorem B1549327 : Blo 610295 1549327 := bstep (se 1 (by rfl) ⟨1161995, by rfl⟩ : syracuseStep 1549327 = 2323991) B2323991
theorem B3482797 : Blo 610295 3482797 := bstep (se 3 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 3482797 = 1306049) B1306049
theorem B3712229 : Blo 610295 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B4400365 : Blo 610295 4400365 := bstep (se 3 (by rfl) ⟨825068, by rfl⟩ : syracuseStep 4400365 = 1650137) B1650137
theorem B1549601 : Blo 610295 1549601 := bstep (se 2 (by rfl) ⟨581100, by rfl⟩ : syracuseStep 1549601 = 1162201) B1162201
theorem B3089987 : Blo 610295 3089987 := bstep (se 1 (by rfl) ⟨2317490, by rfl⟩ : syracuseStep 3089987 = 4634981) B4634981
theorem B7939889 : Blo 610295 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B1746775 : Blo 610295 1746775 := bstep (se 1 (by rfl) ⟨1310081, by rfl⟩ : syracuseStep 1746775 = 2620163) B2620163
theorem B3090311 : Blo 610295 3090311 := bstep (se 1 (by rfl) ⟨2317733, by rfl⟩ : syracuseStep 3090311 = 4635467) B4635467
theorem B1747003 : Blo 610295 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1747129 : Blo 610295 1747129 := bstep (se 2 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 1747129 = 1310347) B1310347
theorem B1550603 : Blo 610295 1550603 := bstep (se 1 (by rfl) ⟨1162952, by rfl⟩ : syracuseStep 1550603 = 2325905) B2325905
theorem B1551251 : Blo 610295 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B2796611 : Blo 610295 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B1551545 : Blo 610295 1551545 := bstep (se 2 (by rfl) ⟨581829, by rfl⟩ : syracuseStep 1551545 = 1163659) B1163659
theorem B3485213 : Blo 610295 3485213 := bstep (se 3 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 3485213 = 1306955) B1306955
theorem B1158715 : Blo 610295 1158715 := bstep (se 1 (by rfl) ⟨869036, by rfl⟩ : syracuseStep 1158715 = 1738073) B1738073
theorem B1650547 : Blo 610295 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1552243 : Blo 610295 1552243 := bstep (se 1 (by rfl) ⟨1164182, by rfl⟩ : syracuseStep 1552243 = 2328365) B2328365
theorem B1552385 : Blo 610295 1552385 := bstep (se 2 (by rfl) ⟨582144, by rfl⟩ : syracuseStep 1552385 = 1164289) B1164289
theorem B1159201 : Blo 610295 1159201 := bstep (se 2 (by rfl) ⟨434700, by rfl⟩ : syracuseStep 1159201 = 869401) B869401
theorem B1749053 : Blo 610295 1749053 := bstep (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) B655895
theorem B733303 : Blo 610295 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B5878109 : Blo 610295 5878109 := bstep (se 3 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 5878109 = 2204291) B2204291
theorem B3715463 : Blo 610295 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B1552841 : Blo 610295 1552841 := bstep (se 2 (by rfl) ⟨582315, by rfl⟩ : syracuseStep 1552841 = 1164631) B1164631
theorem B1651499 : Blo 610295 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B1553195 : Blo 610295 1553195 := bstep (se 1 (by rfl) ⟨1164896, by rfl⟩ : syracuseStep 1553195 = 2329793) B2329793
theorem B2798621 : Blo 610295 2798621 := bstep (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) B1049483
theorem B23540867 : Blo 610295 23540867 := bstep (se 1 (by rfl) ⟨17655650, by rfl⟩ : syracuseStep 23540867 = 35311301) B35311301
theorem B1160507 : Blo 610295 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B3093875 : Blo 610295 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B1554187 : Blo 610295 1554187 := bstep (se 1 (by rfl) ⟨1165640, by rfl⟩ : syracuseStep 1554187 = 2331281) B2331281
theorem B1160993 : Blo 610295 1160993 := bstep (se 2 (by rfl) ⟨435372, by rfl⟩ : syracuseStep 1160993 = 870745) B870745
theorem B14137163 : Blo 610295 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B3094361 : Blo 610295 3094361 := bstep (se 2 (by rfl) ⟨1160385, by rfl⟩ : syracuseStep 3094361 = 2320771) B2320771
theorem B1554329 : Blo 610295 1554329 := bstep (se 2 (by rfl) ⟨582873, by rfl⟩ : syracuseStep 1554329 = 1165747) B1165747
theorem B1161145 : Blo 610295 1161145 := bstep (se 2 (by rfl) ⟨435429, by rfl⟩ : syracuseStep 1161145 = 870859) B870859
theorem B3487697 : Blo 610295 3487697 := bstep (se 2 (by rfl) ⟨1307886, by rfl⟩ : syracuseStep 3487697 = 2615773) B2615773
theorem B1914881 : Blo 610295 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B1554491 : Blo 610295 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B931913 : Blo 610295 931913 := bstep (se 2 (by rfl) ⟨349467, by rfl⟩ : syracuseStep 931913 = 698935) B698935
theorem B1030279 : Blo 610295 1030279 := bstep (se 1 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 1030279 = 1545419) B1545419
theorem B5028155 : Blo 610295 5028155 := bstep (se 1 (by rfl) ⟨3771116, by rfl⟩ : syracuseStep 5028155 = 7542233) B7542233
theorem B1554835 : Blo 610295 1554835 := bstep (se 1 (by rfl) ⟨1166126, by rfl⟩ : syracuseStep 1554835 = 2332253) B2332253
theorem B735787 : Blo 610295 735787 := bstep (se 1 (by rfl) ⟨551840, by rfl⟩ : syracuseStep 735787 = 1103681) B1103681
theorem B1030927 : Blo 610295 1030927 := bstep (se 1 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 1030927 = 1546391) B1546391
theorem B1031467 : Blo 610295 1031467 := bstep (se 1 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 1031467 = 1547201) B1547201
theorem B736571 : Blo 610295 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B1031609 : Blo 610295 1031609 := bstep (se 2 (by rfl) ⟨386853, by rfl⟩ : syracuseStep 1031609 = 773707) B773707
theorem B4406737 : Blo 610295 4406737 := bstep (se 2 (by rfl) ⟨1652526, by rfl⟩ : syracuseStep 4406737 = 3305053) B3305053
theorem B1162937 : Blo 610295 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B3489587 : Blo 610295 3489587 := bstep (se 1 (by rfl) ⟨2617190, by rfl⟩ : syracuseStep 3489587 = 5234381) B5234381
theorem B3096467 : Blo 610295 3096467 := bstep (se 1 (by rfl) ⟨2322350, by rfl⟩ : syracuseStep 3096467 = 4644701) B4644701
theorem B1392569 : Blo 610295 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B8503319 : Blo 610295 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B1032311 : Blo 610295 1032311 := bstep (se 1 (by rfl) ⟨774233, by rfl⟩ : syracuseStep 1032311 = 1548467) B1548467
theorem B9421073 : Blo 610295 9421073 := bstep (se 2 (by rfl) ⟨3532902, by rfl⟩ : syracuseStep 9421073 = 7065805) B7065805
theorem B3359027 : Blo 610295 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B1032763 : Blo 610295 1032763 := bstep (se 1 (by rfl) ⟨774572, by rfl⟩ : syracuseStep 1032763 = 1549145) B1549145
theorem B5653111 : Blo 610295 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B8372929 : Blo 610295 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B1032905 : Blo 610295 1032905 := bstep (se 2 (by rfl) ⟨387339, by rfl⟩ : syracuseStep 1032905 = 774679) B774679
theorem B2212609 : Blo 610295 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B2212667 : Blo 610295 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B1196947 : Blo 610295 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1655867 : Blo 610295 1655867 := bstep (se 1 (by rfl) ⟨1241900, by rfl⟩ : syracuseStep 1655867 = 2483801) B2483801
theorem B4637897 : Blo 610295 4637897 := bstep (se 2 (by rfl) ⟨1739211, by rfl⟩ : syracuseStep 4637897 = 3478423) B3478423
theorem B3491045 : Blo 610295 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B1033607 : Blo 610295 1033607 := bstep (se 1 (by rfl) ⟨775205, by rfl⟩ : syracuseStep 1033607 = 1550411) B1550411
theorem B2213405 : Blo 610295 2213405 := bstep (se 3 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 2213405 = 830027) B830027
theorem B1164935 : Blo 610295 1164935 := bstep (se 1 (by rfl) ⟨873701, by rfl⟩ : syracuseStep 1164935 = 1747403) B1747403
theorem B3524411 : Blo 610295 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B1034255 : Blo 610295 1034255 := bstep (se 1 (by rfl) ⟨775691, by rfl⟩ : syracuseStep 1034255 = 1551383) B1551383
theorem B772411 : Blo 610295 772411 := bstep (se 1 (by rfl) ⟨579308, by rfl⟩ : syracuseStep 772411 = 1158617) B1158617
theorem B1034795 : Blo 610295 1034795 := bstep (se 1 (by rfl) ⟨776096, by rfl⟩ : syracuseStep 1034795 = 1552193) B1552193
theorem B9423479 : Blo 610295 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B2116367 : Blo 610295 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B3099545 : Blo 610295 3099545 := bstep (se 2 (by rfl) ⟨1162329, by rfl⟩ : syracuseStep 3099545 = 2324659) B2324659
theorem B1035193 : Blo 610295 1035193 := bstep (se 2 (by rfl) ⟨388197, by rfl⟩ : syracuseStep 1035193 = 776395) B776395
theorem B8834285 : Blo 610295 8834285 := bstep (se 3 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 8834285 = 3312857) B3312857
theorem B773383 : Blo 610295 773383 := bstep (se 1 (by rfl) ⟨580037, by rfl⟩ : syracuseStep 773383 = 1160075) B1160075
theorem B6278417 : Blo 610295 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B1035895 : Blo 610295 1035895 := bstep (se 1 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 1035895 = 1553843) B1553843
theorem B773803 : Blo 610295 773803 := bstep (se 1 (by rfl) ⟨580352, by rfl⟩ : syracuseStep 773803 = 1160705) B1160705
theorem B2608955 : Blo 610295 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B1036091 : Blo 610295 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B774031 : Blo 610295 774031 := bstep (se 1 (by rfl) ⟨580523, by rfl⟩ : syracuseStep 774031 = 1161047) B1161047
theorem B1658809 : Blo 610295 1658809 := bstep (se 2 (by rfl) ⟨622053, by rfl⟩ : syracuseStep 1658809 = 1244107) B1244107
theorem B610311 : Blo 610295 610311 := bstep (se 1 (by rfl) ⟨457733, by rfl⟩ : syracuseStep 610311 = 915467) B915467
theorem B6606859 : Blo 610295 6606859 := bstep (se 1 (by rfl) ⟨4955144, by rfl⟩ : syracuseStep 6606859 = 9910289) B9910289
theorem B610319 : Blo 610295 610319 := bstep (se 1 (by rfl) ⟨457739, by rfl⟩ : syracuseStep 610319 = 915479) B915479
theorem B610363 : Blo 610295 610363 := bstep (se 1 (by rfl) ⟨457772, by rfl⟩ : syracuseStep 610363 = 915545) B915545
theorem B610439 : Blo 610295 610439 := bstep (se 1 (by rfl) ⟨457829, by rfl⟩ : syracuseStep 610439 = 915659) B915659
theorem B610447 : Blo 610295 610447 := bstep (se 1 (by rfl) ⟨457835, by rfl⟩ : syracuseStep 610447 = 915671) B915671
theorem B610491 : Blo 610295 610491 := bstep (se 1 (by rfl) ⟨457868, by rfl⟩ : syracuseStep 610491 = 915737) B915737
theorem B1036489 : Blo 610295 1036489 := bstep (se 2 (by rfl) ⟨388683, by rfl⟩ : syracuseStep 1036489 = 777367) B777367
theorem B610567 : Blo 610295 610567 := bstep (se 1 (by rfl) ⟨457925, by rfl⟩ : syracuseStep 610567 = 915851) B915851
theorem B610575 : Blo 610295 610575 := bstep (se 1 (by rfl) ⟨457931, by rfl⟩ : syracuseStep 610575 = 915863) B915863
theorem B610619 : Blo 610295 610619 := bstep (se 1 (by rfl) ⟨457964, by rfl⟩ : syracuseStep 610619 = 915929) B915929
theorem B610695 : Blo 610295 610695 := bstep (se 1 (by rfl) ⟨458021, by rfl⟩ : syracuseStep 610695 = 916043) B916043
theorem B3494279 : Blo 610295 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B610703 : Blo 610295 610703 := bstep (se 1 (by rfl) ⟨458027, by rfl⟩ : syracuseStep 610703 = 916055) B916055
theorem B610747 : Blo 610295 610747 := bstep (se 1 (by rfl) ⟨458060, by rfl⟩ : syracuseStep 610747 = 916121) B916121
theorem B610823 : Blo 610295 610823 := bstep (se 1 (by rfl) ⟨458117, by rfl⟩ : syracuseStep 610823 = 916235) B916235
theorem B610831 : Blo 610295 610831 := bstep (se 1 (by rfl) ⟨458123, by rfl⟩ : syracuseStep 610831 = 916247) B916247
theorem B610875 : Blo 610295 610875 := bstep (se 1 (by rfl) ⟨458156, by rfl⟩ : syracuseStep 610875 = 916313) B916313
theorem B3494461 : Blo 610295 3494461 := bstep (se 3 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 3494461 = 1310423) B1310423
theorem B774775 : Blo 610295 774775 := bstep (se 1 (by rfl) ⟨581081, by rfl⟩ : syracuseStep 774775 = 1162163) B1162163
theorem B54317699 : Blo 610295 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B610951 : Blo 610295 610951 := bstep (se 1 (by rfl) ⟨458213, by rfl⟩ : syracuseStep 610951 = 916427) B916427
theorem B610959 : Blo 610295 610959 := bstep (se 1 (by rfl) ⟨458219, by rfl⟩ : syracuseStep 610959 = 916439) B916439
theorem B611003 : Blo 610295 611003 := bstep (se 1 (by rfl) ⟨458252, by rfl⟩ : syracuseStep 611003 = 916505) B916505
theorem B611079 : Blo 610295 611079 := bstep (se 1 (by rfl) ⟨458309, by rfl⟩ : syracuseStep 611079 = 916619) B916619
theorem B611087 : Blo 610295 611087 := bstep (se 1 (by rfl) ⟨458315, by rfl⟩ : syracuseStep 611087 = 916631) B916631
theorem B611131 : Blo 610295 611131 := bstep (se 1 (by rfl) ⟨458348, by rfl⟩ : syracuseStep 611131 = 916697) B916697
theorem B611207 : Blo 610295 611207 := bstep (se 1 (by rfl) ⟨458405, by rfl⟩ : syracuseStep 611207 = 916811) B916811
theorem B611215 : Blo 610295 611215 := bstep (se 1 (by rfl) ⟨458411, by rfl⟩ : syracuseStep 611215 = 916823) B916823
theorem B611259 : Blo 610295 611259 := bstep (se 1 (by rfl) ⟨458444, by rfl⟩ : syracuseStep 611259 = 916889) B916889
theorem B775099 : Blo 610295 775099 := bstep (se 1 (by rfl) ⟨581324, by rfl⟩ : syracuseStep 775099 = 1162649) B1162649
theorem B611335 : Blo 610295 611335 := bstep (se 1 (by rfl) ⟨458501, by rfl⟩ : syracuseStep 611335 = 917003) B917003
theorem B611343 : Blo 610295 611343 := bstep (se 1 (by rfl) ⟨458507, by rfl⟩ : syracuseStep 611343 = 917015) B917015
theorem B611387 : Blo 610295 611387 := bstep (se 1 (by rfl) ⟨458540, by rfl⟩ : syracuseStep 611387 = 917081) B917081
theorem B611463 : Blo 610295 611463 := bstep (se 1 (by rfl) ⟨458597, by rfl⟩ : syracuseStep 611463 = 917195) B917195
theorem B611471 : Blo 610295 611471 := bstep (se 1 (by rfl) ⟨458603, by rfl⟩ : syracuseStep 611471 = 917207) B917207
theorem B611515 : Blo 610295 611515 := bstep (se 1 (by rfl) ⟨458636, by rfl⟩ : syracuseStep 611515 = 917273) B917273
theorem B611591 : Blo 610295 611591 := bstep (se 1 (by rfl) ⟨458693, by rfl⟩ : syracuseStep 611591 = 917387) B917387
theorem B611599 : Blo 610295 611599 := bstep (se 1 (by rfl) ⟨458699, by rfl⟩ : syracuseStep 611599 = 917399) B917399
theorem B611643 : Blo 610295 611643 := bstep (se 1 (by rfl) ⟨458732, by rfl⟩ : syracuseStep 611643 = 917465) B917465
theorem B611719 : Blo 610295 611719 := bstep (se 1 (by rfl) ⟨458789, by rfl⟩ : syracuseStep 611719 = 917579) B917579
theorem B611727 : Blo 610295 611727 := bstep (se 1 (by rfl) ⟨458795, by rfl⟩ : syracuseStep 611727 = 917591) B917591
theorem B4412819 : Blo 610295 4412819 := bstep (se 1 (by rfl) ⟨3309614, by rfl⟩ : syracuseStep 4412819 = 6619229) B6619229
theorem B1660313 : Blo 610295 1660313 := bstep (se 2 (by rfl) ⟨622617, by rfl⟩ : syracuseStep 1660313 = 1245235) B1245235
theorem B775595 : Blo 610295 775595 := bstep (se 1 (by rfl) ⟨581696, by rfl⟩ : syracuseStep 775595 = 1163393) B1163393
theorem B3102137 : Blo 610295 3102137 := bstep (se 2 (by rfl) ⟨1163301, by rfl⟩ : syracuseStep 3102137 = 2326603) B2326603
theorem B611771 : Blo 610295 611771 := bstep (se 1 (by rfl) ⟨458828, by rfl⟩ : syracuseStep 611771 = 917657) B917657
theorem B873929 : Blo 610295 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B611847 : Blo 610295 611847 := bstep (se 1 (by rfl) ⟨458885, by rfl⟩ : syracuseStep 611847 = 917771) B917771
theorem B611855 : Blo 610295 611855 := bstep (se 1 (by rfl) ⟨458891, by rfl⟩ : syracuseStep 611855 = 917783) B917783
theorem B2610731 : Blo 610295 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B611899 : Blo 610295 611899 := bstep (se 1 (by rfl) ⟨458924, by rfl⟩ : syracuseStep 611899 = 917849) B917849
theorem B611975 : Blo 610295 611975 := bstep (se 1 (by rfl) ⟨458981, by rfl⟩ : syracuseStep 611975 = 917963) B917963
theorem B611983 : Blo 610295 611983 := bstep (se 1 (by rfl) ⟨458987, by rfl⟩ : syracuseStep 611983 = 917975) B917975
theorem B612027 : Blo 610295 612027 := bstep (se 1 (by rfl) ⟨459020, by rfl⟩ : syracuseStep 612027 = 918041) B918041
theorem B612103 : Blo 610295 612103 := bstep (se 1 (by rfl) ⟨459077, by rfl⟩ : syracuseStep 612103 = 918155) B918155
theorem B612111 : Blo 610295 612111 := bstep (se 1 (by rfl) ⟨459083, by rfl⟩ : syracuseStep 612111 = 918167) B918167
theorem B612155 : Blo 610295 612155 := bstep (se 1 (by rfl) ⟨459116, by rfl⟩ : syracuseStep 612155 = 918233) B918233
theorem B612231 : Blo 610295 612231 := bstep (se 1 (by rfl) ⟨459173, by rfl⟩ : syracuseStep 612231 = 918347) B918347
theorem B776071 : Blo 610295 776071 := bstep (se 1 (by rfl) ⟨582053, by rfl⟩ : syracuseStep 776071 = 1164107) B1164107
theorem B612239 : Blo 610295 612239 := bstep (se 1 (by rfl) ⟨459179, by rfl⟩ : syracuseStep 612239 = 918359) B918359
theorem B6969239 : Blo 610295 6969239 := bstep (se 1 (by rfl) ⟨5226929, by rfl⟩ : syracuseStep 6969239 = 10453859) B10453859
theorem B612283 : Blo 610295 612283 := bstep (se 1 (by rfl) ⟨459212, by rfl⟩ : syracuseStep 612283 = 918425) B918425
theorem B612359 : Blo 610295 612359 := bstep (se 1 (by rfl) ⟨459269, by rfl⟩ : syracuseStep 612359 = 918539) B918539
theorem B612367 : Blo 610295 612367 := bstep (se 1 (by rfl) ⟨459275, by rfl⟩ : syracuseStep 612367 = 918551) B918551
theorem B612411 : Blo 610295 612411 := bstep (se 1 (by rfl) ⟨459308, by rfl⟩ : syracuseStep 612411 = 918617) B918617
theorem B2873411 : Blo 610295 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B612487 : Blo 610295 612487 := bstep (se 1 (by rfl) ⟨459365, by rfl⟩ : syracuseStep 612487 = 918731) B918731
theorem B612495 : Blo 610295 612495 := bstep (se 1 (by rfl) ⟨459371, by rfl⟩ : syracuseStep 612495 = 918743) B918743
theorem B612539 : Blo 610295 612539 := bstep (se 1 (by rfl) ⟨459404, by rfl⟩ : syracuseStep 612539 = 918809) B918809
theorem B3496193 : Blo 610295 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B612615 : Blo 610295 612615 := bstep (se 1 (by rfl) ⟨459461, by rfl⟩ : syracuseStep 612615 = 918923) B918923
theorem B612623 : Blo 610295 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B612667 : Blo 610295 612667 := bstep (se 1 (by rfl) ⟨459500, by rfl⟩ : syracuseStep 612667 = 919001) B919001
theorem B776567 : Blo 610295 776567 := bstep (se 1 (by rfl) ⟨582425, by rfl⟩ : syracuseStep 776567 = 1164851) B1164851
theorem B612743 : Blo 610295 612743 := bstep (se 1 (by rfl) ⟨459557, by rfl⟩ : syracuseStep 612743 = 919115) B919115
theorem B612751 : Blo 610295 612751 := bstep (se 1 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 612751 = 919127) B919127
theorem B612795 : Blo 610295 612795 := bstep (se 1 (by rfl) ⟨459596, by rfl⟩ : syracuseStep 612795 = 919193) B919193
theorem B3725777 : Blo 610295 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B612871 : Blo 610295 612871 := bstep (se 1 (by rfl) ⟨459653, by rfl⟩ : syracuseStep 612871 = 919307) B919307
theorem B2611723 : Blo 610295 2611723 := bstep (se 1 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 2611723 = 3917585) B3917585
theorem B612879 : Blo 610295 612879 := bstep (se 1 (by rfl) ⟨459659, by rfl⟩ : syracuseStep 612879 = 919319) B919319
theorem B776719 : Blo 610295 776719 := bstep (se 1 (by rfl) ⟨582539, by rfl⟩ : syracuseStep 776719 = 1165079) B1165079
theorem B612923 : Blo 610295 612923 := bstep (se 1 (by rfl) ⟨459692, by rfl⟩ : syracuseStep 612923 = 919385) B919385
theorem B28269121 : Blo 610295 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B612999 : Blo 610295 612999 := bstep (se 1 (by rfl) ⟨459749, by rfl⟩ : syracuseStep 612999 = 919499) B919499
theorem B613007 : Blo 610295 613007 := bstep (se 1 (by rfl) ⟨459755, by rfl⟩ : syracuseStep 613007 = 919511) B919511
theorem B12114613 : Blo 610295 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B613051 : Blo 610295 613051 := bstep (se 1 (by rfl) ⟨459788, by rfl⟩ : syracuseStep 613051 = 919577) B919577
theorem B776891 : Blo 610295 776891 := bstep (se 1 (by rfl) ⟨582668, by rfl⟩ : syracuseStep 776891 = 1165337) B1165337
theorem B3103433 : Blo 610295 3103433 := bstep (se 2 (by rfl) ⟨1163787, by rfl⟩ : syracuseStep 3103433 = 2327575) B2327575
theorem B613127 : Blo 610295 613127 := bstep (se 1 (by rfl) ⟨459845, by rfl⟩ : syracuseStep 613127 = 919691) B919691
theorem B1858315 : Blo 610295 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B613135 : Blo 610295 613135 := bstep (se 1 (by rfl) ⟨459851, by rfl⟩ : syracuseStep 613135 = 919703) B919703
theorem B1104683 : Blo 610295 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B613179 : Blo 610295 613179 := bstep (se 1 (by rfl) ⟨459884, by rfl⟩ : syracuseStep 613179 = 919769) B919769
theorem B1956743 : Blo 610295 1956743 := bstep (se 1 (by rfl) ⟨1467557, by rfl⟩ : syracuseStep 1956743 = 2935115) B2935115
theorem B613255 : Blo 610295 613255 := bstep (se 1 (by rfl) ⟨459941, by rfl⟩ : syracuseStep 613255 = 919883) B919883
theorem B613263 : Blo 610295 613263 := bstep (se 1 (by rfl) ⟨459947, by rfl⟩ : syracuseStep 613263 = 919895) B919895
theorem B613307 : Blo 610295 613307 := bstep (se 1 (by rfl) ⟨459980, by rfl⟩ : syracuseStep 613307 = 919961) B919961
theorem B613383 : Blo 610295 613383 := bstep (se 1 (by rfl) ⟨460037, by rfl⟩ : syracuseStep 613383 = 920075) B920075
theorem B613391 : Blo 610295 613391 := bstep (se 1 (by rfl) ⟨460043, by rfl⟩ : syracuseStep 613391 = 920087) B920087
theorem B2317355 : Blo 610295 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B613435 : Blo 610295 613435 := bstep (se 1 (by rfl) ⟨460076, by rfl⟩ : syracuseStep 613435 = 920153) B920153
theorem B613511 : Blo 610295 613511 := bstep (se 1 (by rfl) ⟨460133, by rfl⟩ : syracuseStep 613511 = 920267) B920267
theorem B613519 : Blo 610295 613519 := bstep (se 1 (by rfl) ⟨460139, by rfl⟩ : syracuseStep 613519 = 920279) B920279
theorem B613563 : Blo 610295 613563 := bstep (se 1 (by rfl) ⟨460172, by rfl⟩ : syracuseStep 613563 = 920345) B920345
theorem B613639 : Blo 610295 613639 := bstep (se 1 (by rfl) ⟨460229, by rfl⟩ : syracuseStep 613639 = 920459) B920459
theorem B613647 : Blo 610295 613647 := bstep (se 1 (by rfl) ⟨460235, by rfl⟩ : syracuseStep 613647 = 920471) B920471
theorem B613691 : Blo 610295 613691 := bstep (se 1 (by rfl) ⟨460268, by rfl⟩ : syracuseStep 613691 = 920537) B920537
theorem B14179643 : Blo 610295 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B613767 : Blo 610295 613767 := bstep (se 1 (by rfl) ⟨460325, by rfl⟩ : syracuseStep 613767 = 920651) B920651
theorem B613775 : Blo 610295 613775 := bstep (se 1 (by rfl) ⟨460331, by rfl⟩ : syracuseStep 613775 = 920663) B920663
theorem B613819 : Blo 610295 613819 := bstep (se 1 (by rfl) ⟨460364, by rfl⟩ : syracuseStep 613819 = 920729) B920729
theorem B613895 : Blo 610295 613895 := bstep (se 1 (by rfl) ⟨460421, by rfl⟩ : syracuseStep 613895 = 920843) B920843
theorem B613903 : Blo 610295 613903 := bstep (se 1 (by rfl) ⟨460427, by rfl⟩ : syracuseStep 613903 = 920855) B920855
theorem B1859105 : Blo 610295 1859105 := bstep (se 2 (by rfl) ⟨697164, by rfl⟩ : syracuseStep 1859105 = 1394329) B1394329
theorem B613947 : Blo 610295 613947 := bstep (se 1 (by rfl) ⟨460460, by rfl⟩ : syracuseStep 613947 = 920921) B920921
theorem B1007239 : Blo 610295 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B614023 : Blo 610295 614023 := bstep (se 1 (by rfl) ⟨460517, by rfl⟩ : syracuseStep 614023 = 921035) B921035
theorem B614031 : Blo 610295 614031 := bstep (se 1 (by rfl) ⟨460523, by rfl⟩ : syracuseStep 614031 = 921047) B921047
theorem B614075 : Blo 610295 614075 := bstep (se 1 (by rfl) ⟨460556, by rfl⟩ : syracuseStep 614075 = 921113) B921113
theorem B614151 : Blo 610295 614151 := bstep (se 1 (by rfl) ⟨460613, by rfl⟩ : syracuseStep 614151 = 921227) B921227
theorem B614159 : Blo 610295 614159 := bstep (se 1 (by rfl) ⟨460619, by rfl⟩ : syracuseStep 614159 = 921239) B921239
theorem B614203 : Blo 610295 614203 := bstep (se 1 (by rfl) ⟨460652, by rfl⟩ : syracuseStep 614203 = 921305) B921305
theorem B614279 : Blo 610295 614279 := bstep (se 1 (by rfl) ⟨460709, by rfl⟩ : syracuseStep 614279 = 921419) B921419
theorem B614287 : Blo 610295 614287 := bstep (se 1 (by rfl) ⟨460715, by rfl⟩ : syracuseStep 614287 = 921431) B921431
theorem B8970263 : Blo 610295 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B2973953 : Blo 610295 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B1466923 : Blo 610295 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B1466999 : Blo 610295 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B14377817 : Blo 610295 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B2319313 : Blo 610295 2319313 := bstep (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) B1739485
theorem B2942189 : Blo 610295 2942189 := bstep (se 3 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 2942189 = 1103321) B1103321
theorem B2319617 : Blo 610295 2319617 := bstep (se 2 (by rfl) ⟨869856, by rfl⟩ : syracuseStep 2319617 = 1739713) B1739713
theorem B8381729 : Blo 610295 8381729 := bstep (se 2 (by rfl) ⟨3143148, by rfl⟩ : syracuseStep 8381729 = 6286297) B6286297
theorem B8807939 : Blo 610295 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B1959511 : Blo 610295 1959511 := bstep (se 1 (by rfl) ⟨1469633, by rfl⟩ : syracuseStep 1959511 = 2939267) B2939267
theorem B1468019 : Blo 610295 1468019 := bstep (se 1 (by rfl) ⟨1101014, by rfl⟩ : syracuseStep 1468019 = 2202029) B2202029
theorem B2320073 : Blo 610295 2320073 := bstep (se 2 (by rfl) ⟨870027, by rfl⟩ : syracuseStep 2320073 = 1740055) B1740055
theorem B1468307 : Blo 610295 1468307 := bstep (se 1 (by rfl) ⟨1101230, by rfl⟩ : syracuseStep 1468307 = 2202461) B2202461
theorem B1959947 : Blo 610295 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B1959997 : Blo 610295 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B6973613 : Blo 610295 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B1566977 : Blo 610295 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B4974995 : Blo 610295 4974995 := bstep (se 1 (by rfl) ⟨3731246, by rfl⟩ : syracuseStep 4974995 = 7462493) B7462493
theorem B1468961 : Blo 610295 1468961 := bstep (se 2 (by rfl) ⟨550860, by rfl⟩ : syracuseStep 1468961 = 1101721) B1101721
theorem B7269041 : Blo 610295 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B4647617 : Blo 610295 4647617 := bstep (se 2 (by rfl) ⟨1742856, by rfl⟩ : syracuseStep 4647617 = 3485713) B3485713
theorem B2616097 : Blo 610295 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B5041693 : Blo 610295 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B7433795 : Blo 610295 7433795 := bstep (se 1 (by rfl) ⟨5575346, by rfl⟩ : syracuseStep 7433795 = 11150693) B11150693
theorem B1961729 : Blo 610295 1961729 := bstep (se 2 (by rfl) ⟨735648, by rfl⟩ : syracuseStep 1961729 = 1471297) B1471297
theorem B1240847 : Blo 610295 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B2092915 : Blo 610295 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B3305765 : Blo 610295 3305765 := bstep (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) B619831
theorem B3109265 : Blo 610295 3109265 := bstep (se 2 (by rfl) ⟨1165974, by rfl⟩ : syracuseStep 3109265 = 2331949) B2331949
theorem B979499 : Blo 610295 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B2323201 : Blo 610295 2323201 := bstep (se 2 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 2323201 = 1742401) B1742401
theorem B2061071 : Blo 610295 2061071 := bstep (se 1 (by rfl) ⟨1545803, by rfl⟩ : syracuseStep 2061071 = 3091607) B3091607
theorem B6615857 : Blo 610295 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B652303 : Blo 610295 652303 := bstep (se 1 (by rfl) ⟨489227, by rfl⟩ : syracuseStep 652303 = 978455) B978455
theorem B2946071 : Blo 610295 2946071 := bstep (se 1 (by rfl) ⟨2209553, by rfl⟩ : syracuseStep 2946071 = 4419107) B4419107
theorem B2061341 : Blo 610295 2061341 := bstep (se 3 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 2061341 = 773003) B773003
theorem B1307963 : Blo 610295 1307963 := bstep (se 1 (by rfl) ⟨980972, by rfl⟩ : syracuseStep 1307963 = 1961945) B1961945
theorem B6714809 : Blo 610295 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B9434627 : Blo 610295 9434627 := bstep (se 1 (by rfl) ⟨7075970, by rfl⟩ : syracuseStep 9434627 = 14151941) B14151941
theorem B1865227 : Blo 610295 1865227 := bstep (se 1 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 1865227 = 2797841) B2797841
theorem B3929629 : Blo 610295 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B22410827 : Blo 610295 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B1373831 : Blo 610295 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B1374011 : Blo 610295 1374011 := bstep (se 1 (by rfl) ⟨1030508, by rfl⟩ : syracuseStep 1374011 = 2061017) B2061017
theorem B1374137 : Blo 610295 1374137 := bstep (se 2 (by rfl) ⟨515301, by rfl⟩ : syracuseStep 1374137 = 1030603) B1030603
theorem B980921 : Blo 610295 980921 := bstep (se 2 (by rfl) ⟨367845, by rfl⟩ : syracuseStep 980921 = 735691) B735691
theorem B4651019 : Blo 610295 4651019 := bstep (se 1 (by rfl) ⟨3488264, by rfl⟩ : syracuseStep 4651019 = 6976529) B6976529
theorem B15267857 : Blo 610295 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B915515 : Blo 610295 915515 := bstep (se 1 (by rfl) ⟨686636, by rfl⟩ : syracuseStep 915515 = 1373273) B1373273
theorem B2619479 : Blo 610295 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B915575 : Blo 610295 915575 := bstep (se 1 (by rfl) ⟨686681, by rfl⟩ : syracuseStep 915575 = 1373363) B1373363
theorem B2488439 : Blo 610295 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B915599 : Blo 610295 915599 := bstep (se 1 (by rfl) ⟨686699, by rfl⟩ : syracuseStep 915599 = 1373399) B1373399
theorem B915641 : Blo 610295 915641 := bstep (se 2 (by rfl) ⟨343365, by rfl⟩ : syracuseStep 915641 = 686731) B686731
theorem B915719 : Blo 610295 915719 := bstep (se 1 (by rfl) ⟨686789, by rfl⟩ : syracuseStep 915719 = 1373579) B1373579
theorem B1374479 : Blo 610295 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B1964303 : Blo 610295 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1374497 : Blo 610295 1374497 := bstep (se 2 (by rfl) ⟨515436, by rfl⟩ : syracuseStep 1374497 = 1030873) B1030873
theorem B915755 : Blo 610295 915755 := bstep (se 1 (by rfl) ⟨686816, by rfl⟩ : syracuseStep 915755 = 1373633) B1373633
theorem B915785 : Blo 610295 915785 := bstep (se 2 (by rfl) ⟨343419, by rfl⟩ : syracuseStep 915785 = 686839) B686839
theorem B1767827 : Blo 610295 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B2062745 : Blo 610295 2062745 := bstep (se 2 (by rfl) ⟨773529, by rfl⟩ : syracuseStep 2062745 = 1547059) B1547059
theorem B915899 : Blo 610295 915899 := bstep (se 1 (by rfl) ⟨686924, by rfl⟩ : syracuseStep 915899 = 1373849) B1373849
theorem B915959 : Blo 610295 915959 := bstep (se 1 (by rfl) ⟨686969, by rfl⟩ : syracuseStep 915959 = 1373939) B1373939
theorem B915983 : Blo 610295 915983 := bstep (se 1 (by rfl) ⟨686987, by rfl⟩ : syracuseStep 915983 = 1373975) B1373975
theorem B916025 : Blo 610295 916025 := bstep (se 2 (by rfl) ⟨343509, by rfl⟩ : syracuseStep 916025 = 687019) B687019
theorem B1374839 : Blo 610295 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B916103 : Blo 610295 916103 := bstep (se 1 (by rfl) ⟨687077, by rfl⟩ : syracuseStep 916103 = 1374155) B1374155
theorem B916139 : Blo 610295 916139 := bstep (se 1 (by rfl) ⟨687104, by rfl⟩ : syracuseStep 916139 = 1374209) B1374209
theorem B916169 : Blo 610295 916169 := bstep (se 2 (by rfl) ⟨343563, by rfl⟩ : syracuseStep 916169 = 687127) B687127
theorem B1375019 : Blo 610295 1375019 := bstep (se 1 (by rfl) ⟨1031264, by rfl⟩ : syracuseStep 1375019 = 2062529) B2062529
theorem B916283 : Blo 610295 916283 := bstep (se 1 (by rfl) ⟨687212, by rfl⟩ : syracuseStep 916283 = 1374425) B1374425
theorem B7863155 : Blo 610295 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B916343 : Blo 610295 916343 := bstep (se 1 (by rfl) ⟨687257, by rfl⟩ : syracuseStep 916343 = 1374515) B1374515
theorem B686983 : Blo 610295 686983 := bstep (se 1 (by rfl) ⟨515237, by rfl⟩ : syracuseStep 686983 = 1030475) B1030475
theorem B916367 : Blo 610295 916367 := bstep (se 1 (by rfl) ⟨687275, by rfl⟩ : syracuseStep 916367 = 1374551) B1374551
theorem B916409 : Blo 610295 916409 := bstep (se 2 (by rfl) ⟨343653, by rfl⟩ : syracuseStep 916409 = 687307) B687307
theorem B916487 : Blo 610295 916487 := bstep (se 1 (by rfl) ⟨687365, by rfl⟩ : syracuseStep 916487 = 1374731) B1374731
theorem B916523 : Blo 610295 916523 := bstep (se 1 (by rfl) ⟨687392, by rfl⟩ : syracuseStep 916523 = 1374785) B1374785
theorem B687163 : Blo 610295 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B916553 : Blo 610295 916553 := bstep (se 2 (by rfl) ⟨343707, by rfl⟩ : syracuseStep 916553 = 687415) B687415
theorem B2063447 : Blo 610295 2063447 := bstep (se 1 (by rfl) ⟨1547585, by rfl⟩ : syracuseStep 2063447 = 3095171) B3095171
theorem B1375379 : Blo 610295 1375379 := bstep (se 1 (by rfl) ⟨1031534, by rfl⟩ : syracuseStep 1375379 = 2063069) B2063069
theorem B1571987 : Blo 610295 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B1473689 : Blo 610295 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B916667 : Blo 610295 916667 := bstep (se 1 (by rfl) ⟨687500, by rfl⟩ : syracuseStep 916667 = 1375001) B1375001
theorem B1375433 : Blo 610295 1375433 := bstep (se 2 (by rfl) ⟨515787, by rfl⟩ : syracuseStep 1375433 = 1031575) B1031575
theorem B916727 : Blo 610295 916727 := bstep (se 1 (by rfl) ⟨687545, by rfl⟩ : syracuseStep 916727 = 1375091) B1375091
theorem B916751 : Blo 610295 916751 := bstep (se 1 (by rfl) ⟨687563, by rfl⟩ : syracuseStep 916751 = 1375127) B1375127
theorem B916793 : Blo 610295 916793 := bstep (se 2 (by rfl) ⟨343797, by rfl⟩ : syracuseStep 916793 = 687595) B687595
theorem B916871 : Blo 610295 916871 := bstep (se 1 (by rfl) ⟨687653, by rfl⟩ : syracuseStep 916871 = 1375307) B1375307
theorem B916907 : Blo 610295 916907 := bstep (se 1 (by rfl) ⟨687680, by rfl⟩ : syracuseStep 916907 = 1375361) B1375361
theorem B916937 : Blo 610295 916937 := bstep (se 2 (by rfl) ⟨343851, by rfl⟩ : syracuseStep 916937 = 687703) B687703
theorem B785911 : Blo 610295 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B687631 : Blo 610295 687631 := bstep (se 1 (by rfl) ⟨515723, by rfl⟩ : syracuseStep 687631 = 1031447) B1031447
theorem B917051 : Blo 610295 917051 := bstep (se 1 (by rfl) ⟨687788, by rfl⟩ : syracuseStep 917051 = 1375577) B1375577
theorem B2063933 : Blo 610295 2063933 := bstep (se 3 (by rfl) ⟨386987, by rfl⟩ : syracuseStep 2063933 = 773975) B773975
theorem B2326103 : Blo 610295 2326103 := bstep (se 1 (by rfl) ⟨1744577, by rfl⟩ : syracuseStep 2326103 = 3489155) B3489155
theorem B917111 : Blo 610295 917111 := bstep (se 1 (by rfl) ⟨687833, by rfl⟩ : syracuseStep 917111 = 1375667) B1375667
theorem B917135 : Blo 610295 917135 := bstep (se 1 (by rfl) ⟨687851, by rfl⟩ : syracuseStep 917135 = 1375703) B1375703
theorem B917177 : Blo 610295 917177 := bstep (se 2 (by rfl) ⟨343941, by rfl⟩ : syracuseStep 917177 = 687883) B687883
theorem B917255 : Blo 610295 917255 := bstep (se 1 (by rfl) ⟨687941, by rfl⟩ : syracuseStep 917255 = 1375883) B1375883
theorem B917291 : Blo 610295 917291 := bstep (se 1 (by rfl) ⟨687968, by rfl⟩ : syracuseStep 917291 = 1375937) B1375937
theorem B917321 : Blo 610295 917321 := bstep (se 2 (by rfl) ⟨343995, by rfl⟩ : syracuseStep 917321 = 687991) B687991
theorem B1376135 : Blo 610295 1376135 := bstep (se 1 (by rfl) ⟨1032101, by rfl⟩ : syracuseStep 1376135 = 2064203) B2064203
theorem B4652963 : Blo 610295 4652963 := bstep (se 1 (by rfl) ⟨3489722, by rfl⟩ : syracuseStep 4652963 = 6979445) B6979445
theorem B917435 : Blo 610295 917435 := bstep (se 1 (by rfl) ⟨688076, by rfl⟩ : syracuseStep 917435 = 1376153) B1376153
theorem B2621393 : Blo 610295 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B917495 : Blo 610295 917495 := bstep (se 1 (by rfl) ⟨688121, by rfl⟩ : syracuseStep 917495 = 1376243) B1376243
theorem B917513 : Blo 610295 917513 := bstep (se 2 (by rfl) ⟨344067, by rfl⟩ : syracuseStep 917513 = 688135) B688135
theorem B5668879 : Blo 610295 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B917543 : Blo 610295 917543 := bstep (se 1 (by rfl) ⟨688157, by rfl⟩ : syracuseStep 917543 = 1376315) B1376315
theorem B688207 : Blo 610295 688207 := bstep (se 1 (by rfl) ⟨516155, by rfl⟩ : syracuseStep 688207 = 1032311) B1032311
theorem B917627 : Blo 610295 917627 := bstep (se 1 (by rfl) ⟨688220, by rfl⟩ : syracuseStep 917627 = 1376441) B1376441
theorem B1245307 : Blo 610295 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B917753 : Blo 610295 917753 := bstep (se 2 (by rfl) ⟨344157, by rfl⟩ : syracuseStep 917753 = 688315) B688315
theorem B917855 : Blo 610295 917855 := bstep (se 1 (by rfl) ⟨688391, by rfl⟩ : syracuseStep 917855 = 1376783) B1376783
theorem B917867 : Blo 610295 917867 := bstep (se 1 (by rfl) ⟨688400, by rfl⟩ : syracuseStep 917867 = 1376801) B1376801
theorem B688603 : Blo 610295 688603 := bstep (se 1 (by rfl) ⟨516452, by rfl⟩ : syracuseStep 688603 = 1032905) B1032905
theorem B2064905 : Blo 610295 2064905 := bstep (se 2 (by rfl) ⟨774339, by rfl⟩ : syracuseStep 2064905 = 1548679) B1548679
theorem B3932705 : Blo 610295 3932705 := bstep (se 2 (by rfl) ⟨1474764, by rfl⟩ : syracuseStep 3932705 = 2949529) B2949529
theorem B1475111 : Blo 610295 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B918095 : Blo 610295 918095 := bstep (se 1 (by rfl) ⟨688571, by rfl⟩ : syracuseStep 918095 = 1377143) B1377143
theorem B1311329 : Blo 610295 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B1376891 : Blo 610295 1376891 := bstep (se 1 (by rfl) ⟨1032668, by rfl⟩ : syracuseStep 1376891 = 2065337) B2065337
theorem B7930541 : Blo 610295 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B918215 : Blo 610295 918215 := bstep (se 1 (by rfl) ⟨688661, by rfl⟩ : syracuseStep 918215 = 1377323) B1377323
theorem B1377017 : Blo 610295 1377017 := bstep (se 2 (by rfl) ⟨516381, by rfl⟩ : syracuseStep 1377017 = 1032763) B1032763
theorem B2327363 : Blo 610295 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B7537481 : Blo 610295 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B918377 : Blo 610295 918377 := bstep (se 2 (by rfl) ⟨344391, by rfl⟩ : syracuseStep 918377 = 688783) B688783
theorem B4195219 : Blo 610295 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B689071 : Blo 610295 689071 := bstep (se 1 (by rfl) ⟨516803, by rfl⟩ : syracuseStep 689071 = 1033607) B1033607
theorem B918455 : Blo 610295 918455 := bstep (se 1 (by rfl) ⟨688841, by rfl⟩ : syracuseStep 918455 = 1377683) B1377683
theorem B8258507 : Blo 610295 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B918491 : Blo 610295 918491 := bstep (se 1 (by rfl) ⟨688868, by rfl⟩ : syracuseStep 918491 = 1377737) B1377737
theorem B2950145 : Blo 610295 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1377287 : Blo 610295 1377287 := bstep (se 1 (by rfl) ⟨1032965, by rfl⟩ : syracuseStep 1377287 = 2065931) B2065931
theorem B1475603 : Blo 610295 1475603 := bstep (se 1 (by rfl) ⟨1106702, by rfl⟩ : syracuseStep 1475603 = 2213405) B2213405
theorem B1967161 : Blo 610295 1967161 := bstep (se 2 (by rfl) ⟨737685, by rfl⟩ : syracuseStep 1967161 = 1475371) B1475371
theorem B1377359 : Blo 610295 1377359 := bstep (se 1 (by rfl) ⟨1033019, by rfl⟩ : syracuseStep 1377359 = 2066039) B2066039
theorem B1967275 : Blo 610295 1967275 := bstep (se 1 (by rfl) ⟨1475456, by rfl⟩ : syracuseStep 1967275 = 2950913) B2950913
theorem B689503 : Blo 610295 689503 := bstep (se 1 (by rfl) ⟨517127, by rfl⟩ : syracuseStep 689503 = 1034255) B1034255
theorem B2065769 : Blo 610295 2065769 := bstep (se 2 (by rfl) ⟨774663, by rfl⟩ : syracuseStep 2065769 = 1549327) B1549327
theorem B8390051 : Blo 610295 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B918959 : Blo 610295 918959 := bstep (se 1 (by rfl) ⟨689219, by rfl⟩ : syracuseStep 918959 = 1378439) B1378439
theorem B1377755 : Blo 610295 1377755 := bstep (se 1 (by rfl) ⟨1033316, by rfl⟩ : syracuseStep 1377755 = 2066633) B2066633
theorem B7865819 : Blo 610295 7865819 := bstep (se 1 (by rfl) ⟨5899364, by rfl⟩ : syracuseStep 7865819 = 11798729) B11798729
theorem B919049 : Blo 610295 919049 := bstep (se 2 (by rfl) ⟨344643, by rfl⟩ : syracuseStep 919049 = 689287) B689287
theorem B919079 : Blo 610295 919079 := bstep (se 1 (by rfl) ⟨689309, by rfl⟩ : syracuseStep 919079 = 1378619) B1378619
theorem B919163 : Blo 610295 919163 := bstep (se 1 (by rfl) ⟨689372, by rfl⟩ : syracuseStep 919163 = 1378745) B1378745
theorem B5867153 : Blo 610295 5867153 := bstep (se 2 (by rfl) ⟨2200182, by rfl⟩ : syracuseStep 5867153 = 4400365) B4400365
theorem B689863 : Blo 610295 689863 := bstep (se 1 (by rfl) ⟨517397, by rfl⟩ : syracuseStep 689863 = 1034795) B1034795
theorem B919289 : Blo 610295 919289 := bstep (se 2 (by rfl) ⟨344733, by rfl⟩ : syracuseStep 919289 = 689467) B689467
theorem B4654907 : Blo 610295 4654907 := bstep (se 1 (by rfl) ⟨3491180, by rfl⟩ : syracuseStep 4654907 = 6982361) B6982361
theorem B1410911 : Blo 610295 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B919391 : Blo 610295 919391 := bstep (se 1 (by rfl) ⟨689543, by rfl⟩ : syracuseStep 919391 = 1379087) B1379087
theorem B919403 : Blo 610295 919403 := bstep (se 1 (by rfl) ⟨689552, by rfl⟩ : syracuseStep 919403 = 1379105) B1379105
theorem B1378223 : Blo 610295 1378223 := bstep (se 1 (by rfl) ⟨1033667, by rfl⟩ : syracuseStep 1378223 = 2067335) B2067335
theorem B2066363 : Blo 610295 2066363 := bstep (se 1 (by rfl) ⟨1549772, by rfl⟩ : syracuseStep 2066363 = 3099545) B3099545
theorem B919631 : Blo 610295 919631 := bstep (se 1 (by rfl) ⟨689723, by rfl⟩ : syracuseStep 919631 = 1379447) B1379447
theorem B1378475 : Blo 610295 1378475 := bstep (se 1 (by rfl) ⟨1033856, by rfl⟩ : syracuseStep 1378475 = 2067713) B2067713
theorem B919751 : Blo 610295 919751 := bstep (se 1 (by rfl) ⟨689813, by rfl⟩ : syracuseStep 919751 = 1379627) B1379627
theorem B919913 : Blo 610295 919913 := bstep (se 2 (by rfl) ⟨344967, by rfl⟩ : syracuseStep 919913 = 689935) B689935
theorem B919991 : Blo 610295 919991 := bstep (se 1 (by rfl) ⟨689993, by rfl⟩ : syracuseStep 919991 = 1379987) B1379987
theorem B2329033 : Blo 610295 2329033 := bstep (se 2 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 2329033 = 1746775) B1746775
theorem B920027 : Blo 610295 920027 := bstep (se 1 (by rfl) ⟨690020, by rfl⟩ : syracuseStep 920027 = 1380041) B1380041
theorem B1739303 : Blo 610295 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B690727 : Blo 610295 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B16714421 : Blo 610295 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1379015 : Blo 610295 1379015 := bstep (se 1 (by rfl) ⟨1034261, by rfl⟩ : syracuseStep 1379015 = 2068523) B2068523
theorem B2329337 : Blo 610295 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B2329505 : Blo 610295 2329505 := bstep (se 2 (by rfl) ⟨873564, by rfl⟩ : syracuseStep 2329505 = 1747129) B1747129
theorem B2329519 : Blo 610295 2329519 := bstep (se 1 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 2329519 = 3494279) B3494279
theorem B920495 : Blo 610295 920495 := bstep (se 1 (by rfl) ⟨690371, by rfl⟩ : syracuseStep 920495 = 1380743) B1380743
theorem B920585 : Blo 610295 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B920615 : Blo 610295 920615 := bstep (se 1 (by rfl) ⟨690461, by rfl⟩ : syracuseStep 920615 = 1380923) B1380923
theorem B36211799 : Blo 610295 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B920699 : Blo 610295 920699 := bstep (se 1 (by rfl) ⟨690524, by rfl⟩ : syracuseStep 920699 = 1381049) B1381049
theorem B920825 : Blo 610295 920825 := bstep (se 2 (by rfl) ⟨345309, by rfl⟩ : syracuseStep 920825 = 690619) B690619
theorem B920927 : Blo 610295 920927 := bstep (se 1 (by rfl) ⟨690695, by rfl⟩ : syracuseStep 920927 = 1381391) B1381391
theorem B920939 : Blo 610295 920939 := bstep (se 1 (by rfl) ⟨690704, by rfl⟩ : syracuseStep 920939 = 1381409) B1381409
theorem B22351277 : Blo 610295 22351277 := bstep (se 3 (by rfl) ⟨4190864, by rfl⟩ : syracuseStep 22351277 = 8381729) B8381729
theorem B1379879 : Blo 610295 1379879 := bstep (se 1 (by rfl) ⟨1034909, by rfl⟩ : syracuseStep 1379879 = 2069819) B2069819
theorem B921167 : Blo 610295 921167 := bstep (se 1 (by rfl) ⟨690875, by rfl⟩ : syracuseStep 921167 = 1381751) B1381751
theorem B2068091 : Blo 610295 2068091 := bstep (se 1 (by rfl) ⟨1551068, by rfl⟩ : syracuseStep 2068091 = 3102137) B3102137
theorem B6295163 : Blo 610295 6295163 := bstep (se 1 (by rfl) ⟨4721372, by rfl⟩ : syracuseStep 6295163 = 9442745) B9442745
theorem B921287 : Blo 610295 921287 := bstep (se 1 (by rfl) ⟨690965, by rfl⟩ : syracuseStep 921287 = 1381931) B1381931
theorem B11767517 : Blo 610295 11767517 := bstep (se 3 (by rfl) ⟨2206409, by rfl⟩ : syracuseStep 11767517 = 4412819) B4412819
theorem B2068253 : Blo 610295 2068253 := bstep (se 3 (by rfl) ⟨387797, by rfl⟩ : syracuseStep 2068253 = 775595) B775595
theorem B1380203 : Blo 610295 1380203 := bstep (se 1 (by rfl) ⟨1035152, by rfl⟩ : syracuseStep 1380203 = 2070305) B2070305
theorem B2330477 : Blo 610295 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B7868279 : Blo 610295 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B5246855 : Blo 610295 5246855 := bstep (se 1 (by rfl) ⟨3935141, by rfl⟩ : syracuseStep 5246855 = 7870283) B7870283
theorem B1380257 : Blo 610295 1380257 := bstep (se 2 (by rfl) ⟨517596, by rfl⟩ : syracuseStep 1380257 = 1035193) B1035193
theorem B2330795 : Blo 610295 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B1380599 : Blo 610295 1380599 := bstep (se 1 (by rfl) ⟨1035449, by rfl⟩ : syracuseStep 1380599 = 2070899) B2070899
theorem B2068955 : Blo 610295 2068955 := bstep (se 1 (by rfl) ⟨1551716, by rfl⟩ : syracuseStep 2068955 = 3103433) B3103433
theorem B6296237 : Blo 610295 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1544903 : Blo 610295 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B1544953 : Blo 610295 1544953 := bstep (se 2 (by rfl) ⟨579357, by rfl⟩ : syracuseStep 1544953 = 1158715) B1158715
theorem B1381193 : Blo 610295 1381193 := bstep (se 2 (by rfl) ⟨517947, by rfl⟩ : syracuseStep 1381193 = 1035895) B1035895
theorem B2790553 : Blo 610295 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B2069657 : Blo 610295 2069657 := bstep (se 2 (by rfl) ⟨776121, by rfl⟩ : syracuseStep 2069657 = 1552243) B1552243
theorem B1545601 : Blo 610295 1545601 := bstep (se 2 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 1545601 = 1159201) B1159201
theorem B3478949 : Blo 610295 3478949 := bstep (se 4 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 3478949 = 652303) B652303
theorem B6985277 : Blo 610295 6985277 := bstep (se 3 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 6985277 = 2619479) B2619479
theorem B1381985 : Blo 610295 1381985 := bstep (se 2 (by rfl) ⟨518244, by rfl⟩ : syracuseStep 1381985 = 1036489) B1036489
theorem B4659281 : Blo 610295 4659281 := bstep (se 2 (by rfl) ⟨1747230, by rfl⟩ : syracuseStep 4659281 = 3494461) B3494461
theorem B1546411 : Blo 610295 1546411 := bstep (se 1 (by rfl) ⟨1159808, by rfl⟩ : syracuseStep 1546411 = 2319617) B2319617
theorem B2070845 : Blo 610295 2070845 := bstep (se 3 (by rfl) ⟨388283, by rfl⟩ : syracuseStep 2070845 = 776567) B776567
theorem B5871959 : Blo 610295 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B1546715 : Blo 610295 1546715 := bstep (se 1 (by rfl) ⟨1160036, by rfl⟩ : syracuseStep 1546715 = 2320073) B2320073
theorem B9935405 : Blo 610295 9935405 := bstep (se 3 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 9935405 = 3725777) B3725777
theorem B3316663 : Blo 610295 3316663 := bstep (se 1 (by rfl) ⟨2487497, by rfl⟩ : syracuseStep 3316663 = 4974995) B4974995
theorem B2071709 : Blo 610295 2071709 := bstep (se 3 (by rfl) ⟨388445, by rfl⟩ : syracuseStep 2071709 = 776891) B776891
theorem B2072249 : Blo 610295 2072249 := bstep (se 2 (by rfl) ⟨777093, by rfl⟩ : syracuseStep 2072249 = 1554187) B1554187
theorem B4955863 : Blo 610295 4955863 := bstep (se 1 (by rfl) ⟨3716897, by rfl⟩ : syracuseStep 4955863 = 7433795) B7433795
theorem B827231 : Blo 610295 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B1548193 : Blo 610295 1548193 := bstep (se 2 (by rfl) ⟨580572, by rfl⟩ : syracuseStep 1548193 = 1161145) B1161145
theorem B2203843 : Blo 610295 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B2072843 : Blo 610295 2072843 := bstep (se 1 (by rfl) ⟨1554632, by rfl⟩ : syracuseStep 2072843 = 3109265) B3109265
theorem B2073113 : Blo 610295 2073113 := bstep (se 2 (by rfl) ⟨777417, by rfl⟩ : syracuseStep 2073113 = 1554835) B1554835
theorem B3482297 : Blo 610295 3482297 := bstep (se 2 (by rfl) ⟨1305861, by rfl⟩ : syracuseStep 3482297 = 2611723) B2611723
theorem B37692161 : Blo 610295 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B3352103 : Blo 610295 3352103 := bstep (se 1 (by rfl) ⟨2514077, by rfl⟩ : syracuseStep 3352103 = 5028155) B5028155
theorem B149038841 : Blo 610295 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B5875649 : Blo 610295 5875649 := bstep (se 2 (by rfl) ⟨2203368, by rfl⟩ : syracuseStep 5875649 = 4406737) B4406737
theorem B1550735 : Blo 610295 1550735 := bstep (se 1 (by rfl) ⟨1163051, by rfl⟩ : syracuseStep 1550735 = 2326103) B2326103
theorem B928379 : Blo 610295 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B1747595 : Blo 610295 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B1551059 : Blo 610295 1551059 := bstep (se 1 (by rfl) ⟨1163294, by rfl⟩ : syracuseStep 1551059 = 2326589) B2326589
theorem B4664141 : Blo 610295 4664141 := bstep (se 3 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 4664141 = 1749053) B1749053
theorem B2206727 : Blo 610295 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B929017 : Blo 610295 929017 := bstep (se 2 (by rfl) ⟨348381, by rfl⟩ : syracuseStep 929017 = 696763) B696763
theorem B3910949 : Blo 610295 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B16166279 : Blo 610295 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B3091931 : Blo 610295 3091931 := bstep (se 1 (by rfl) ⟨2318948, by rfl⟩ : syracuseStep 3091931 = 4637897) B4637897
theorem B8957405 : Blo 610295 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B1552223 : Blo 610295 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B1159019 : Blo 610295 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B6959033 : Blo 610295 6959033 := bstep (se 2 (by rfl) ⟨2609637, by rfl⟩ : syracuseStep 6959033 = 5219275) B5219275
theorem B3092417 : Blo 610295 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B4960271 : Blo 610295 4960271 := bstep (se 1 (by rfl) ⟨3720203, by rfl⟩ : syracuseStep 4960271 = 7440407) B7440407
theorem B1159247 : Blo 610295 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B1159687 : Blo 610295 1159687 := bstep (se 1 (by rfl) ⟨869765, by rfl⟩ : syracuseStep 1159687 = 1739531) B1739531
theorem B1553327 : Blo 610295 1553327 := bstep (se 1 (by rfl) ⟨1164995, by rfl⟩ : syracuseStep 1553327 = 2329991) B2329991
theorem B1160743 : Blo 610295 1160743 := bstep (se 1 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 1160743 = 1741115) B1741115
theorem B1029881 : Blo 610295 1029881 := bstep (se 2 (by rfl) ⟨386205, by rfl⟩ : syracuseStep 1029881 = 772411) B772411
theorem B1030063 : Blo 610295 1030063 := bstep (se 1 (by rfl) ⟨772547, by rfl⟩ : syracuseStep 1030063 = 1545095) B1545095
theorem B1030151 : Blo 610295 1030151 := bstep (se 1 (by rfl) ⟨772613, by rfl⟩ : syracuseStep 1030151 = 1545227) B1545227
theorem B1554511 : Blo 610295 1554511 := bstep (se 1 (by rfl) ⟨1165883, by rfl⟩ : syracuseStep 1554511 = 2331767) B2331767
theorem B4241497 : Blo 610295 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B3094685 : Blo 610295 3094685 := bstep (se 3 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 3094685 = 1160507) B1160507
theorem B1030495 : Blo 610295 1030495 := bstep (se 1 (by rfl) ⟨772871, by rfl⟩ : syracuseStep 1030495 = 1545743) B1545743
theorem B3488129 : Blo 610295 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B1030583 : Blo 610295 1030583 := bstep (se 1 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 1030583 = 1545875) B1545875
theorem B2800187 : Blo 610295 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B1915607 : Blo 610295 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B6961949 : Blo 610295 6961949 := bstep (se 3 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 6961949 = 2610731) B2610731
theorem B1031177 : Blo 610295 1031177 := bstep (se 2 (by rfl) ⟨386691, by rfl⟩ : syracuseStep 1031177 = 773383) B773383
theorem B1031339 : Blo 610295 1031339 := bstep (se 1 (by rfl) ⟨773504, by rfl⟩ : syracuseStep 1031339 = 1547009) B1547009
theorem B1162451 : Blo 610295 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B1162603 : Blo 610295 1162603 := bstep (se 1 (by rfl) ⟨871952, by rfl⟩ : syracuseStep 1162603 = 1743905) B1743905
theorem B3095981 : Blo 610295 3095981 := bstep (se 3 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 3095981 = 1160993) B1160993
theorem B9453095 : Blo 610295 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B1031737 : Blo 610295 1031737 := bstep (se 2 (by rfl) ⟨386901, by rfl⟩ : syracuseStep 1031737 = 773803) B773803
theorem B1162831 : Blo 610295 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B1031879 : Blo 610295 1031879 := bstep (se 1 (by rfl) ⟨773909, by rfl⟩ : syracuseStep 1031879 = 1547819) B1547819
theorem B1032041 : Blo 610295 1032041 := bstep (se 2 (by rfl) ⟨387015, by rfl⟩ : syracuseStep 1032041 = 774031) B774031
theorem B2211745 : Blo 610295 2211745 := bstep (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) B1658809
theorem B5980175 : Blo 610295 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B40714285 : Blo 610295 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B1032439 : Blo 610295 1032439 := bstep (se 1 (by rfl) ⟨774329, by rfl⟩ : syracuseStep 1032439 = 1548659) B1548659
theorem B6635837 : Blo 610295 6635837 := bstep (se 3 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 6635837 = 2488439) B2488439
theorem B1032635 : Blo 610295 1032635 := bstep (se 1 (by rfl) ⟨774476, by rfl⟩ : syracuseStep 1032635 = 1548953) B1548953
theorem B1032743 : Blo 610295 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B9585211 : Blo 610295 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B2474819 : Blo 610295 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B1033033 : Blo 610295 1033033 := bstep (se 2 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 1033033 = 774775) B774775
theorem B1033067 : Blo 610295 1033067 := bstep (se 1 (by rfl) ⟨774800, by rfl⟩ : syracuseStep 1033067 = 1549601) B1549601
theorem B3097601 : Blo 610295 3097601 := bstep (se 2 (by rfl) ⟨1161600, by rfl⟩ : syracuseStep 3097601 = 2323201) B2323201
theorem B5293259 : Blo 610295 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B1033465 : Blo 610295 1033465 := bstep (se 2 (by rfl) ⟨387549, by rfl⟩ : syracuseStep 1033465 = 775099) B775099
theorem B1033735 : Blo 610295 1033735 := bstep (se 1 (by rfl) ⟨775301, by rfl⟩ : syracuseStep 1033735 = 1550603) B1550603
theorem B3098411 : Blo 610295 3098411 := bstep (se 1 (by rfl) ⟨2323808, by rfl⟩ : syracuseStep 3098411 = 4647617) B4647617
theorem B19384109 : Blo 610295 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B1034167 : Blo 610295 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B1034363 : Blo 610295 1034363 := bstep (se 1 (by rfl) ⟨775772, by rfl⟩ : syracuseStep 1034363 = 1551545) B1551545
theorem B1034761 : Blo 610295 1034761 := bstep (se 2 (by rfl) ⟨388035, by rfl⟩ : syracuseStep 1034761 = 776071) B776071
theorem B1034923 : Blo 610295 1034923 := bstep (se 1 (by rfl) ⟨776192, by rfl⟩ : syracuseStep 1034923 = 1552385) B1552385
theorem B26889029 : Blo 610295 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B7457629 : Blo 610295 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B3918739 : Blo 610295 3918739 := bstep (se 1 (by rfl) ⟨2939054, by rfl⟩ : syracuseStep 3918739 = 5878109) B5878109
theorem B2476975 : Blo 610295 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B1035227 : Blo 610295 1035227 := bstep (se 1 (by rfl) ⟨776420, by rfl⟩ : syracuseStep 1035227 = 1552841) B1552841
theorem B11455681 : Blo 610295 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B1100999 : Blo 610295 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B1035463 : Blo 610295 1035463 := bstep (se 1 (by rfl) ⟨776597, by rfl⟩ : syracuseStep 1035463 = 1553195) B1553195
theorem B4410571 : Blo 610295 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B1035625 : Blo 610295 1035625 := bstep (se 2 (by rfl) ⟨388359, by rfl⟩ : syracuseStep 1035625 = 776719) B776719
theorem B871975 : Blo 610295 871975 := bstep (se 1 (by rfl) ⟨653981, by rfl⟩ : syracuseStep 871975 = 1307963) B1307963
theorem B4476539 : Blo 610295 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B2477753 : Blo 610295 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B9424775 : Blo 610295 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B1036219 : Blo 610295 1036219 := bstep (se 1 (by rfl) ⟨777164, by rfl⟩ : syracuseStep 1036219 = 1554329) B1554329
theorem B3100679 : Blo 610295 3100679 := bstep (se 1 (by rfl) ⟨2325509, by rfl⟩ : syracuseStep 3100679 = 4651019) B4651019
theorem B610343 : Blo 610295 610343 := bstep (se 1 (by rfl) ⟨457757, by rfl⟩ : syracuseStep 610343 = 915515) B915515
theorem B1036327 : Blo 610295 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B610383 : Blo 610295 610383 := bstep (se 1 (by rfl) ⟨457787, by rfl⟩ : syracuseStep 610383 = 915575) B915575
theorem B610399 : Blo 610295 610399 := bstep (se 1 (by rfl) ⟨457799, by rfl⟩ : syracuseStep 610399 = 915599) B915599
theorem B610427 : Blo 610295 610427 := bstep (se 1 (by rfl) ⟨457820, by rfl⟩ : syracuseStep 610427 = 915641) B915641
theorem B610479 : Blo 610295 610479 := bstep (se 1 (by rfl) ⟨457859, by rfl⟩ : syracuseStep 610479 = 915719) B915719
theorem B610503 : Blo 610295 610503 := bstep (se 1 (by rfl) ⟨457877, by rfl⟩ : syracuseStep 610503 = 915755) B915755
theorem B610523 : Blo 610295 610523 := bstep (se 1 (by rfl) ⟨457892, by rfl⟩ : syracuseStep 610523 = 915785) B915785
theorem B610599 : Blo 610295 610599 := bstep (se 1 (by rfl) ⟨457949, by rfl⟩ : syracuseStep 610599 = 915899) B915899
theorem B610639 : Blo 610295 610639 := bstep (se 1 (by rfl) ⟨457979, by rfl⟩ : syracuseStep 610639 = 915959) B915959
theorem B610655 : Blo 610295 610655 := bstep (se 1 (by rfl) ⟨457991, by rfl⟩ : syracuseStep 610655 = 915983) B915983
theorem B610683 : Blo 610295 610683 := bstep (se 1 (by rfl) ⟨458012, by rfl⟩ : syracuseStep 610683 = 916025) B916025
theorem B610735 : Blo 610295 610735 := bstep (se 1 (by rfl) ⟨458051, by rfl⟩ : syracuseStep 610735 = 916103) B916103
theorem B610759 : Blo 610295 610759 := bstep (se 1 (by rfl) ⟨458069, by rfl⟩ : syracuseStep 610759 = 916139) B916139
theorem B610779 : Blo 610295 610779 := bstep (se 1 (by rfl) ⟨458084, by rfl⟩ : syracuseStep 610779 = 916169) B916169
theorem B3101165 : Blo 610295 3101165 := bstep (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) B1162937
theorem B610855 : Blo 610295 610855 := bstep (se 1 (by rfl) ⟨458141, by rfl⟩ : syracuseStep 610855 = 916283) B916283
theorem B610895 : Blo 610295 610895 := bstep (se 1 (by rfl) ⟨458171, by rfl⟩ : syracuseStep 610895 = 916343) B916343
theorem B610911 : Blo 610295 610911 := bstep (se 1 (by rfl) ⟨458183, by rfl⟩ : syracuseStep 610911 = 916367) B916367
theorem B8802917 : Blo 610295 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B610939 : Blo 610295 610939 := bstep (se 1 (by rfl) ⟨458204, by rfl⟩ : syracuseStep 610939 = 916409) B916409
theorem B610991 : Blo 610295 610991 := bstep (se 1 (by rfl) ⟨458243, by rfl⟩ : syracuseStep 610991 = 916487) B916487
theorem B611015 : Blo 610295 611015 := bstep (se 1 (by rfl) ⟨458261, by rfl⟩ : syracuseStep 611015 = 916523) B916523
theorem B611035 : Blo 610295 611035 := bstep (se 1 (by rfl) ⟨458276, by rfl⟩ : syracuseStep 611035 = 916553) B916553
theorem B611111 : Blo 610295 611111 := bstep (se 1 (by rfl) ⟨458333, by rfl⟩ : syracuseStep 611111 = 916667) B916667
theorem B611151 : Blo 610295 611151 := bstep (se 1 (by rfl) ⟨458363, by rfl⟩ : syracuseStep 611151 = 916727) B916727
theorem B611167 : Blo 610295 611167 := bstep (se 1 (by rfl) ⟨458375, by rfl⟩ : syracuseStep 611167 = 916751) B916751
theorem B611195 : Blo 610295 611195 := bstep (se 1 (by rfl) ⟨458396, by rfl⟩ : syracuseStep 611195 = 916793) B916793
theorem B611247 : Blo 610295 611247 := bstep (se 1 (by rfl) ⟨458435, by rfl⟩ : syracuseStep 611247 = 916871) B916871
theorem B611271 : Blo 610295 611271 := bstep (se 1 (by rfl) ⟨458453, by rfl⟩ : syracuseStep 611271 = 916907) B916907
theorem B611291 : Blo 610295 611291 := bstep (se 1 (by rfl) ⟨458468, by rfl⟩ : syracuseStep 611291 = 916937) B916937
theorem B611367 : Blo 610295 611367 := bstep (se 1 (by rfl) ⟨458525, by rfl⟩ : syracuseStep 611367 = 917051) B917051
theorem B611407 : Blo 610295 611407 := bstep (se 1 (by rfl) ⟨458555, by rfl⟩ : syracuseStep 611407 = 917111) B917111
theorem B611423 : Blo 610295 611423 := bstep (se 1 (by rfl) ⟨458567, by rfl⟩ : syracuseStep 611423 = 917135) B917135
theorem B611451 : Blo 610295 611451 := bstep (se 1 (by rfl) ⟨458588, by rfl⟩ : syracuseStep 611451 = 917177) B917177
theorem B611503 : Blo 610295 611503 := bstep (se 1 (by rfl) ⟨458627, by rfl⟩ : syracuseStep 611503 = 917255) B917255
theorem B611527 : Blo 610295 611527 := bstep (se 1 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 611527 = 917291) B917291
theorem B611547 : Blo 610295 611547 := bstep (se 1 (by rfl) ⟨458660, by rfl⟩ : syracuseStep 611547 = 917321) B917321
theorem B3101975 : Blo 610295 3101975 := bstep (se 1 (by rfl) ⟨2326481, by rfl⟩ : syracuseStep 3101975 = 4652963) B4652963
theorem B611623 : Blo 610295 611623 := bstep (se 1 (by rfl) ⟨458717, by rfl⟩ : syracuseStep 611623 = 917435) B917435
theorem B611663 : Blo 610295 611663 := bstep (se 1 (by rfl) ⟨458747, by rfl⟩ : syracuseStep 611663 = 917495) B917495
theorem B611679 : Blo 610295 611679 := bstep (se 1 (by rfl) ⟨458759, by rfl⟩ : syracuseStep 611679 = 917519) B917519
theorem B611707 : Blo 610295 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B611759 : Blo 610295 611759 := bstep (se 1 (by rfl) ⟨458819, by rfl⟩ : syracuseStep 611759 = 917639) B917639
theorem B611783 : Blo 610295 611783 := bstep (se 1 (by rfl) ⟨458837, by rfl⟩ : syracuseStep 611783 = 917675) B917675
theorem B611803 : Blo 610295 611803 := bstep (se 1 (by rfl) ⟨458852, by rfl⟩ : syracuseStep 611803 = 917705) B917705
theorem B6280715 : Blo 610295 6280715 := bstep (se 1 (by rfl) ⟨4710536, by rfl⟩ : syracuseStep 6280715 = 9421073) B9421073
theorem B611879 : Blo 610295 611879 := bstep (se 1 (by rfl) ⟨458909, by rfl⟩ : syracuseStep 611879 = 917819) B917819
theorem B611919 : Blo 610295 611919 := bstep (se 1 (by rfl) ⟨458939, by rfl⟩ : syracuseStep 611919 = 917879) B917879
theorem B611935 : Blo 610295 611935 := bstep (se 1 (by rfl) ⟨458951, by rfl⟩ : syracuseStep 611935 = 917903) B917903
theorem B611963 : Blo 610295 611963 := bstep (se 1 (by rfl) ⟨458972, by rfl⟩ : syracuseStep 611963 = 917945) B917945
theorem B612015 : Blo 610295 612015 := bstep (se 1 (by rfl) ⟨459011, by rfl⟩ : syracuseStep 612015 = 918023) B918023
theorem B612039 : Blo 610295 612039 := bstep (se 1 (by rfl) ⟨459029, by rfl⟩ : syracuseStep 612039 = 918059) B918059
theorem B612059 : Blo 610295 612059 := bstep (se 1 (by rfl) ⟨459044, by rfl⟩ : syracuseStep 612059 = 918089) B918089
theorem B612135 : Blo 610295 612135 := bstep (se 1 (by rfl) ⟨459101, by rfl⟩ : syracuseStep 612135 = 918203) B918203
theorem B612175 : Blo 610295 612175 := bstep (se 1 (by rfl) ⟨459131, by rfl⟩ : syracuseStep 612175 = 918263) B918263
theorem B612191 : Blo 610295 612191 := bstep (se 1 (by rfl) ⟨459143, by rfl⟩ : syracuseStep 612191 = 918287) B918287
theorem B612219 : Blo 610295 612219 := bstep (se 1 (by rfl) ⟨459164, by rfl⟩ : syracuseStep 612219 = 918329) B918329
theorem B612271 : Blo 610295 612271 := bstep (se 1 (by rfl) ⟨459203, by rfl⟩ : syracuseStep 612271 = 918407) B918407
theorem B612295 : Blo 610295 612295 := bstep (se 1 (by rfl) ⟨459221, by rfl⟩ : syracuseStep 612295 = 918443) B918443
theorem B612315 : Blo 610295 612315 := bstep (se 1 (by rfl) ⟨459236, by rfl⟩ : syracuseStep 612315 = 918473) B918473
theorem B612391 : Blo 610295 612391 := bstep (se 1 (by rfl) ⟨459293, by rfl⟩ : syracuseStep 612391 = 918587) B918587
theorem B1103911 : Blo 610295 1103911 := bstep (se 1 (by rfl) ⟨827933, by rfl⟩ : syracuseStep 1103911 = 1655867) B1655867
theorem B1955897 : Blo 610295 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B612431 : Blo 610295 612431 := bstep (se 1 (by rfl) ⟨459323, by rfl⟩ : syracuseStep 612431 = 918647) B918647
theorem B612447 : Blo 610295 612447 := bstep (se 1 (by rfl) ⟨459335, by rfl⟩ : syracuseStep 612447 = 918671) B918671
theorem B612475 : Blo 610295 612475 := bstep (se 1 (by rfl) ⟨459356, by rfl⟩ : syracuseStep 612475 = 918713) B918713
theorem B612527 : Blo 610295 612527 := bstep (se 1 (by rfl) ⟨459395, by rfl⟩ : syracuseStep 612527 = 918791) B918791
theorem B612551 : Blo 610295 612551 := bstep (se 1 (by rfl) ⟨459413, by rfl⟩ : syracuseStep 612551 = 918827) B918827
theorem B612571 : Blo 610295 612571 := bstep (se 1 (by rfl) ⟨459428, by rfl⟩ : syracuseStep 612571 = 918857) B918857
theorem B11163905 : Blo 610295 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B612647 : Blo 610295 612647 := bstep (se 1 (by rfl) ⟨459485, by rfl⟩ : syracuseStep 612647 = 918971) B918971
theorem B612687 : Blo 610295 612687 := bstep (se 1 (by rfl) ⟨459515, by rfl⟩ : syracuseStep 612687 = 919031) B919031
theorem B612703 : Blo 610295 612703 := bstep (se 1 (by rfl) ⟨459527, by rfl⟩ : syracuseStep 612703 = 919055) B919055
theorem B612731 : Blo 610295 612731 := bstep (se 1 (by rfl) ⟨459548, by rfl⟩ : syracuseStep 612731 = 919097) B919097
theorem B612783 : Blo 610295 612783 := bstep (se 1 (by rfl) ⟨459587, by rfl⟩ : syracuseStep 612783 = 919175) B919175
theorem B776623 : Blo 610295 776623 := bstep (se 1 (by rfl) ⟨582467, by rfl⟩ : syracuseStep 776623 = 1164935) B1164935
theorem B612807 : Blo 610295 612807 := bstep (se 1 (by rfl) ⟨459605, by rfl⟩ : syracuseStep 612807 = 919211) B919211
theorem B612827 : Blo 610295 612827 := bstep (se 1 (by rfl) ⟨459620, by rfl⟩ : syracuseStep 612827 = 919241) B919241
theorem B612903 : Blo 610295 612903 := bstep (se 1 (by rfl) ⟨459677, by rfl⟩ : syracuseStep 612903 = 919355) B919355
theorem B612943 : Blo 610295 612943 := bstep (se 1 (by rfl) ⟨459707, by rfl⟩ : syracuseStep 612943 = 919415) B919415
theorem B612959 : Blo 610295 612959 := bstep (se 1 (by rfl) ⟨459719, by rfl⟩ : syracuseStep 612959 = 919439) B919439
theorem B612987 : Blo 610295 612987 := bstep (se 1 (by rfl) ⟨459740, by rfl⟩ : syracuseStep 612987 = 919481) B919481
theorem B613039 : Blo 610295 613039 := bstep (se 1 (by rfl) ⟨459779, by rfl⟩ : syracuseStep 613039 = 919559) B919559
theorem B613063 : Blo 610295 613063 := bstep (se 1 (by rfl) ⟨459797, by rfl⟩ : syracuseStep 613063 = 919595) B919595
theorem B613083 : Blo 610295 613083 := bstep (se 1 (by rfl) ⟨459812, by rfl⟩ : syracuseStep 613083 = 919625) B919625
theorem B50420465 : Blo 610295 50420465 := bstep (se 2 (by rfl) ⟨18907674, by rfl⟩ : syracuseStep 50420465 = 37815349) B37815349
theorem B2611997 : Blo 610295 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B613159 : Blo 610295 613159 := bstep (se 1 (by rfl) ⟨459869, by rfl⟩ : syracuseStep 613159 = 919739) B919739
theorem B613199 : Blo 610295 613199 := bstep (se 1 (by rfl) ⟨459899, by rfl⟩ : syracuseStep 613199 = 919799) B919799
theorem B613215 : Blo 610295 613215 := bstep (se 1 (by rfl) ⟨459911, by rfl⟩ : syracuseStep 613215 = 919823) B919823
theorem B3103595 : Blo 610295 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B613243 : Blo 610295 613243 := bstep (se 1 (by rfl) ⟨459932, by rfl⟩ : syracuseStep 613243 = 919865) B919865
theorem B4643729 : Blo 610295 4643729 := bstep (se 2 (by rfl) ⟨1741398, by rfl⟩ : syracuseStep 4643729 = 3482797) B3482797
theorem B613295 : Blo 610295 613295 := bstep (se 1 (by rfl) ⟨459971, by rfl⟩ : syracuseStep 613295 = 919943) B919943
theorem B613319 : Blo 610295 613319 := bstep (se 1 (by rfl) ⟨459989, by rfl⟩ : syracuseStep 613319 = 919979) B919979
theorem B613339 : Blo 610295 613339 := bstep (se 1 (by rfl) ⟨460004, by rfl⟩ : syracuseStep 613339 = 920009) B920009
theorem B613415 : Blo 610295 613415 := bstep (se 1 (by rfl) ⟨460061, by rfl⟩ : syracuseStep 613415 = 920123) B920123
theorem B2317369 : Blo 610295 2317369 := bstep (se 2 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 2317369 = 1738027) B1738027
theorem B8805455 : Blo 610295 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B6282319 : Blo 610295 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B613455 : Blo 610295 613455 := bstep (se 1 (by rfl) ⟨460091, by rfl⟩ : syracuseStep 613455 = 920183) B920183
theorem B613471 : Blo 610295 613471 := bstep (se 1 (by rfl) ⟨460103, by rfl⟩ : syracuseStep 613471 = 920207) B920207
theorem B613499 : Blo 610295 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B613551 : Blo 610295 613551 := bstep (se 1 (by rfl) ⟨460163, by rfl⟩ : syracuseStep 613551 = 920327) B920327
theorem B613575 : Blo 610295 613575 := bstep (se 1 (by rfl) ⟨460181, by rfl⟩ : syracuseStep 613575 = 920363) B920363
theorem B613595 : Blo 610295 613595 := bstep (se 1 (by rfl) ⟨460196, by rfl⟩ : syracuseStep 613595 = 920393) B920393
theorem B613671 : Blo 610295 613671 := bstep (se 1 (by rfl) ⟨460253, by rfl⟩ : syracuseStep 613671 = 920507) B920507
theorem B613711 : Blo 610295 613711 := bstep (se 1 (by rfl) ⟨460283, by rfl⟩ : syracuseStep 613711 = 920567) B920567
theorem B613727 : Blo 610295 613727 := bstep (se 1 (by rfl) ⟨460295, by rfl⟩ : syracuseStep 613727 = 920591) B920591
theorem B2317673 : Blo 610295 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B613755 : Blo 610295 613755 := bstep (se 1 (by rfl) ⟨460316, by rfl⟩ : syracuseStep 613755 = 920633) B920633
theorem B613807 : Blo 610295 613807 := bstep (se 1 (by rfl) ⟨460355, by rfl⟩ : syracuseStep 613807 = 920711) B920711
theorem B613831 : Blo 610295 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B2612681 : Blo 610295 2612681 := bstep (se 2 (by rfl) ⟨979755, by rfl⟩ : syracuseStep 2612681 = 1959511) B1959511
theorem B613851 : Blo 610295 613851 := bstep (se 1 (by rfl) ⟨460388, by rfl⟩ : syracuseStep 613851 = 920777) B920777
theorem B5889523 : Blo 610295 5889523 := bstep (se 1 (by rfl) ⟨4417142, by rfl⟩ : syracuseStep 5889523 = 8834285) B8834285
theorem B3104243 : Blo 610295 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B4185611 : Blo 610295 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B613927 : Blo 610295 613927 := bstep (se 1 (by rfl) ⟨460445, by rfl⟩ : syracuseStep 613927 = 920891) B920891
theorem B613967 : Blo 610295 613967 := bstep (se 1 (by rfl) ⟨460475, by rfl⟩ : syracuseStep 613967 = 920951) B920951
theorem B613983 : Blo 610295 613983 := bstep (se 1 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 613983 = 920975) B920975
theorem B614011 : Blo 610295 614011 := bstep (se 1 (by rfl) ⟨460508, by rfl⟩ : syracuseStep 614011 = 921017) B921017
theorem B614063 : Blo 610295 614063 := bstep (se 1 (by rfl) ⟨460547, by rfl⟩ : syracuseStep 614063 = 921095) B921095
theorem B614087 : Blo 610295 614087 := bstep (se 1 (by rfl) ⟨460565, by rfl⟩ : syracuseStep 614087 = 921131) B921131
theorem B614107 : Blo 610295 614107 := bstep (se 1 (by rfl) ⟨460580, by rfl⟩ : syracuseStep 614107 = 921161) B921161
theorem B614183 : Blo 610295 614183 := bstep (se 1 (by rfl) ⟨460637, by rfl⟩ : syracuseStep 614183 = 921275) B921275
theorem B614223 : Blo 610295 614223 := bstep (se 1 (by rfl) ⟨460667, by rfl⟩ : syracuseStep 614223 = 921335) B921335
theorem B614239 : Blo 610295 614239 := bstep (se 1 (by rfl) ⟨460679, by rfl⟩ : syracuseStep 614239 = 921359) B921359
theorem B614267 : Blo 610295 614267 := bstep (se 1 (by rfl) ⟨460700, by rfl⟩ : syracuseStep 614267 = 921401) B921401
theorem B4415417 : Blo 610295 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B2613329 : Blo 610295 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B3924197 : Blo 610295 3924197 := bstep (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) B735787
theorem B2974013 : Blo 610295 2974013 := bstep (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) B1115255
theorem B3105539 : Blo 610295 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B1106875 : Blo 610295 1106875 := bstep (se 1 (by rfl) ⟨830156, by rfl⟩ : syracuseStep 1106875 = 1660313) B1660313
theorem B4646159 : Blo 610295 4646159 := bstep (se 1 (by rfl) ⟨3484619, by rfl⟩ : syracuseStep 4646159 = 6969239) B6969239
theorem B1468115 : Blo 610295 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B4417375 : Blo 610295 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B1304495 : Blo 610295 1304495 := bstep (se 1 (by rfl) ⟨978371, by rfl⟩ : syracuseStep 1304495 = 1956743) B1956743
theorem B6383717 : Blo 610295 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B9398429 : Blo 610295 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B3107159 : Blo 610295 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B1239403 : Blo 610295 1239403 := bstep (se 1 (by rfl) ⟨929552, by rfl⟩ : syracuseStep 1239403 = 1859105) B1859105
theorem B2615789 : Blo 610295 2615789 := bstep (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) B980921
theorem B5106349 : Blo 610295 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B8809145 : Blo 610295 8809145 := bstep (se 2 (by rfl) ⟨3303429, by rfl⟩ : syracuseStep 8809145 = 6606859) B6606859
theorem B1469459 : Blo 610295 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B977999 : Blo 610295 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B2321561 : Blo 610295 2321561 := bstep (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) B1741171
theorem B1961459 : Blo 610295 1961459 := bstep (se 1 (by rfl) ⟨1471094, by rfl⟩ : syracuseStep 1961459 = 2942189) B2942189
theorem B2322017 : Blo 610295 2322017 := bstep (se 2 (by rfl) ⟨870756, by rfl⟩ : syracuseStep 2322017 = 1741513) B1741513
theorem B2059991 : Blo 610295 2059991 := bstep (se 1 (by rfl) ⟨1544993, by rfl⟩ : syracuseStep 2059991 = 3089987) B3089987
theorem B978679 : Blo 610295 978679 := bstep (se 1 (by rfl) ⟨734009, by rfl⟩ : syracuseStep 978679 = 1468019) B1468019
theorem B2060207 : Blo 610295 2060207 := bstep (se 1 (by rfl) ⟨1545155, by rfl⟩ : syracuseStep 2060207 = 3090311) B3090311
theorem B978871 : Blo 610295 978871 := bstep (se 1 (by rfl) ⟨734153, by rfl⟩ : syracuseStep 978871 = 1468307) B1468307
theorem B1306631 : Blo 610295 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B4649075 : Blo 610295 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B979307 : Blo 610295 979307 := bstep (se 1 (by rfl) ⟨734480, by rfl⟩ : syracuseStep 979307 = 1468961) B1468961
theorem B2486969 : Blo 610295 2486969 := bstep (se 2 (by rfl) ⟨932613, by rfl⟩ : syracuseStep 2486969 = 1865227) B1865227
theorem B5239505 : Blo 610295 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B2945821 : Blo 610295 2945821 := bstep (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) B1104683
theorem B2323475 : Blo 610295 2323475 := bstep (se 1 (by rfl) ⟨1742606, by rfl⟩ : syracuseStep 2323475 = 3485213) B3485213
theorem B1307819 : Blo 610295 1307819 := bstep (se 1 (by rfl) ⟨980864, by rfl⟩ : syracuseStep 1307819 = 1961729) B1961729
theorem B1373705 : Blo 610295 1373705 := bstep (se 2 (by rfl) ⟨515139, by rfl⟩ : syracuseStep 1373705 = 1030279) B1030279
theorem B1374047 : Blo 610295 1374047 := bstep (se 1 (by rfl) ⟨1030535, by rfl⟩ : syracuseStep 1374047 = 2061071) B2061071
theorem B1964047 : Blo 610295 1964047 := bstep (se 1 (by rfl) ⟨1473035, by rfl⟩ : syracuseStep 1964047 = 2946071) B2946071
theorem B1374227 : Blo 610295 1374227 := bstep (se 1 (by rfl) ⟨1030670, by rfl⟩ : syracuseStep 1374227 = 2061341) B2061341
theorem B1865747 : Blo 610295 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B15693911 : Blo 610295 15693911 := bstep (se 1 (by rfl) ⟨11770433, by rfl⟩ : syracuseStep 15693911 = 23540867) B23540867
theorem B1964189 : Blo 610295 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B16152817 : Blo 610295 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B2062583 : Blo 610295 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B6289751 : Blo 610295 6289751 := bstep (se 1 (by rfl) ⟨4717313, by rfl⟩ : syracuseStep 6289751 = 9434627) B9434627
theorem B1374569 : Blo 610295 1374569 := bstep (se 2 (by rfl) ⟨515463, by rfl⟩ : syracuseStep 1374569 = 1030927) B1030927
theorem B14940551 : Blo 610295 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B915887 : Blo 610295 915887 := bstep (se 1 (by rfl) ⟨686915, by rfl⟩ : syracuseStep 915887 = 1373831) B1373831
theorem B915977 : Blo 610295 915977 := bstep (se 2 (by rfl) ⟨343491, by rfl⟩ : syracuseStep 915977 = 686983) B686983
theorem B916007 : Blo 610295 916007 := bstep (se 1 (by rfl) ⟨687005, by rfl⟩ : syracuseStep 916007 = 1374011) B1374011
theorem B2062907 : Blo 610295 2062907 := bstep (se 1 (by rfl) ⟨1547180, by rfl⟩ : syracuseStep 2062907 = 3094361) B3094361
theorem B916091 : Blo 610295 916091 := bstep (se 1 (by rfl) ⟨687068, by rfl⟩ : syracuseStep 916091 = 1374137) B1374137
theorem B2325131 : Blo 610295 2325131 := bstep (se 1 (by rfl) ⟨1743848, by rfl⟩ : syracuseStep 2325131 = 3487697) B3487697
theorem B621275 : Blo 610295 621275 := bstep (se 1 (by rfl) ⟨465956, by rfl⟩ : syracuseStep 621275 = 931913) B931913
theorem B916217 : Blo 610295 916217 := bstep (se 2 (by rfl) ⟨343581, by rfl⟩ : syracuseStep 916217 = 687163) B687163
theorem B2063177 : Blo 610295 2063177 := bstep (se 2 (by rfl) ⟨773691, by rfl⟩ : syracuseStep 2063177 = 1547383) B1547383
theorem B916319 : Blo 610295 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B1309535 : Blo 610295 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B916331 : Blo 610295 916331 := bstep (se 1 (by rfl) ⟨687248, by rfl⟩ : syracuseStep 916331 = 1374497) B1374497
theorem B1178551 : Blo 610295 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B1375163 : Blo 610295 1375163 := bstep (se 1 (by rfl) ⟨1031372, by rfl⟩ : syracuseStep 1375163 = 2062745) B2062745
theorem B1375289 : Blo 610295 1375289 := bstep (se 2 (by rfl) ⟨515733, by rfl⟩ : syracuseStep 1375289 = 1031467) B1031467
theorem B916559 : Blo 610295 916559 := bstep (se 1 (by rfl) ⟨687419, by rfl⟩ : syracuseStep 916559 = 1374839) B1374839
theorem B916679 : Blo 610295 916679 := bstep (se 1 (by rfl) ⟨687509, by rfl⟩ : syracuseStep 916679 = 1375019) B1375019
theorem B5242103 : Blo 610295 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B1047881 : Blo 610295 1047881 := bstep (se 2 (by rfl) ⟨392955, by rfl⟩ : syracuseStep 1047881 = 785911) B785911
theorem B916841 : Blo 610295 916841 := bstep (se 2 (by rfl) ⟨343815, by rfl⟩ : syracuseStep 916841 = 687631) B687631
theorem B1375631 : Blo 610295 1375631 := bstep (se 1 (by rfl) ⟨1031723, by rfl⟩ : syracuseStep 1375631 = 2063447) B2063447
theorem B916919 : Blo 610295 916919 := bstep (se 1 (by rfl) ⟨687689, by rfl⟩ : syracuseStep 916919 = 1375379) B1375379
theorem B1047991 : Blo 610295 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B982459 : Blo 610295 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B916955 : Blo 610295 916955 := bstep (se 1 (by rfl) ⟨687716, by rfl⟩ : syracuseStep 916955 = 1375433) B1375433
theorem B1342985 : Blo 610295 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B687739 : Blo 610295 687739 := bstep (se 1 (by rfl) ⟨515804, by rfl⟩ : syracuseStep 687739 = 1031609) B1031609
theorem B1375955 : Blo 610295 1375955 := bstep (se 1 (by rfl) ⟨1031966, by rfl⟩ : syracuseStep 1375955 = 2063933) B2063933
theorem B2326391 : Blo 610295 2326391 := bstep (se 1 (by rfl) ⟨1744793, by rfl⟩ : syracuseStep 2326391 = 3489587) B3489587
theorem B917423 : Blo 610295 917423 := bstep (se 1 (by rfl) ⟨688067, by rfl⟩ : syracuseStep 917423 = 1376135) B1376135
theorem B2064311 : Blo 610295 2064311 := bstep (se 1 (by rfl) ⟨1548233, by rfl⟩ : syracuseStep 2064311 = 3096467) B3096467
theorem B917609 : Blo 610295 917609 := bstep (se 2 (by rfl) ⟨344103, by rfl⟩ : syracuseStep 917609 = 688207) B688207
theorem B4423891 : Blo 610295 4423891 := bstep (se 1 (by rfl) ⟨3317918, by rfl⟩ : syracuseStep 4423891 = 6635837) B6635837
theorem B688423 : Blo 610295 688423 := bstep (se 1 (by rfl) ⟨516317, by rfl⟩ : syracuseStep 688423 = 1032635) B1032635
theorem B1376585 : Blo 610295 1376585 := bstep (se 2 (by rfl) ⟨516219, by rfl⟩ : syracuseStep 1376585 = 1032439) B1032439
theorem B1376603 : Blo 610295 1376603 := bstep (se 1 (by rfl) ⟨1032452, by rfl⟩ : syracuseStep 1376603 = 2064905) B2064905
theorem B2621803 : Blo 610295 2621803 := bstep (se 1 (by rfl) ⟨1966352, by rfl⟩ : syracuseStep 2621803 = 3932705) B3932705
theorem B688495 : Blo 610295 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B917927 : Blo 610295 917927 := bstep (se 1 (by rfl) ⟨688445, by rfl⟩ : syracuseStep 917927 = 1376891) B1376891
theorem B918011 : Blo 610295 918011 := bstep (se 1 (by rfl) ⟨688508, by rfl⟩ : syracuseStep 918011 = 1377017) B1377017
theorem B688711 : Blo 610295 688711 := bstep (se 1 (by rfl) ⟨516533, by rfl⟩ : syracuseStep 688711 = 1033067) B1033067
theorem B918137 : Blo 610295 918137 := bstep (se 2 (by rfl) ⟨344301, by rfl⟩ : syracuseStep 918137 = 688603) B688603
theorem B5505671 : Blo 610295 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B2065067 : Blo 610295 2065067 := bstep (se 1 (by rfl) ⟨1548800, by rfl⟩ : syracuseStep 2065067 = 3097601) B3097601
theorem B1966763 : Blo 610295 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B918191 : Blo 610295 918191 := bstep (se 1 (by rfl) ⟨688643, by rfl⟩ : syracuseStep 918191 = 1377287) B1377287
theorem B983735 : Blo 610295 983735 := bstep (se 1 (by rfl) ⟨737801, by rfl⟩ : syracuseStep 983735 = 1475603) B1475603
theorem B918239 : Blo 610295 918239 := bstep (se 1 (by rfl) ⟨688679, by rfl⟩ : syracuseStep 918239 = 1377359) B1377359
theorem B12780281 : Blo 610295 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B1377179 : Blo 610295 1377179 := bstep (se 1 (by rfl) ⟨1032884, by rfl⟩ : syracuseStep 1377179 = 2065769) B2065769
theorem B918503 : Blo 610295 918503 := bstep (se 1 (by rfl) ⟨688877, by rfl⟩ : syracuseStep 918503 = 1377755) B1377755
theorem B5243879 : Blo 610295 5243879 := bstep (se 1 (by rfl) ⟨3932909, by rfl⟩ : syracuseStep 5243879 = 7865819) B7865819
theorem B1377377 : Blo 610295 1377377 := bstep (se 2 (by rfl) ⟨516516, by rfl⟩ : syracuseStep 1377377 = 1033033) B1033033
theorem B2065607 : Blo 610295 2065607 := bstep (se 1 (by rfl) ⟨1549205, by rfl⟩ : syracuseStep 2065607 = 3098411) B3098411
theorem B918761 : Blo 610295 918761 := bstep (se 2 (by rfl) ⟨344535, by rfl⟩ : syracuseStep 918761 = 689071) B689071
theorem B1475833 : Blo 610295 1475833 := bstep (se 2 (by rfl) ⟨553437, by rfl⟩ : syracuseStep 1475833 = 1106875) B1106875
theorem B918815 : Blo 610295 918815 := bstep (se 1 (by rfl) ⟨689111, by rfl⟩ : syracuseStep 918815 = 1378223) B1378223
theorem B1377575 : Blo 610295 1377575 := bstep (se 1 (by rfl) ⟨1033181, by rfl⟩ : syracuseStep 1377575 = 2066363) B2066363
theorem B2622881 : Blo 610295 2622881 := bstep (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) B1967161
theorem B689575 : Blo 610295 689575 := bstep (se 1 (by rfl) ⟨517181, by rfl⟩ : syracuseStep 689575 = 1034363) B1034363
theorem B3933629 : Blo 610295 3933629 := bstep (se 3 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 3933629 = 1475111) B1475111
theorem B918983 : Blo 610295 918983 := bstep (se 1 (by rfl) ⟨689237, by rfl⟩ : syracuseStep 918983 = 1378475) B1378475
theorem B2623033 : Blo 610295 2623033 := bstep (se 2 (by rfl) ⟨983637, by rfl⟩ : syracuseStep 2623033 = 1967275) B1967275
theorem B1377953 : Blo 610295 1377953 := bstep (se 2 (by rfl) ⟨516732, by rfl⟩ : syracuseStep 1377953 = 1033465) B1033465
theorem B11142947 : Blo 610295 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B919337 : Blo 610295 919337 := bstep (se 2 (by rfl) ⟨344751, by rfl⟩ : syracuseStep 919337 = 689503) B689503
theorem B919343 : Blo 610295 919343 := bstep (se 1 (by rfl) ⟨689507, by rfl⟩ : syracuseStep 919343 = 1379015) B1379015
theorem B17926019 : Blo 610295 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B690151 : Blo 610295 690151 := bstep (se 1 (by rfl) ⟨517613, by rfl⟩ : syracuseStep 690151 = 1035227) B1035227
theorem B1378313 : Blo 610295 1378313 := bstep (se 2 (by rfl) ⟨516867, by rfl⟩ : syracuseStep 1378313 = 1033735) B1033735
theorem B919817 : Blo 610295 919817 := bstep (se 2 (by rfl) ⟨344931, by rfl⟩ : syracuseStep 919817 = 689863) B689863
theorem B919919 : Blo 610295 919919 := bstep (se 1 (by rfl) ⟨689939, by rfl⟩ : syracuseStep 919919 = 1379879) B1379879
theorem B2984359 : Blo 610295 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B1378727 : Blo 610295 1378727 := bstep (se 1 (by rfl) ⟨1034045, by rfl⟩ : syracuseStep 1378727 = 2068091) B2068091
theorem B1378835 : Blo 610295 1378835 := bstep (se 1 (by rfl) ⟨1034126, by rfl⟩ : syracuseStep 1378835 = 2068253) B2068253
theorem B920135 : Blo 610295 920135 := bstep (se 1 (by rfl) ⟨690101, by rfl⟩ : syracuseStep 920135 = 1380203) B1380203
theorem B1378889 : Blo 610295 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B5245519 : Blo 610295 5245519 := bstep (se 1 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 5245519 = 7868279) B7868279
theorem B920171 : Blo 610295 920171 := bstep (se 1 (by rfl) ⟨690128, by rfl⟩ : syracuseStep 920171 = 1380257) B1380257
theorem B2067119 : Blo 610295 2067119 := bstep (se 1 (by rfl) ⟨1550339, by rfl⟩ : syracuseStep 2067119 = 3100679) B3100679
theorem B920399 : Blo 610295 920399 := bstep (se 1 (by rfl) ⟨690299, by rfl⟩ : syracuseStep 920399 = 1380599) B1380599
theorem B1379303 : Blo 610295 1379303 := bstep (se 1 (by rfl) ⟨1034477, by rfl⟩ : syracuseStep 1379303 = 2068955) B2068955
theorem B2067443 : Blo 610295 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B5868611 : Blo 610295 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B4197491 : Blo 610295 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B920795 : Blo 610295 920795 := bstep (se 1 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 920795 = 1381193) B1381193
theorem B1379681 : Blo 610295 1379681 := bstep (se 2 (by rfl) ⟨517380, by rfl⟩ : syracuseStep 1379681 = 1034761) B1034761
theorem B920969 : Blo 610295 920969 := bstep (se 2 (by rfl) ⟨345363, by rfl⟩ : syracuseStep 920969 = 690727) B690727
theorem B1379771 : Blo 610295 1379771 := bstep (se 1 (by rfl) ⟨1034828, by rfl⟩ : syracuseStep 1379771 = 2069657) B2069657
theorem B2067983 : Blo 610295 2067983 := bstep (se 1 (by rfl) ⟨1550987, by rfl⟩ : syracuseStep 2067983 = 3101975) B3101975
theorem B1379897 : Blo 610295 1379897 := bstep (se 2 (by rfl) ⟨517461, by rfl⟩ : syracuseStep 1379897 = 1034923) B1034923
theorem B4656851 : Blo 610295 4656851 := bstep (se 1 (by rfl) ⟨3492638, by rfl⟩ : syracuseStep 4656851 = 6985277) B6985277
theorem B921323 : Blo 610295 921323 := bstep (se 1 (by rfl) ⟨690992, by rfl⟩ : syracuseStep 921323 = 1381985) B1381985
theorem B7442603 : Blo 610295 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B1380563 : Blo 610295 1380563 := bstep (se 1 (by rfl) ⟨1035422, by rfl⟩ : syracuseStep 1380563 = 2070845) B2070845
theorem B15274241 : Blo 610295 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B1380617 : Blo 610295 1380617 := bstep (se 2 (by rfl) ⟨517731, by rfl⟩ : syracuseStep 1380617 = 1035463) B1035463
theorem B6623603 : Blo 610295 6623603 := bstep (se 1 (by rfl) ⟨4967702, by rfl⟩ : syracuseStep 6623603 = 9935405) B9935405
theorem B1380833 : Blo 610295 1380833 := bstep (se 2 (by rfl) ⟨517812, by rfl⟩ : syracuseStep 1380833 = 1035625) B1035625
theorem B1741331 : Blo 610295 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B2069063 : Blo 610295 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B5870303 : Blo 610295 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B1381139 : Blo 610295 1381139 := bstep (se 1 (by rfl) ⟨1035854, by rfl⟩ : syracuseStep 1381139 = 2071709) B2071709
theorem B1545115 : Blo 610295 1545115 := bstep (se 1 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 1545115 = 2317673) B2317673
theorem B1741787 : Blo 610295 1741787 := bstep (se 1 (by rfl) ⟨1306340, by rfl⟩ : syracuseStep 1741787 = 2612681) B2612681
theorem B2069495 : Blo 610295 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B2790407 : Blo 610295 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B1381499 : Blo 610295 1381499 := bstep (se 1 (by rfl) ⟨1036124, by rfl⟩ : syracuseStep 1381499 = 2072249) B2072249
theorem B1381625 : Blo 610295 1381625 := bstep (se 2 (by rfl) ⟨518109, by rfl⟩ : syracuseStep 1381625 = 1036219) B1036219
theorem B1381769 : Blo 610295 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B1742219 : Blo 610295 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B1381895 : Blo 610295 1381895 := bstep (se 1 (by rfl) ⟨1036421, by rfl⟩ : syracuseStep 1381895 = 2072843) B2072843
theorem B1382075 : Blo 610295 1382075 := bstep (se 1 (by rfl) ⟨1036556, by rfl⟩ : syracuseStep 1382075 = 2073113) B2073113
theorem B2070359 : Blo 610295 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B1546249 : Blo 610295 1546249 := bstep (se 2 (by rfl) ⟨579843, by rfl⟩ : syracuseStep 1546249 = 1159687) B1159687
theorem B2234735 : Blo 610295 2234735 := bstep (se 1 (by rfl) ⟨1676051, by rfl⟩ : syracuseStep 2234735 = 3352103) B3352103
theorem B99359227 : Blo 610295 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B6265619 : Blo 610295 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B2071439 : Blo 610295 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B1743859 : Blo 610295 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B4660253 : Blo 610295 4660253 := bstep (se 3 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 4660253 = 1747595) B1747595
theorem B5872763 : Blo 610295 5872763 := bstep (se 1 (by rfl) ⟨4404572, by rfl⟩ : syracuseStep 5872763 = 8809145) B8809145
theorem B1547657 : Blo 610295 1547657 := bstep (se 2 (by rfl) ⟨580371, by rfl⟩ : syracuseStep 1547657 = 1160743) B1160743
theorem B1547707 : Blo 610295 1547707 := bstep (se 1 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 1547707 = 2321561) B2321561
theorem B5971603 : Blo 610295 5971603 := bstep (se 1 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 5971603 = 8957405) B8957405
theorem B1548011 : Blo 610295 1548011 := bstep (se 1 (by rfl) ⟨1161008, by rfl⟩ : syracuseStep 1548011 = 2322017) B2322017
theorem B2072681 : Blo 610295 2072681 := bstep (se 2 (by rfl) ⟨777255, by rfl⟩ : syracuseStep 2072681 = 1554511) B1554511
theorem B21537089 : Blo 610295 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B1548983 : Blo 610295 1548983 := bstep (se 1 (by rfl) ⟨1161737, by rfl⟩ : syracuseStep 1548983 = 2323475) B2323475
theorem B3581293 : Blo 610295 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B10462607 : Blo 610295 10462607 := bstep (se 1 (by rfl) ⟨7846955, by rfl⟩ : syracuseStep 10462607 = 15693911) B15693911
theorem B3089825 : Blo 610295 3089825 := bstep (se 2 (by rfl) ⟨1158684, by rfl⟩ : syracuseStep 3089825 = 2317369) B2317369
theorem B16787101 : Blo 610295 16787101 := bstep (se 3 (by rfl) ⟨3147581, by rfl⟩ : syracuseStep 16787101 = 6295163) B6295163
theorem B1550087 : Blo 610295 1550087 := bstep (se 1 (by rfl) ⟨1162565, by rfl⟩ : syracuseStep 1550087 = 2325131) B2325131
theorem B1550137 : Blo 610295 1550137 := bstep (se 2 (by rfl) ⟨581301, by rfl⟩ : syracuseStep 1550137 = 1162603) B1162603
theorem B1550441 : Blo 610295 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B698587 : Blo 610295 698587 := bstep (se 1 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 698587 = 1047881) B1047881
theorem B2205949 : Blo 610295 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B6302063 : Blo 610295 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B1550927 : Blo 610295 1550927 := bstep (se 1 (by rfl) ⟨1163195, by rfl⟩ : syracuseStep 1550927 = 2326391) B2326391
theorem B5287027 : Blo 610295 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B1649879 : Blo 610295 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B1551575 : Blo 610295 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B5024987 : Blo 610295 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B10431989 : Blo 610295 10431989 := bstep (se 5 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 10431989 = 977999) B977999
theorem B3911435 : Blo 610295 3911435 := bstep (se 1 (by rfl) ⟨2933576, by rfl⟩ : syracuseStep 3911435 = 5867153) B5867153
theorem B12922739 : Blo 610295 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1159535 : Blo 610295 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B1552891 : Blo 610295 1552891 := bstep (se 1 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 1552891 = 2329337) B2329337
theorem B1553003 : Blo 610295 1553003 := bstep (se 1 (by rfl) ⟨1164752, by rfl⟩ : syracuseStep 1553003 = 2329505) B2329505
theorem B1651835 : Blo 610295 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B7845011 : Blo 610295 7845011 := bstep (se 1 (by rfl) ⟨5883758, by rfl⟩ : syracuseStep 7845011 = 11767517) B11767517
theorem B1553651 : Blo 610295 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1553863 : Blo 610295 1553863 := bstep (se 1 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 1553863 = 2330795) B2330795
theorem B1029935 : Blo 610295 1029935 := bstep (se 1 (by rfl) ⟨772451, by rfl⟩ : syracuseStep 1029935 = 1544903) B1544903
theorem B1652537 : Blo 610295 1652537 := bstep (se 2 (by rfl) ⟨619701, by rfl⟩ : syracuseStep 1652537 = 1239403) B1239403
theorem B9943505 : Blo 610295 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B5224985 : Blo 610295 5224985 := bstep (se 2 (by rfl) ⟨1959369, by rfl⟩ : syracuseStep 5224985 = 3918739) B3918739
theorem B3914639 : Blo 610295 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B5880761 : Blo 610295 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B1031143 : Blo 610295 1031143 := bstep (se 1 (by rfl) ⟨773357, by rfl⟩ : syracuseStep 1031143 = 1546715) B1546715
theorem B3095819 : Blo 610295 3095819 := bstep (se 1 (by rfl) ⟨2321864, by rfl⟩ : syracuseStep 3095819 = 4643729) B4643729
theorem B1982675 : Blo 610295 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B3097439 : Blo 610295 3097439 := bstep (se 1 (by rfl) ⟨2323079, by rfl⟩ : syracuseStep 3097439 = 4646159) B4646159
theorem B869663 : Blo 610295 869663 := bstep (se 1 (by rfl) ⟨652247, by rfl⟩ : syracuseStep 869663 = 1304495) B1304495
theorem B3917099 : Blo 610295 3917099 := bstep (se 1 (by rfl) ⟨2937824, by rfl⟩ : syracuseStep 3917099 = 5875649) B5875649
theorem B3720737 : Blo 610295 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B1033823 : Blo 610295 1033823 := bstep (se 1 (by rfl) ⟨775367, by rfl⟩ : syracuseStep 1033823 = 1550735) B1550735
theorem B2475677 : Blo 610295 2475677 := bstep (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) B928379
theorem B1034039 : Blo 610295 1034039 := bstep (se 1 (by rfl) ⟨775529, by rfl⟩ : syracuseStep 1034039 = 1551059) B1551059
theorem B1656733 : Blo 610295 1656733 := bstep (se 3 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 1656733 = 621275) B621275
theorem B2607299 : Blo 610295 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B1034815 : Blo 610295 1034815 := bstep (se 1 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 1034815 = 1552223) B1552223
theorem B772679 : Blo 610295 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B4639355 : Blo 610295 4639355 := bstep (se 1 (by rfl) ⟨3479516, by rfl⟩ : syracuseStep 4639355 = 6959033) B6959033
theorem B871087 : Blo 610295 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B3918557 : Blo 610295 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B772831 : Blo 610295 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B3099383 : Blo 610295 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B5655329 : Blo 610295 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B1657979 : Blo 610295 1657979 := bstep (se 1 (by rfl) ⟨1243484, by rfl⟩ : syracuseStep 1657979 = 2486969) B2486969
theorem B3493003 : Blo 610295 3493003 := bstep (se 1 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 3493003 = 5239505) B5239505
theorem B2935997 : Blo 610295 2935997 := bstep (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) B1100999
theorem B3099869 : Blo 610295 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B1035497 : Blo 610295 1035497 := bstep (se 2 (by rfl) ⟨388311, by rfl⟩ : syracuseStep 1035497 = 776623) B776623
theorem B1035551 : Blo 610295 1035551 := bstep (se 1 (by rfl) ⟨776663, by rfl⟩ : syracuseStep 1035551 = 1553327) B1553327
theorem B871879 : Blo 610295 871879 := bstep (se 1 (by rfl) ⟨653909, by rfl⟩ : syracuseStep 871879 = 1307819) B1307819
theorem B8376425 : Blo 610295 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B610591 : Blo 610295 610591 := bstep (se 1 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 610591 = 915887) B915887
theorem B610651 : Blo 610295 610651 := bstep (se 1 (by rfl) ⟨457988, by rfl⟩ : syracuseStep 610651 = 915977) B915977
theorem B610671 : Blo 610295 610671 := bstep (se 1 (by rfl) ⟨458003, by rfl⟩ : syracuseStep 610671 = 916007) B916007
theorem B610727 : Blo 610295 610727 := bstep (se 1 (by rfl) ⟨458045, by rfl⟩ : syracuseStep 610727 = 916091) B916091
theorem B610811 : Blo 610295 610811 := bstep (se 1 (by rfl) ⟨458108, by rfl⟩ : syracuseStep 610811 = 916217) B916217
theorem B4641299 : Blo 610295 4641299 := bstep (se 1 (by rfl) ⟨3480974, by rfl⟩ : syracuseStep 4641299 = 6961949) B6961949
theorem B610879 : Blo 610295 610879 := bstep (se 1 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 610879 = 916319) B916319
theorem B873023 : Blo 610295 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B610887 : Blo 610295 610887 := bstep (se 1 (by rfl) ⟨458165, by rfl⟩ : syracuseStep 610887 = 916331) B916331
theorem B1397321 : Blo 610295 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B7852697 : Blo 610295 7852697 := bstep (se 2 (by rfl) ⟨2944761, by rfl⟩ : syracuseStep 7852697 = 5889523) B5889523
theorem B611039 : Blo 610295 611039 := bstep (se 1 (by rfl) ⟨458279, by rfl⟩ : syracuseStep 611039 = 916559) B916559
theorem B611119 : Blo 610295 611119 := bstep (se 1 (by rfl) ⟨458339, by rfl⟩ : syracuseStep 611119 = 916679) B916679
theorem B3494735 : Blo 610295 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B611227 : Blo 610295 611227 := bstep (se 1 (by rfl) ⟨458420, by rfl⟩ : syracuseStep 611227 = 916841) B916841
theorem B6607817 : Blo 610295 6607817 := bstep (se 2 (by rfl) ⟨2477931, by rfl⟩ : syracuseStep 6607817 = 4955863) B4955863
theorem B611279 : Blo 610295 611279 := bstep (se 1 (by rfl) ⟨458459, by rfl⟩ : syracuseStep 611279 = 916919) B916919
theorem B611303 : Blo 610295 611303 := bstep (se 1 (by rfl) ⟨458477, by rfl⟩ : syracuseStep 611303 = 916955) B916955
theorem B611615 : Blo 610295 611615 := bstep (se 1 (by rfl) ⟨458711, by rfl⟩ : syracuseStep 611615 = 917423) B917423
theorem B611675 : Blo 610295 611675 := bstep (se 1 (by rfl) ⟨458756, by rfl⟩ : syracuseStep 611675 = 917513) B917513
theorem B3986783 : Blo 610295 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B7558505 : Blo 610295 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B611695 : Blo 610295 611695 := bstep (se 1 (by rfl) ⟨458771, by rfl⟩ : syracuseStep 611695 = 917543) B917543
theorem B54285713 : Blo 610295 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B611751 : Blo 610295 611751 := bstep (se 1 (by rfl) ⟨458813, by rfl⟩ : syracuseStep 611751 = 917627) B917627
theorem B1660409 : Blo 610295 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B611835 : Blo 610295 611835 := bstep (se 1 (by rfl) ⟨458876, by rfl⟩ : syracuseStep 611835 = 917753) B917753
theorem B5887525 : Blo 610295 5887525 := bstep (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) B1103911
theorem B611903 : Blo 610295 611903 := bstep (se 1 (by rfl) ⟨458927, by rfl⟩ : syracuseStep 611903 = 917855) B917855
theorem B611911 : Blo 610295 611911 := bstep (se 1 (by rfl) ⟨458933, by rfl⟩ : syracuseStep 611911 = 917867) B917867
theorem B2938457 : Blo 610295 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B612063 : Blo 610295 612063 := bstep (se 1 (by rfl) ⟨459047, by rfl⟩ : syracuseStep 612063 = 918095) B918095
theorem B612143 : Blo 610295 612143 := bstep (se 1 (by rfl) ⟨459107, by rfl⟩ : syracuseStep 612143 = 918215) B918215
theorem B612251 : Blo 610295 612251 := bstep (se 1 (by rfl) ⟨459188, by rfl⟩ : syracuseStep 612251 = 918377) B918377
theorem B612303 : Blo 610295 612303 := bstep (se 1 (by rfl) ⟨459227, by rfl⟩ : syracuseStep 612303 = 918455) B918455
theorem B612327 : Blo 610295 612327 := bstep (se 1 (by rfl) ⟨459245, by rfl⟩ : syracuseStep 612327 = 918491) B918491
theorem B3528839 : Blo 610295 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B5593367 : Blo 610295 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B612639 : Blo 610295 612639 := bstep (se 1 (by rfl) ⟨459479, by rfl⟩ : syracuseStep 612639 = 918959) B918959
theorem B612699 : Blo 610295 612699 := bstep (se 1 (by rfl) ⟨459524, by rfl⟩ : syracuseStep 612699 = 919049) B919049
theorem B612719 : Blo 610295 612719 := bstep (se 1 (by rfl) ⟨459539, by rfl⟩ : syracuseStep 612719 = 919079) B919079
theorem B612775 : Blo 610295 612775 := bstep (se 1 (by rfl) ⟨459581, by rfl⟩ : syracuseStep 612775 = 919163) B919163
theorem B612859 : Blo 610295 612859 := bstep (se 1 (by rfl) ⟨459644, by rfl⟩ : syracuseStep 612859 = 919289) B919289
theorem B5593625 : Blo 610295 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B3103271 : Blo 610295 3103271 := bstep (se 1 (by rfl) ⟨2327453, by rfl⟩ : syracuseStep 3103271 = 4654907) B4654907
theorem B940607 : Blo 610295 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B612927 : Blo 610295 612927 := bstep (se 1 (by rfl) ⟨459695, by rfl⟩ : syracuseStep 612927 = 919391) B919391
theorem B612935 : Blo 610295 612935 := bstep (se 1 (by rfl) ⟨459701, by rfl⟩ : syracuseStep 612935 = 919403) B919403
theorem B613087 : Blo 610295 613087 := bstep (se 1 (by rfl) ⟨459815, by rfl⟩ : syracuseStep 613087 = 919631) B919631
theorem B613167 : Blo 610295 613167 := bstep (se 1 (by rfl) ⟨459875, by rfl⟩ : syracuseStep 613167 = 919751) B919751
theorem B613275 : Blo 610295 613275 := bstep (se 1 (by rfl) ⟨459956, by rfl⟩ : syracuseStep 613275 = 919913) B919913
theorem B3496877 : Blo 610295 3496877 := bstep (se 3 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 3496877 = 1311329) B1311329
theorem B613327 : Blo 610295 613327 := bstep (se 1 (by rfl) ⟨459995, by rfl⟩ : syracuseStep 613327 = 919991) B919991
theorem B613351 : Blo 610295 613351 := bstep (se 1 (by rfl) ⟨460013, by rfl⟩ : syracuseStep 613351 = 920027) B920027
theorem B613663 : Blo 610295 613663 := bstep (se 1 (by rfl) ⟨460247, by rfl⟩ : syracuseStep 613663 = 920495) B920495
theorem B613723 : Blo 610295 613723 := bstep (se 1 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 613723 = 920585) B920585
theorem B613743 : Blo 610295 613743 := bstep (se 1 (by rfl) ⟨460307, by rfl⟩ : syracuseStep 613743 = 920615) B920615
theorem B24141199 : Blo 610295 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B613799 : Blo 610295 613799 := bstep (se 1 (by rfl) ⟨460349, by rfl⟩ : syracuseStep 613799 = 920699) B920699
theorem B613883 : Blo 610295 613883 := bstep (se 1 (by rfl) ⟨460412, by rfl⟩ : syracuseStep 613883 = 920825) B920825
theorem B613951 : Blo 610295 613951 := bstep (se 1 (by rfl) ⟨460463, by rfl⟩ : syracuseStep 613951 = 920927) B920927
theorem B613959 : Blo 610295 613959 := bstep (se 1 (by rfl) ⟨460469, by rfl⟩ : syracuseStep 613959 = 920939) B920939
theorem B14900851 : Blo 610295 14900851 := bstep (se 1 (by rfl) ⟨11175638, by rfl⟩ : syracuseStep 14900851 = 22351277) B22351277
theorem B614111 : Blo 610295 614111 := bstep (se 1 (by rfl) ⟨460583, by rfl⟩ : syracuseStep 614111 = 921167) B921167
theorem B5889833 : Blo 610295 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B614191 : Blo 610295 614191 := bstep (se 1 (by rfl) ⟨460643, by rfl⟩ : syracuseStep 614191 = 921287) B921287
theorem B6283183 : Blo 610295 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B3497903 : Blo 610295 3497903 := bstep (se 1 (by rfl) ⟨2623427, by rfl⟩ : syracuseStep 3497903 = 5246855) B5246855
theorem B3105377 : Blo 610295 3105377 := bstep (se 2 (by rfl) ⟨1164516, by rfl⟩ : syracuseStep 3105377 = 2329033) B2329033
theorem B6808465 : Blo 610295 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B2319299 : Blo 610295 2319299 := bstep (se 1 (by rfl) ⟨1739474, by rfl⟩ : syracuseStep 2319299 = 3478949) B3478949
theorem B4187143 : Blo 610295 4187143 := bstep (se 1 (by rfl) ⟨3140357, by rfl⟩ : syracuseStep 4187143 = 6280715) B6280715
theorem B3302633 : Blo 610295 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B3106025 : Blo 610295 3106025 := bstep (se 2 (by rfl) ⟨1164759, by rfl⟩ : syracuseStep 3106025 = 2329519) B2329519
theorem B1303931 : Blo 610295 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B3106187 : Blo 610295 3106187 := bstep (se 1 (by rfl) ⟨2329640, by rfl⟩ : syracuseStep 3106187 = 4659281) B4659281
theorem B1238689 : Blo 610295 1238689 := bstep (se 2 (by rfl) ⟨464508, by rfl⟩ : syracuseStep 1238689 = 929017) B929017
theorem B33613643 : Blo 610295 33613643 := bstep (se 1 (by rfl) ⟨25210232, by rfl⟩ : syracuseStep 33613643 = 50420465) B50420465
theorem B6285605 : Blo 610295 6285605 := bstep (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) B1178551
theorem B1304905 : Blo 610295 1304905 := bstep (se 2 (by rfl) ⟨489339, by rfl⟩ : syracuseStep 1304905 = 978679) B978679
theorem B1305161 : Blo 610295 1305161 := bstep (se 2 (by rfl) ⟨489435, by rfl⟩ : syracuseStep 1305161 = 978871) B978871
theorem B2943611 : Blo 610295 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B2616131 : Blo 610295 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B2321531 : Blo 610295 2321531 := bstep (se 1 (by rfl) ⟨1741148, by rfl⟩ : syracuseStep 2321531 = 3482297) B3482297
theorem B25128107 : Blo 610295 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B2059937 : Blo 610295 2059937 := bstep (se 2 (by rfl) ⟨772476, by rfl⟩ : syracuseStep 2059937 = 1544953) B1544953
theorem B39841469 : Blo 610295 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B3927761 : Blo 610295 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B978743 : Blo 610295 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B4255811 : Blo 610295 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B2060801 : Blo 610295 2060801 := bstep (se 2 (by rfl) ⟨772800, by rfl⟩ : syracuseStep 2060801 = 1545601) B1545601
theorem B3109427 : Blo 610295 3109427 := bstep (se 1 (by rfl) ⟨2332070, by rfl⟩ : syracuseStep 3109427 = 4664141) B4664141
theorem B5108285 : Blo 610295 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B1471151 : Blo 610295 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B10777519 : Blo 610295 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B2061287 : Blo 610295 2061287 := bstep (se 1 (by rfl) ⟨1545965, by rfl⟩ : syracuseStep 2061287 = 3091931) B3091931
theorem B1307639 : Blo 610295 1307639 := bstep (se 1 (by rfl) ⟨980729, by rfl⟩ : syracuseStep 1307639 = 1961459) B1961459
theorem B1373327 : Blo 610295 1373327 := bstep (se 1 (by rfl) ⟨1029995, by rfl⟩ : syracuseStep 1373327 = 2059991) B2059991
theorem B1373417 : Blo 610295 1373417 := bstep (se 2 (by rfl) ⟨515031, by rfl⟩ : syracuseStep 1373417 = 1030063) B1030063
theorem B1373471 : Blo 610295 1373471 := bstep (se 1 (by rfl) ⟨1030103, by rfl⟩ : syracuseStep 1373471 = 2060207) B2060207
theorem B2061611 : Blo 610295 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B3306847 : Blo 610295 3306847 := bstep (se 1 (by rfl) ⟨2480135, by rfl⟩ : syracuseStep 3306847 = 4960271) B4960271
theorem B2618729 : Blo 610295 2618729 := bstep (se 2 (by rfl) ⟨982023, by rfl⟩ : syracuseStep 2618729 = 1964047) B1964047
theorem B4650533 : Blo 610295 4650533 := bstep (se 4 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 4650533 = 871975) B871975
theorem B2061881 : Blo 610295 2061881 := bstep (se 2 (by rfl) ⟨773205, by rfl⟩ : syracuseStep 2061881 = 1546411) B1546411
theorem B652871 : Blo 610295 652871 := bstep (se 1 (by rfl) ⟨489653, by rfl⟩ : syracuseStep 652871 = 979307) B979307
theorem B1373993 : Blo 610295 1373993 := bstep (se 2 (by rfl) ⟨515247, by rfl⟩ : syracuseStep 1373993 = 1030495) B1030495
theorem B915803 : Blo 610295 915803 := bstep (se 1 (by rfl) ⟨686852, by rfl⟩ : syracuseStep 915803 = 1373705) B1373705
theorem B686587 : Blo 610295 686587 := bstep (se 1 (by rfl) ⟨514940, by rfl⟩ : syracuseStep 686587 = 1029881) B1029881
theorem B916031 : Blo 610295 916031 := bstep (se 1 (by rfl) ⟨687023, by rfl⟩ : syracuseStep 916031 = 1374047) B1374047
theorem B4422217 : Blo 610295 4422217 := bstep (se 2 (by rfl) ⟨1658331, by rfl⟩ : syracuseStep 4422217 = 3316663) B3316663
theorem B686767 : Blo 610295 686767 := bstep (se 1 (by rfl) ⟨515075, by rfl⟩ : syracuseStep 686767 = 1030151) B1030151
theorem B916151 : Blo 610295 916151 := bstep (se 1 (by rfl) ⟨687113, by rfl⟩ : syracuseStep 916151 = 1374227) B1374227
theorem B1243831 : Blo 610295 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B2063123 : Blo 610295 2063123 := bstep (se 1 (by rfl) ⟨1547342, by rfl⟩ : syracuseStep 2063123 = 3094685) B3094685
theorem B1309459 : Blo 610295 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B1375055 : Blo 610295 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B4193167 : Blo 610295 4193167 := bstep (se 1 (by rfl) ⟨3144875, by rfl⟩ : syracuseStep 4193167 = 6289751) B6289751
theorem B916379 : Blo 610295 916379 := bstep (se 1 (by rfl) ⟨687284, by rfl⟩ : syracuseStep 916379 = 1374569) B1374569
theorem B2325419 : Blo 610295 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B687055 : Blo 610295 687055 := bstep (se 1 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 687055 = 1030583) B1030583
theorem B1375271 : Blo 610295 1375271 := bstep (se 1 (by rfl) ⟨1031453, by rfl⟩ : syracuseStep 1375271 = 2062907) B2062907
theorem B1866791 : Blo 610295 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B1375451 : Blo 610295 1375451 := bstep (se 1 (by rfl) ⟨1031588, by rfl⟩ : syracuseStep 1375451 = 2063177) B2063177
theorem B1309945 : Blo 610295 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B916775 : Blo 610295 916775 := bstep (se 1 (by rfl) ⟨687581, by rfl⟩ : syracuseStep 916775 = 1375163) B1375163
theorem B687451 : Blo 610295 687451 := bstep (se 1 (by rfl) ⟨515588, by rfl⟩ : syracuseStep 687451 = 1031177) B1031177
theorem B916859 : Blo 610295 916859 := bstep (se 1 (by rfl) ⟨687644, by rfl⟩ : syracuseStep 916859 = 1375289) B1375289
theorem B1375649 : Blo 610295 1375649 := bstep (se 2 (by rfl) ⟨515868, by rfl⟩ : syracuseStep 1375649 = 1031737) B1031737
theorem B687559 : Blo 610295 687559 := bstep (se 1 (by rfl) ⟨515669, by rfl⟩ : syracuseStep 687559 = 1031339) B1031339
theorem B916985 : Blo 610295 916985 := bstep (se 2 (by rfl) ⟨343869, by rfl⟩ : syracuseStep 916985 = 687739) B687739
theorem B917087 : Blo 610295 917087 := bstep (se 1 (by rfl) ⟨687815, by rfl⟩ : syracuseStep 917087 = 1375631) B1375631
theorem B2063987 : Blo 610295 2063987 := bstep (se 1 (by rfl) ⟨1547990, by rfl⟩ : syracuseStep 2063987 = 3095981) B3095981
theorem B687919 : Blo 610295 687919 := bstep (se 1 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 687919 = 1031879) B1031879
theorem B917303 : Blo 610295 917303 := bstep (se 1 (by rfl) ⟨687977, by rfl⟩ : syracuseStep 917303 = 1375955) B1375955
theorem B2064257 : Blo 610295 2064257 := bstep (se 2 (by rfl) ⟨774096, by rfl⟩ : syracuseStep 2064257 = 1548193) B1548193
theorem B2948993 : Blo 610295 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B688027 : Blo 610295 688027 := bstep (se 1 (by rfl) ⟨516020, by rfl⟩ : syracuseStep 688027 = 1032041) B1032041
theorem B1376207 : Blo 610295 1376207 := bstep (se 1 (by rfl) ⟨1032155, by rfl⟩ : syracuseStep 1376207 = 2064311) B2064311
theorem B917723 : Blo 610295 917723 := bstep (se 1 (by rfl) ⟨688292, by rfl⟩ : syracuseStep 917723 = 1376585) B1376585
theorem B917735 : Blo 610295 917735 := bstep (se 1 (by rfl) ⟨688301, by rfl⟩ : syracuseStep 917735 = 1376603) B1376603
theorem B5898521 : Blo 610295 5898521 := bstep (se 2 (by rfl) ⟨2211945, by rfl⟩ : syracuseStep 5898521 = 4423891) B4423891
theorem B917897 : Blo 610295 917897 := bstep (se 2 (by rfl) ⟨344211, by rfl⟩ : syracuseStep 917897 = 688423) B688423
theorem B3670447 : Blo 610295 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B1376711 : Blo 610295 1376711 := bstep (se 1 (by rfl) ⟨1032533, by rfl⟩ : syracuseStep 1376711 = 2065067) B2065067
theorem B1311175 : Blo 610295 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B655823 : Blo 610295 655823 := bstep (se 1 (by rfl) ⟨491867, by rfl⟩ : syracuseStep 655823 = 983735) B983735
theorem B917993 : Blo 610295 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B8520187 : Blo 610295 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B2064959 : Blo 610295 2064959 := bstep (se 1 (by rfl) ⟨1548719, by rfl⟩ : syracuseStep 2064959 = 3097439) B3097439
theorem B918119 : Blo 610295 918119 := bstep (se 1 (by rfl) ⟨688589, by rfl⟩ : syracuseStep 918119 = 1377179) B1377179
theorem B918251 : Blo 610295 918251 := bstep (se 1 (by rfl) ⟨688688, by rfl⟩ : syracuseStep 918251 = 1377377) B1377377
theorem B918281 : Blo 610295 918281 := bstep (se 2 (by rfl) ⟨344355, by rfl⟩ : syracuseStep 918281 = 688711) B688711
theorem B1377071 : Blo 610295 1377071 := bstep (se 1 (by rfl) ⟨1032803, by rfl⟩ : syracuseStep 1377071 = 2065607) B2065607
theorem B918383 : Blo 610295 918383 := bstep (se 1 (by rfl) ⟨688787, by rfl⟩ : syracuseStep 918383 = 1377575) B1377575
theorem B2622419 : Blo 610295 2622419 := bstep (se 1 (by rfl) ⟨1966814, by rfl⟩ : syracuseStep 2622419 = 3933629) B3933629
theorem B689215 : Blo 610295 689215 := bstep (se 1 (by rfl) ⟨516911, by rfl⟩ : syracuseStep 689215 = 1033823) B1033823
theorem B918635 : Blo 610295 918635 := bstep (se 1 (by rfl) ⟨688976, by rfl⟩ : syracuseStep 918635 = 1377953) B1377953
theorem B9077953 : Blo 610295 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B689359 : Blo 610295 689359 := bstep (se 1 (by rfl) ⟨517019, by rfl⟩ : syracuseStep 689359 = 1034039) B1034039
theorem B918875 : Blo 610295 918875 := bstep (se 1 (by rfl) ⟨689156, by rfl⟩ : syracuseStep 918875 = 1378313) B1378313
theorem B1738199 : Blo 610295 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B2328061 : Blo 610295 2328061 := bstep (se 3 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 2328061 = 873023) B873023
theorem B919151 : Blo 610295 919151 := bstep (se 1 (by rfl) ⟨689363, by rfl⟩ : syracuseStep 919151 = 1378727) B1378727
theorem B1967777 : Blo 610295 1967777 := bstep (se 2 (by rfl) ⟨737916, by rfl⟩ : syracuseStep 1967777 = 1475833) B1475833
theorem B919223 : Blo 610295 919223 := bstep (se 1 (by rfl) ⟨689417, by rfl⟩ : syracuseStep 919223 = 1378835) B1378835
theorem B919259 : Blo 610295 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B1378079 : Blo 610295 1378079 := bstep (se 1 (by rfl) ⟨1033559, by rfl⟩ : syracuseStep 1378079 = 2067119) B2067119
theorem B2066255 : Blo 610295 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B3770219 : Blo 610295 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B919433 : Blo 610295 919433 := bstep (se 2 (by rfl) ⟨344787, by rfl⟩ : syracuseStep 919433 = 689575) B689575
theorem B919535 : Blo 610295 919535 := bstep (se 1 (by rfl) ⟨689651, by rfl⟩ : syracuseStep 919535 = 1379303) B1379303
theorem B1378295 : Blo 610295 1378295 := bstep (se 1 (by rfl) ⟨1033721, by rfl⟩ : syracuseStep 1378295 = 2067443) B2067443
theorem B2066579 : Blo 610295 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B690331 : Blo 610295 690331 := bstep (se 1 (by rfl) ⟨517748, by rfl⟩ : syracuseStep 690331 = 1035497) B1035497
theorem B690367 : Blo 610295 690367 := bstep (se 1 (by rfl) ⟨517775, by rfl⟩ : syracuseStep 690367 = 1035551) B1035551
theorem B22382801 : Blo 610295 22382801 := bstep (se 2 (by rfl) ⟨8393550, by rfl⟩ : syracuseStep 22382801 = 16787101) B16787101
theorem B919787 : Blo 610295 919787 := bstep (se 1 (by rfl) ⟨689840, by rfl⟩ : syracuseStep 919787 = 1379681) B1379681
theorem B919847 : Blo 610295 919847 := bstep (se 1 (by rfl) ⟨689885, by rfl⟩ : syracuseStep 919847 = 1379771) B1379771
theorem B1378655 : Blo 610295 1378655 := bstep (se 1 (by rfl) ⟨1033991, by rfl⟩ : syracuseStep 1378655 = 2067983) B2067983
theorem B919931 : Blo 610295 919931 := bstep (se 1 (by rfl) ⟨689948, by rfl⟩ : syracuseStep 919931 = 1379897) B1379897
theorem B2066849 : Blo 610295 2066849 := bstep (se 2 (by rfl) ⟨775068, by rfl⟩ : syracuseStep 2066849 = 1550137) B1550137
theorem B920201 : Blo 610295 920201 := bstep (se 2 (by rfl) ⟨345075, by rfl⟩ : syracuseStep 920201 = 690151) B690151
theorem B7441085 : Blo 610295 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B920375 : Blo 610295 920375 := bstep (se 1 (by rfl) ⟨690281, by rfl⟩ : syracuseStep 920375 = 1380563) B1380563
theorem B920411 : Blo 610295 920411 := bstep (se 1 (by rfl) ⟨690308, by rfl⟩ : syracuseStep 920411 = 1380617) B1380617
theorem B920555 : Blo 610295 920555 := bstep (se 1 (by rfl) ⟨690416, by rfl⟩ : syracuseStep 920555 = 1380833) B1380833
theorem B1379375 : Blo 610295 1379375 := bstep (se 1 (by rfl) ⟨1034531, by rfl⟩ : syracuseStep 1379375 = 2069063) B2069063
theorem B1739873 : Blo 610295 1739873 := bstep (se 2 (by rfl) ⟨652452, by rfl⟩ : syracuseStep 1739873 = 1304905) B1304905
theorem B920759 : Blo 610295 920759 := bstep (se 1 (by rfl) ⟨690569, by rfl⟩ : syracuseStep 920759 = 1381139) B1381139
theorem B2329823 : Blo 610295 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B1379663 : Blo 610295 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B920999 : Blo 610295 920999 := bstep (se 1 (by rfl) ⟨690749, by rfl⟩ : syracuseStep 920999 = 1381499) B1381499
theorem B1379753 : Blo 610295 1379753 := bstep (se 2 (by rfl) ⟨517407, by rfl⟩ : syracuseStep 1379753 = 1034815) B1034815
theorem B921083 : Blo 610295 921083 := bstep (se 1 (by rfl) ⟨690812, by rfl⟩ : syracuseStep 921083 = 1381625) B1381625
theorem B2657855 : Blo 610295 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B921179 : Blo 610295 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B921263 : Blo 610295 921263 := bstep (se 1 (by rfl) ⟨690947, by rfl⟩ : syracuseStep 921263 = 1381895) B1381895
theorem B921383 : Blo 610295 921383 := bstep (se 1 (by rfl) ⟨691037, by rfl⟩ : syracuseStep 921383 = 1382075) B1382075
theorem B1380239 : Blo 610295 1380239 := bstep (se 1 (by rfl) ⟨1035179, by rfl⟩ : syracuseStep 1380239 = 2070359) B2070359
theorem B7049369 : Blo 610295 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B4657337 : Blo 610295 4657337 := bstep (se 2 (by rfl) ⟨1746501, by rfl⟩ : syracuseStep 4657337 = 3493003) B3493003
theorem B1740989 : Blo 610295 1740989 := bstep (se 3 (by rfl) ⟨326435, by rfl⟩ : syracuseStep 1740989 = 652871) B652871
theorem B7835885 : Blo 610295 7835885 := bstep (se 3 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 7835885 = 2938457) B2938457
theorem B2068847 : Blo 610295 2068847 := bstep (se 1 (by rfl) ⟨1551635, by rfl⟩ : syracuseStep 2068847 = 3103271) B3103271
theorem B627071 : Blo 610295 627071 := bstep (se 1 (by rfl) ⟨470303, by rfl⟩ : syracuseStep 627071 = 940607) B940607
theorem B1380959 : Blo 610295 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B2331251 : Blo 610295 2331251 := bstep (se 1 (by rfl) ⟨1748438, by rfl⟩ : syracuseStep 2331251 = 3496877) B3496877
theorem B57480101 : Blo 610295 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B2331935 : Blo 610295 2331935 := bstep (se 1 (by rfl) ⟨1748951, by rfl⟩ : syracuseStep 2331935 = 3497903) B3497903
theorem B1381787 : Blo 610295 1381787 := bstep (se 1 (by rfl) ⟨1036340, by rfl⟩ : syracuseStep 1381787 = 2072681) B2072681
theorem B14358059 : Blo 610295 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B2070251 : Blo 610295 2070251 := bstep (se 1 (by rfl) ⟨1552688, by rfl⟩ : syracuseStep 2070251 = 3105377) B3105377
theorem B1546199 : Blo 610295 1546199 := bstep (se 1 (by rfl) ⟨1159649, by rfl⟩ : syracuseStep 1546199 = 2319299) B2319299
theorem B2070521 : Blo 610295 2070521 := bstep (se 2 (by rfl) ⟨776445, by rfl⟩ : syracuseStep 2070521 = 1552891) B1552891
theorem B2070683 : Blo 610295 2070683 := bstep (se 1 (by rfl) ⟨1553012, by rfl⟩ : syracuseStep 2070683 = 3106025) B3106025
theorem B2201755 : Blo 610295 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B2070791 : Blo 610295 2070791 := bstep (se 1 (by rfl) ⟨1553093, by rfl⟩ : syracuseStep 2070791 = 3106187) B3106187
theorem B1744087 : Blo 610295 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B2071817 : Blo 610295 2071817 := bstep (se 2 (by rfl) ⟨776931, by rfl⟩ : syracuseStep 2071817 = 1553863) B1553863
theorem B1547687 : Blo 610295 1547687 := bstep (se 1 (by rfl) ⟨1160765, by rfl⟩ : syracuseStep 1547687 = 2321531) B2321531
theorem B16752071 : Blo 610295 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B3349991 : Blo 610295 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B6954659 : Blo 610295 6954659 := bstep (se 1 (by rfl) ⟨5215994, by rfl⟩ : syracuseStep 6954659 = 10431989) B10431989
theorem B2072951 : Blo 610295 2072951 := bstep (se 1 (by rfl) ⟨1554713, by rfl⟩ : syracuseStep 2072951 = 3109427) B3109427
theorem B1745819 : Blo 610295 1745819 := bstep (se 1 (by rfl) ⟨1309364, by rfl⟩ : syracuseStep 1745819 = 2618729) B2618729
theorem B1745945 : Blo 610295 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B6629003 : Blo 610295 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B1746593 : Blo 610295 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B3483323 : Blo 610295 3483323 := bstep (se 1 (by rfl) ⟨2612492, by rfl⟩ : syracuseStep 3483323 = 5224985) B5224985
theorem B32188265 : Blo 610295 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1550279 : Blo 610295 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B19867801 : Blo 610295 19867801 := bstep (se 2 (by rfl) ⟨7450425, by rfl⟩ : syracuseStep 19867801 = 14900851) B14900851
theorem B5287133 : Blo 610295 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B1748587 : Blo 610295 1748587 := bstep (se 1 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 1748587 = 2622881) B2622881
theorem B3092093 : Blo 610295 3092093 := bstep (se 3 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 3092093 = 1159535) B1159535
theorem B1650451 : Blo 610295 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B5582857 : Blo 610295 5582857 := bstep (se 2 (by rfl) ⟨2093571, by rfl⟩ : syracuseStep 5582857 = 4187143) B4187143
theorem B3092903 : Blo 610295 3092903 := bstep (se 1 (by rfl) ⟨2319677, by rfl⟩ : syracuseStep 3092903 = 4639355) B4639355
theorem B3912407 : Blo 610295 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B2798327 : Blo 610295 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1651585 : Blo 610295 1651585 := bstep (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) B1238689
theorem B2208977 : Blo 610295 2208977 := bstep (se 2 (by rfl) ⟨828366, by rfl⟩ : syracuseStep 2208977 = 1656733) B1656733
theorem B5584283 : Blo 610295 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B4961735 : Blo 610295 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B3094199 : Blo 610295 3094199 := bstep (se 1 (by rfl) ⟨2320649, by rfl⟩ : syracuseStep 3094199 = 4641299) B4641299
theorem B1160887 : Blo 610295 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B931547 : Blo 610295 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B3913535 : Blo 610295 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B3979145 : Blo 610295 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B4405211 : Blo 610295 4405211 := bstep (se 1 (by rfl) ⟨3303908, by rfl⟩ : syracuseStep 4405211 = 6607817) B6607817
theorem B1161191 : Blo 610295 1161191 := bstep (se 1 (by rfl) ⟨870893, by rfl⟩ : syracuseStep 1161191 = 1741787) B1741787
theorem B6994025 : Blo 610295 6994025 := bstep (se 2 (by rfl) ⟨2622759, by rfl⟩ : syracuseStep 6994025 = 5245519) B5245519
theorem B1161449 : Blo 610295 1161449 := bstep (se 2 (by rfl) ⟨435543, by rfl⟩ : syracuseStep 1161449 = 871087) B871087
theorem B1161479 : Blo 610295 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B36190475 : Blo 610295 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B1030441 : Blo 610295 1030441 := bstep (se 2 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 1030441 = 772831) B772831
theorem B1489823 : Blo 610295 1489823 := bstep (se 1 (by rfl) ⟨1117367, by rfl⟩ : syracuseStep 1489823 = 2234735) B2234735
theorem B4177079 : Blo 610295 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B1162505 : Blo 610295 1162505 := bstep (se 2 (by rfl) ⟨435939, by rfl⟩ : syracuseStep 1162505 = 871879) B871879
theorem B3915175 : Blo 610295 3915175 := bstep (se 1 (by rfl) ⟨2936381, by rfl⟩ : syracuseStep 3915175 = 5872763) B5872763
theorem B1031771 : Blo 610295 1031771 := bstep (se 1 (by rfl) ⟨773828, by rfl⟩ : syracuseStep 1031771 = 1547657) B1547657
theorem B1032007 : Blo 610295 1032007 := bstep (se 1 (by rfl) ⟨774005, by rfl⟩ : syracuseStep 1032007 = 1548011) B1548011
theorem B1032655 : Blo 610295 1032655 := bstep (se 1 (by rfl) ⟨774491, by rfl⟩ : syracuseStep 1032655 = 1548983) B1548983
theorem B16761613 : Blo 610295 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B869287 : Blo 610295 869287 := bstep (se 1 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 869287 = 1303931) B1303931
theorem B1033391 : Blo 610295 1033391 := bstep (se 1 (by rfl) ⟨775043, by rfl⟩ : syracuseStep 1033391 = 1550087) B1550087
theorem B1033627 : Blo 610295 1033627 := bstep (se 1 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 1033627 = 1550441) B1550441
theorem B870107 : Blo 610295 870107 := bstep (se 1 (by rfl) ⟨652580, by rfl⟩ : syracuseStep 870107 = 1305161) B1305161
theorem B1033951 : Blo 610295 1033951 := bstep (se 1 (by rfl) ⟨775463, by rfl⟩ : syracuseStep 1033951 = 1550927) B1550927
theorem B4409129 : Blo 610295 4409129 := bstep (se 2 (by rfl) ⟨1653423, by rfl⟩ : syracuseStep 4409129 = 3306847) B3306847
theorem B7850033 : Blo 610295 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B1099919 : Blo 610295 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B1034383 : Blo 610295 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B26560979 : Blo 610295 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B2607623 : Blo 610295 2607623 := bstep (se 1 (by rfl) ⟨1955717, by rfl⟩ : syracuseStep 2607623 = 3911435) B3911435
theorem B2837207 : Blo 610295 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B1035335 : Blo 610295 1035335 := bstep (se 1 (by rfl) ⟨776501, by rfl⟩ : syracuseStep 1035335 = 1553003) B1553003
theorem B871759 : Blo 610295 871759 := bstep (se 1 (by rfl) ⟨653819, by rfl⟩ : syracuseStep 871759 = 1307639) B1307639
theorem B1101223 : Blo 610295 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B5230007 : Blo 610295 5230007 := bstep (se 1 (by rfl) ⟨3922505, by rfl⟩ : syracuseStep 5230007 = 7845011) B7845011
theorem B1035767 : Blo 610295 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B1658441 : Blo 610295 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B3100355 : Blo 610295 3100355 := bstep (se 1 (by rfl) ⟨2325266, by rfl⟩ : syracuseStep 3100355 = 4650533) B4650533
theorem B5590889 : Blo 610295 5590889 := bstep (se 2 (by rfl) ⟨2096583, by rfl⟩ : syracuseStep 5590889 = 4193167) B4193167
theorem B1101691 : Blo 610295 1101691 := bstep (se 1 (by rfl) ⟨826268, by rfl⟩ : syracuseStep 1101691 = 1652537) B1652537
theorem B610535 : Blo 610295 610535 := bstep (se 1 (by rfl) ⟨457901, by rfl⟩ : syracuseStep 610535 = 915803) B915803
theorem B610687 : Blo 610295 610687 := bstep (se 1 (by rfl) ⟨458015, by rfl⟩ : syracuseStep 610687 = 916031) B916031
theorem B610767 : Blo 610295 610767 := bstep (se 1 (by rfl) ⟨458075, by rfl⟩ : syracuseStep 610767 = 916151) B916151
theorem B2609759 : Blo 610295 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B610919 : Blo 610295 610919 := bstep (se 1 (by rfl) ⟨458189, by rfl⟩ : syracuseStep 610919 = 916379) B916379
theorem B3920507 : Blo 610295 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B2609981 : Blo 610295 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B611183 : Blo 610295 611183 := bstep (se 1 (by rfl) ⟨458387, by rfl⟩ : syracuseStep 611183 = 916775) B916775
theorem B611239 : Blo 610295 611239 := bstep (se 1 (by rfl) ⟨458429, by rfl⟩ : syracuseStep 611239 = 916859) B916859
theorem B611323 : Blo 610295 611323 := bstep (se 1 (by rfl) ⟨458492, by rfl⟩ : syracuseStep 611323 = 916985) B916985
theorem B611391 : Blo 610295 611391 := bstep (se 1 (by rfl) ⟨458543, by rfl⟩ : syracuseStep 611391 = 917087) B917087
theorem B611535 : Blo 610295 611535 := bstep (se 1 (by rfl) ⟨458651, by rfl⟩ : syracuseStep 611535 = 917303) B917303
theorem B8377577 : Blo 610295 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B611739 : Blo 610295 611739 := bstep (se 1 (by rfl) ⟨458804, by rfl⟩ : syracuseStep 611739 = 917609) B917609
theorem B611951 : Blo 610295 611951 := bstep (se 1 (by rfl) ⟨458963, by rfl⟩ : syracuseStep 611951 = 917927) B917927
theorem B612007 : Blo 610295 612007 := bstep (se 1 (by rfl) ⟨459005, by rfl⟩ : syracuseStep 612007 = 918011) B918011
theorem B612091 : Blo 610295 612091 := bstep (se 1 (by rfl) ⟨459068, by rfl⟩ : syracuseStep 612091 = 918137) B918137
theorem B612127 : Blo 610295 612127 := bstep (se 1 (by rfl) ⟨459095, by rfl⟩ : syracuseStep 612127 = 918191) B918191
theorem B3495737 : Blo 610295 3495737 := bstep (se 2 (by rfl) ⟨1310901, by rfl⟩ : syracuseStep 3495737 = 2621803) B2621803
theorem B612159 : Blo 610295 612159 := bstep (se 1 (by rfl) ⟨459119, by rfl⟩ : syracuseStep 612159 = 918239) B918239
theorem B612335 : Blo 610295 612335 := bstep (se 1 (by rfl) ⟨459251, by rfl⟩ : syracuseStep 612335 = 918503) B918503
theorem B3495919 : Blo 610295 3495919 := bstep (se 1 (by rfl) ⟨2621939, by rfl⟩ : syracuseStep 3495919 = 5243879) B5243879
theorem B612507 : Blo 610295 612507 := bstep (se 1 (by rfl) ⟨459380, by rfl⟩ : syracuseStep 612507 = 918761) B918761
theorem B612543 : Blo 610295 612543 := bstep (se 1 (by rfl) ⟨459407, by rfl⟩ : syracuseStep 612543 = 918815) B918815
theorem B2611399 : Blo 610295 2611399 := bstep (se 1 (by rfl) ⟨1958549, by rfl⟩ : syracuseStep 2611399 = 3917099) B3917099
theorem B612655 : Blo 610295 612655 := bstep (se 1 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 612655 = 918983) B918983
theorem B2480491 : Blo 610295 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B7428631 : Blo 610295 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B612891 : Blo 610295 612891 := bstep (se 1 (by rfl) ⟨459668, by rfl⟩ : syracuseStep 612891 = 919337) B919337
theorem B612895 : Blo 610295 612895 := bstep (se 1 (by rfl) ⟨459671, by rfl⟩ : syracuseStep 612895 = 919343) B919343
theorem B11950679 : Blo 610295 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B613211 : Blo 610295 613211 := bstep (se 1 (by rfl) ⟨459908, by rfl⟩ : syracuseStep 613211 = 919817) B919817
theorem B613279 : Blo 610295 613279 := bstep (se 1 (by rfl) ⟨459959, by rfl⟩ : syracuseStep 613279 = 919919) B919919
theorem B613423 : Blo 610295 613423 := bstep (se 1 (by rfl) ⟨460067, by rfl⟩ : syracuseStep 613423 = 920135) B920135
theorem B613447 : Blo 610295 613447 := bstep (se 1 (by rfl) ⟨460085, by rfl⟩ : syracuseStep 613447 = 920171) B920171
theorem B4775057 : Blo 610295 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B613599 : Blo 610295 613599 := bstep (se 1 (by rfl) ⟨460199, by rfl⟩ : syracuseStep 613599 = 920399) B920399
theorem B3497377 : Blo 610295 3497377 := bstep (se 2 (by rfl) ⟨1311516, by rfl⟩ : syracuseStep 3497377 = 2623033) B2623033
theorem B1105319 : Blo 610295 1105319 := bstep (se 1 (by rfl) ⟨828989, by rfl⟩ : syracuseStep 1105319 = 1657979) B1657979
theorem B1957331 : Blo 610295 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B613863 : Blo 610295 613863 := bstep (se 1 (by rfl) ⟨460397, by rfl⟩ : syracuseStep 613863 = 920795) B920795
theorem B613979 : Blo 610295 613979 := bstep (se 1 (by rfl) ⟨460484, by rfl⟩ : syracuseStep 613979 = 920969) B920969
theorem B3104567 : Blo 610295 3104567 := bstep (se 1 (by rfl) ⟨2328425, by rfl⟩ : syracuseStep 3104567 = 4656851) B4656851
theorem B614215 : Blo 610295 614215 := bstep (se 1 (by rfl) ⟨460661, by rfl⟩ : syracuseStep 614215 = 921323) B921323
theorem B529915877 : Blo 610295 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B10182827 : Blo 610295 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B4415735 : Blo 610295 4415735 := bstep (se 1 (by rfl) ⟨3311801, by rfl⟩ : syracuseStep 4415735 = 6623603) B6623603
theorem B2941265 : Blo 610295 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B5235131 : Blo 610295 5235131 := bstep (se 1 (by rfl) ⟨3926348, by rfl⟩ : syracuseStep 5235131 = 7852697) B7852697
theorem B2319101 : Blo 610295 2319101 := bstep (se 3 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 2319101 = 869663) B869663
theorem B5039003 : Blo 610295 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B1106939 : Blo 610295 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B2352559 : Blo 610295 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B3728911 : Blo 610295 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B3729083 : Blo 610295 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B14903189 : Blo 610295 14903189 := bstep (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) B698587
theorem B3106835 : Blo 610295 3106835 := bstep (se 1 (by rfl) ⟨2330126, by rfl⟩ : syracuseStep 3106835 = 4660253) B4660253
theorem B3926555 : Blo 610295 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B6975071 : Blo 610295 6975071 := bstep (se 1 (by rfl) ⟨5231303, by rfl⟩ : syracuseStep 6975071 = 10462607) B10462607
theorem B2059883 : Blo 610295 2059883 := bstep (se 1 (by rfl) ⟨1544912, by rfl⟩ : syracuseStep 2059883 = 3089825) B3089825
theorem B16805501 : Blo 610295 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B2060153 : Blo 610295 2060153 := bstep (se 2 (by rfl) ⟨772557, by rfl⟩ : syracuseStep 2060153 = 1545115) B1545115
theorem B22409095 : Blo 610295 22409095 := bstep (se 1 (by rfl) ⟨16806821, by rfl⟩ : syracuseStep 22409095 = 33613643) B33613643
theorem B2060477 : Blo 610295 2060477 := bstep (se 3 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 2060477 = 772679) B772679
theorem B1962407 : Blo 610295 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B10449485 : Blo 610295 10449485 := bstep (se 3 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 10449485 = 3918557) B3918557
theorem B1373291 : Blo 610295 1373291 := bstep (se 1 (by rfl) ⟨1029968, by rfl⟩ : syracuseStep 1373291 = 2059937) B2059937
theorem B2618507 : Blo 610295 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B8615159 : Blo 610295 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B2061665 : Blo 610295 2061665 := bstep (se 2 (by rfl) ⟨773124, by rfl⟩ : syracuseStep 2061665 = 1546249) B1546249
theorem B1373867 : Blo 610295 1373867 := bstep (se 1 (by rfl) ⟨1030400, by rfl⟩ : syracuseStep 1373867 = 2060801) B2060801
theorem B3405523 : Blo 610295 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B980767 : Blo 610295 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B1374191 : Blo 610295 1374191 := bstep (se 1 (by rfl) ⟨1030643, by rfl⟩ : syracuseStep 1374191 = 2061287) B2061287
theorem B915449 : Blo 610295 915449 := bstep (se 2 (by rfl) ⟨343293, by rfl⟩ : syracuseStep 915449 = 686587) B686587
theorem B915551 : Blo 610295 915551 := bstep (se 1 (by rfl) ⟨686663, by rfl⟩ : syracuseStep 915551 = 1373327) B1373327
theorem B5896289 : Blo 610295 5896289 := bstep (se 2 (by rfl) ⟨2211108, by rfl⟩ : syracuseStep 5896289 = 4422217) B4422217
theorem B915611 : Blo 610295 915611 := bstep (se 1 (by rfl) ⟨686708, by rfl⟩ : syracuseStep 915611 = 1373417) B1373417
theorem B915647 : Blo 610295 915647 := bstep (se 1 (by rfl) ⟨686735, by rfl⟩ : syracuseStep 915647 = 1373471) B1373471
theorem B1374407 : Blo 610295 1374407 := bstep (se 1 (by rfl) ⟨1030805, by rfl⟩ : syracuseStep 1374407 = 2061611) B2061611
theorem B915689 : Blo 610295 915689 := bstep (se 2 (by rfl) ⟨343383, by rfl⟩ : syracuseStep 915689 = 686767) B686767
theorem B1374587 : Blo 610295 1374587 := bstep (se 1 (by rfl) ⟨1030940, by rfl⟩ : syracuseStep 1374587 = 2061881) B2061881
theorem B915995 : Blo 610295 915995 := bstep (se 1 (by rfl) ⟨686996, by rfl⟩ : syracuseStep 915995 = 1373993) B1373993
theorem B686623 : Blo 610295 686623 := bstep (se 1 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 686623 = 1029935) B1029935
theorem B916073 : Blo 610295 916073 := bstep (se 2 (by rfl) ⟨343527, by rfl⟩ : syracuseStep 916073 = 687055) B687055
theorem B1374857 : Blo 610295 1374857 := bstep (se 2 (by rfl) ⟨515571, by rfl⟩ : syracuseStep 1374857 = 1031143) B1031143
theorem B2325145 : Blo 610295 2325145 := bstep (se 2 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 2325145 = 1743859) B1743859
theorem B916601 : Blo 610295 916601 := bstep (se 2 (by rfl) ⟨343725, by rfl⟩ : syracuseStep 916601 = 687451) B687451
theorem B1375415 : Blo 610295 1375415 := bstep (se 1 (by rfl) ⟨1031561, by rfl⟩ : syracuseStep 1375415 = 2063123) B2063123
theorem B916703 : Blo 610295 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B2063609 : Blo 610295 2063609 := bstep (se 2 (by rfl) ⟨773853, by rfl⟩ : syracuseStep 2063609 = 1547707) B1547707
theorem B916745 : Blo 610295 916745 := bstep (se 2 (by rfl) ⟨343779, by rfl⟩ : syracuseStep 916745 = 687559) B687559
theorem B916847 : Blo 610295 916847 := bstep (se 1 (by rfl) ⟨687635, by rfl⟩ : syracuseStep 916847 = 1375271) B1375271
theorem B1244527 : Blo 610295 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B916967 : Blo 610295 916967 := bstep (se 1 (by rfl) ⟨687725, by rfl⟩ : syracuseStep 916967 = 1375451) B1375451
theorem B2063879 : Blo 610295 2063879 := bstep (se 1 (by rfl) ⟨1547909, by rfl⟩ : syracuseStep 2063879 = 3095819) B3095819
theorem B7962137 : Blo 610295 7962137 := bstep (se 2 (by rfl) ⟨2985801, by rfl⟩ : syracuseStep 7962137 = 5971603) B5971603
theorem B917099 : Blo 610295 917099 := bstep (se 1 (by rfl) ⟨687824, by rfl⟩ : syracuseStep 917099 = 1375649) B1375649
theorem B917225 : Blo 610295 917225 := bstep (se 2 (by rfl) ⟨343959, by rfl⟩ : syracuseStep 917225 = 687919) B687919
theorem B1375991 : Blo 610295 1375991 := bstep (se 1 (by rfl) ⟨1031993, by rfl⟩ : syracuseStep 1375991 = 2063987) B2063987
theorem B917369 : Blo 610295 917369 := bstep (se 2 (by rfl) ⟨344013, by rfl⟩ : syracuseStep 917369 = 688027) B688027
theorem B1376171 : Blo 610295 1376171 := bstep (se 1 (by rfl) ⟨1032128, by rfl⟩ : syracuseStep 1376171 = 2064257) B2064257
theorem B1965995 : Blo 610295 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B917471 : Blo 610295 917471 := bstep (se 1 (by rfl) ⟨688103, by rfl⟩ : syracuseStep 917471 = 1376207) B1376207
theorem B3932347 : Blo 610295 3932347 := bstep (se 1 (by rfl) ⟨2949260, by rfl⟩ : syracuseStep 3932347 = 5898521) B5898521
theorem B917807 : Blo 610295 917807 := bstep (se 1 (by rfl) ⟨688355, by rfl⟩ : syracuseStep 917807 = 1376711) B1376711
theorem B1376639 : Blo 610295 1376639 := bstep (se 1 (by rfl) ⟨1032479, by rfl⟩ : syracuseStep 1376639 = 2064959) B2064959
theorem B918047 : Blo 610295 918047 := bstep (se 1 (by rfl) ⟨688535, by rfl⟩ : syracuseStep 918047 = 1377071) B1377071
theorem B1376873 : Blo 610295 1376873 := bstep (se 2 (by rfl) ⟨516327, by rfl⟩ : syracuseStep 1376873 = 1032655) B1032655
theorem B688927 : Blo 610295 688927 := bstep (se 1 (by rfl) ⟨516695, by rfl⟩ : syracuseStep 688927 = 1033391) B1033391
theorem B22348817 : Blo 610295 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B1311851 : Blo 610295 1311851 := bstep (se 1 (by rfl) ⟨983888, by rfl⟩ : syracuseStep 1311851 = 1967777) B1967777
theorem B918719 : Blo 610295 918719 := bstep (se 1 (by rfl) ⟨689039, by rfl⟩ : syracuseStep 918719 = 1378079) B1378079
theorem B1377503 : Blo 610295 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B918863 : Blo 610295 918863 := bstep (se 1 (by rfl) ⟨689147, by rfl⟩ : syracuseStep 918863 = 1378295) B1378295
theorem B918953 : Blo 610295 918953 := bstep (se 2 (by rfl) ⟨344607, by rfl⟩ : syracuseStep 918953 = 689215) B689215
theorem B1377719 : Blo 610295 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B919103 : Blo 610295 919103 := bstep (se 1 (by rfl) ⟨689327, by rfl⟩ : syracuseStep 919103 = 1378655) B1378655
theorem B919145 : Blo 610295 919145 := bstep (se 2 (by rfl) ⟨344679, by rfl⟩ : syracuseStep 919145 = 689359) B689359
theorem B1377899 : Blo 610295 1377899 := bstep (se 1 (by rfl) ⟨1033424, by rfl⟩ : syracuseStep 1377899 = 2066849) B2066849
theorem B1738415 : Blo 610295 1738415 := bstep (se 1 (by rfl) ⟨1303811, by rfl⟩ : syracuseStep 1738415 = 2607623) B2607623
theorem B1378169 : Blo 610295 1378169 := bstep (se 2 (by rfl) ⟨516813, by rfl⟩ : syracuseStep 1378169 = 1033627) B1033627
theorem B919583 : Blo 610295 919583 := bstep (se 1 (by rfl) ⟨689687, by rfl⟩ : syracuseStep 919583 = 1379375) B1379375
theorem B690223 : Blo 610295 690223 := bstep (se 1 (by rfl) ⟨517667, by rfl⟩ : syracuseStep 690223 = 1035335) B1035335
theorem B919775 : Blo 610295 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B919835 : Blo 610295 919835 := bstep (se 1 (by rfl) ⟨689876, by rfl⟩ : syracuseStep 919835 = 1379753) B1379753
theorem B1378601 : Blo 610295 1378601 := bstep (se 2 (by rfl) ⟨516975, by rfl⟩ : syracuseStep 1378601 = 1033951) B1033951
theorem B690511 : Blo 610295 690511 := bstep (se 1 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 690511 = 1035767) B1035767
theorem B1771903 : Blo 610295 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B2066903 : Blo 610295 2066903 := bstep (se 1 (by rfl) ⟨1550177, by rfl⟩ : syracuseStep 2066903 = 3100355) B3100355
theorem B920159 : Blo 610295 920159 := bstep (se 1 (by rfl) ⟨690119, by rfl⟩ : syracuseStep 920159 = 1380239) B1380239
theorem B1379177 : Blo 610295 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B920441 : Blo 610295 920441 := bstep (se 2 (by rfl) ⟨345165, by rfl⟩ : syracuseStep 920441 = 690331) B690331
theorem B1379231 : Blo 610295 1379231 := bstep (se 1 (by rfl) ⟨1034423, by rfl⟩ : syracuseStep 1379231 = 2068847) B2068847
theorem B920489 : Blo 610295 920489 := bstep (se 2 (by rfl) ⟨345183, by rfl⟩ : syracuseStep 920489 = 690367) B690367
theorem B1739839 : Blo 610295 1739839 := bstep (se 1 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 1739839 = 2609759) B2609759
theorem B920639 : Blo 610295 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1739987 : Blo 610295 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B921191 : Blo 610295 921191 := bstep (se 1 (by rfl) ⟨690893, by rfl⟩ : syracuseStep 921191 = 1381787) B1381787
theorem B9572039 : Blo 610295 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1380167 : Blo 610295 1380167 := bstep (se 1 (by rfl) ⟨1035125, by rfl⟩ : syracuseStep 1380167 = 2070251) B2070251
theorem B2330491 : Blo 610295 2330491 := bstep (se 1 (by rfl) ⟨1747868, by rfl⟩ : syracuseStep 2330491 = 3495737) B3495737
theorem B6688757 : Blo 610295 6688757 := bstep (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) B627071
theorem B1380347 : Blo 610295 1380347 := bstep (se 1 (by rfl) ⟨1035260, by rfl⟩ : syracuseStep 1380347 = 2070521) B2070521
theorem B1380455 : Blo 610295 1380455 := bstep (se 1 (by rfl) ⟨1035341, by rfl⟩ : syracuseStep 1380455 = 2070683) B2070683
theorem B1380527 : Blo 610295 1380527 := bstep (se 1 (by rfl) ⟨1035395, by rfl⟩ : syracuseStep 1380527 = 2070791) B2070791
theorem B7967119 : Blo 610295 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B3183371 : Blo 610295 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B2331449 : Blo 610295 2331449 := bstep (se 2 (by rfl) ⟨874293, by rfl⟩ : syracuseStep 2331449 = 1748587) B1748587
theorem B1381211 : Blo 610295 1381211 := bstep (se 1 (by rfl) ⟨1035908, by rfl⟩ : syracuseStep 1381211 = 2071817) B2071817
theorem B2233327 : Blo 610295 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2200601 : Blo 610295 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B2069711 : Blo 610295 2069711 := bstep (se 1 (by rfl) ⟨1552283, by rfl⟩ : syracuseStep 2069711 = 3104567) B3104567
theorem B353277251 : Blo 610295 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B7443809 : Blo 610295 7443809 := bstep (se 2 (by rfl) ⟨2791428, by rfl⟩ : syracuseStep 7443809 = 5582857) B5582857
theorem B6788551 : Blo 610295 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B1381967 : Blo 610295 1381967 := bstep (se 1 (by rfl) ⟨1036475, by rfl⟩ : syracuseStep 1381967 = 2072951) B2072951
theorem B1546067 : Blo 610295 1546067 := bstep (se 1 (by rfl) ⟨1159550, by rfl⟩ : syracuseStep 1546067 = 2319101) B2319101
theorem B2202113 : Blo 610295 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B9935459 : Blo 610295 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B2071223 : Blo 610295 2071223 := bstep (se 1 (by rfl) ⟨1553417, by rfl⟩ : syracuseStep 2071223 = 3106835) B3106835
theorem B1547849 : Blo 610295 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B4661225 : Blo 610295 4661225 := bstep (se 2 (by rfl) ⟨1747959, by rfl⟩ : syracuseStep 4661225 = 3495919) B3495919
theorem B3481865 : Blo 610295 3481865 := bstep (se 2 (by rfl) ⟨1305699, by rfl⟩ : syracuseStep 3481865 = 2611399) B2611399
theorem B14099021 : Blo 610295 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B9904841 : Blo 610295 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B1745671 : Blo 610295 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B5743439 : Blo 610295 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B5219549 : Blo 610295 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B4662683 : Blo 610295 4662683 := bstep (se 1 (by rfl) ⟨3497012, by rfl⟩ : syracuseStep 4662683 = 6994025) B6994025
theorem B24126983 : Blo 610295 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B4663169 : Blo 610295 4663169 := bstep (se 2 (by rfl) ⟨1748688, by rfl⟩ : syracuseStep 4663169 = 3497377) B3497377
theorem B5220233 : Blo 610295 5220233 := bstep (se 2 (by rfl) ⟨1957587, by rfl⟩ : syracuseStep 5220233 = 3915175) B3915175
theorem B993215 : Blo 610295 993215 := bstep (se 1 (by rfl) ⟨744911, by rfl⟩ : syracuseStep 993215 = 1489823) B1489823
theorem B5875685 : Blo 610295 5875685 := bstep (se 4 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 5875685 = 1101691) B1101691
theorem B4893929 : Blo 610295 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B1748233 : Blo 610295 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B1748279 : Blo 610295 1748279 := bstep (se 1 (by rfl) ⟨1311209, by rfl⟩ : syracuseStep 1748279 = 2622419) B2622419
theorem B1158799 : Blo 610295 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B1748861 : Blo 610295 1748861 := bstep (se 3 (by rfl) ⟨327911, by rfl⟩ : syracuseStep 1748861 = 655823) B655823
theorem B1159049 : Blo 610295 1159049 := bstep (se 2 (by rfl) ⟨434643, by rfl⟩ : syracuseStep 1159049 = 869287) B869287
theorem B14921867 : Blo 610295 14921867 := bstep (se 1 (by rfl) ⟨11191400, by rfl⟩ : syracuseStep 14921867 = 22382801) B22382801
theorem B12103937 : Blo 610295 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B17707319 : Blo 610295 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B1159915 : Blo 610295 1159915 := bstep (se 1 (by rfl) ⟨869936, by rfl⟩ : syracuseStep 1159915 = 1739873) B1739873
theorem B1553215 : Blo 610295 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B3486671 : Blo 610295 3486671 := bstep (se 1 (by rfl) ⟨2615003, by rfl⟩ : syracuseStep 3486671 = 5230007) B5230007
theorem B4699579 : Blo 610295 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B1160659 : Blo 610295 1160659 := bstep (se 1 (by rfl) ⟨870494, by rfl⟩ : syracuseStep 1160659 = 1740989) B1740989
theorem B5223923 : Blo 610295 5223923 := bstep (se 1 (by rfl) ⟨3917942, by rfl⟩ : syracuseStep 5223923 = 7835885) B7835885
theorem B26490401 : Blo 610295 26490401 := bstep (se 2 (by rfl) ⟨9933900, by rfl⟩ : syracuseStep 26490401 = 19867801) B19867801
theorem B1554167 : Blo 610295 1554167 := bstep (se 1 (by rfl) ⟨1165625, by rfl⟩ : syracuseStep 1554167 = 2331251) B2331251
theorem B38320067 : Blo 610295 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B5585051 : Blo 610295 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B1554623 : Blo 610295 1554623 := bstep (se 1 (by rfl) ⟨1165967, by rfl⟩ : syracuseStep 1554623 = 2331935) B2331935
theorem B1030799 : Blo 610295 1030799 := bstep (se 1 (by rfl) ⟨773099, by rfl⟩ : syracuseStep 1030799 = 1546199) B1546199
theorem B1162345 : Blo 610295 1162345 := bstep (se 2 (by rfl) ⟨435879, by rfl⟩ : syracuseStep 1162345 = 871759) B871759
theorem B9944221 : Blo 610295 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B1031791 : Blo 610295 1031791 := bstep (se 1 (by rfl) ⟨773843, by rfl⟩ : syracuseStep 1031791 = 1547687) B1547687
theorem B736879 : Blo 610295 736879 := bstep (se 1 (by rfl) ⟨552659, by rfl⟩ : syracuseStep 736879 = 1105319) B1105319
theorem B4636439 : Blo 610295 4636439 := bstep (se 1 (by rfl) ⟨3477329, by rfl⟩ : syracuseStep 4636439 = 6954659) B6954659
theorem B3490087 : Blo 610295 3490087 := bstep (se 1 (by rfl) ⟨2617565, by rfl⟩ : syracuseStep 3490087 = 5235131) B5235131
theorem B2933117 : Blo 610295 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B3359335 : Blo 610295 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B1163879 : Blo 610295 1163879 := bstep (se 1 (by rfl) ⟨872909, by rfl⟩ : syracuseStep 1163879 = 1745819) B1745819
theorem B737959 : Blo 610295 737959 := bstep (se 1 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 737959 = 1106939) B1106939
theorem B1163963 : Blo 610295 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B3097277 : Blo 610295 3097277 := bstep (se 3 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 3097277 = 1161479) B1161479
theorem B1164395 : Blo 610295 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1033519 : Blo 610295 1033519 := bstep (se 1 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 1033519 = 1550279) B1550279
theorem B19842893 : Blo 610295 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B6637477 : Blo 610295 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B4540697 : Blo 610295 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B2935673 : Blo 610295 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B6966323 : Blo 610295 6966323 := bstep (se 1 (by rfl) ⟨5224742, by rfl⟩ : syracuseStep 6966323 = 10449485) B10449485
theorem B2608271 : Blo 610295 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B3100193 : Blo 610295 3100193 := bstep (se 2 (by rfl) ⟨1162572, by rfl⟩ : syracuseStep 3100193 = 2325145) B2325145
theorem B3722855 : Blo 610295 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B2609023 : Blo 610295 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B2936807 : Blo 610295 2936807 := bstep (se 1 (by rfl) ⟨2202605, by rfl⟩ : syracuseStep 2936807 = 4405211) B4405211
theorem B774127 : Blo 610295 774127 := bstep (se 1 (by rfl) ⟨580595, by rfl⟩ : syracuseStep 774127 = 1161191) B1161191
theorem B610299 : Blo 610295 610299 := bstep (se 1 (by rfl) ⟨457724, by rfl⟩ : syracuseStep 610299 = 915449) B915449
theorem B610367 : Blo 610295 610367 := bstep (se 1 (by rfl) ⟨457775, by rfl⟩ : syracuseStep 610367 = 915551) B915551
theorem B610407 : Blo 610295 610407 := bstep (se 1 (by rfl) ⟨457805, by rfl⟩ : syracuseStep 610407 = 915611) B915611
theorem B610431 : Blo 610295 610431 := bstep (se 1 (by rfl) ⟨457823, by rfl⟩ : syracuseStep 610431 = 915647) B915647
theorem B610459 : Blo 610295 610459 := bstep (se 1 (by rfl) ⟨457844, by rfl⟩ : syracuseStep 610459 = 915689) B915689
theorem B774299 : Blo 610295 774299 := bstep (se 1 (by rfl) ⟨580724, by rfl⟩ : syracuseStep 774299 = 1161449) B1161449
theorem B5230757 : Blo 610295 5230757 := bstep (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) B980767
theorem B610663 : Blo 610295 610663 := bstep (se 1 (by rfl) ⟨457997, by rfl⟩ : syracuseStep 610663 = 915995) B915995
theorem B610715 : Blo 610295 610715 := bstep (se 1 (by rfl) ⟨458036, by rfl⟩ : syracuseStep 610715 = 916073) B916073
theorem B611067 : Blo 610295 611067 := bstep (se 1 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 611067 = 916601) B916601
theorem B611135 : Blo 610295 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B611163 : Blo 610295 611163 := bstep (se 1 (by rfl) ⟨458372, by rfl⟩ : syracuseStep 611163 = 916745) B916745
theorem B775003 : Blo 610295 775003 := bstep (se 1 (by rfl) ⟨581252, by rfl⟩ : syracuseStep 775003 = 1162505) B1162505
theorem B611231 : Blo 610295 611231 := bstep (se 1 (by rfl) ⟨458423, by rfl⟩ : syracuseStep 611231 = 916847) B916847
theorem B611311 : Blo 610295 611311 := bstep (se 1 (by rfl) ⟨458483, by rfl⟩ : syracuseStep 611311 = 916967) B916967
theorem B611399 : Blo 610295 611399 := bstep (se 1 (by rfl) ⟨458549, by rfl⟩ : syracuseStep 611399 = 917099) B917099
theorem B611483 : Blo 610295 611483 := bstep (se 1 (by rfl) ⟨458612, by rfl⟩ : syracuseStep 611483 = 917225) B917225
theorem B611579 : Blo 610295 611579 := bstep (se 1 (by rfl) ⟨458684, by rfl⟩ : syracuseStep 611579 = 917369) B917369
theorem B611647 : Blo 610295 611647 := bstep (se 1 (by rfl) ⟨458735, by rfl⟩ : syracuseStep 611647 = 917471) B917471
theorem B611815 : Blo 610295 611815 := bstep (se 1 (by rfl) ⟨458861, by rfl⟩ : syracuseStep 611815 = 917723) B917723
theorem B611823 : Blo 610295 611823 := bstep (se 1 (by rfl) ⟨458867, by rfl⟩ : syracuseStep 611823 = 917735) B917735
theorem B611931 : Blo 610295 611931 := bstep (se 1 (by rfl) ⟨458948, by rfl⟩ : syracuseStep 611931 = 917897) B917897
theorem B611995 : Blo 610295 611995 := bstep (se 1 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 611995 = 917993) B917993
theorem B612079 : Blo 610295 612079 := bstep (se 1 (by rfl) ⟨459059, by rfl⟩ : syracuseStep 612079 = 918119) B918119
theorem B612167 : Blo 610295 612167 := bstep (se 1 (by rfl) ⟨459125, by rfl⟩ : syracuseStep 612167 = 918251) B918251
theorem B612187 : Blo 610295 612187 := bstep (se 1 (by rfl) ⟨459140, by rfl⟩ : syracuseStep 612187 = 918281) B918281
theorem B612255 : Blo 610295 612255 := bstep (se 1 (by rfl) ⟨459191, by rfl⟩ : syracuseStep 612255 = 918383) B918383
theorem B11360249 : Blo 610295 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B612423 : Blo 610295 612423 := bstep (se 1 (by rfl) ⟨459317, by rfl⟩ : syracuseStep 612423 = 918635) B918635
theorem B612583 : Blo 610295 612583 := bstep (se 1 (by rfl) ⟨459437, by rfl⟩ : syracuseStep 612583 = 918875) B918875
theorem B612767 : Blo 610295 612767 := bstep (se 1 (by rfl) ⟨459575, by rfl⟩ : syracuseStep 612767 = 919151) B919151
theorem B612815 : Blo 610295 612815 := bstep (se 1 (by rfl) ⟨459611, by rfl⟩ : syracuseStep 612815 = 919223) B919223
theorem B612839 : Blo 610295 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B2939419 : Blo 610295 2939419 := bstep (se 1 (by rfl) ⟨2204564, by rfl⟩ : syracuseStep 2939419 = 4409129) B4409129
theorem B2513479 : Blo 610295 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B612955 : Blo 610295 612955 := bstep (se 1 (by rfl) ⟨459716, by rfl⟩ : syracuseStep 612955 = 919433) B919433
theorem B613023 : Blo 610295 613023 := bstep (se 1 (by rfl) ⟨459767, by rfl⟩ : syracuseStep 613023 = 919535) B919535
theorem B5233355 : Blo 610295 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B613191 : Blo 610295 613191 := bstep (se 1 (by rfl) ⟨459893, by rfl⟩ : syracuseStep 613191 = 919787) B919787
theorem B613231 : Blo 610295 613231 := bstep (se 1 (by rfl) ⟨459923, by rfl⟩ : syracuseStep 613231 = 919847) B919847
theorem B613287 : Blo 610295 613287 := bstep (se 1 (by rfl) ⟨459965, by rfl⟩ : syracuseStep 613287 = 919931) B919931
theorem B613467 : Blo 610295 613467 := bstep (se 1 (by rfl) ⟨460100, by rfl⟩ : syracuseStep 613467 = 920201) B920201
theorem B613583 : Blo 610295 613583 := bstep (se 1 (by rfl) ⟨460187, by rfl⟩ : syracuseStep 613583 = 920375) B920375
theorem B613607 : Blo 610295 613607 := bstep (se 1 (by rfl) ⟨460205, by rfl⟩ : syracuseStep 613607 = 920411) B920411
theorem B3136745 : Blo 610295 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B7462205 : Blo 610295 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B613703 : Blo 610295 613703 := bstep (se 1 (by rfl) ⟨460277, by rfl⟩ : syracuseStep 613703 = 920555) B920555
theorem B3104081 : Blo 610295 3104081 := bstep (se 2 (by rfl) ⟨1164030, by rfl⟩ : syracuseStep 3104081 = 2328061) B2328061
theorem B4971881 : Blo 610295 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B613839 : Blo 610295 613839 := bstep (se 1 (by rfl) ⟨460379, by rfl⟩ : syracuseStep 613839 = 920759) B920759
theorem B613999 : Blo 610295 613999 := bstep (se 1 (by rfl) ⟨460499, by rfl⟩ : syracuseStep 613999 = 920999) B920999
theorem B614055 : Blo 610295 614055 := bstep (se 1 (by rfl) ⟨460541, by rfl⟩ : syracuseStep 614055 = 921083) B921083
theorem B614119 : Blo 610295 614119 := bstep (se 1 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 614119 = 921179) B921179
theorem B614175 : Blo 610295 614175 := bstep (se 1 (by rfl) ⟨460631, by rfl⟩ : syracuseStep 614175 = 921263) B921263
theorem B614255 : Blo 610295 614255 := bstep (se 1 (by rfl) ⟨460691, by rfl⟩ : syracuseStep 614255 = 921383) B921383
theorem B3727259 : Blo 610295 3727259 := bstep (se 1 (by rfl) ⟨2795444, by rfl⟩ : syracuseStep 3727259 = 5590889) B5590889
theorem B3104891 : Blo 610295 3104891 := bstep (se 1 (by rfl) ⟨2328668, by rfl⟩ : syracuseStep 3104891 = 4657337) B4657337
theorem B2613671 : Blo 610295 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B1468297 : Blo 610295 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B2320285 : Blo 610295 2320285 := bstep (se 3 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 2320285 = 870107) B870107
theorem B2484125 : Blo 610295 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B11168047 : Blo 610295 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B29878793 : Blo 610295 29878793 := bstep (se 2 (by rfl) ⟨11204547, by rfl⟩ : syracuseStep 29878793 = 22409095) B22409095
theorem B2943823 : Blo 610295 2943823 := bstep (se 1 (by rfl) ⟨2207867, by rfl⟩ : syracuseStep 2943823 = 4415735) B4415735
theorem B1960843 : Blo 610295 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B4419335 : Blo 610295 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B2322215 : Blo 610295 2322215 := bstep (se 1 (by rfl) ⟨1741661, by rfl⟩ : syracuseStep 2322215 = 3483323) B3483323
theorem B21458843 : Blo 610295 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B2617703 : Blo 610295 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B7565885 : Blo 610295 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B4650047 : Blo 610295 4650047 := bstep (se 1 (by rfl) ⟨3487535, by rfl⟩ : syracuseStep 4650047 = 6975071) B6975071
theorem B1373255 : Blo 610295 1373255 := bstep (se 1 (by rfl) ⟨1029941, by rfl⟩ : syracuseStep 1373255 = 2059883) B2059883
theorem B2061395 : Blo 610295 2061395 := bstep (se 1 (by rfl) ⟨1546046, by rfl⟩ : syracuseStep 2061395 = 3092093) B3092093
theorem B11203667 : Blo 610295 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B1373435 : Blo 610295 1373435 := bstep (se 1 (by rfl) ⟨1030076, by rfl⟩ : syracuseStep 1373435 = 2060153) B2060153
theorem B1373651 : Blo 610295 1373651 := bstep (se 1 (by rfl) ⟨1030238, by rfl⟩ : syracuseStep 1373651 = 2060477) B2060477
theorem B2061935 : Blo 610295 2061935 := bstep (se 1 (by rfl) ⟨1546451, by rfl⟩ : syracuseStep 2061935 = 3092903) B3092903
theorem B1308271 : Blo 610295 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B1373921 : Blo 610295 1373921 := bstep (se 2 (by rfl) ⟨515220, by rfl⟩ : syracuseStep 1373921 = 1030441) B1030441
theorem B3307321 : Blo 610295 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B915497 : Blo 610295 915497 := bstep (se 2 (by rfl) ⟨343311, by rfl⟩ : syracuseStep 915497 = 686623) B686623
theorem B915527 : Blo 610295 915527 := bstep (se 1 (by rfl) ⟨686645, by rfl⟩ : syracuseStep 915527 = 1373291) B1373291
theorem B1472651 : Blo 610295 1472651 := bstep (se 1 (by rfl) ⟨1104488, by rfl⟩ : syracuseStep 1472651 = 2208977) B2208977
theorem B1374443 : Blo 610295 1374443 := bstep (se 1 (by rfl) ⟨1030832, by rfl⟩ : syracuseStep 1374443 = 2061665) B2061665
theorem B3307823 : Blo 610295 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B915911 : Blo 610295 915911 := bstep (se 1 (by rfl) ⟨686933, by rfl⟩ : syracuseStep 915911 = 1373867) B1373867
theorem B2062799 : Blo 610295 2062799 := bstep (se 1 (by rfl) ⟨1547099, by rfl⟩ : syracuseStep 2062799 = 3094199) B3094199
theorem B2652763 : Blo 610295 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B916127 : Blo 610295 916127 := bstep (se 1 (by rfl) ⟨687095, by rfl⟩ : syracuseStep 916127 = 1374191) B1374191
theorem B3930859 : Blo 610295 3930859 := bstep (se 1 (by rfl) ⟨2948144, by rfl⟩ : syracuseStep 3930859 = 5896289) B5896289
theorem B916271 : Blo 610295 916271 := bstep (se 1 (by rfl) ⟨687203, by rfl⟩ : syracuseStep 916271 = 1374407) B1374407
theorem B4422509 : Blo 610295 4422509 := bstep (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) B1658441
theorem B916391 : Blo 610295 916391 := bstep (se 1 (by rfl) ⟨687293, by rfl⟩ : syracuseStep 916391 = 1374587) B1374587
theorem B2325449 : Blo 610295 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B916571 : Blo 610295 916571 := bstep (se 1 (by rfl) ⟨687428, by rfl⟩ : syracuseStep 916571 = 1374857) B1374857
theorem B2784719 : Blo 610295 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B916943 : Blo 610295 916943 := bstep (se 1 (by rfl) ⟨687707, by rfl⟩ : syracuseStep 916943 = 1375415) B1375415
theorem B1375739 : Blo 610295 1375739 := bstep (se 1 (by rfl) ⟨1031804, by rfl⟩ : syracuseStep 1375739 = 2063609) B2063609
theorem B1375919 : Blo 610295 1375919 := bstep (se 1 (by rfl) ⟨1031939, by rfl⟩ : syracuseStep 1375919 = 2063879) B2063879
theorem B5308091 : Blo 610295 5308091 := bstep (se 1 (by rfl) ⟨3981068, by rfl⟩ : syracuseStep 5308091 = 7962137) B7962137
theorem B687847 : Blo 610295 687847 := bstep (se 1 (by rfl) ⟨515885, by rfl⟩ : syracuseStep 687847 = 1031771) B1031771
theorem B1376009 : Blo 610295 1376009 := bstep (se 2 (by rfl) ⟨516003, by rfl⟩ : syracuseStep 1376009 = 1032007) B1032007
theorem B917327 : Blo 610295 917327 := bstep (se 1 (by rfl) ⟨687995, by rfl⟩ : syracuseStep 917327 = 1375991) B1375991
theorem B917447 : Blo 610295 917447 := bstep (se 1 (by rfl) ⟨688085, by rfl⟩ : syracuseStep 917447 = 1376171) B1376171
theorem B1310663 : Blo 610295 1310663 := bstep (se 1 (by rfl) ⟨982997, by rfl⟩ : syracuseStep 1310663 = 1965995) B1965995
theorem B5243129 : Blo 610295 5243129 := bstep (se 2 (by rfl) ⟨1966173, by rfl⟩ : syracuseStep 5243129 = 3932347) B3932347
theorem B917759 : Blo 610295 917759 := bstep (se 1 (by rfl) ⟨688319, by rfl⟩ : syracuseStep 917759 = 1376639) B1376639
theorem B4653449 : Blo 610295 4653449 := bstep (se 2 (by rfl) ⟨1745043, by rfl⟩ : syracuseStep 4653449 = 3490087) B3490087
theorem B917915 : Blo 610295 917915 := bstep (se 1 (by rfl) ⟨688436, by rfl⟩ : syracuseStep 917915 = 1376873) B1376873
theorem B2064797 : Blo 610295 2064797 := bstep (se 3 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 2064797 = 774299) B774299
theorem B2064851 : Blo 610295 2064851 := bstep (se 1 (by rfl) ⟨1548638, by rfl⟩ : syracuseStep 2064851 = 3097277) B3097277
theorem B918335 : Blo 610295 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B983945 : Blo 610295 983945 := bstep (se 2 (by rfl) ⟨368979, by rfl⟩ : syracuseStep 983945 = 737959) B737959
theorem B918479 : Blo 610295 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B2327561 : Blo 610295 2327561 := bstep (se 2 (by rfl) ⟨872835, by rfl⟩ : syracuseStep 2327561 = 1745671) B1745671
theorem B918569 : Blo 610295 918569 := bstep (se 2 (by rfl) ⟨344463, by rfl⟩ : syracuseStep 918569 = 688927) B688927
theorem B918599 : Blo 610295 918599 := bstep (se 1 (by rfl) ⟨688949, by rfl⟩ : syracuseStep 918599 = 1377899) B1377899
theorem B918779 : Blo 610295 918779 := bstep (se 1 (by rfl) ⟨689084, by rfl⟩ : syracuseStep 918779 = 1378169) B1378169
theorem B919067 : Blo 610295 919067 := bstep (se 1 (by rfl) ⟨689300, by rfl⟩ : syracuseStep 919067 = 1378601) B1378601
theorem B1377935 : Blo 610295 1377935 := bstep (se 1 (by rfl) ⟨1033451, by rfl⟩ : syracuseStep 1377935 = 2066903) B2066903
theorem B1378025 : Blo 610295 1378025 := bstep (se 2 (by rfl) ⟨516759, by rfl⟩ : syracuseStep 1378025 = 1033519) B1033519
theorem B919451 : Blo 610295 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B919487 : Blo 610295 919487 := bstep (se 1 (by rfl) ⟨689615, by rfl⟩ : syracuseStep 919487 = 1379231) B1379231
theorem B1738847 : Blo 610295 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B2066795 : Blo 610295 2066795 := bstep (se 1 (by rfl) ⟨1550096, by rfl⟩ : syracuseStep 2066795 = 3100193) B3100193
theorem B920111 : Blo 610295 920111 := bstep (se 1 (by rfl) ⟨690083, by rfl⟩ : syracuseStep 920111 = 1380167) B1380167
theorem B8849969 : Blo 610295 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B920231 : Blo 610295 920231 := bstep (se 1 (by rfl) ⟨690173, by rfl⟩ : syracuseStep 920231 = 1380347) B1380347
theorem B920297 : Blo 610295 920297 := bstep (se 2 (by rfl) ⟨345111, by rfl⟩ : syracuseStep 920297 = 690223) B690223
theorem B920303 : Blo 610295 920303 := bstep (se 1 (by rfl) ⟨690227, by rfl⟩ : syracuseStep 920303 = 1380455) B1380455
theorem B920351 : Blo 610295 920351 := bstep (se 1 (by rfl) ⟨690263, by rfl⟩ : syracuseStep 920351 = 1380527) B1380527
theorem B920681 : Blo 610295 920681 := bstep (se 2 (by rfl) ⟨345255, by rfl⟩ : syracuseStep 920681 = 690511) B690511
theorem B2362537 : Blo 610295 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B920807 : Blo 610295 920807 := bstep (se 1 (by rfl) ⟨690605, by rfl⟩ : syracuseStep 920807 = 1381211) B1381211
theorem B1379807 : Blo 610295 1379807 := bstep (se 1 (by rfl) ⟨1034855, by rfl⟩ : syracuseStep 1379807 = 2069711) B2069711
theorem B921311 : Blo 610295 921311 := bstep (se 1 (by rfl) ⟨690983, by rfl⟩ : syracuseStep 921311 = 1381967) B1381967
theorem B7573499 : Blo 610295 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B2330977 : Blo 610295 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B6623639 : Blo 610295 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B1380815 : Blo 610295 1380815 := bstep (se 1 (by rfl) ⟨1035611, by rfl⟩ : syracuseStep 1380815 = 2071223) B2071223
theorem B1545065 : Blo 610295 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B2069387 : Blo 610295 2069387 := bstep (se 1 (by rfl) ⟨1552040, by rfl⟩ : syracuseStep 2069387 = 3104081) B3104081
theorem B3314587 : Blo 610295 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B3478697 : Blo 610295 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B2069927 : Blo 610295 2069927 := bstep (se 1 (by rfl) ⟨1552445, by rfl⟩ : syracuseStep 2069927 = 3104891) B3104891
theorem B1742447 : Blo 610295 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B10622825 : Blo 610295 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B3479699 : Blo 610295 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B1546553 : Blo 610295 1546553 := bstep (se 2 (by rfl) ⟨579957, by rfl⟩ : syracuseStep 1546553 = 1159915) B1159915
theorem B2070953 : Blo 610295 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B3480155 : Blo 610295 3480155 := bstep (se 1 (by rfl) ⟨2610116, by rfl⟩ : syracuseStep 3480155 = 5220233) B5220233
theorem B662143 : Blo 610295 662143 := bstep (se 1 (by rfl) ⟨496607, by rfl⟩ : syracuseStep 662143 = 993215) B993215
theorem B5872301 : Blo 610295 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B6266105 : Blo 610295 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B9051401 : Blo 610295 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B1547545 : Blo 610295 1547545 := bstep (se 2 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 1547545 = 1160659) B1160659
theorem B1744361 : Blo 610295 1744361 := bstep (se 2 (by rfl) ⟨654135, by rfl⟩ : syracuseStep 1744361 = 1308271) B1308271
theorem B1548143 : Blo 610295 1548143 := bstep (se 1 (by rfl) ⟨1161107, by rfl⟩ : syracuseStep 1548143 = 2322215) B2322215
theorem B8069291 : Blo 610295 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B11804879 : Blo 610295 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B1745135 : Blo 610295 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B8364653 : Blo 610295 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B3351305 : Blo 610295 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B3482615 : Blo 610295 3482615 := bstep (se 1 (by rfl) ⟨2611961, by rfl⟩ : syracuseStep 3482615 = 5223923) B5223923
theorem B1549793 : Blo 610295 1549793 := bstep (se 2 (by rfl) ⟨581172, by rfl⟩ : syracuseStep 1549793 = 1162345) B1162345
theorem B2205215 : Blo 610295 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B17639045 : Blo 610295 17639045 := bstep (se 4 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 17639045 = 3307321) B3307321
theorem B1550299 : Blo 610295 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B3090797 : Blo 610295 3090797 := bstep (se 3 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 3090797 = 1159049) B1159049
theorem B3090959 : Blo 610295 3090959 := bstep (se 1 (by rfl) ⟨2318219, by rfl⟩ : syracuseStep 3090959 = 4636439) B4636439
theorem B17836685 : Blo 610295 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B39791645 : Blo 610295 39791645 := bstep (se 3 (by rfl) ⟨7460933, by rfl⟩ : syracuseStep 39791645 = 14921867) B14921867
theorem B1158943 : Blo 610295 1158943 := bstep (se 1 (by rfl) ⟨869207, by rfl⟩ : syracuseStep 1158943 = 1738415) B1738415
theorem B3027131 : Blo 610295 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B1159991 : Blo 610295 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B3093713 : Blo 610295 3093713 := bstep (se 2 (by rfl) ⟨1160142, by rfl⟩ : syracuseStep 3093713 = 2320285) B2320285
theorem B3487171 : Blo 610295 3487171 := bstep (se 1 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 3487171 = 5230757) B5230757
theorem B14890729 : Blo 610295 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B1554299 : Blo 610295 1554299 := bstep (se 1 (by rfl) ⟨1165724, by rfl⟩ : syracuseStep 1554299 = 2331449) B2331449
theorem B235518167 : Blo 610295 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B4962539 : Blo 610295 4962539 := bstep (se 1 (by rfl) ⟨3721904, by rfl⟩ : syracuseStep 4962539 = 7443809) B7443809
theorem B1030711 : Blo 610295 1030711 := bstep (se 1 (by rfl) ⟨773033, by rfl⟩ : syracuseStep 1030711 = 1546067) B1546067
theorem B3488903 : Blo 610295 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B1031899 : Blo 610295 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B1032169 : Blo 610295 1032169 := bstep (se 2 (by rfl) ⟨387063, by rfl⟩ : syracuseStep 1032169 = 774127) B774127
theorem B14893469 : Blo 610295 14893469 := bstep (se 3 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 14893469 = 5585051) B5585051
theorem B6603227 : Blo 610295 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B1033337 : Blo 610295 1033337 := bstep (se 2 (by rfl) ⟨387501, by rfl⟩ : syracuseStep 1033337 = 775003) B775003
theorem B1656083 : Blo 610295 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B3917123 : Blo 610295 3917123 := bstep (se 1 (by rfl) ⟨2937842, by rfl⟩ : syracuseStep 3917123 = 5875685) B5875685
theorem B3262619 : Blo 610295 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B1165519 : Blo 610295 1165519 := bstep (se 1 (by rfl) ⟨874139, by rfl⟩ : syracuseStep 1165519 = 1748279) B1748279
theorem B1165907 : Blo 610295 1165907 := bstep (se 1 (by rfl) ⟨874430, by rfl⟩ : syracuseStep 1165907 = 1748861) B1748861
theorem B14305895 : Blo 610295 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B3919225 : Blo 610295 3919225 := bstep (se 2 (by rfl) ⟨1469709, by rfl⟩ : syracuseStep 3919225 = 2939419) B2939419
theorem B3100031 : Blo 610295 3100031 := bstep (se 1 (by rfl) ⟨2325023, by rfl⟩ : syracuseStep 3100031 = 4650047) B4650047
theorem B1036111 : Blo 610295 1036111 := bstep (se 1 (by rfl) ⟨777083, by rfl⟩ : syracuseStep 1036111 = 1554167) B1554167
theorem B25546711 : Blo 610295 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B610331 : Blo 610295 610331 := bstep (se 1 (by rfl) ⟨457748, by rfl⟩ : syracuseStep 610331 = 915497) B915497
theorem B610351 : Blo 610295 610351 := bstep (se 1 (by rfl) ⟨457763, by rfl⟩ : syracuseStep 610351 = 915527) B915527
theorem B1036415 : Blo 610295 1036415 := bstep (se 1 (by rfl) ⟨777311, by rfl⟩ : syracuseStep 1036415 = 1554623) B1554623
theorem B13258961 : Blo 610295 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B610607 : Blo 610295 610607 := bstep (se 1 (by rfl) ⟨457955, by rfl⟩ : syracuseStep 610607 = 915911) B915911
theorem B610751 : Blo 610295 610751 := bstep (se 1 (by rfl) ⟨458063, by rfl⟩ : syracuseStep 610751 = 916127) B916127
theorem B610847 : Blo 610295 610847 := bstep (se 1 (by rfl) ⟨458135, by rfl⟩ : syracuseStep 610847 = 916271) B916271
theorem B610927 : Blo 610295 610927 := bstep (se 1 (by rfl) ⟨458195, by rfl⟩ : syracuseStep 610927 = 916391) B916391
theorem B611047 : Blo 610295 611047 := bstep (se 1 (by rfl) ⟨458285, by rfl⟩ : syracuseStep 611047 = 916571) B916571
theorem B1856479 : Blo 610295 1856479 := bstep (se 1 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 1856479 = 2784719) B2784719
theorem B611295 : Blo 610295 611295 := bstep (se 1 (by rfl) ⟨458471, by rfl⟩ : syracuseStep 611295 = 916943) B916943
theorem B611551 : Blo 610295 611551 := bstep (se 1 (by rfl) ⟨458663, by rfl⟩ : syracuseStep 611551 = 917327) B917327
theorem B611631 : Blo 610295 611631 := bstep (se 1 (by rfl) ⟨458723, by rfl⟩ : syracuseStep 611631 = 917447) B917447
theorem B873775 : Blo 610295 873775 := bstep (se 1 (by rfl) ⟨655331, by rfl⟩ : syracuseStep 873775 = 1310663) B1310663
theorem B611871 : Blo 610295 611871 := bstep (se 1 (by rfl) ⟨458903, by rfl⟩ : syracuseStep 611871 = 917807) B917807
theorem B1955411 : Blo 610295 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B612031 : Blo 610295 612031 := bstep (se 1 (by rfl) ⟨459023, by rfl⟩ : syracuseStep 612031 = 918047) B918047
theorem B775919 : Blo 610295 775919 := bstep (se 1 (by rfl) ⟨581939, by rfl⟩ : syracuseStep 775919 = 1163879) B1163879
theorem B775975 : Blo 610295 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B14899211 : Blo 610295 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B874567 : Blo 610295 874567 := bstep (se 1 (by rfl) ⟨655925, by rfl⟩ : syracuseStep 874567 = 1311851) B1311851
theorem B612479 : Blo 610295 612479 := bstep (se 1 (by rfl) ⟨459359, by rfl⟩ : syracuseStep 612479 = 918719) B918719
theorem B4479113 : Blo 610295 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B612575 : Blo 610295 612575 := bstep (se 1 (by rfl) ⟨459431, by rfl⟩ : syracuseStep 612575 = 918863) B918863
theorem B612635 : Blo 610295 612635 := bstep (se 1 (by rfl) ⟨459476, by rfl⟩ : syracuseStep 612635 = 918953) B918953
theorem B612735 : Blo 610295 612735 := bstep (se 1 (by rfl) ⟨459551, by rfl⟩ : syracuseStep 612735 = 919103) B919103
theorem B612763 : Blo 610295 612763 := bstep (se 1 (by rfl) ⟨459572, by rfl⟩ : syracuseStep 612763 = 919145) B919145
theorem B13228595 : Blo 610295 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B613055 : Blo 610295 613055 := bstep (se 1 (by rfl) ⟨459791, by rfl⟩ : syracuseStep 613055 = 919583) B919583
theorem B613183 : Blo 610295 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B613223 : Blo 610295 613223 := bstep (se 1 (by rfl) ⟨459917, by rfl⟩ : syracuseStep 613223 = 919835) B919835
theorem B613439 : Blo 610295 613439 := bstep (se 1 (by rfl) ⟨460079, by rfl⟩ : syracuseStep 613439 = 920159) B920159
theorem B1957115 : Blo 610295 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B613627 : Blo 610295 613627 := bstep (se 1 (by rfl) ⟨460220, by rfl⟩ : syracuseStep 613627 = 920441) B920441
theorem B613659 : Blo 610295 613659 := bstep (se 1 (by rfl) ⟨460244, by rfl⟩ : syracuseStep 613659 = 920489) B920489
theorem B4644215 : Blo 610295 4644215 := bstep (se 1 (by rfl) ⟨3483161, by rfl⟩ : syracuseStep 4644215 = 6966323) B6966323
theorem B613759 : Blo 610295 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B614127 : Blo 610295 614127 := bstep (se 1 (by rfl) ⟨460595, by rfl⟩ : syracuseStep 614127 = 921191) B921191
theorem B6381359 : Blo 610295 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B1957871 : Blo 610295 1957871 := bstep (se 1 (by rfl) ⟨1468403, by rfl⟩ : syracuseStep 1957871 = 2936807) B2936807
theorem B3105053 : Blo 610295 3105053 := bstep (se 3 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 3105053 = 1164395) B1164395
theorem B2122247 : Blo 610295 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B1467067 : Blo 610295 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B3925097 : Blo 610295 3925097 := bstep (se 2 (by rfl) ⟨1471911, by rfl⟩ : syracuseStep 3925097 = 2943823) B2943823
theorem B2614457 : Blo 610295 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B2319785 : Blo 610295 2319785 := bstep (se 2 (by rfl) ⟨869919, by rfl⟩ : syracuseStep 2319785 = 1739839) B1739839
theorem B4974803 : Blo 610295 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B3107321 : Blo 610295 3107321 := bstep (se 2 (by rfl) ⟨1165245, by rfl⟩ : syracuseStep 3107321 = 2330491) B2330491
theorem B2484839 : Blo 610295 2484839 := bstep (se 1 (by rfl) ⟨1863629, by rfl⟩ : syracuseStep 2484839 = 3727259) B3727259
theorem B3107483 : Blo 610295 3107483 := bstep (se 1 (by rfl) ⟨2330612, by rfl⟩ : syracuseStep 3107483 = 4661225) B4661225
theorem B2321243 : Blo 610295 2321243 := bstep (se 1 (by rfl) ⟨1740932, by rfl⟩ : syracuseStep 2321243 = 3481865) B3481865
theorem B9399347 : Blo 610295 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B3828959 : Blo 610295 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B3108455 : Blo 610295 3108455 := bstep (se 1 (by rfl) ⟨2331341, by rfl⟩ : syracuseStep 3108455 = 4662683) B4662683
theorem B16084655 : Blo 610295 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B3108779 : Blo 610295 3108779 := bstep (se 1 (by rfl) ⟨2331584, by rfl⟩ : syracuseStep 3108779 = 4663169) B4663169
theorem B2977769 : Blo 610295 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B19919195 : Blo 610295 19919195 := bstep (se 1 (by rfl) ⟨14939396, by rfl⟩ : syracuseStep 19919195 = 29878793) B29878793
theorem B2946223 : Blo 610295 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B5043923 : Blo 610295 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B2324447 : Blo 610295 2324447 := bstep (se 1 (by rfl) ⟨1743335, by rfl⟩ : syracuseStep 2324447 = 3486671) B3486671
theorem B915503 : Blo 610295 915503 := bstep (se 1 (by rfl) ⟨686627, by rfl⟩ : syracuseStep 915503 = 1373255) B1373255
theorem B1374263 : Blo 610295 1374263 := bstep (se 1 (by rfl) ⟨1030697, by rfl⟩ : syracuseStep 1374263 = 2061395) B2061395
theorem B7469111 : Blo 610295 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B3537017 : Blo 610295 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B915623 : Blo 610295 915623 := bstep (se 1 (by rfl) ⟨686717, by rfl⟩ : syracuseStep 915623 = 1373435) B1373435
theorem B915767 : Blo 610295 915767 := bstep (se 1 (by rfl) ⟨686825, by rfl⟩ : syracuseStep 915767 = 1373651) B1373651
theorem B5241145 : Blo 610295 5241145 := bstep (se 2 (by rfl) ⟨1965429, by rfl⟩ : syracuseStep 5241145 = 3930859) B3930859
theorem B17660267 : Blo 610295 17660267 := bstep (se 1 (by rfl) ⟨13245200, by rfl⟩ : syracuseStep 17660267 = 26490401) B26490401
theorem B1374623 : Blo 610295 1374623 := bstep (se 1 (by rfl) ⟨1030967, by rfl⟩ : syracuseStep 1374623 = 2061935) B2061935
theorem B915947 : Blo 610295 915947 := bstep (se 1 (by rfl) ⟨686960, by rfl⟩ : syracuseStep 915947 = 1373921) B1373921
theorem B981767 : Blo 610295 981767 := bstep (se 1 (by rfl) ⟨736325, by rfl⟩ : syracuseStep 981767 = 1472651) B1472651
theorem B916295 : Blo 610295 916295 := bstep (se 1 (by rfl) ⟨687221, by rfl⟩ : syracuseStep 916295 = 1374443) B1374443
theorem B9927613 : Blo 610295 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B1375199 : Blo 610295 1375199 := bstep (se 1 (by rfl) ⟨1031399, by rfl⟩ : syracuseStep 1375199 = 2062799) B2062799
theorem B687199 : Blo 610295 687199 := bstep (se 1 (by rfl) ⟨515399, by rfl⟩ : syracuseStep 687199 = 1030799) B1030799
theorem B2948339 : Blo 610295 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B7830917 : Blo 610295 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B1375721 : Blo 610295 1375721 := bstep (se 2 (by rfl) ⟨515895, by rfl⟩ : syracuseStep 1375721 = 1031791) B1031791
theorem B982505 : Blo 610295 982505 := bstep (se 2 (by rfl) ⟨368439, by rfl⟩ : syracuseStep 982505 = 736879) B736879
theorem B917129 : Blo 610295 917129 := bstep (se 2 (by rfl) ⟨343923, by rfl⟩ : syracuseStep 917129 = 687847) B687847
theorem B917159 : Blo 610295 917159 := bstep (se 1 (by rfl) ⟨687869, by rfl⟩ : syracuseStep 917159 = 1375739) B1375739
theorem B917279 : Blo 610295 917279 := bstep (se 1 (by rfl) ⟨687959, by rfl⟩ : syracuseStep 917279 = 1375919) B1375919
theorem B3538727 : Blo 610295 3538727 := bstep (se 1 (by rfl) ⟨2654045, by rfl⟩ : syracuseStep 3538727 = 5308091) B5308091
theorem B917339 : Blo 610295 917339 := bstep (se 1 (by rfl) ⟨688004, by rfl⟩ : syracuseStep 917339 = 1376009) B1376009
theorem B1376531 : Blo 610295 1376531 := bstep (se 1 (by rfl) ⟨1032398, by rfl⟩ : syracuseStep 1376531 = 2064797) B2064797
theorem B9928979 : Blo 610295 9928979 := bstep (se 1 (by rfl) ⟨7446734, by rfl⟩ : syracuseStep 9928979 = 14893469) B14893469
theorem B1376567 : Blo 610295 1376567 := bstep (se 1 (by rfl) ⟨1032425, by rfl⟩ : syracuseStep 1376567 = 2064851) B2064851
theorem B688891 : Blo 610295 688891 := bstep (se 1 (by rfl) ⟨516668, by rfl⟩ : syracuseStep 688891 = 1033337) B1033337
theorem B918623 : Blo 610295 918623 := bstep (se 1 (by rfl) ⟨688967, by rfl⟩ : syracuseStep 918623 = 1377935) B1377935
theorem B918683 : Blo 610295 918683 := bstep (se 1 (by rfl) ⟨689012, by rfl⟩ : syracuseStep 918683 = 1378025) B1378025
theorem B1377863 : Blo 610295 1377863 := bstep (se 1 (by rfl) ⟨1033397, by rfl⟩ : syracuseStep 1377863 = 2066795) B2066795
theorem B5899979 : Blo 610295 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B9537263 : Blo 610295 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B2066687 : Blo 610295 2066687 := bstep (se 1 (by rfl) ⟨1550015, by rfl⟩ : syracuseStep 2066687 = 3100031) B3100031
theorem B919871 : Blo 610295 919871 := bstep (se 1 (by rfl) ⟨689903, by rfl⟩ : syracuseStep 919871 = 1379807) B1379807
theorem B2623853 : Blo 610295 2623853 := bstep (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) B983945
theorem B2067065 : Blo 610295 2067065 := bstep (se 2 (by rfl) ⟨775149, by rfl⟩ : syracuseStep 2067065 = 1550299) B1550299
theorem B5048999 : Blo 610295 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B690943 : Blo 610295 690943 := bstep (se 1 (by rfl) ⟨518207, by rfl⟩ : syracuseStep 690943 = 1036415) B1036415
theorem B920543 : Blo 610295 920543 := bstep (se 1 (by rfl) ⟨690407, by rfl⟩ : syracuseStep 920543 = 1380815) B1380815
theorem B1379591 : Blo 610295 1379591 := bstep (se 1 (by rfl) ⟨1034693, by rfl⟩ : syracuseStep 1379591 = 2069387) B2069387
theorem B1379951 : Blo 610295 1379951 := bstep (se 1 (by rfl) ⟨1034963, by rfl⟩ : syracuseStep 1379951 = 2069927) B2069927
theorem B7081883 : Blo 610295 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B9932807 : Blo 610295 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B2986075 : Blo 610295 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B1380635 : Blo 610295 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B8819063 : Blo 610295 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B2069117 : Blo 610295 2069117 := bstep (se 3 (by rfl) ⟨387959, by rfl⟩ : syracuseStep 2069117 = 775919) B775919
theorem B6034267 : Blo 610295 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B1545257 : Blo 610295 1545257 := bstep (se 2 (by rfl) ⟨579471, by rfl⟩ : syracuseStep 1545257 = 1158943) B1158943
theorem B1381481 : Blo 610295 1381481 := bstep (se 2 (by rfl) ⟨518055, by rfl⟩ : syracuseStep 1381481 = 1036111) B1036111
theorem B5379527 : Blo 610295 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B7869919 : Blo 610295 7869919 := bstep (se 1 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 7869919 = 11804879) B11804879
theorem B2070035 : Blo 610295 2070035 := bstep (se 1 (by rfl) ⟨1552526, by rfl⟩ : syracuseStep 2070035 = 3105053) B3105053
theorem B1414831 : Blo 610295 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B5576435 : Blo 610295 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B1742971 : Blo 610295 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B1546523 : Blo 610295 1546523 := bstep (se 1 (by rfl) ⟨1159892, by rfl⟩ : syracuseStep 1546523 = 2319785) B2319785
theorem B3316535 : Blo 610295 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B2071547 : Blo 610295 2071547 := bstep (se 1 (by rfl) ⟨1553660, by rfl⟩ : syracuseStep 2071547 = 3107321) B3107321
theorem B2071655 : Blo 610295 2071655 := bstep (se 1 (by rfl) ⟨1553741, by rfl⟩ : syracuseStep 2071655 = 3107483) B3107483
theorem B1547495 : Blo 610295 1547495 := bstep (se 1 (by rfl) ⟨1160621, by rfl⟩ : syracuseStep 1547495 = 2321243) B2321243
theorem B6266231 : Blo 610295 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B2072303 : Blo 610295 2072303 := bstep (se 1 (by rfl) ⟨1554227, by rfl⟩ : syracuseStep 2072303 = 3108455) B3108455
theorem B10723103 : Blo 610295 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B2072519 : Blo 610295 2072519 := bstep (se 1 (by rfl) ⟨1554389, by rfl⟩ : syracuseStep 2072519 = 3108779) B3108779
theorem B13279463 : Blo 610295 13279463 := bstep (se 1 (by rfl) ⟨9959597, by rfl⟩ : syracuseStep 13279463 = 19919195) B19919195
theorem B6988193 : Blo 610295 6988193 := bstep (se 2 (by rfl) ⟨2620572, by rfl⟩ : syracuseStep 6988193 = 5241145) B5241145
theorem B1549631 : Blo 610295 1549631 := bstep (se 1 (by rfl) ⟨1162223, by rfl⟩ : syracuseStep 1549631 = 2324447) B2324447
theorem B11773511 : Blo 610295 11773511 := bstep (se 1 (by rfl) ⟨8830133, by rfl⟩ : syracuseStep 11773511 = 17660267) B17660267
theorem B5220611 : Blo 610295 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B7940717 : Blo 610295 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B4402151 : Blo 610295 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B1551707 : Blo 610295 1551707 := bstep (se 1 (by rfl) ⟨1163780, by rfl⟩ : syracuseStep 1551707 = 2327561) B2327561
theorem B1554025 : Blo 610295 1554025 := bstep (se 2 (by rfl) ⟨582759, by rfl⟩ : syracuseStep 1554025 = 1165519) B1165519
theorem B1030043 : Blo 610295 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B1161631 : Blo 610295 1161631 := bstep (se 1 (by rfl) ⟨871223, by rfl⟩ : syracuseStep 1161631 = 1742447) B1742447
theorem B1031035 : Blo 610295 1031035 := bstep (se 1 (by rfl) ⟨773276, by rfl⟩ : syracuseStep 1031035 = 1546553) B1546553
theorem B3914867 : Blo 610295 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B5225633 : Blo 610295 5225633 := bstep (se 2 (by rfl) ⟨1959612, by rfl⟩ : syracuseStep 5225633 = 3919225) B3919225
theorem B4177403 : Blo 610295 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B3096143 : Blo 610295 3096143 := bstep (se 1 (by rfl) ⟨2322107, by rfl⟩ : syracuseStep 3096143 = 4644215) B4644215
theorem B1162907 : Blo 610295 1162907 := bstep (se 1 (by rfl) ⟨872180, by rfl⟩ : syracuseStep 1162907 = 1744361) B1744361
theorem B1032095 : Blo 610295 1032095 := bstep (se 1 (by rfl) ⟨774071, by rfl⟩ : syracuseStep 1032095 = 1548143) B1548143
theorem B34062281 : Blo 610295 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B1163423 : Blo 610295 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B4636925 : Blo 610295 4636925 := bstep (se 3 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 4636925 = 1738847) B1738847
theorem B8700317 : Blo 610295 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B12600197 : Blo 610295 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B1033195 : Blo 610295 1033195 := bstep (se 1 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 1033195 = 1549793) B1549793
theorem B2475305 : Blo 610295 2475305 := bstep (se 2 (by rfl) ⟨928239, by rfl⟩ : syracuseStep 2475305 = 1856479) B1856479
theorem B1165033 : Blo 610295 1165033 := bstep (se 2 (by rfl) ⟨436887, by rfl⟩ : syracuseStep 1165033 = 873775) B873775
theorem B1656559 : Blo 610295 1656559 := bstep (se 1 (by rfl) ⟨1242419, by rfl⟩ : syracuseStep 1656559 = 2484839) B2484839
theorem B26527763 : Blo 610295 26527763 := bstep (se 1 (by rfl) ⟨19895822, by rfl⟩ : syracuseStep 26527763 = 39791645) B39791645
theorem B1034633 : Blo 610295 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B1166089 : Blo 610295 1166089 := bstep (se 2 (by rfl) ⟨437283, by rfl⟩ : syracuseStep 1166089 = 874567) B874567
theorem B2018087 : Blo 610295 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B773327 : Blo 610295 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B3362615 : Blo 610295 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1036199 : Blo 610295 1036199 := bstep (se 1 (by rfl) ⟨777149, by rfl⟩ : syracuseStep 1036199 = 1554299) B1554299
theorem B610335 : Blo 610295 610335 := bstep (se 1 (by rfl) ⟨457751, by rfl⟩ : syracuseStep 610335 = 915503) B915503
theorem B610415 : Blo 610295 610415 := bstep (se 1 (by rfl) ⟨457811, by rfl⟩ : syracuseStep 610415 = 915623) B915623
theorem B157012111 : Blo 610295 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B610511 : Blo 610295 610511 := bstep (se 1 (by rfl) ⟨457883, by rfl⟩ : syracuseStep 610511 = 915767) B915767
theorem B610631 : Blo 610295 610631 := bstep (se 1 (by rfl) ⟨457973, by rfl⟩ : syracuseStep 610631 = 915947) B915947
theorem B610863 : Blo 610295 610863 := bstep (se 1 (by rfl) ⟨458147, by rfl⟩ : syracuseStep 610863 = 916295) B916295
theorem B611419 : Blo 610295 611419 := bstep (se 1 (by rfl) ⟨458564, by rfl⟩ : syracuseStep 611419 = 917129) B917129
theorem B611439 : Blo 610295 611439 := bstep (se 1 (by rfl) ⟨458579, by rfl⟩ : syracuseStep 611439 = 917159) B917159
theorem B611519 : Blo 610295 611519 := bstep (se 1 (by rfl) ⟨458639, by rfl⟩ : syracuseStep 611519 = 917279) B917279
theorem B611559 : Blo 610295 611559 := bstep (se 1 (by rfl) ⟨458669, by rfl⟩ : syracuseStep 611559 = 917339) B917339
theorem B3495419 : Blo 610295 3495419 := bstep (se 1 (by rfl) ⟨2621564, by rfl⟩ : syracuseStep 3495419 = 5243129) B5243129
theorem B611839 : Blo 610295 611839 := bstep (se 1 (by rfl) ⟨458879, by rfl⟩ : syracuseStep 611839 = 917759) B917759
theorem B3102299 : Blo 610295 3102299 := bstep (se 1 (by rfl) ⟨2326724, by rfl⟩ : syracuseStep 3102299 = 4653449) B4653449
theorem B611943 : Blo 610295 611943 := bstep (se 1 (by rfl) ⟨458957, by rfl⟩ : syracuseStep 611943 = 917915) B917915
theorem B612223 : Blo 610295 612223 := bstep (se 1 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 612223 = 918335) B918335
theorem B612319 : Blo 610295 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B612379 : Blo 610295 612379 := bstep (se 1 (by rfl) ⟨459284, by rfl⟩ : syracuseStep 612379 = 918569) B918569
theorem B612399 : Blo 610295 612399 := bstep (se 1 (by rfl) ⟨459299, by rfl⟩ : syracuseStep 612399 = 918599) B918599
theorem B612519 : Blo 610295 612519 := bstep (se 1 (by rfl) ⟨459389, by rfl⟩ : syracuseStep 612519 = 918779) B918779
theorem B2611415 : Blo 610295 2611415 := bstep (se 1 (by rfl) ⟨1958561, by rfl⟩ : syracuseStep 2611415 = 3917123) B3917123
theorem B1956089 : Blo 610295 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B612711 : Blo 610295 612711 := bstep (se 1 (by rfl) ⟨459533, by rfl⟩ : syracuseStep 612711 = 919067) B919067
theorem B612967 : Blo 610295 612967 := bstep (se 1 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 612967 = 919451) B919451
theorem B612991 : Blo 610295 612991 := bstep (se 1 (by rfl) ⟨459743, by rfl⟩ : syracuseStep 612991 = 919487) B919487
theorem B613407 : Blo 610295 613407 := bstep (se 1 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 613407 = 920111) B920111
theorem B777271 : Blo 610295 777271 := bstep (se 1 (by rfl) ⟨582953, by rfl⟩ : syracuseStep 777271 = 1165907) B1165907
theorem B613487 : Blo 610295 613487 := bstep (se 1 (by rfl) ⟨460115, by rfl⟩ : syracuseStep 613487 = 920231) B920231
theorem B613531 : Blo 610295 613531 := bstep (se 1 (by rfl) ⟨460148, by rfl⟩ : syracuseStep 613531 = 920297) B920297
theorem B613535 : Blo 610295 613535 := bstep (se 1 (by rfl) ⟨460151, by rfl⟩ : syracuseStep 613535 = 920303) B920303
theorem B613567 : Blo 610295 613567 := bstep (se 1 (by rfl) ⟨460175, by rfl⟩ : syracuseStep 613567 = 920351) B920351
theorem B8936813 : Blo 610295 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B613787 : Blo 610295 613787 := bstep (se 1 (by rfl) ⟨460340, by rfl⟩ : syracuseStep 613787 = 920681) B920681
theorem B613871 : Blo 610295 613871 := bstep (se 1 (by rfl) ⟨460403, by rfl⟩ : syracuseStep 613871 = 920807) B920807
theorem B614207 : Blo 610295 614207 := bstep (se 1 (by rfl) ⟨460655, by rfl⟩ : syracuseStep 614207 = 921311) B921311
theorem B8839307 : Blo 610295 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B4415759 : Blo 610295 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B4416221 : Blo 610295 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B2319131 : Blo 610295 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B1303607 : Blo 610295 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B2319799 : Blo 610295 2319799 := bstep (se 1 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 2319799 = 3479699) B3479699
theorem B2320103 : Blo 610295 2320103 := bstep (se 1 (by rfl) ⟨1740077, by rfl⟩ : syracuseStep 2320103 = 3480155) B3480155
theorem B1304743 : Blo 610295 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B4254239 : Blo 610295 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B1305247 : Blo 610295 1305247 := bstep (se 1 (by rfl) ⟨978935, by rfl⟩ : syracuseStep 1305247 = 1957871) B1957871
theorem B3107969 : Blo 610295 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B2321743 : Blo 610295 2321743 := bstep (se 1 (by rfl) ⟨1741307, by rfl⟩ : syracuseStep 2321743 = 3482615) B3482615
theorem B2616731 : Blo 610295 2616731 := bstep (se 1 (by rfl) ⟨1962548, by rfl⟩ : syracuseStep 2616731 = 3925097) B3925097
theorem B1470143 : Blo 610295 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B11759363 : Blo 610295 11759363 := bstep (se 1 (by rfl) ⟨8819522, by rfl⟩ : syracuseStep 11759363 = 17639045) B17639045
theorem B4419449 : Blo 610295 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B3928297 : Blo 610295 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B2060531 : Blo 610295 2060531 := bstep (se 1 (by rfl) ⟨1545398, by rfl⟩ : syracuseStep 2060531 = 3090797) B3090797
theorem B2060639 : Blo 610295 2060639 := bstep (se 1 (by rfl) ⟨1545479, by rfl⟩ : syracuseStep 2060639 = 3090959) B3090959
theorem B11891123 : Blo 610295 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B4649561 : Blo 610295 4649561 := bstep (se 2 (by rfl) ⟨1743585, by rfl⟩ : syracuseStep 4649561 = 3487171) B3487171
theorem B2618045 : Blo 610295 2618045 := bstep (se 3 (by rfl) ⟨490883, by rfl⟩ : syracuseStep 2618045 = 981767) B981767
theorem B2552639 : Blo 610295 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B19854305 : Blo 610295 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B1374281 : Blo 610295 1374281 := bstep (se 2 (by rfl) ⟨515355, by rfl⟩ : syracuseStep 1374281 = 1030711) B1030711
theorem B2062475 : Blo 610295 2062475 := bstep (se 1 (by rfl) ⟨1546856, by rfl⟩ : syracuseStep 2062475 = 3093713) B3093713
theorem B882857 : Blo 610295 882857 := bstep (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) B662143
theorem B13236817 : Blo 610295 13236817 := bstep (se 2 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 13236817 = 9927613) B9927613
theorem B916175 : Blo 610295 916175 := bstep (se 1 (by rfl) ⟨687131, by rfl⟩ : syracuseStep 916175 = 1374263) B1374263
theorem B4979407 : Blo 610295 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B2358011 : Blo 610295 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B916265 : Blo 610295 916265 := bstep (se 2 (by rfl) ⟨343599, by rfl⟩ : syracuseStep 916265 = 687199) B687199
theorem B3308359 : Blo 610295 3308359 := bstep (se 1 (by rfl) ⟨2481269, by rfl⟩ : syracuseStep 3308359 = 4962539) B4962539
theorem B916415 : Blo 610295 916415 := bstep (se 1 (by rfl) ⟨687311, by rfl⟩ : syracuseStep 916415 = 1374623) B1374623
theorem B2063393 : Blo 610295 2063393 := bstep (se 2 (by rfl) ⟨773772, by rfl⟩ : syracuseStep 2063393 = 1547545) B1547545
theorem B916799 : Blo 610295 916799 := bstep (se 1 (by rfl) ⟨687599, by rfl⟩ : syracuseStep 916799 = 1375199) B1375199
theorem B2325935 : Blo 610295 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B1965559 : Blo 610295 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B1375865 : Blo 610295 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B917147 : Blo 610295 917147 := bstep (se 1 (by rfl) ⟨687860, by rfl⟩ : syracuseStep 917147 = 1375721) B1375721
theorem B655003 : Blo 610295 655003 := bstep (se 1 (by rfl) ⟨491252, by rfl⟩ : syracuseStep 655003 = 982505) B982505
theorem B2359151 : Blo 610295 2359151 := bstep (se 1 (by rfl) ⟨1769363, by rfl⟩ : syracuseStep 2359151 = 3538727) B3538727
theorem B1376225 : Blo 610295 1376225 := bstep (se 2 (by rfl) ⟨516084, by rfl⟩ : syracuseStep 1376225 = 1032169) B1032169
theorem B917687 : Blo 610295 917687 := bstep (se 1 (by rfl) ⟨688265, by rfl⟩ : syracuseStep 917687 = 1376531) B1376531
theorem B6619319 : Blo 610295 6619319 := bstep (se 1 (by rfl) ⟨4964489, by rfl⟩ : syracuseStep 6619319 = 9928979) B9928979
theorem B917711 : Blo 610295 917711 := bstep (se 1 (by rfl) ⟨688283, by rfl⟩ : syracuseStep 917711 = 1376567) B1376567
theorem B5800211 : Blo 610295 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B15925733 : Blo 610295 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B918521 : Blo 610295 918521 := bstep (se 2 (by rfl) ⟨344445, by rfl⟩ : syracuseStep 918521 = 688891) B688891
theorem B918575 : Blo 610295 918575 := bstep (se 1 (by rfl) ⟨688931, by rfl⟩ : syracuseStep 918575 = 1377863) B1377863
theorem B6358175 : Blo 610295 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B1377593 : Blo 610295 1377593 := bstep (se 2 (by rfl) ⟨516597, by rfl⟩ : syracuseStep 1377593 = 1033195) B1033195
theorem B1377791 : Blo 610295 1377791 := bstep (se 1 (by rfl) ⟨1033343, by rfl⟩ : syracuseStep 1377791 = 2066687) B2066687
theorem B689755 : Blo 610295 689755 := bstep (se 1 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 689755 = 1034633) B1034633
theorem B1378043 : Blo 610295 1378043 := bstep (se 1 (by rfl) ⟨1033532, by rfl⟩ : syracuseStep 1378043 = 2067065) B2067065
theorem B1345391 : Blo 610295 1345391 := bstep (se 1 (by rfl) ⟨1009043, by rfl⟩ : syracuseStep 1345391 = 2018087) B2018087
theorem B919727 : Blo 610295 919727 := bstep (se 1 (by rfl) ⟨689795, by rfl⟩ : syracuseStep 919727 = 1379591) B1379591
theorem B919967 : Blo 610295 919967 := bstep (se 1 (by rfl) ⟨689975, by rfl⟩ : syracuseStep 919967 = 1379951) B1379951
theorem B4721255 : Blo 610295 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B690799 : Blo 610295 690799 := bstep (se 1 (by rfl) ⟨518099, by rfl⟩ : syracuseStep 690799 = 1036199) B1036199
theorem B6621871 : Blo 610295 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B920423 : Blo 610295 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B1739657 : Blo 610295 1739657 := bstep (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) B1304743
theorem B1379411 : Blo 610295 1379411 := bstep (se 1 (by rfl) ⟨1034558, by rfl⟩ : syracuseStep 1379411 = 2069117) B2069117
theorem B920987 : Blo 610295 920987 := bstep (se 1 (by rfl) ⟨690740, by rfl⟩ : syracuseStep 920987 = 1381481) B1381481
theorem B1740329 : Blo 610295 1740329 := bstep (se 2 (by rfl) ⟨652623, by rfl⟩ : syracuseStep 1740329 = 1305247) B1305247
theorem B2330279 : Blo 610295 2330279 := bstep (se 1 (by rfl) ⟨1747709, by rfl⟩ : syracuseStep 2330279 = 3495419) B3495419
theorem B921257 : Blo 610295 921257 := bstep (se 2 (by rfl) ⟨345471, by rfl⟩ : syracuseStep 921257 = 690943) B690943
theorem B1380023 : Blo 610295 1380023 := bstep (se 1 (by rfl) ⟨1035017, by rfl⟩ : syracuseStep 1380023 = 2070035) B2070035
theorem B2068199 : Blo 610295 2068199 := bstep (se 1 (by rfl) ⟨1551149, by rfl⟩ : syracuseStep 2068199 = 3102299) B3102299
theorem B1740943 : Blo 610295 1740943 := bstep (se 1 (by rfl) ⟨1305707, by rfl⟩ : syracuseStep 1740943 = 2611415) B2611415
theorem B15733277 : Blo 610295 15733277 := bstep (se 3 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 15733277 = 5899979) B5899979
theorem B1381031 : Blo 610295 1381031 := bstep (se 1 (by rfl) ⟨1035773, by rfl⟩ : syracuseStep 1381031 = 2071547) B2071547
theorem B1381103 : Blo 610295 1381103 := bstep (se 1 (by rfl) ⟨1035827, by rfl⟩ : syracuseStep 1381103 = 2071655) B2071655
theorem B1381535 : Blo 610295 1381535 := bstep (se 1 (by rfl) ⟨1036151, by rfl⟩ : syracuseStep 1381535 = 2072303) B2072303
theorem B7148735 : Blo 610295 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B1381679 : Blo 610295 1381679 := bstep (se 1 (by rfl) ⟨1036259, by rfl⟩ : syracuseStep 1381679 = 2072519) B2072519
theorem B8852975 : Blo 610295 8852975 := bstep (se 1 (by rfl) ⟨6639731, by rfl⟩ : syracuseStep 8852975 = 13279463) B13279463
theorem B4658795 : Blo 610295 4658795 := bstep (se 1 (by rfl) ⟨3494096, by rfl⟩ : syracuseStep 4658795 = 6988193) B6988193
theorem B1546087 : Blo 610295 1546087 := bstep (se 1 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 1546087 = 2319131) B2319131
theorem B5216237 : Blo 610295 5216237 := bstep (se 3 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 5216237 = 1956089) B1956089
theorem B1546735 : Blo 610295 1546735 := bstep (se 1 (by rfl) ⟨1160051, by rfl⟩ : syracuseStep 1546735 = 2320103) B2320103
theorem B11344637 : Blo 610295 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B3480407 : Blo 610295 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B10493225 : Blo 610295 10493225 := bstep (se 2 (by rfl) ⟨3934959, by rfl⟩ : syracuseStep 10493225 = 7869919) B7869919
theorem B2071979 : Blo 610295 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B2072033 : Blo 610295 2072033 := bstep (se 2 (by rfl) ⟨777012, by rfl⟩ : syracuseStep 2072033 = 1554025) B1554025
theorem B1744487 : Blo 610295 1744487 := bstep (se 1 (by rfl) ⟨1308365, by rfl⟩ : syracuseStep 1744487 = 2616731) B2616731
theorem B7839575 : Blo 610295 7839575 := bstep (se 1 (by rfl) ⟨5879681, by rfl⟩ : syracuseStep 7839575 = 11759363) B11759363
theorem B1745363 : Blo 610295 1745363 := bstep (se 1 (by rfl) ⟨1309022, by rfl⟩ : syracuseStep 1745363 = 2618045) B2618045
theorem B1548841 : Blo 610295 1548841 := bstep (se 2 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 1548841 = 1161631) B1161631
theorem B3483755 : Blo 610295 3483755 := bstep (se 1 (by rfl) ⟨2612816, by rfl⟩ : syracuseStep 3483755 = 5225633) B5225633
theorem B1550623 : Blo 610295 1550623 := bstep (se 1 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 1550623 = 2325935) B2325935
theorem B3091283 : Blo 610295 3091283 := bstep (se 1 (by rfl) ⟨2318462, by rfl⟩ : syracuseStep 3091283 = 4636925) B4636925
theorem B8400131 : Blo 610295 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B837397925 : Blo 610295 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B1650203 : Blo 610295 1650203 := bstep (se 1 (by rfl) ⟨1237652, by rfl⟩ : syracuseStep 1650203 = 2475305) B2475305
theorem B3093065 : Blo 610295 3093065 := bstep (se 2 (by rfl) ⟨1159899, by rfl⟩ : syracuseStep 3093065 = 2319799) B2319799
theorem B143471573 : Blo 610295 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B1553377 : Blo 610295 1553377 := bstep (se 2 (by rfl) ⟨582516, by rfl⟩ : syracuseStep 1553377 = 1165033) B1165033
theorem B2208745 : Blo 610295 2208745 := bstep (se 2 (by rfl) ⟨828279, by rfl⟩ : syracuseStep 2208745 = 1656559) B1656559
theorem B5879375 : Blo 610295 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B1030171 : Blo 610295 1030171 := bstep (se 1 (by rfl) ⟨772628, by rfl⟩ : syracuseStep 1030171 = 1545257) B1545257
theorem B1554785 : Blo 610295 1554785 := bstep (se 2 (by rfl) ⟨583044, by rfl⟩ : syracuseStep 1554785 = 1166089) B1166089
theorem B3717623 : Blo 610295 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B1031015 : Blo 610295 1031015 := bstep (se 1 (by rfl) ⟨773261, by rfl⟩ : syracuseStep 1031015 = 1546523) B1546523
theorem B3095657 : Blo 610295 3095657 := bstep (se 2 (by rfl) ⟨1160871, by rfl⟩ : syracuseStep 3095657 = 2321743) B2321743
theorem B2211023 : Blo 610295 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B1031663 : Blo 610295 1031663 := bstep (se 1 (by rfl) ⟨773747, by rfl⟩ : syracuseStep 1031663 = 1547495) B1547495
theorem B4177487 : Blo 610295 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B869071 : Blo 610295 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B1033087 : Blo 610295 1033087 := bstep (se 1 (by rfl) ⟨774815, by rfl⟩ : syracuseStep 1033087 = 1549631) B1549631
theorem B6996941 : Blo 610295 6996941 := bstep (se 3 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 6996941 = 2623853) B2623853
theorem B7849007 : Blo 610295 7849007 := bstep (se 1 (by rfl) ⟨5886755, by rfl⟩ : syracuseStep 7849007 = 11773511) B11773511
theorem B8045689 : Blo 610295 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B5293811 : Blo 610295 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2934767 : Blo 610295 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B1034471 : Blo 610295 1034471 := bstep (se 1 (by rfl) ⟨775853, by rfl⟩ : syracuseStep 1034471 = 1551707) B1551707
theorem B1886441 : Blo 610295 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B3099707 : Blo 610295 3099707 := bstep (se 1 (by rfl) ⟨2324780, by rfl⟩ : syracuseStep 3099707 = 4649561) B4649561
theorem B17649089 : Blo 610295 17649089 := bstep (se 2 (by rfl) ⟨6618408, by rfl⟩ : syracuseStep 17649089 = 13236817) B13236817
theorem B6639209 : Blo 610295 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B4411145 : Blo 610295 4411145 := bstep (se 2 (by rfl) ⟨1654179, by rfl⟩ : syracuseStep 4411145 = 3308359) B3308359
theorem B1036361 : Blo 610295 1036361 := bstep (se 2 (by rfl) ⟨388635, by rfl⟩ : syracuseStep 1036361 = 777271) B777271
theorem B610783 : Blo 610295 610783 := bstep (se 1 (by rfl) ⟨458087, by rfl⟩ : syracuseStep 610783 = 916175) B916175
theorem B610843 : Blo 610295 610843 := bstep (se 1 (by rfl) ⟨458132, by rfl⟩ : syracuseStep 610843 = 916265) B916265
theorem B610943 : Blo 610295 610943 := bstep (se 1 (by rfl) ⟨458207, by rfl⟩ : syracuseStep 610943 = 916415) B916415
theorem B2609911 : Blo 610295 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B873337 : Blo 610295 873337 := bstep (se 2 (by rfl) ⟨327501, by rfl⟩ : syracuseStep 873337 = 655003) B655003
theorem B611199 : Blo 610295 611199 := bstep (se 1 (by rfl) ⟨458399, by rfl⟩ : syracuseStep 611199 = 916799) B916799
theorem B611431 : Blo 610295 611431 := bstep (se 1 (by rfl) ⟨458573, by rfl⟩ : syracuseStep 611431 = 917147) B917147
theorem B775271 : Blo 610295 775271 := bstep (se 1 (by rfl) ⟨581453, by rfl⟩ : syracuseStep 775271 = 1162907) B1162907
theorem B3102461 : Blo 610295 3102461 := bstep (se 3 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 3102461 = 1163423) B1163423
theorem B612415 : Blo 610295 612415 := bstep (se 1 (by rfl) ⟨459311, by rfl⟩ : syracuseStep 612415 = 918623) B918623
theorem B612455 : Blo 610295 612455 := bstep (se 1 (by rfl) ⟨459341, by rfl⟩ : syracuseStep 612455 = 918683) B918683
theorem B17685175 : Blo 610295 17685175 := bstep (se 1 (by rfl) ⟨13263881, by rfl⟩ : syracuseStep 17685175 = 26527763) B26527763
theorem B613247 : Blo 610295 613247 := bstep (se 1 (by rfl) ⟨459935, by rfl⟩ : syracuseStep 613247 = 919871) B919871
theorem B3365999 : Blo 610295 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B613695 : Blo 610295 613695 := bstep (se 1 (by rfl) ⟨460271, by rfl⟩ : syracuseStep 613695 = 920543) B920543
theorem B14345405 : Blo 610295 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B5957875 : Blo 610295 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B5892871 : Blo 610295 5892871 := bstep (se 1 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 5892871 = 8839307) B8839307
theorem B2943839 : Blo 610295 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B5237729 : Blo 610295 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B2354285 : Blo 610295 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B2944147 : Blo 610295 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B6288029 : Blo 610295 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B980095 : Blo 610295 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B2946299 : Blo 610295 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B1373687 : Blo 610295 1373687 := bstep (se 1 (by rfl) ⟨1030265, by rfl⟩ : syracuseStep 1373687 = 2060531) B2060531
theorem B2323961 : Blo 610295 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B1373759 : Blo 610295 1373759 := bstep (se 1 (by rfl) ⟨1030319, by rfl⟩ : syracuseStep 1373759 = 2060639) B2060639
theorem B7927415 : Blo 610295 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B2062205 : Blo 610295 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B13236203 : Blo 610295 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B27228149 : Blo 610295 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B1374713 : Blo 610295 1374713 := bstep (se 2 (by rfl) ⟨515517, by rfl⟩ : syracuseStep 1374713 = 1031035) B1031035
theorem B686695 : Blo 610295 686695 := bstep (se 1 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 686695 = 1030043) B1030043
theorem B916187 : Blo 610295 916187 := bstep (se 1 (by rfl) ⟨687140, by rfl⟩ : syracuseStep 916187 = 1374281) B1374281
theorem B1374983 : Blo 610295 1374983 := bstep (se 1 (by rfl) ⟨1031237, by rfl⟩ : syracuseStep 1374983 = 2062475) B2062475
theorem B2620745 : Blo 610295 2620745 := bstep (se 2 (by rfl) ⟨982779, by rfl⟩ : syracuseStep 2620745 = 1965559) B1965559
theorem B1375595 : Blo 610295 1375595 := bstep (se 1 (by rfl) ⟨1031696, by rfl⟩ : syracuseStep 1375595 = 2063393) B2063393
theorem B2784935 : Blo 610295 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B2064095 : Blo 610295 2064095 := bstep (se 1 (by rfl) ⟨1548071, by rfl⟩ : syracuseStep 2064095 = 3096143) B3096143
theorem B917243 : Blo 610295 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B1572767 : Blo 610295 1572767 := bstep (se 1 (by rfl) ⟨1179575, by rfl⟩ : syracuseStep 1572767 = 2359151) B2359151
theorem B688063 : Blo 610295 688063 := bstep (se 1 (by rfl) ⟨516047, by rfl⟩ : syracuseStep 688063 = 1032095) B1032095
theorem B22708187 : Blo 610295 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B917483 : Blo 610295 917483 := bstep (se 1 (by rfl) ⟨688112, by rfl⟩ : syracuseStep 917483 = 1376225) B1376225
theorem B3866807 : Blo 610295 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B10617155 : Blo 610295 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B2065121 : Blo 610295 2065121 := bstep (se 2 (by rfl) ⟨774420, by rfl⟩ : syracuseStep 2065121 = 1548841) B1548841
theorem B918395 : Blo 610295 918395 := bstep (se 1 (by rfl) ⟨688796, by rfl⟩ : syracuseStep 918395 = 1377593) B1377593
theorem B918527 : Blo 610295 918527 := bstep (se 1 (by rfl) ⟨688895, by rfl⟩ : syracuseStep 918527 = 1377791) B1377791
theorem B918695 : Blo 610295 918695 := bstep (se 1 (by rfl) ⟨689021, by rfl⟩ : syracuseStep 918695 = 1378043) B1378043
theorem B1377449 : Blo 610295 1377449 := bstep (se 2 (by rfl) ⟨516543, by rfl⟩ : syracuseStep 1377449 = 1033087) B1033087
theorem B689647 : Blo 610295 689647 := bstep (se 1 (by rfl) ⟨517235, by rfl⟩ : syracuseStep 689647 = 1034471) B1034471
theorem B3147503 : Blo 610295 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B2066471 : Blo 610295 2066471 := bstep (se 1 (by rfl) ⟨1549853, by rfl⟩ : syracuseStep 2066471 = 3099707) B3099707
theorem B919607 : Blo 610295 919607 := bstep (se 1 (by rfl) ⟨689705, by rfl⟩ : syracuseStep 919607 = 1379411) B1379411
theorem B919673 : Blo 610295 919673 := bstep (se 2 (by rfl) ⟨344877, by rfl⟩ : syracuseStep 919673 = 689755) B689755
theorem B11766059 : Blo 610295 11766059 := bstep (se 1 (by rfl) ⟨8824544, by rfl⟩ : syracuseStep 11766059 = 17649089) B17649089
theorem B4426139 : Blo 610295 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B20122037 : Blo 610295 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B920015 : Blo 610295 920015 := bstep (se 1 (by rfl) ⟨690011, by rfl⟩ : syracuseStep 920015 = 1380023) B1380023
theorem B1378799 : Blo 610295 1378799 := bstep (se 1 (by rfl) ⟨1034099, by rfl⟩ : syracuseStep 1378799 = 2068199) B2068199
theorem B690907 : Blo 610295 690907 := bstep (se 1 (by rfl) ⟨518180, by rfl⟩ : syracuseStep 690907 = 1036361) B1036361
theorem B2067389 : Blo 610295 2067389 := bstep (se 3 (by rfl) ⟨387635, by rfl⟩ : syracuseStep 2067389 = 775271) B775271
theorem B10488851 : Blo 610295 10488851 := bstep (se 1 (by rfl) ⟨7866638, by rfl⟩ : syracuseStep 10488851 = 15733277) B15733277
theorem B2067497 : Blo 610295 2067497 := bstep (se 2 (by rfl) ⟨775311, by rfl⟩ : syracuseStep 2067497 = 1550623) B1550623
theorem B920687 : Blo 610295 920687 := bstep (se 1 (by rfl) ⟨690515, by rfl⟩ : syracuseStep 920687 = 1381031) B1381031
theorem B920735 : Blo 610295 920735 := bstep (se 1 (by rfl) ⟨690551, by rfl⟩ : syracuseStep 920735 = 1381103) B1381103
theorem B921023 : Blo 610295 921023 := bstep (se 1 (by rfl) ⟨690767, by rfl⟩ : syracuseStep 921023 = 1381535) B1381535
theorem B921065 : Blo 610295 921065 := bstep (se 2 (by rfl) ⟨345399, by rfl⟩ : syracuseStep 921065 = 690799) B690799
theorem B921119 : Blo 610295 921119 := bstep (se 1 (by rfl) ⟨690839, by rfl⟩ : syracuseStep 921119 = 1381679) B1381679
theorem B5901983 : Blo 610295 5901983 := bstep (se 1 (by rfl) ⟨4426487, by rfl⟩ : syracuseStep 5901983 = 8852975) B8852975
theorem B2068307 : Blo 610295 2068307 := bstep (se 1 (by rfl) ⟨1551230, by rfl⟩ : syracuseStep 2068307 = 3102461) B3102461
theorem B3477491 : Blo 610295 3477491 := bstep (se 1 (by rfl) ⟨2608118, by rfl⟩ : syracuseStep 3477491 = 5216237) B5216237
theorem B1381319 : Blo 610295 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B1381355 : Blo 610295 1381355 := bstep (se 1 (by rfl) ⟨1036016, by rfl⟩ : syracuseStep 1381355 = 2072033) B2072033
theorem B3479881 : Blo 610295 3479881 := bstep (se 2 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 3479881 = 2609911) B2609911
theorem B2071169 : Blo 610295 2071169 := bstep (se 2 (by rfl) ⟨776688, by rfl⟩ : syracuseStep 2071169 = 1553377) B1553377
theorem B1549307 : Blo 610295 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B5284943 : Blo 610295 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B8824135 : Blo 610295 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B1747163 : Blo 610295 1747163 := bstep (se 1 (by rfl) ⟨1310372, by rfl⟩ : syracuseStep 1747163 = 2620745) B2620745
theorem B4664627 : Blo 610295 4664627 := bstep (se 1 (by rfl) ⟨3498470, by rfl⟩ : syracuseStep 4664627 = 6996941) B6996941
theorem B4238783 : Blo 610295 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B1158761 : Blo 610295 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B896927 : Blo 610295 896927 := bstep (se 1 (by rfl) ⟨672695, by rfl⟩ : syracuseStep 896927 = 1345391) B1345391
theorem B10727585 : Blo 610295 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B1159771 : Blo 610295 1159771 := bstep (se 1 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 1159771 = 1739657) B1739657
theorem B1160219 : Blo 610295 1160219 := bstep (se 1 (by rfl) ⟨870164, by rfl⟩ : syracuseStep 1160219 = 1740329) B1740329
theorem B1553519 : Blo 610295 1553519 := bstep (se 1 (by rfl) ⟨1165139, by rfl⟩ : syracuseStep 1553519 = 2330279) B2330279
theorem B4765823 : Blo 610295 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B8829161 : Blo 610295 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B2243999 : Blo 610295 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B6995483 : Blo 610295 6995483 := bstep (se 1 (by rfl) ⟨5246612, by rfl⟩ : syracuseStep 6995483 = 10493225) B10493225
theorem B1162991 : Blo 610295 1162991 := bstep (se 1 (by rfl) ⟨872243, by rfl⟩ : syracuseStep 1162991 = 1744487) B1744487
theorem B5226383 : Blo 610295 5226383 := bstep (se 1 (by rfl) ⟨3919787, by rfl⟩ : syracuseStep 5226383 = 7839575) B7839575
theorem B1163575 : Blo 610295 1163575 := bstep (se 1 (by rfl) ⟨872681, by rfl⟩ : syracuseStep 1163575 = 1745363) B1745363
theorem B1164449 : Blo 610295 1164449 := bstep (se 2 (by rfl) ⟨436668, by rfl⟩ : syracuseStep 1164449 = 873337) B873337
theorem B9913661 : Blo 610295 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B3491819 : Blo 610295 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B1100135 : Blo 610295 1100135 := bstep (se 1 (by rfl) ⟨825101, by rfl⟩ : syracuseStep 1100135 = 1650203) B1650203
theorem B6278093 : Blo 610295 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B23580233 : Blo 610295 23580233 := bstep (se 2 (by rfl) ⟨8842587, by rfl⟩ : syracuseStep 23580233 = 17685175) B17685175
theorem B3919583 : Blo 610295 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B1036523 : Blo 610295 1036523 := bstep (se 1 (by rfl) ⟨777392, by rfl⟩ : syracuseStep 1036523 = 1554785) B1554785
theorem B610791 : Blo 610295 610791 := bstep (se 1 (by rfl) ⟨458093, by rfl⟩ : syracuseStep 610791 = 916187) B916187
theorem B1856623 : Blo 610295 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B611495 : Blo 610295 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B611655 : Blo 610295 611655 := bstep (se 1 (by rfl) ⟨458741, by rfl⟩ : syracuseStep 611655 = 917483) B917483
theorem B611791 : Blo 610295 611791 := bstep (se 1 (by rfl) ⟨458843, by rfl⟩ : syracuseStep 611791 = 917687) B917687
theorem B4412879 : Blo 610295 4412879 := bstep (se 1 (by rfl) ⟨3309659, by rfl⟩ : syracuseStep 4412879 = 6619319) B6619319
theorem B611807 : Blo 610295 611807 := bstep (se 1 (by rfl) ⟨458855, by rfl⟩ : syracuseStep 611807 = 917711) B917711
theorem B612347 : Blo 610295 612347 := bstep (se 1 (by rfl) ⟨459260, by rfl⟩ : syracuseStep 612347 = 918521) B918521
theorem B612383 : Blo 610295 612383 := bstep (se 1 (by rfl) ⟨459287, by rfl⟩ : syracuseStep 612383 = 918575) B918575
theorem B5232671 : Blo 610295 5232671 := bstep (se 1 (by rfl) ⟨3924503, by rfl⟩ : syracuseStep 5232671 = 7849007) B7849007
theorem B3529207 : Blo 610295 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B31775333 : Blo 610295 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B1956511 : Blo 610295 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B613151 : Blo 610295 613151 := bstep (se 1 (by rfl) ⟨459863, by rfl⟩ : syracuseStep 613151 = 919727) B919727
theorem B613311 : Blo 610295 613311 := bstep (se 1 (by rfl) ⟨459983, by rfl⟩ : syracuseStep 613311 = 919967) B919967
theorem B613615 : Blo 610295 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B613991 : Blo 610295 613991 := bstep (se 1 (by rfl) ⟨460493, by rfl⟩ : syracuseStep 613991 = 920987) B920987
theorem B614171 : Blo 610295 614171 := bstep (se 1 (by rfl) ⟨460628, by rfl⟩ : syracuseStep 614171 = 921257) B921257
theorem B7856797 : Blo 610295 7856797 := bstep (se 3 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 7856797 = 2946299) B2946299
theorem B7857161 : Blo 610295 7857161 := bstep (se 2 (by rfl) ⟨2946435, by rfl⟩ : syracuseStep 7857161 = 5892871) B5892871
theorem B3105863 : Blo 610295 3105863 := bstep (se 1 (by rfl) ⟨2329397, by rfl⟩ : syracuseStep 3105863 = 4658795) B4658795
theorem B3925529 : Blo 610295 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B7563091 : Blo 610295 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B2320271 : Blo 610295 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B2321257 : Blo 610295 2321257 := bstep (se 2 (by rfl) ⟨870471, by rfl⟩ : syracuseStep 2321257 = 1740943) B1740943
theorem B9563603 : Blo 610295 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B2944993 : Blo 610295 2944993 := bstep (se 2 (by rfl) ⟨1104372, by rfl⟩ : syracuseStep 2944993 = 2208745) B2208745
theorem B2322503 : Blo 610295 2322503 := bstep (se 1 (by rfl) ⟨1741877, by rfl⟩ : syracuseStep 2322503 = 3483755) B3483755
theorem B1306793 : Blo 610295 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B2060855 : Blo 610295 2060855 := bstep (se 1 (by rfl) ⟨1545641, by rfl⟩ : syracuseStep 2060855 = 3091283) B3091283
theorem B1962559 : Blo 610295 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B5600087 : Blo 610295 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B558265283 : Blo 610295 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B2061449 : Blo 610295 2061449 := bstep (se 2 (by rfl) ⟨773043, by rfl⟩ : syracuseStep 2061449 = 1546087) B1546087
theorem B1373561 : Blo 610295 1373561 := bstep (se 2 (by rfl) ⟨515085, by rfl⟩ : syracuseStep 1373561 = 1030171) B1030171
theorem B2062043 : Blo 610295 2062043 := bstep (se 1 (by rfl) ⟨1546532, by rfl⟩ : syracuseStep 2062043 = 3093065) B3093065
theorem B4192019 : Blo 610295 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B5896061 : Blo 610295 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B95647715 : Blo 610295 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B2062313 : Blo 610295 2062313 := bstep (se 2 (by rfl) ⟨773367, by rfl⟩ : syracuseStep 2062313 = 1546735) B1546735
theorem B915593 : Blo 610295 915593 := bstep (se 2 (by rfl) ⟨343347, by rfl⟩ : syracuseStep 915593 = 686695) B686695
theorem B915791 : Blo 610295 915791 := bstep (se 1 (by rfl) ⟨686843, by rfl⟩ : syracuseStep 915791 = 1373687) B1373687
theorem B915839 : Blo 610295 915839 := bstep (se 1 (by rfl) ⟨686879, by rfl⟩ : syracuseStep 915839 = 1373759) B1373759
theorem B1374803 : Blo 610295 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B18152099 : Blo 610295 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B916475 : Blo 610295 916475 := bstep (se 1 (by rfl) ⟨687356, by rfl⟩ : syracuseStep 916475 = 1374713) B1374713
theorem B916655 : Blo 610295 916655 := bstep (se 1 (by rfl) ⟨687491, by rfl⟩ : syracuseStep 916655 = 1374983) B1374983
theorem B687343 : Blo 610295 687343 := bstep (se 1 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 687343 = 1031015) B1031015
theorem B11763053 : Blo 610295 11763053 := bstep (se 3 (by rfl) ⟨2205572, by rfl⟩ : syracuseStep 11763053 = 4411145) B4411145
theorem B2063771 : Blo 610295 2063771 := bstep (se 1 (by rfl) ⟨1547828, by rfl⟩ : syracuseStep 2063771 = 3095657) B3095657
theorem B917063 : Blo 610295 917063 := bstep (se 1 (by rfl) ⟨687797, by rfl⟩ : syracuseStep 917063 = 1375595) B1375595
theorem B687775 : Blo 610295 687775 := bstep (se 1 (by rfl) ⟨515831, by rfl⟩ : syracuseStep 687775 = 1031663) B1031663
theorem B2784991 : Blo 610295 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B1376063 : Blo 610295 1376063 := bstep (se 1 (by rfl) ⟨1032047, by rfl⟩ : syracuseStep 1376063 = 2064095) B2064095
theorem B917417 : Blo 610295 917417 := bstep (se 2 (by rfl) ⟨344031, by rfl⟩ : syracuseStep 917417 = 688063) B688063
theorem B1048511 : Blo 610295 1048511 := bstep (se 1 (by rfl) ⟨786383, by rfl⟩ : syracuseStep 1048511 = 1572767) B1572767
theorem B15138791 : Blo 610295 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B7078103 : Blo 610295 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B1376747 : Blo 610295 1376747 := bstep (se 1 (by rfl) ⟨1032560, by rfl⟩ : syracuseStep 1376747 = 2065121) B2065121
theorem B918299 : Blo 610295 918299 := bstep (se 1 (by rfl) ⟨688724, by rfl⟩ : syracuseStep 918299 = 1377449) B1377449
theorem B2327879 : Blo 610295 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1377647 : Blo 610295 1377647 := bstep (se 1 (by rfl) ⟨1033235, by rfl⟩ : syracuseStep 1377647 = 2066471) B2066471
theorem B2950759 : Blo 610295 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B919199 : Blo 610295 919199 := bstep (se 1 (by rfl) ⟨689399, by rfl⟩ : syracuseStep 919199 = 1378799) B1378799
theorem B11765513 : Blo 610295 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B1378259 : Blo 610295 1378259 := bstep (se 1 (by rfl) ⟨1033694, by rfl⟩ : syracuseStep 1378259 = 2067389) B2067389
theorem B919529 : Blo 610295 919529 := bstep (se 2 (by rfl) ⟨344823, by rfl⟩ : syracuseStep 919529 = 689647) B689647
theorem B1378331 : Blo 610295 1378331 := bstep (se 1 (by rfl) ⟨1033748, by rfl⟩ : syracuseStep 1378331 = 2067497) B2067497
theorem B3934655 : Blo 610295 3934655 := bstep (se 1 (by rfl) ⟨2950991, by rfl⟩ : syracuseStep 3934655 = 5901983) B5901983
theorem B1378871 : Blo 610295 1378871 := bstep (se 1 (by rfl) ⟨1034153, by rfl⟩ : syracuseStep 1378871 = 2068307) B2068307
theorem B691015 : Blo 610295 691015 := bstep (se 1 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 691015 = 1036523) B1036523
theorem B920879 : Blo 610295 920879 := bstep (se 1 (by rfl) ⟨690659, by rfl⟩ : syracuseStep 920879 = 1381319) B1381319
theorem B920903 : Blo 610295 920903 := bstep (se 1 (by rfl) ⟨690677, by rfl⟩ : syracuseStep 920903 = 1381355) B1381355
theorem B921209 : Blo 610295 921209 := bstep (se 2 (by rfl) ⟨345453, by rfl⟩ : syracuseStep 921209 = 690907) B690907
theorem B1380779 : Blo 610295 1380779 := bstep (se 1 (by rfl) ⟨1035584, by rfl⟩ : syracuseStep 1380779 = 2071169) B2071169
theorem B8393341 : Blo 610295 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B2070575 : Blo 610295 2070575 := bstep (se 1 (by rfl) ⟨1552931, by rfl⟩ : syracuseStep 2070575 = 3105863) B3105863
theorem B1546361 : Blo 610295 1546361 := bstep (se 2 (by rfl) ⟨579885, by rfl⟩ : syracuseStep 1546361 = 1159771) B1159771
theorem B1546847 : Blo 610295 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B2825855 : Blo 610295 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B1548335 : Blo 610295 1548335 := bstep (se 1 (by rfl) ⟨1161251, by rfl⟩ : syracuseStep 1548335 = 2322503) B2322503
theorem B7151723 : Blo 610295 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B2794679 : Blo 610295 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B25502941 : Blo 610295 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B12101399 : Blo 610295 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B7842035 : Blo 610295 7842035 := bstep (se 1 (by rfl) ⟨5881526, by rfl⟩ : syracuseStep 7842035 = 11763053) B11763053
theorem B3713321 : Blo 610295 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B4663655 : Blo 610295 4663655 := bstep (se 1 (by rfl) ⟨3497741, by rfl⟩ : syracuseStep 4663655 = 6995483) B6995483
theorem B2796029 : Blo 610295 2796029 := bstep (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) B1048511
theorem B3484255 : Blo 610295 3484255 := bstep (se 1 (by rfl) ⟨2613191, by rfl⟩ : syracuseStep 3484255 = 5226383) B5226383
theorem B1551433 : Blo 610295 1551433 := bstep (se 2 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 1551433 = 1163575) B1163575
theorem B3484781 : Blo 610295 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B7844039 : Blo 610295 7844039 := bstep (se 1 (by rfl) ⟨5883029, by rfl⟩ : syracuseStep 7844039 = 11766059) B11766059
theorem B733423 : Blo 610295 733423 := bstep (se 1 (by rfl) ⟨550067, by rfl⟩ : syracuseStep 733423 = 1100135) B1100135
theorem B13414691 : Blo 610295 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B6992567 : Blo 610295 6992567 := bstep (se 1 (by rfl) ⟨5244425, by rfl⟩ : syracuseStep 6992567 = 10488851) B10488851
theorem B10466981 : Blo 610295 10466981 := bstep (se 4 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 10466981 = 1962559) B1962559
theorem B3095009 : Blo 610295 3095009 := bstep (se 2 (by rfl) ⟨1160628, by rfl⟩ : syracuseStep 3095009 = 2321257) B2321257
theorem B3488447 : Blo 610295 3488447 := bstep (se 1 (by rfl) ⟨2616335, by rfl⟩ : syracuseStep 3488447 = 5232671) B5232671
theorem B1032871 : Blo 610295 1032871 := bstep (se 1 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 1032871 = 1549307) B1549307
theorem B3523295 : Blo 610295 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B338936885 : Blo 610295 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B1164775 : Blo 610295 1164775 := bstep (se 1 (by rfl) ⟨873581, by rfl⟩ : syracuseStep 1164775 = 1747163) B1747163
theorem B2475497 : Blo 610295 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B772507 : Blo 610295 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B4639841 : Blo 610295 4639841 := bstep (se 2 (by rfl) ⟨1739940, by rfl⟩ : syracuseStep 4639841 = 3479881) B3479881
theorem B4705609 : Blo 610295 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B773479 : Blo 610295 773479 := bstep (se 1 (by rfl) ⟨580109, by rfl⟩ : syracuseStep 773479 = 1160219) B1160219
theorem B1035679 : Blo 610295 1035679 := bstep (se 1 (by rfl) ⟨776759, by rfl⟩ : syracuseStep 1035679 = 1553519) B1553519
theorem B2608681 : Blo 610295 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B610395 : Blo 610295 610395 := bstep (se 1 (by rfl) ⟨457796, by rfl⟩ : syracuseStep 610395 = 915593) B915593
theorem B5886107 : Blo 610295 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B610527 : Blo 610295 610527 := bstep (se 1 (by rfl) ⟨457895, by rfl⟩ : syracuseStep 610527 = 915791) B915791
theorem B610559 : Blo 610295 610559 := bstep (se 1 (by rfl) ⟨457919, by rfl⟩ : syracuseStep 610559 = 915839) B915839
theorem B610983 : Blo 610295 610983 := bstep (se 1 (by rfl) ⟨458237, by rfl⟩ : syracuseStep 610983 = 916475) B916475
theorem B611103 : Blo 610295 611103 := bstep (se 1 (by rfl) ⟨458327, by rfl⟩ : syracuseStep 611103 = 916655) B916655
theorem B1495999 : Blo 610295 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B611375 : Blo 610295 611375 := bstep (se 1 (by rfl) ⟨458531, by rfl⟩ : syracuseStep 611375 = 917063) B917063
theorem B775327 : Blo 610295 775327 := bstep (se 1 (by rfl) ⟨581495, by rfl⟩ : syracuseStep 775327 = 1162991) B1162991
theorem B611611 : Blo 610295 611611 := bstep (se 1 (by rfl) ⟨458708, by rfl⟩ : syracuseStep 611611 = 917417) B917417
theorem B2577871 : Blo 610295 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B612263 : Blo 610295 612263 := bstep (se 1 (by rfl) ⟨459197, by rfl⟩ : syracuseStep 612263 = 918395) B918395
theorem B612351 : Blo 610295 612351 := bstep (se 1 (by rfl) ⟨459263, by rfl⟩ : syracuseStep 612351 = 918527) B918527
theorem B776299 : Blo 610295 776299 := bstep (se 1 (by rfl) ⟨582224, by rfl⟩ : syracuseStep 776299 = 1164449) B1164449
theorem B612463 : Blo 610295 612463 := bstep (se 1 (by rfl) ⟨459347, by rfl⟩ : syracuseStep 612463 = 918695) B918695
theorem B10475729 : Blo 610295 10475729 := bstep (se 2 (by rfl) ⟨3928398, by rfl⟩ : syracuseStep 10475729 = 7856797) B7856797
theorem B6609107 : Blo 610295 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B613071 : Blo 610295 613071 := bstep (se 1 (by rfl) ⟨459803, by rfl⟩ : syracuseStep 613071 = 919607) B919607
theorem B613115 : Blo 610295 613115 := bstep (se 1 (by rfl) ⟨459836, by rfl⟩ : syracuseStep 613115 = 919673) B919673
theorem B613343 : Blo 610295 613343 := bstep (se 1 (by rfl) ⟨460007, by rfl⟩ : syracuseStep 613343 = 920015) B920015
theorem B4185395 : Blo 610295 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B613791 : Blo 610295 613791 := bstep (se 1 (by rfl) ⟨460343, by rfl⟩ : syracuseStep 613791 = 920687) B920687
theorem B613823 : Blo 610295 613823 := bstep (se 1 (by rfl) ⟨460367, by rfl⟩ : syracuseStep 613823 = 920735) B920735
theorem B614015 : Blo 610295 614015 := bstep (se 1 (by rfl) ⟨460511, by rfl⟩ : syracuseStep 614015 = 921023) B921023
theorem B614043 : Blo 610295 614043 := bstep (se 1 (by rfl) ⟨460532, by rfl⟩ : syracuseStep 614043 = 921065) B921065
theorem B614079 : Blo 610295 614079 := bstep (se 1 (by rfl) ⟨460559, by rfl⟩ : syracuseStep 614079 = 921119) B921119
theorem B15720155 : Blo 610295 15720155 := bstep (se 1 (by rfl) ⟨11790116, by rfl⟩ : syracuseStep 15720155 = 23580233) B23580233
theorem B10084121 : Blo 610295 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B2613055 : Blo 610295 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B2318327 : Blo 610295 2318327 := bstep (se 1 (by rfl) ⟨1738745, by rfl⟩ : syracuseStep 2318327 = 3477491) B3477491
theorem B2941919 : Blo 610295 2941919 := bstep (se 1 (by rfl) ⟨2206439, by rfl⟩ : syracuseStep 2941919 = 4412879) B4412879
theorem B3926657 : Blo 610295 3926657 := bstep (se 2 (by rfl) ⟨1472496, by rfl⟩ : syracuseStep 3926657 = 2944993) B2944993
theorem B5238107 : Blo 610295 5238107 := bstep (se 1 (by rfl) ⟨3928580, by rfl⟩ : syracuseStep 5238107 = 7857161) B7857161
theorem B2617019 : Blo 610295 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B3109751 : Blo 610295 3109751 := bstep (se 1 (by rfl) ⟨2332313, by rfl⟩ : syracuseStep 3109751 = 4664627) B4664627
theorem B1373903 : Blo 610295 1373903 := bstep (se 1 (by rfl) ⟨1030427, by rfl⟩ : syracuseStep 1373903 = 2060855) B2060855
theorem B3733391 : Blo 610295 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B372176855 : Blo 610295 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B1374299 : Blo 610295 1374299 := bstep (se 1 (by rfl) ⟨1030724, by rfl⟩ : syracuseStep 1374299 = 2061449) B2061449
theorem B915707 : Blo 610295 915707 := bstep (se 1 (by rfl) ⟨686780, by rfl⟩ : syracuseStep 915707 = 1373561) B1373561
theorem B1374695 : Blo 610295 1374695 := bstep (se 1 (by rfl) ⟨1031021, by rfl⟩ : syracuseStep 1374695 = 2062043) B2062043
theorem B3930707 : Blo 610295 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B63765143 : Blo 610295 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B1374875 : Blo 610295 1374875 := bstep (se 1 (by rfl) ⟨1031156, by rfl⟩ : syracuseStep 1374875 = 2062313) B2062313
theorem B3177215 : Blo 610295 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B916457 : Blo 610295 916457 := bstep (se 2 (by rfl) ⟨343671, by rfl⟩ : syracuseStep 916457 = 687343) B687343
theorem B916535 : Blo 610295 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B917033 : Blo 610295 917033 := bstep (se 2 (by rfl) ⟨343887, by rfl⟩ : syracuseStep 917033 = 687775) B687775
theorem B1375847 : Blo 610295 1375847 := bstep (se 1 (by rfl) ⟨1031885, by rfl⟩ : syracuseStep 1375847 = 2063771) B2063771
theorem B2391805 : Blo 610295 2391805 := bstep (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) B896927
theorem B917375 : Blo 610295 917375 := bstep (se 1 (by rfl) ⟨688031, by rfl⟩ : syracuseStep 917375 = 1376063) B1376063
theorem B10092527 : Blo 610295 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B4718735 : Blo 610295 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B917831 : Blo 610295 917831 := bstep (se 1 (by rfl) ⟨688373, by rfl⟩ : syracuseStep 917831 = 1376747) B1376747
theorem B1377161 : Blo 610295 1377161 := bstep (se 2 (by rfl) ⟨516435, by rfl⟩ : syracuseStep 1377161 = 1032871) B1032871
theorem B918431 : Blo 610295 918431 := bstep (se 1 (by rfl) ⟨688823, by rfl⟩ : syracuseStep 918431 = 1377647) B1377647
theorem B918839 : Blo 610295 918839 := bstep (se 1 (by rfl) ⟨689129, by rfl⟩ : syracuseStep 918839 = 1378259) B1378259
theorem B918887 : Blo 610295 918887 := bstep (se 1 (by rfl) ⟨689165, by rfl⟩ : syracuseStep 918887 = 1378331) B1378331
theorem B2623103 : Blo 610295 2623103 := bstep (se 1 (by rfl) ⟨1967327, by rfl⟩ : syracuseStep 2623103 = 3934655) B3934655
theorem B919247 : Blo 610295 919247 := bstep (se 1 (by rfl) ⟨689435, by rfl⟩ : syracuseStep 919247 = 1378871) B1378871
theorem B3934345 : Blo 610295 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B920519 : Blo 610295 920519 := bstep (se 1 (by rfl) ⟨690389, by rfl⟩ : syracuseStep 920519 = 1380779) B1380779
theorem B921353 : Blo 610295 921353 := bstep (se 2 (by rfl) ⟨345507, by rfl⟩ : syracuseStep 921353 = 691015) B691015
theorem B1380383 : Blo 610295 1380383 := bstep (se 1 (by rfl) ⟨1035287, by rfl⟩ : syracuseStep 1380383 = 2070575) B2070575
theorem B2068577 : Blo 610295 2068577 := bstep (se 2 (by rfl) ⟨775716, by rfl⟩ : syracuseStep 2068577 = 1551433) B1551433
theorem B6983819 : Blo 610295 6983819 := bstep (se 1 (by rfl) ⟨5237864, by rfl⟩ : syracuseStep 6983819 = 10475729) B10475729
theorem B1380905 : Blo 610295 1380905 := bstep (se 2 (by rfl) ⟨517839, by rfl⟩ : syracuseStep 1380905 = 1035679) B1035679
theorem B3478241 : Blo 610295 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B2790263 : Blo 610295 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B6722747 : Blo 610295 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B1545551 : Blo 610295 1545551 := bstep (se 1 (by rfl) ⟨1159163, by rfl⟩ : syracuseStep 1545551 = 2318327) B2318327
theorem B9902189 : Blo 610295 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B8067599 : Blo 610295 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B1744679 : Blo 610295 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B4661711 : Blo 610295 4661711 := bstep (se 1 (by rfl) ⟨3496283, by rfl⟩ : syracuseStep 4661711 = 6992567) B6992567
theorem B2073167 : Blo 610295 2073167 := bstep (se 1 (by rfl) ⟨1554875, by rfl⟩ : syracuseStep 2073167 = 3109751) B3109751
theorem B42510095 : Blo 610295 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B3189073 : Blo 610295 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B3484073 : Blo 610295 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B6728351 : Blo 610295 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B1551919 : Blo 610295 1551919 := bstep (se 1 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 1551919 = 2327879) B2327879
theorem B1650331 : Blo 610295 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B7843675 : Blo 610295 7843675 := bstep (se 1 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 7843675 = 11765513) B11765513
theorem B1553033 : Blo 610295 1553033 := bstep (se 2 (by rfl) ⟨582387, by rfl⟩ : syracuseStep 1553033 = 1164775) B1164775
theorem B3093227 : Blo 610295 3093227 := bstep (se 1 (by rfl) ⟨2319920, by rfl⟩ : syracuseStep 3093227 = 4639841) B4639841
theorem B1030009 : Blo 610295 1030009 := bstep (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) B772507
theorem B1030907 : Blo 610295 1030907 := bstep (se 1 (by rfl) ⟨773180, by rfl⟩ : syracuseStep 1030907 = 1546361) B1546361
theorem B4406071 : Blo 610295 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B1031231 : Blo 610295 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B6274145 : Blo 610295 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B1031305 : Blo 610295 1031305 := bstep (se 2 (by rfl) ⟨386739, by rfl⟩ : syracuseStep 1031305 = 773479) B773479
theorem B1883903 : Blo 610295 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B1032223 : Blo 610295 1032223 := bstep (se 1 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 1032223 = 1548335) B1548335
theorem B4767815 : Blo 610295 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B11191121 : Blo 610295 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B5228023 : Blo 610295 5228023 := bstep (se 1 (by rfl) ⟨3921017, by rfl⟩ : syracuseStep 5228023 = 7842035) B7842035
theorem B1033769 : Blo 610295 1033769 := bstep (se 2 (by rfl) ⟨387663, by rfl⟩ : syracuseStep 1033769 = 775327) B775327
theorem B3492071 : Blo 610295 3492071 := bstep (se 1 (by rfl) ⟨2619053, by rfl⟩ : syracuseStep 3492071 = 5238107) B5238107
theorem B5229359 : Blo 610295 5229359 := bstep (se 1 (by rfl) ⟨3922019, by rfl⟩ : syracuseStep 5229359 = 7844039) B7844039
theorem B1035065 : Blo 610295 1035065 := bstep (se 2 (by rfl) ⟨388149, by rfl⟩ : syracuseStep 1035065 = 776299) B776299
theorem B610471 : Blo 610295 610471 := bstep (se 1 (by rfl) ⟨457853, by rfl⟩ : syracuseStep 610471 = 915707) B915707
theorem B2118143 : Blo 610295 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B610971 : Blo 610295 610971 := bstep (se 1 (by rfl) ⟨458228, by rfl⟩ : syracuseStep 610971 = 916457) B916457
theorem B611023 : Blo 610295 611023 := bstep (se 1 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 611023 = 916535) B916535
theorem B611355 : Blo 610295 611355 := bstep (se 1 (by rfl) ⟨458516, by rfl⟩ : syracuseStep 611355 = 917033) B917033
theorem B611583 : Blo 610295 611583 := bstep (se 1 (by rfl) ⟨458687, by rfl⟩ : syracuseStep 611583 = 917375) B917375
theorem B612199 : Blo 610295 612199 := bstep (se 1 (by rfl) ⟨459149, by rfl⟩ : syracuseStep 612199 = 918299) B918299
theorem B225957923 : Blo 610295 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B35772509 : Blo 610295 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B612799 : Blo 610295 612799 := bstep (se 1 (by rfl) ⟨459599, by rfl⟩ : syracuseStep 612799 = 919199) B919199
theorem B613019 : Blo 610295 613019 := bstep (se 1 (by rfl) ⟨459764, by rfl⟩ : syracuseStep 613019 = 919529) B919529
theorem B34003921 : Blo 610295 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B9395453 : Blo 610295 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B613919 : Blo 610295 613919 := bstep (se 1 (by rfl) ⟨460439, by rfl⟩ : syracuseStep 613919 = 920879) B920879
theorem B613935 : Blo 610295 613935 := bstep (se 1 (by rfl) ⟨460451, by rfl⟩ : syracuseStep 613935 = 920903) B920903
theorem B614139 : Blo 610295 614139 := bstep (se 1 (by rfl) ⟨460604, by rfl⟩ : syracuseStep 614139 = 921209) B921209
theorem B3924071 : Blo 610295 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B4645673 : Blo 610295 4645673 := bstep (se 2 (by rfl) ⟨1742127, by rfl⟩ : syracuseStep 4645673 = 3484255) B3484255
theorem B10480103 : Blo 610295 10480103 := bstep (se 1 (by rfl) ⟨7860077, by rfl⟩ : syracuseStep 10480103 = 15720155) B15720155
theorem B977897 : Blo 610295 977897 := bstep (se 2 (by rfl) ⟨366711, by rfl⟩ : syracuseStep 977897 = 733423) B733423
theorem B1961279 : Blo 610295 1961279 := bstep (se 1 (by rfl) ⟨1470959, by rfl⟩ : syracuseStep 1961279 = 2941919) B2941919
theorem B1863119 : Blo 610295 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B1994665 : Blo 610295 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B3109103 : Blo 610295 3109103 := bstep (se 1 (by rfl) ⟨2331827, by rfl⟩ : syracuseStep 3109103 = 4663655) B4663655
theorem B1864019 : Blo 610295 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B2617771 : Blo 610295 2617771 := bstep (se 1 (by rfl) ⟨1963328, by rfl⟩ : syracuseStep 2617771 = 3926657) B3926657
theorem B3437161 : Blo 610295 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B2323187 : Blo 610295 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B6977987 : Blo 610295 6977987 := bstep (se 1 (by rfl) ⟨5233490, by rfl⟩ : syracuseStep 6977987 = 10466981) B10466981
theorem B915935 : Blo 610295 915935 := bstep (se 1 (by rfl) ⟨686951, by rfl⟩ : syracuseStep 915935 = 1373903) B1373903
theorem B2488927 : Blo 610295 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B248117903 : Blo 610295 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B916199 : Blo 610295 916199 := bstep (se 1 (by rfl) ⟨687149, by rfl⟩ : syracuseStep 916199 = 1374299) B1374299
theorem B2063339 : Blo 610295 2063339 := bstep (se 1 (by rfl) ⟨1547504, by rfl⟩ : syracuseStep 2063339 = 3095009) B3095009
theorem B916463 : Blo 610295 916463 := bstep (se 1 (by rfl) ⟨687347, by rfl⟩ : syracuseStep 916463 = 1374695) B1374695
theorem B2620471 : Blo 610295 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B916583 : Blo 610295 916583 := bstep (se 1 (by rfl) ⟨687437, by rfl⟩ : syracuseStep 916583 = 1374875) B1374875
theorem B2325631 : Blo 610295 2325631 := bstep (se 1 (by rfl) ⟨1744223, by rfl⟩ : syracuseStep 2325631 = 3488447) B3488447
theorem B917231 : Blo 610295 917231 := bstep (se 1 (by rfl) ⟨687923, by rfl⟩ : syracuseStep 917231 = 1375847) B1375847
theorem B1376297 : Blo 610295 1376297 := bstep (se 2 (by rfl) ⟨516111, by rfl⟩ : syracuseStep 1376297 = 1032223) B1032223
theorem B3178543 : Blo 610295 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B3145823 : Blo 610295 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B918107 : Blo 610295 918107 := bstep (se 1 (by rfl) ⟨688580, by rfl⟩ : syracuseStep 918107 = 1377161) B1377161
theorem B689179 : Blo 610295 689179 := bstep (se 1 (by rfl) ⟨516884, by rfl⟩ : syracuseStep 689179 = 1033769) B1033769
theorem B2328047 : Blo 610295 2328047 := bstep (se 1 (by rfl) ⟨1746035, by rfl⟩ : syracuseStep 2328047 = 3492071) B3492071
theorem B690043 : Blo 610295 690043 := bstep (se 1 (by rfl) ⟨517532, by rfl⟩ : syracuseStep 690043 = 1035065) B1035065
theorem B920255 : Blo 610295 920255 := bstep (se 1 (by rfl) ⟨690191, by rfl⟩ : syracuseStep 920255 = 1380383) B1380383
theorem B1379051 : Blo 610295 1379051 := bstep (se 1 (by rfl) ⟨1034288, by rfl⟩ : syracuseStep 1379051 = 2068577) B2068577
theorem B4655879 : Blo 610295 4655879 := bstep (se 1 (by rfl) ⟨3491909, by rfl⟩ : syracuseStep 4655879 = 6983819) B6983819
theorem B5245793 : Blo 610295 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B1412095 : Blo 610295 1412095 := bstep (se 1 (by rfl) ⟨1059071, by rfl⟩ : syracuseStep 1412095 = 2118143) B2118143
theorem B920603 : Blo 610295 920603 := bstep (se 1 (by rfl) ⟨690452, by rfl⟩ : syracuseStep 920603 = 1380905) B1380905
theorem B150638615 : Blo 610295 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B5378399 : Blo 610295 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B2069225 : Blo 610295 2069225 := bstep (se 2 (by rfl) ⟨775959, by rfl⟩ : syracuseStep 2069225 = 1551919) B1551919
theorem B6263635 : Blo 610295 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B2200441 : Blo 610295 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B10458233 : Blo 610295 10458233 := bstep (se 2 (by rfl) ⟨3921837, by rfl⟩ : syracuseStep 10458233 = 7843675) B7843675
theorem B2659553 : Blo 610295 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B1382111 : Blo 610295 1382111 := bstep (se 1 (by rfl) ⟨1036583, by rfl⟩ : syracuseStep 1382111 = 2073167) B2073167
theorem B6986735 : Blo 610295 6986735 := bstep (se 1 (by rfl) ⟨5240051, by rfl⟩ : syracuseStep 6986735 = 10480103) B10480103
theorem B2072735 : Blo 610295 2072735 := bstep (se 1 (by rfl) ⟨1554551, by rfl⟩ : syracuseStep 2072735 = 3109103) B3109103
theorem B1548791 : Blo 610295 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B3318569 : Blo 610295 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B5874761 : Blo 610295 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B5023741 : Blo 610295 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B1748735 : Blo 610295 1748735 := bstep (se 1 (by rfl) ⟨1311551, by rfl⟩ : syracuseStep 1748735 = 2623103) B2623103
theorem B3486239 : Blo 610295 3486239 := bstep (se 1 (by rfl) ⟨2614679, by rfl⟩ : syracuseStep 3486239 = 5229359) B5229359
theorem B18331525 : Blo 610295 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B1030367 : Blo 610295 1030367 := bstep (se 1 (by rfl) ⟨772775, by rfl⟩ : syracuseStep 1030367 = 1545551) B1545551
theorem B6601459 : Blo 610295 6601459 := bstep (se 1 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 6601459 = 9902189) B9902189
theorem B3097115 : Blo 610295 3097115 := bstep (se 1 (by rfl) ⟨2322836, by rfl⟩ : syracuseStep 3097115 = 4645673) B4645673
theorem B3490361 : Blo 610295 3490361 := bstep (se 2 (by rfl) ⟨1308885, by rfl⟩ : syracuseStep 3490361 = 2617771) B2617771
theorem B17942269 : Blo 610295 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B1035355 : Blo 610295 1035355 := bstep (se 1 (by rfl) ⟨776516, by rfl⟩ : syracuseStep 1035355 = 1553033) B1553033
theorem B4968317 : Blo 610295 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B45338561 : Blo 610295 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B3493961 : Blo 610295 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B3100841 : Blo 610295 3100841 := bstep (se 2 (by rfl) ⟨1162815, by rfl⟩ : syracuseStep 3100841 = 2325631) B2325631
theorem B610623 : Blo 610295 610623 := bstep (se 1 (by rfl) ⟨457967, by rfl⟩ : syracuseStep 610623 = 915935) B915935
theorem B610799 : Blo 610295 610799 := bstep (se 1 (by rfl) ⟨458099, by rfl⟩ : syracuseStep 610799 = 916199) B916199
theorem B610975 : Blo 610295 610975 := bstep (se 1 (by rfl) ⟨458231, by rfl⟩ : syracuseStep 610975 = 916463) B916463
theorem B4182763 : Blo 610295 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B611055 : Blo 610295 611055 := bstep (se 1 (by rfl) ⟨458291, by rfl⟩ : syracuseStep 611055 = 916583) B916583
theorem B611487 : Blo 610295 611487 := bstep (se 1 (by rfl) ⟨458615, by rfl⟩ : syracuseStep 611487 = 917231) B917231
theorem B611887 : Blo 610295 611887 := bstep (se 1 (by rfl) ⟨458915, by rfl⟩ : syracuseStep 611887 = 917831) B917831
theorem B7460747 : Blo 610295 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B612287 : Blo 610295 612287 := bstep (se 1 (by rfl) ⟨459215, by rfl⟩ : syracuseStep 612287 = 918431) B918431
theorem B612559 : Blo 610295 612559 := bstep (se 1 (by rfl) ⟨459419, by rfl⟩ : syracuseStep 612559 = 918839) B918839
theorem B4970717 : Blo 610295 4970717 := bstep (se 3 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 4970717 = 1864019) B1864019
theorem B612591 : Blo 610295 612591 := bstep (se 1 (by rfl) ⟨459443, by rfl⟩ : syracuseStep 612591 = 918887) B918887
theorem B612831 : Blo 610295 612831 := bstep (se 1 (by rfl) ⟨459623, by rfl⟩ : syracuseStep 612831 = 919247) B919247
theorem B613679 : Blo 610295 613679 := bstep (se 1 (by rfl) ⟨460259, by rfl⟩ : syracuseStep 613679 = 920519) B920519
theorem B6970697 : Blo 610295 6970697 := bstep (se 2 (by rfl) ⟨2614011, by rfl⟩ : syracuseStep 6970697 = 5228023) B5228023
theorem B614235 : Blo 610295 614235 := bstep (se 1 (by rfl) ⟨460676, by rfl⟩ : syracuseStep 614235 = 921353) B921353
theorem B4252097 : Blo 610295 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B2318827 : Blo 610295 2318827 := bstep (se 1 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 2318827 = 3478241) B3478241
theorem B1860175 : Blo 610295 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B4481831 : Blo 610295 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B23848339 : Blo 610295 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B2616047 : Blo 610295 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B3107807 : Blo 610295 3107807 := bstep (se 1 (by rfl) ⟨2330855, by rfl⟩ : syracuseStep 3107807 = 4661711) B4661711
theorem B28340063 : Blo 610295 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B2322715 : Blo 610295 2322715 := bstep (se 1 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 2322715 = 3484073) B3484073
theorem B651931 : Blo 610295 651931 := bstep (se 1 (by rfl) ⟨488948, by rfl⟩ : syracuseStep 651931 = 977897) B977897
theorem B1307519 : Blo 610295 1307519 := bstep (se 1 (by rfl) ⟨980639, by rfl⟩ : syracuseStep 1307519 = 1961279) B1961279
theorem B1373345 : Blo 610295 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B2062151 : Blo 610295 2062151 := bstep (se 1 (by rfl) ⟨1546613, by rfl⟩ : syracuseStep 2062151 = 3093227) B3093227
theorem B1375073 : Blo 610295 1375073 := bstep (se 2 (by rfl) ⟨515652, by rfl⟩ : syracuseStep 1375073 = 1031305) B1031305
theorem B4651991 : Blo 610295 4651991 := bstep (se 1 (by rfl) ⟨3488993, by rfl⟩ : syracuseStep 4651991 = 6977987) B6977987
theorem B165411935 : Blo 610295 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B687271 : Blo 610295 687271 := bstep (se 1 (by rfl) ⟨515453, by rfl⟩ : syracuseStep 687271 = 1030907) B1030907
theorem B1375559 : Blo 610295 1375559 := bstep (se 1 (by rfl) ⟨1031669, by rfl⟩ : syracuseStep 1375559 = 2063339) B2063339
theorem B687487 : Blo 610295 687487 := bstep (se 1 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 687487 = 1031231) B1031231
theorem B4652477 : Blo 610295 4652477 := bstep (se 3 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 4652477 = 1744679) B1744679
theorem B917531 : Blo 610295 917531 := bstep (se 1 (by rfl) ⟨688148, by rfl⟩ : syracuseStep 917531 = 1376297) B1376297
theorem B2097215 : Blo 610295 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B2064743 : Blo 610295 2064743 := bstep (se 1 (by rfl) ⟨1548557, by rfl⟩ : syracuseStep 2064743 = 3097115) B3097115
theorem B2326907 : Blo 610295 2326907 := bstep (se 1 (by rfl) ⟨1745180, by rfl⟩ : syracuseStep 2326907 = 3490361) B3490361
theorem B918905 : Blo 610295 918905 := bstep (se 2 (by rfl) ⟨344589, by rfl⟩ : syracuseStep 918905 = 689179) B689179
theorem B919367 : Blo 610295 919367 := bstep (se 1 (by rfl) ⟨689525, by rfl⟩ : syracuseStep 919367 = 1379051) B1379051
theorem B23923025 : Blo 610295 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B920057 : Blo 610295 920057 := bstep (se 2 (by rfl) ⟨345021, by rfl⟩ : syracuseStep 920057 = 690043) B690043
theorem B2329307 : Blo 610295 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B2067227 : Blo 610295 2067227 := bstep (se 1 (by rfl) ⟨1550420, by rfl⟩ : syracuseStep 2067227 = 3100841) B3100841
theorem B1379483 : Blo 610295 1379483 := bstep (se 1 (by rfl) ⟨1034612, by rfl⟩ : syracuseStep 1379483 = 2069225) B2069225
theorem B3476965 : Blo 610295 3476965 := bstep (se 4 (by rfl) ⟨325965, by rfl⟩ : syracuseStep 3476965 = 651931) B651931
theorem B1773035 : Blo 610295 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B921407 : Blo 610295 921407 := bstep (se 1 (by rfl) ⟨691055, by rfl⟩ : syracuseStep 921407 = 1382111) B1382111
theorem B1380473 : Blo 610295 1380473 := bstep (se 2 (by rfl) ⟨517677, by rfl⟩ : syracuseStep 1380473 = 1035355) B1035355
theorem B3313811 : Blo 610295 3313811 := bstep (se 1 (by rfl) ⟨2485358, by rfl⟩ : syracuseStep 3313811 = 4970717) B4970717
theorem B4657823 : Blo 610295 4657823 := bstep (se 1 (by rfl) ⟨3493367, by rfl⟩ : syracuseStep 4657823 = 6986735) B6986735
theorem B1381823 : Blo 610295 1381823 := bstep (se 1 (by rfl) ⟨1036367, by rfl⟩ : syracuseStep 1381823 = 2072735) B2072735
theorem B2987887 : Blo 610295 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B5577017 : Blo 610295 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1744031 : Blo 610295 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B2071871 : Blo 610295 2071871 := bstep (se 1 (by rfl) ⟨1553903, by rfl⟩ : syracuseStep 2071871 = 3107807) B3107807
theorem B110274623 : Blo 610295 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B13248845 : Blo 610295 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B4238057 : Blo 610295 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B3091769 : Blo 610295 3091769 := bstep (se 2 (by rfl) ⟨1159413, by rfl⟩ : syracuseStep 3091769 = 2318827) B2318827
theorem B1552031 : Blo 610295 1552031 := bstep (se 1 (by rfl) ⟨1164023, by rfl⟩ : syracuseStep 1552031 = 2328047) B2328047
theorem B31797785 : Blo 610295 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B30225707 : Blo 610295 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B6698321 : Blo 610295 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B3585599 : Blo 610295 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B1882793 : Blo 610295 1882793 := bstep (se 2 (by rfl) ⟨706047, by rfl⟩ : syracuseStep 1882793 = 1412095) B1412095
theorem B2834731 : Blo 610295 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B1032527 : Blo 610295 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B3096953 : Blo 610295 3096953 := bstep (se 2 (by rfl) ⟨1161357, by rfl⟩ : syracuseStep 3096953 = 2322715) B2322715
theorem B2212379 : Blo 610295 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B3916507 : Blo 610295 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B2933921 : Blo 610295 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B1165823 : Blo 610295 1165823 := bstep (se 1 (by rfl) ⟨874367, by rfl⟩ : syracuseStep 1165823 = 1748735) B1748735
theorem B18893375 : Blo 610295 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B871679 : Blo 610295 871679 := bstep (se 1 (by rfl) ⟨653759, by rfl⟩ : syracuseStep 871679 = 1307519) B1307519
theorem B8801945 : Blo 610295 8801945 := bstep (se 2 (by rfl) ⟨3300729, by rfl⟩ : syracuseStep 8801945 = 6601459) B6601459
theorem B3101327 : Blo 610295 3101327 := bstep (se 1 (by rfl) ⟨2325995, by rfl⟩ : syracuseStep 3101327 = 4651991) B4651991
theorem B3101651 : Blo 610295 3101651 := bstep (se 1 (by rfl) ⟨2326238, by rfl⟩ : syracuseStep 3101651 = 4652477) B4652477
theorem B612071 : Blo 610295 612071 := bstep (se 1 (by rfl) ⟨459053, by rfl⟩ : syracuseStep 612071 = 918107) B918107
theorem B2480233 : Blo 610295 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B613503 : Blo 610295 613503 := bstep (se 1 (by rfl) ⟨460127, by rfl⟩ : syracuseStep 613503 = 920255) B920255
theorem B3103919 : Blo 610295 3103919 := bstep (se 1 (by rfl) ⟨2327939, by rfl⟩ : syracuseStep 3103919 = 4655879) B4655879
theorem B3497195 : Blo 610295 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B613735 : Blo 610295 613735 := bstep (se 1 (by rfl) ⟨460301, by rfl⟩ : syracuseStep 613735 = 920603) B920603
theorem B100425743 : Blo 610295 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B6972155 : Blo 610295 6972155 := bstep (se 1 (by rfl) ⟨5229116, by rfl⟩ : syracuseStep 6972155 = 10458233) B10458233
theorem B4973831 : Blo 610295 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B4647131 : Blo 610295 4647131 := bstep (se 1 (by rfl) ⟨3485348, by rfl⟩ : syracuseStep 4647131 = 6970697) B6970697
theorem B8351513 : Blo 610295 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B24442033 : Blo 610295 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B2324159 : Blo 610295 2324159 := bstep (se 1 (by rfl) ⟨1743119, by rfl⟩ : syracuseStep 2324159 = 3486239) B3486239
theorem B915563 : Blo 610295 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B1374767 : Blo 610295 1374767 := bstep (se 1 (by rfl) ⟨1031075, by rfl⟩ : syracuseStep 1374767 = 2062151) B2062151
theorem B686911 : Blo 610295 686911 := bstep (se 1 (by rfl) ⟨515183, by rfl⟩ : syracuseStep 686911 = 1030367) B1030367
theorem B916361 : Blo 610295 916361 := bstep (se 2 (by rfl) ⟨343635, by rfl⟩ : syracuseStep 916361 = 687271) B687271
theorem B916649 : Blo 610295 916649 := bstep (se 2 (by rfl) ⟨343743, by rfl⟩ : syracuseStep 916649 = 687487) B687487
theorem B916715 : Blo 610295 916715 := bstep (se 1 (by rfl) ⟨687536, by rfl⟩ : syracuseStep 916715 = 1375073) B1375073
theorem B917039 : Blo 610295 917039 := bstep (se 1 (by rfl) ⟨687779, by rfl⟩ : syracuseStep 917039 = 1375559) B1375559
theorem B688351 : Blo 610295 688351 := bstep (se 1 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 688351 = 1032527) B1032527
theorem B1376495 : Blo 610295 1376495 := bstep (se 1 (by rfl) ⟨1032371, by rfl⟩ : syracuseStep 1376495 = 2064743) B2064743
theorem B2064635 : Blo 610295 2064635 := bstep (se 1 (by rfl) ⟨1548476, by rfl⟩ : syracuseStep 2064635 = 3096953) B3096953
theorem B1474919 : Blo 610295 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B1378151 : Blo 610295 1378151 := bstep (se 1 (by rfl) ⟨1033613, by rfl⟩ : syracuseStep 1378151 = 2067227) B2067227
theorem B919655 : Blo 610295 919655 := bstep (se 1 (by rfl) ⟨689741, by rfl⟩ : syracuseStep 919655 = 1379483) B1379483
theorem B1182023 : Blo 610295 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B5867963 : Blo 610295 5867963 := bstep (se 1 (by rfl) ⟨4400972, by rfl⟩ : syracuseStep 5867963 = 8801945) B8801945
theorem B920315 : Blo 610295 920315 := bstep (se 1 (by rfl) ⟨690236, by rfl⟩ : syracuseStep 920315 = 1380473) B1380473
theorem B2067551 : Blo 610295 2067551 := bstep (se 1 (by rfl) ⟨1550663, by rfl⟩ : syracuseStep 2067551 = 3101327) B3101327
theorem B2067767 : Blo 610295 2067767 := bstep (se 1 (by rfl) ⟨1550825, by rfl⟩ : syracuseStep 2067767 = 3101651) B3101651
theorem B921215 : Blo 610295 921215 := bstep (se 1 (by rfl) ⟨690911, by rfl⟩ : syracuseStep 921215 = 1381823) B1381823
theorem B2069279 : Blo 610295 2069279 := bstep (se 1 (by rfl) ⟨1551959, by rfl⟩ : syracuseStep 2069279 = 3103919) B3103919
theorem B2331463 : Blo 610295 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B1381247 : Blo 610295 1381247 := bstep (se 1 (by rfl) ⟨1035935, by rfl⟩ : syracuseStep 1381247 = 2071871) B2071871
theorem B66950495 : Blo 610295 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B3315887 : Blo 610295 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B2825371 : Blo 610295 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B4465547 : Blo 610295 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B1549439 : Blo 610295 1549439 := bstep (se 1 (by rfl) ⟨1162079, by rfl⟩ : syracuseStep 1549439 = 2324159) B2324159
theorem B1255195 : Blo 610295 1255195 := bstep (se 1 (by rfl) ⟨941396, by rfl⟩ : syracuseStep 1255195 = 1882793) B1882793
theorem B1551271 : Blo 610295 1551271 := bstep (se 1 (by rfl) ⟨1163453, by rfl⟩ : syracuseStep 1551271 = 2326907) B2326907
theorem B3779641 : Blo 610295 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B5222009 : Blo 610295 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B12595583 : Blo 610295 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B1552871 : Blo 610295 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B2209207 : Blo 610295 2209207 := bstep (se 1 (by rfl) ⟨1656905, by rfl⟩ : syracuseStep 2209207 = 3313811) B3313811
theorem B4635953 : Blo 610295 4635953 := bstep (se 2 (by rfl) ⟨1738482, by rfl⟩ : syracuseStep 4635953 = 3476965) B3476965
theorem B1162687 : Blo 610295 1162687 := bstep (se 1 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 1162687 = 1744031) B1744031
theorem B73516415 : Blo 610295 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B3098087 : Blo 610295 3098087 := bstep (se 1 (by rfl) ⟨2323565, by rfl⟩ : syracuseStep 3098087 = 4647131) B4647131
theorem B8832563 : Blo 610295 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B32589377 : Blo 610295 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B1034687 : Blo 610295 1034687 := bstep (se 1 (by rfl) ⟨776015, by rfl⟩ : syracuseStep 1034687 = 1552031) B1552031
theorem B3983849 : Blo 610295 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B610375 : Blo 610295 610375 := bstep (se 1 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 610375 = 915563) B915563
theorem B610907 : Blo 610295 610907 := bstep (se 1 (by rfl) ⟨458180, by rfl⟩ : syracuseStep 610907 = 916361) B916361
theorem B611099 : Blo 610295 611099 := bstep (se 1 (by rfl) ⟨458324, by rfl⟩ : syracuseStep 611099 = 916649) B916649
theorem B611143 : Blo 610295 611143 := bstep (se 1 (by rfl) ⟨458357, by rfl⟩ : syracuseStep 611143 = 916715) B916715
theorem B611359 : Blo 610295 611359 := bstep (se 1 (by rfl) ⟨458519, by rfl⟩ : syracuseStep 611359 = 917039) B917039
theorem B611687 : Blo 610295 611687 := bstep (se 1 (by rfl) ⟨458765, by rfl⟩ : syracuseStep 611687 = 917531) B917531
theorem B1398143 : Blo 610295 1398143 := bstep (se 1 (by rfl) ⟨1048607, by rfl⟩ : syracuseStep 1398143 = 2097215) B2097215
theorem B612603 : Blo 610295 612603 := bstep (se 1 (by rfl) ⟨459452, by rfl⟩ : syracuseStep 612603 = 918905) B918905
theorem B612911 : Blo 610295 612911 := bstep (se 1 (by rfl) ⟨459683, by rfl⟩ : syracuseStep 612911 = 919367) B919367
theorem B15948683 : Blo 610295 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B613371 : Blo 610295 613371 := bstep (se 1 (by rfl) ⟨460028, by rfl⟩ : syracuseStep 613371 = 920057) B920057
theorem B777215 : Blo 610295 777215 := bstep (se 1 (by rfl) ⟨582911, by rfl⟩ : syracuseStep 777215 = 1165823) B1165823
theorem B614271 : Blo 610295 614271 := bstep (se 1 (by rfl) ⟨460703, by rfl⟩ : syracuseStep 614271 = 921407) B921407
theorem B7823789 : Blo 610295 7823789 := bstep (se 3 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 7823789 = 2933921) B2933921
theorem B3105215 : Blo 610295 3105215 := bstep (se 1 (by rfl) ⟨2328911, by rfl⟩ : syracuseStep 3105215 = 4657823) B4657823
theorem B4648103 : Blo 610295 4648103 := bstep (se 1 (by rfl) ⟨3486077, by rfl⟩ : syracuseStep 4648103 = 6972155) B6972155
theorem B14872045 : Blo 610295 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B2061179 : Blo 610295 2061179 := bstep (se 1 (by rfl) ⟨1545884, by rfl⟩ : syracuseStep 2061179 = 3091769) B3091769
theorem B5567675 : Blo 610295 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B3306977 : Blo 610295 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B21198523 : Blo 610295 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B2324477 : Blo 610295 2324477 := bstep (se 3 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 2324477 = 871679) B871679
theorem B20150471 : Blo 610295 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B2390399 : Blo 610295 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B915881 : Blo 610295 915881 := bstep (se 2 (by rfl) ⟨343455, by rfl⟩ : syracuseStep 915881 = 686911) B686911
theorem B916511 : Blo 610295 916511 := bstep (se 1 (by rfl) ⟨687383, by rfl⟩ : syracuseStep 916511 = 1374767) B1374767
theorem B917663 : Blo 610295 917663 := bstep (se 1 (by rfl) ⟨688247, by rfl⟩ : syracuseStep 917663 = 1376495) B1376495
theorem B1376423 : Blo 610295 1376423 := bstep (se 1 (by rfl) ⟨1032317, by rfl⟩ : syracuseStep 1376423 = 2064635) B2064635
theorem B983279 : Blo 610295 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B917801 : Blo 610295 917801 := bstep (se 2 (by rfl) ⟨344175, by rfl⟩ : syracuseStep 917801 = 688351) B688351
theorem B2065391 : Blo 610295 2065391 := bstep (se 1 (by rfl) ⟨1549043, by rfl⟩ : syracuseStep 2065391 = 3098087) B3098087
theorem B21726251 : Blo 610295 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B918767 : Blo 610295 918767 := bstep (se 1 (by rfl) ⟨689075, by rfl⟩ : syracuseStep 918767 = 1378151) B1378151
theorem B788015 : Blo 610295 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B689791 : Blo 610295 689791 := bstep (se 1 (by rfl) ⟨517343, by rfl⟩ : syracuseStep 689791 = 1034687) B1034687
theorem B2655899 : Blo 610295 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1378367 : Blo 610295 1378367 := bstep (se 1 (by rfl) ⟨1033775, by rfl⟩ : syracuseStep 1378367 = 2067551) B2067551
theorem B1378511 : Blo 610295 1378511 := bstep (se 1 (by rfl) ⟨1033883, by rfl⟩ : syracuseStep 1378511 = 2067767) B2067767
theorem B14847133 : Blo 610295 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B1379519 : Blo 610295 1379519 := bstep (se 1 (by rfl) ⟨1034639, by rfl⟩ : syracuseStep 1379519 = 2069279) B2069279
theorem B920831 : Blo 610295 920831 := bstep (se 1 (by rfl) ⟨690623, by rfl⟩ : syracuseStep 920831 = 1381247) B1381247
theorem B44633663 : Blo 610295 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B2068361 : Blo 610295 2068361 := bstep (se 2 (by rfl) ⟨775635, by rfl⟩ : syracuseStep 2068361 = 1551271) B1551271
theorem B19829393 : Blo 610295 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B5215859 : Blo 610295 5215859 := bstep (se 1 (by rfl) ⟨3911894, by rfl⟩ : syracuseStep 5215859 = 7823789) B7823789
theorem B2070143 : Blo 610295 2070143 := bstep (se 1 (by rfl) ⟨1552607, by rfl⟩ : syracuseStep 2070143 = 3105215) B3105215
theorem B20158085 : Blo 610295 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B3481339 : Blo 610295 3481339 := bstep (se 1 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 3481339 = 5222009) B5222009
theorem B2072573 : Blo 610295 2072573 := bstep (se 3 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 2072573 = 777215) B777215
theorem B8397055 : Blo 610295 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B2204651 : Blo 610295 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B1549651 : Blo 610295 1549651 := bstep (se 1 (by rfl) ⟨1162238, by rfl⟩ : syracuseStep 1549651 = 2324477) B2324477
theorem B6694373 : Blo 610295 6694373 := bstep (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) B1255195
theorem B1550249 : Blo 610295 1550249 := bstep (se 2 (by rfl) ⟨581343, by rfl⟩ : syracuseStep 1550249 = 1162687) B1162687
theorem B3090635 : Blo 610295 3090635 := bstep (se 1 (by rfl) ⟨2317976, by rfl⟩ : syracuseStep 3090635 = 4635953) B4635953
theorem B3911975 : Blo 610295 3911975 := bstep (se 1 (by rfl) ⟨2933981, by rfl⟩ : syracuseStep 3911975 = 5867963) B5867963
theorem B932095 : Blo 610295 932095 := bstep (se 1 (by rfl) ⟨699071, by rfl⟩ : syracuseStep 932095 = 1398143) B1398143
theorem B2210591 : Blo 610295 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B10632455 : Blo 610295 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B1032959 : Blo 610295 1032959 := bstep (se 1 (by rfl) ⟨774719, by rfl⟩ : syracuseStep 1032959 = 1549439) B1549439
theorem B3098735 : Blo 610295 3098735 := bstep (se 1 (by rfl) ⟨2324051, by rfl⟩ : syracuseStep 3098735 = 4648103) B4648103
theorem B28264697 : Blo 610295 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B1035247 : Blo 610295 1035247 := bstep (se 1 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 1035247 = 1552871) B1552871
theorem B1593599 : Blo 610295 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B610587 : Blo 610295 610587 := bstep (se 1 (by rfl) ⟨457940, by rfl⟩ : syracuseStep 610587 = 915881) B915881
theorem B611007 : Blo 610295 611007 := bstep (se 1 (by rfl) ⟨458255, by rfl⟩ : syracuseStep 611007 = 916511) B916511
theorem B5888375 : Blo 610295 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B613103 : Blo 610295 613103 := bstep (se 1 (by rfl) ⟨459827, by rfl⟩ : syracuseStep 613103 = 919655) B919655
theorem B613543 : Blo 610295 613543 := bstep (se 1 (by rfl) ⟨460157, by rfl⟩ : syracuseStep 613543 = 920315) B920315
theorem B614143 : Blo 610295 614143 := bstep (se 1 (by rfl) ⟨460607, by rfl⟩ : syracuseStep 614143 = 921215) B921215
theorem B196043773 : Blo 610295 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B2977031 : Blo 610295 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B15068645 : Blo 610295 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B3108617 : Blo 610295 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B2945609 : Blo 610295 2945609 := bstep (se 2 (by rfl) ⟨1104603, by rfl⟩ : syracuseStep 2945609 = 2209207) B2209207
theorem B1374119 : Blo 610295 1374119 := bstep (se 1 (by rfl) ⟨1030589, by rfl⟩ : syracuseStep 1374119 = 2061179) B2061179
theorem B13433647 : Blo 610295 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B917615 : Blo 610295 917615 := bstep (se 1 (by rfl) ⟨688211, by rfl⟩ : syracuseStep 917615 = 1376423) B1376423
theorem B688639 : Blo 610295 688639 := bstep (se 1 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 688639 = 1032959) B1032959
theorem B2622077 : Blo 610295 2622077 := bstep (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) B983279
theorem B1376927 : Blo 610295 1376927 := bstep (se 1 (by rfl) ⟨1032695, by rfl⟩ : syracuseStep 1376927 = 2065391) B2065391
theorem B14484167 : Blo 610295 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B1770599 : Blo 610295 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B261391697 : Blo 610295 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B918911 : Blo 610295 918911 := bstep (se 1 (by rfl) ⟨689183, by rfl⟩ : syracuseStep 918911 = 1378367) B1378367
theorem B2065823 : Blo 610295 2065823 := bstep (se 1 (by rfl) ⟨1549367, by rfl⟩ : syracuseStep 2065823 = 3098735) B3098735
theorem B919007 : Blo 610295 919007 := bstep (se 1 (by rfl) ⟨689255, by rfl⟩ : syracuseStep 919007 = 1378511) B1378511
theorem B18843131 : Blo 610295 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B2066201 : Blo 610295 2066201 := bstep (se 2 (by rfl) ⟨774825, by rfl⟩ : syracuseStep 2066201 = 1549651) B1549651
theorem B919679 : Blo 610295 919679 := bstep (se 1 (by rfl) ⟨689759, by rfl⟩ : syracuseStep 919679 = 1379519) B1379519
theorem B919721 : Blo 610295 919721 := bstep (se 2 (by rfl) ⟨344895, by rfl⟩ : syracuseStep 919721 = 689791) B689791
theorem B29755775 : Blo 610295 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B1378907 : Blo 610295 1378907 := bstep (se 1 (by rfl) ⟨1034180, by rfl⟩ : syracuseStep 1378907 = 2068361) B2068361
theorem B3477239 : Blo 610295 3477239 := bstep (se 1 (by rfl) ⟨2607929, by rfl⟩ : syracuseStep 3477239 = 5215859) B5215859
theorem B1380095 : Blo 610295 1380095 := bstep (se 1 (by rfl) ⟨1035071, by rfl⟩ : syracuseStep 1380095 = 2070143) B2070143
theorem B13438723 : Blo 610295 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B1380329 : Blo 610295 1380329 := bstep (se 2 (by rfl) ⟨517623, by rfl⟩ : syracuseStep 1380329 = 1035247) B1035247
theorem B2101373 : Blo 610295 2101373 := bstep (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) B788015
theorem B19796177 : Blo 610295 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B1381715 : Blo 610295 1381715 := bstep (se 1 (by rfl) ⟨1036286, by rfl⟩ : syracuseStep 1381715 = 2072573) B2072573
theorem B2072411 : Blo 610295 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B7938749 : Blo 610295 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B7088303 : Blo 610295 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B13219595 : Blo 610295 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B1033499 : Blo 610295 1033499 := bstep (se 1 (by rfl) ⟨775124, by rfl⟩ : syracuseStep 1033499 = 1550249) B1550249
theorem B10045763 : Blo 610295 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B2607983 : Blo 610295 2607983 := bstep (se 1 (by rfl) ⟨1955987, by rfl⟩ : syracuseStep 2607983 = 3911975) B3911975
theorem B17911529 : Blo 610295 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B4641785 : Blo 610295 4641785 := bstep (se 2 (by rfl) ⟨1740669, by rfl⟩ : syracuseStep 4641785 = 3481339) B3481339
theorem B611775 : Blo 610295 611775 := bstep (se 1 (by rfl) ⟨458831, by rfl⟩ : syracuseStep 611775 = 917663) B917663
theorem B611867 : Blo 610295 611867 := bstep (se 1 (by rfl) ⟨458900, by rfl⟩ : syracuseStep 611867 = 917801) B917801
theorem B11196073 : Blo 610295 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B4249597 : Blo 610295 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B612511 : Blo 610295 612511 := bstep (se 1 (by rfl) ⟨459383, by rfl⟩ : syracuseStep 612511 = 918767) B918767
theorem B613887 : Blo 610295 613887 := bstep (se 1 (by rfl) ⟨460415, by rfl⟩ : syracuseStep 613887 = 920831) B920831
theorem B17851661 : Blo 610295 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B3925583 : Blo 610295 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B1469767 : Blo 610295 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B2060423 : Blo 610295 2060423 := bstep (se 1 (by rfl) ⟨1545317, by rfl⟩ : syracuseStep 2060423 = 3090635) B3090635
theorem B1242793 : Blo 610295 1242793 := bstep (se 2 (by rfl) ⟨466047, by rfl⟩ : syracuseStep 1242793 = 932095) B932095
theorem B1963739 : Blo 610295 1963739 := bstep (se 1 (by rfl) ⟨1472804, by rfl⟩ : syracuseStep 1963739 = 2945609) B2945609
theorem B916079 : Blo 610295 916079 := bstep (se 1 (by rfl) ⟨687059, by rfl⟩ : syracuseStep 916079 = 1374119) B1374119
theorem B1473727 : Blo 610295 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B917951 : Blo 610295 917951 := bstep (se 1 (by rfl) ⟨688463, by rfl⟩ : syracuseStep 917951 = 1376927) B1376927
theorem B52789805 : Blo 610295 52789805 := bstep (se 3 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 52789805 = 19796177) B19796177
theorem B918185 : Blo 610295 918185 := bstep (se 2 (by rfl) ⟨344319, by rfl⟩ : syracuseStep 918185 = 688639) B688639
theorem B688999 : Blo 610295 688999 := bstep (se 1 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 688999 = 1033499) B1033499
theorem B174261131 : Blo 610295 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B1377215 : Blo 610295 1377215 := bstep (se 1 (by rfl) ⟨1032911, by rfl⟩ : syracuseStep 1377215 = 2065823) B2065823
theorem B1377467 : Blo 610295 1377467 := bstep (se 1 (by rfl) ⟨1033100, by rfl⟩ : syracuseStep 1377467 = 2066201) B2066201
theorem B919271 : Blo 610295 919271 := bstep (se 1 (by rfl) ⟨689453, by rfl⟩ : syracuseStep 919271 = 1378907) B1378907
theorem B1738655 : Blo 610295 1738655 := bstep (se 1 (by rfl) ⟨1303991, by rfl⟩ : syracuseStep 1738655 = 2607983) B2607983
theorem B920063 : Blo 610295 920063 := bstep (se 1 (by rfl) ⟨690047, by rfl⟩ : syracuseStep 920063 = 1380095) B1380095
theorem B920219 : Blo 610295 920219 := bstep (se 1 (by rfl) ⟨690164, by rfl⟩ : syracuseStep 920219 = 1380329) B1380329
theorem B4721597 : Blo 610295 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B921143 : Blo 610295 921143 := bstep (se 1 (by rfl) ⟨690857, by rfl⟩ : syracuseStep 921143 = 1381715) B1381715
theorem B1381607 : Blo 610295 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B11901107 : Blo 610295 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B4725535 : Blo 610295 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B6628229 : Blo 610295 6628229 := bstep (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) B1242793
theorem B1748051 : Blo 610295 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B12562087 : Blo 610295 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B6697175 : Blo 610295 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B19837183 : Blo 610295 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B11941019 : Blo 610295 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B3094523 : Blo 610295 3094523 := bstep (se 1 (by rfl) ⟨2320892, by rfl⟩ : syracuseStep 3094523 = 4641785) B4641785
theorem B5292499 : Blo 610295 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B14928097 : Blo 610295 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B610719 : Blo 610295 610719 := bstep (se 1 (by rfl) ⟨458039, by rfl⟩ : syracuseStep 610719 = 916079) B916079
theorem B611743 : Blo 610295 611743 := bstep (se 1 (by rfl) ⟨458807, by rfl⟩ : syracuseStep 611743 = 917615) B917615
theorem B9656111 : Blo 610295 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B612607 : Blo 610295 612607 := bstep (se 1 (by rfl) ⟨459455, by rfl⟩ : syracuseStep 612607 = 918911) B918911
theorem B612671 : Blo 610295 612671 := bstep (se 1 (by rfl) ⟨459503, by rfl⟩ : syracuseStep 612671 = 919007) B919007
theorem B613119 : Blo 610295 613119 := bstep (se 1 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 613119 = 919679) B919679
theorem B613147 : Blo 610295 613147 := bstep (se 1 (by rfl) ⟨459860, by rfl⟩ : syracuseStep 613147 = 919721) B919721
theorem B2318159 : Blo 610295 2318159 := bstep (se 1 (by rfl) ⟨1738619, by rfl⟩ : syracuseStep 2318159 = 3477239) B3477239
theorem B1400915 : Blo 610295 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1959689 : Blo 610295 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B17918297 : Blo 610295 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B2617055 : Blo 610295 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B5666129 : Blo 610295 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B1373615 : Blo 610295 1373615 := bstep (se 1 (by rfl) ⟨1030211, by rfl⟩ : syracuseStep 1373615 = 2060423) B2060423
theorem B1309159 : Blo 610295 1309159 := bstep (se 1 (by rfl) ⟨981869, by rfl⟩ : syracuseStep 1309159 = 1963739) B1963739
theorem B8813063 : Blo 610295 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B1964969 : Blo 610295 1964969 := bstep (se 2 (by rfl) ⟨736863, by rfl⟩ : syracuseStep 1964969 = 1473727) B1473727
theorem B3735773 : Blo 610295 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B35193203 : Blo 610295 35193203 := bstep (se 1 (by rfl) ⟨26394902, by rfl⟩ : syracuseStep 35193203 = 52789805) B52789805
theorem B17859133 : Blo 610295 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B918143 : Blo 610295 918143 := bstep (se 1 (by rfl) ⟨688607, by rfl⟩ : syracuseStep 918143 = 1377215) B1377215
theorem B918311 : Blo 610295 918311 := bstep (se 1 (by rfl) ⟨688733, by rfl⟩ : syracuseStep 918311 = 1377467) B1377467
theorem B918665 : Blo 610295 918665 := bstep (se 2 (by rfl) ⟨344499, by rfl⟩ : syracuseStep 918665 = 688999) B688999
theorem B3147731 : Blo 610295 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B921071 : Blo 610295 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B7934071 : Blo 610295 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B16749449 : Blo 610295 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B1545439 : Blo 610295 1545439 := bstep (se 1 (by rfl) ⟨1159079, by rfl⟩ : syracuseStep 1545439 = 2318159) B2318159
theorem B26449577 : Blo 610295 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B23501501 : Blo 610295 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B1744703 : Blo 610295 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B1745545 : Blo 610295 1745545 := bstep (se 2 (by rfl) ⟨654579, by rfl⟩ : syracuseStep 1745545 = 1309159) B1309159
theorem B3777419 : Blo 610295 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B6300713 : Blo 610295 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B116174087 : Blo 610295 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B7056665 : Blo 610295 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B1159103 : Blo 610295 1159103 := bstep (se 1 (by rfl) ⟨869327, by rfl⟩ : syracuseStep 1159103 = 1738655) B1738655
theorem B19904129 : Blo 610295 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B6437407 : Blo 610295 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B11945531 : Blo 610295 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B1165367 : Blo 610295 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B611967 : Blo 610295 611967 := bstep (se 1 (by rfl) ⟨458975, by rfl⟩ : syracuseStep 611967 = 917951) B917951
theorem B612123 : Blo 610295 612123 := bstep (se 1 (by rfl) ⟨459092, by rfl⟩ : syracuseStep 612123 = 918185) B918185
theorem B612847 : Blo 610295 612847 := bstep (se 1 (by rfl) ⟨459635, by rfl⟩ : syracuseStep 612847 = 919271) B919271
theorem B613375 : Blo 610295 613375 := bstep (se 1 (by rfl) ⟨460031, by rfl⟩ : syracuseStep 613375 = 920063) B920063
theorem B613479 : Blo 610295 613479 := bstep (se 1 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 613479 = 920219) B920219
theorem B614095 : Blo 610295 614095 := bstep (se 1 (by rfl) ⟨460571, by rfl⟩ : syracuseStep 614095 = 921143) B921143
theorem B4418819 : Blo 610295 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B1306459 : Blo 610295 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B7960679 : Blo 610295 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B915743 : Blo 610295 915743 := bstep (se 1 (by rfl) ⟨686807, by rfl⟩ : syracuseStep 915743 = 1373615) B1373615
theorem B2063015 : Blo 610295 2063015 := bstep (se 1 (by rfl) ⟨1547261, by rfl⟩ : syracuseStep 2063015 = 3094523) B3094523
theorem B1309979 : Blo 610295 1309979 := bstep (se 1 (by rfl) ⟨982484, by rfl⟩ : syracuseStep 1309979 = 1964969) B1964969
theorem B2490515 : Blo 610295 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B23462135 : Blo 610295 23462135 := bstep (se 1 (by rfl) ⟨17596601, by rfl⟩ : syracuseStep 23462135 = 35193203) B35193203
theorem B2327393 : Blo 610295 2327393 := bstep (se 2 (by rfl) ⟨872772, by rfl⟩ : syracuseStep 2327393 = 1745545) B1745545
theorem B7963687 : Blo 610295 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B2098487 : Blo 610295 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B17633051 : Blo 610295 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B15667667 : Blo 610295 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B10073117 : Blo 610295 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B1163135 : Blo 610295 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B77449391 : Blo 610295 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B4704443 : Blo 610295 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B772735 : Blo 610295 772735 := bstep (se 1 (by rfl) ⟨579551, by rfl⟩ : syracuseStep 772735 = 1159103) B1159103
theorem B3493277 : Blo 610295 3493277 := bstep (se 3 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 3493277 = 1309979) B1309979
theorem B610495 : Blo 610295 610495 := bstep (se 1 (by rfl) ⟨457871, by rfl⟩ : syracuseStep 610495 = 915743) B915743
theorem B6967781 : Blo 610295 6967781 := bstep (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) B1306459
theorem B612095 : Blo 610295 612095 := bstep (se 1 (by rfl) ⟨459071, by rfl⟩ : syracuseStep 612095 = 918143) B918143
theorem B612207 : Blo 610295 612207 := bstep (se 1 (by rfl) ⟨459155, by rfl⟩ : syracuseStep 612207 = 918311) B918311
theorem B23812177 : Blo 610295 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B612443 : Blo 610295 612443 := bstep (se 1 (by rfl) ⟨459332, by rfl⟩ : syracuseStep 612443 = 918665) B918665
theorem B614047 : Blo 610295 614047 := bstep (se 1 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 614047 = 921071) B921071
theorem B16801901 : Blo 610295 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B11166299 : Blo 610295 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B3107645 : Blo 610295 3107645 := bstep (se 3 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 3107645 = 1165367) B1165367
theorem B10578761 : Blo 610295 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B2060585 : Blo 610295 2060585 := bstep (se 2 (by rfl) ⟨772719, by rfl⟩ : syracuseStep 2060585 = 1545439) B1545439
theorem B2945879 : Blo 610295 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B8583209 : Blo 610295 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B13269419 : Blo 610295 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B5307119 : Blo 610295 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B1375343 : Blo 610295 1375343 := bstep (se 1 (by rfl) ⟨1031507, by rfl⟩ : syracuseStep 1375343 = 2063015) B2063015
theorem B2328851 : Blo 610295 2328851 := bstep (se 1 (by rfl) ⟨1746638, by rfl⟩ : syracuseStep 2328851 = 3493277) B3493277
theorem B42472997 : Blo 610295 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B7444199 : Blo 610295 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B2071763 : Blo 610295 2071763 := bstep (se 1 (by rfl) ⟨1553822, by rfl⟩ : syracuseStep 2071763 = 3107645) B3107645
theorem B7052507 : Blo 610295 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B15641423 : Blo 610295 15641423 := bstep (se 1 (by rfl) ⟨11731067, by rfl⟩ : syracuseStep 15641423 = 23462135) B23462135
theorem B1551595 : Blo 610295 1551595 := bstep (se 1 (by rfl) ⟨1163696, by rfl⟩ : syracuseStep 1551595 = 2327393) B2327393
theorem B1030313 : Blo 610295 1030313 := bstep (se 2 (by rfl) ⟨386367, by rfl⟩ : syracuseStep 1030313 = 772735) B772735
theorem B5722139 : Blo 610295 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B775423 : Blo 610295 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B1660343 : Blo 610295 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B51632927 : Blo 610295 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B3136295 : Blo 610295 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B11755367 : Blo 610295 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B26861645 : Blo 610295 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B10445111 : Blo 610295 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B4645187 : Blo 610295 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B5595965 : Blo 610295 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B11201267 : Blo 610295 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B31749569 : Blo 610295 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B1373723 : Blo 610295 1373723 := bstep (se 1 (by rfl) ⟨1030292, by rfl⟩ : syracuseStep 1373723 = 2060585) B2060585
theorem B1963919 : Blo 610295 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B8846279 : Blo 610295 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B3538079 : Blo 610295 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B916895 : Blo 610295 916895 := bstep (se 1 (by rfl) ⟨687671, by rfl⟩ : syracuseStep 916895 = 1375343) B1375343
theorem B71631053 : Blo 610295 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B28315331 : Blo 610295 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B2068793 : Blo 610295 2068793 := bstep (se 2 (by rfl) ⟨775797, by rfl⟩ : syracuseStep 2068793 = 1551595) B1551595
theorem B1381175 : Blo 610295 1381175 := bstep (se 1 (by rfl) ⟨1035881, by rfl⟩ : syracuseStep 1381175 = 2071763) B2071763
theorem B7836911 : Blo 610295 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B10427615 : Blo 610295 10427615 := bstep (se 1 (by rfl) ⟨7820711, by rfl⟩ : syracuseStep 10427615 = 15641423) B15641423
theorem B1552567 : Blo 610295 1552567 := bstep (se 1 (by rfl) ⟨1164425, by rfl⟩ : syracuseStep 1552567 = 2328851) B2328851
theorem B3814759 : Blo 610295 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B4962799 : Blo 610295 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B34421951 : Blo 610295 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B17710325 : Blo 610295 17710325 := bstep (se 5 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 17710325 = 1660343) B1660343
theorem B4701671 : Blo 610295 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B6963407 : Blo 610295 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B3096791 : Blo 610295 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B1033897 : Blo 610295 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B611263 : Blo 610295 611263 := bstep (se 1 (by rfl) ⟨458447, by rfl⟩ : syracuseStep 611263 = 916895) B916895
theorem B2090863 : Blo 610295 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B3730643 : Blo 610295 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B7467511 : Blo 610295 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B21166379 : Blo 610295 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B915815 : Blo 610295 915815 := bstep (se 1 (by rfl) ⟨686861, by rfl⟩ : syracuseStep 915815 = 1373723) B1373723
theorem B1309279 : Blo 610295 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B686875 : Blo 610295 686875 := bstep (se 1 (by rfl) ⟨515156, by rfl⟩ : syracuseStep 686875 = 1030313) B1030313
theorem B5897519 : Blo 610295 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B2358719 : Blo 610295 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B2064527 : Blo 610295 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B1378529 : Blo 610295 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B18876887 : Blo 610295 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B1379195 : Blo 610295 1379195 := bstep (se 1 (by rfl) ⟨1034396, by rfl⟩ : syracuseStep 1379195 = 2068793) B2068793
theorem B920783 : Blo 610295 920783 := bstep (se 1 (by rfl) ⟨690587, by rfl⟩ : syracuseStep 920783 = 1381175) B1381175
theorem B6951743 : Blo 610295 6951743 := bstep (se 1 (by rfl) ⟨5213807, by rfl⟩ : syracuseStep 6951743 = 10427615) B10427615
theorem B2070089 : Blo 610295 2070089 := bstep (se 2 (by rfl) ⟨776283, by rfl⟩ : syracuseStep 2070089 = 1552567) B1552567
theorem B1745705 : Blo 610295 1745705 := bstep (se 2 (by rfl) ⟨654639, by rfl⟩ : syracuseStep 1745705 = 1309279) B1309279
theorem B11151269 : Blo 610295 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B22947967 : Blo 610295 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B11806883 : Blo 610295 11806883 := bstep (se 1 (by rfl) ⟨8855162, by rfl⟩ : syracuseStep 11806883 = 17710325) B17710325
theorem B47754035 : Blo 610295 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B5224607 : Blo 610295 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B14110919 : Blo 610295 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B610543 : Blo 610295 610543 := bstep (se 1 (by rfl) ⟨457907, by rfl⟩ : syracuseStep 610543 = 915815) B915815
theorem B3134447 : Blo 610295 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B4642271 : Blo 610295 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B9956681 : Blo 610295 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B20345381 : Blo 610295 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B2487095 : Blo 610295 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B6617065 : Blo 610295 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B915833 : Blo 610295 915833 := bstep (se 2 (by rfl) ⟨343437, by rfl⟩ : syracuseStep 915833 = 686875) B686875
theorem B3931679 : Blo 610295 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B1572479 : Blo 610295 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B1376351 : Blo 610295 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B122389157 : Blo 610295 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B919019 : Blo 610295 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B12584591 : Blo 610295 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B919463 : Blo 610295 919463 := bstep (se 1 (by rfl) ⟨689597, by rfl⟩ : syracuseStep 919463 = 1379195) B1379195
theorem B9407279 : Blo 610295 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B1380059 : Blo 610295 1380059 := bstep (se 1 (by rfl) ⟨1035044, by rfl⟩ : syracuseStep 1380059 = 2070089) B2070089
theorem B7871255 : Blo 610295 7871255 := bstep (se 1 (by rfl) ⟨5903441, by rfl⟩ : syracuseStep 7871255 = 11806883) B11806883
theorem B8822753 : Blo 610295 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B3483071 : Blo 610295 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B4634495 : Blo 610295 4634495 := bstep (se 1 (by rfl) ⟨3475871, by rfl⟩ : syracuseStep 4634495 = 6951743) B6951743
theorem B3094847 : Blo 610295 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1163803 : Blo 610295 1163803 := bstep (se 1 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 1163803 = 1745705) B1745705
theorem B31836023 : Blo 610295 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B6637787 : Blo 610295 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B1658063 : Blo 610295 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B610555 : Blo 610295 610555 := bstep (se 1 (by rfl) ⟨457916, by rfl⟩ : syracuseStep 610555 = 915833) B915833
theorem B613855 : Blo 610295 613855 := bstep (se 1 (by rfl) ⟨460391, by rfl⟩ : syracuseStep 613855 = 920783) B920783
theorem B2089631 : Blo 610295 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B7434179 : Blo 610295 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B13563587 : Blo 610295 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B10484477 : Blo 610295 10484477 := bstep (se 3 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 10484477 = 3931679) B3931679
theorem B1048319 : Blo 610295 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B917567 : Blo 610295 917567 := bstep (se 1 (by rfl) ⟨688175, by rfl⟩ : syracuseStep 917567 = 1376351) B1376351
theorem B81592771 : Blo 610295 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B8389727 : Blo 610295 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B4425191 : Blo 610295 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B920039 : Blo 610295 920039 := bstep (se 1 (by rfl) ⟨690029, by rfl⟩ : syracuseStep 920039 = 1380059) B1380059
theorem B5247503 : Blo 610295 5247503 := bstep (se 1 (by rfl) ⟨3935627, by rfl⟩ : syracuseStep 5247503 = 7871255) B7871255
theorem B4956119 : Blo 610295 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B3089663 : Blo 610295 3089663 := bstep (se 1 (by rfl) ⟨2317247, by rfl⟩ : syracuseStep 3089663 = 4634495) B4634495
theorem B6989651 : Blo 610295 6989651 := bstep (se 1 (by rfl) ⟨5242238, by rfl⟩ : syracuseStep 6989651 = 10484477) B10484477
theorem B698879 : Blo 610295 698879 := bstep (se 1 (by rfl) ⟨524159, by rfl⟩ : syracuseStep 698879 = 1048319) B1048319
theorem B1551737 : Blo 610295 1551737 := bstep (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) B1163803
theorem B6271519 : Blo 610295 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B5881835 : Blo 610295 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B1393087 : Blo 610295 1393087 := bstep (se 1 (by rfl) ⟨1044815, by rfl⟩ : syracuseStep 1393087 = 2089631) B2089631
theorem B612679 : Blo 610295 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B21224015 : Blo 610295 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B612975 : Blo 610295 612975 := bstep (se 1 (by rfl) ⟨459731, by rfl⟩ : syracuseStep 612975 = 919463) B919463
theorem B1105375 : Blo 610295 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B2322047 : Blo 610295 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B9042391 : Blo 610295 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B2063231 : Blo 610295 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B108790361 : Blo 610295 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B2950127 : Blo 610295 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B8362025 : Blo 610295 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B4659767 : Blo 610295 4659767 := bstep (se 1 (by rfl) ⟨3494825, by rfl⟩ : syracuseStep 4659767 = 6989651) B6989651
theorem B1548031 : Blo 610295 1548031 := bstep (se 1 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 1548031 = 2322047) B2322047
theorem B1034491 : Blo 610295 1034491 := bstep (se 1 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 1034491 = 1551737) B1551737
theorem B3921223 : Blo 610295 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B611711 : Blo 610295 611711 := bstep (se 1 (by rfl) ⟨458783, by rfl⟩ : syracuseStep 611711 = 917567) B917567
theorem B1857449 : Blo 610295 1857449 := bstep (se 2 (by rfl) ⟨696543, by rfl⟩ : syracuseStep 1857449 = 1393087) B1393087
theorem B5593151 : Blo 610295 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B613359 : Blo 610295 613359 := bstep (se 1 (by rfl) ⟨460019, by rfl⟩ : syracuseStep 613359 = 920039) B920039
theorem B3498335 : Blo 610295 3498335 := bstep (se 1 (by rfl) ⟨2623751, by rfl⟩ : syracuseStep 3498335 = 5247503) B5247503
theorem B14149343 : Blo 610295 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B3304079 : Blo 610295 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B2059775 : Blo 610295 2059775 := bstep (se 1 (by rfl) ⟨1544831, by rfl⟩ : syracuseStep 2059775 = 3089663) B3089663
theorem B1863677 : Blo 610295 1863677 := bstep (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) B698879
theorem B12056521 : Blo 610295 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B1375487 : Blo 610295 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B1473833 : Blo 610295 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B1966751 : Blo 610295 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B1379321 : Blo 610295 1379321 := bstep (se 2 (by rfl) ⟨517245, by rfl⟩ : syracuseStep 1379321 = 1034491) B1034491
theorem B5574683 : Blo 610295 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B4953197 : Blo 610295 4953197 := bstep (se 3 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 4953197 = 1857449) B1857449
theorem B2332223 : Blo 610295 2332223 := bstep (se 1 (by rfl) ⟨1749167, by rfl⟩ : syracuseStep 2332223 = 3498335) B3498335
theorem B2202719 : Blo 610295 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B72526907 : Blo 610295 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B5228297 : Blo 610295 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B16075361 : Blo 610295 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B3728767 : Blo 610295 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B3106511 : Blo 610295 3106511 := bstep (se 1 (by rfl) ⟨2329883, by rfl⟩ : syracuseStep 3106511 = 4659767) B4659767
theorem B9432895 : Blo 610295 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B1373183 : Blo 610295 1373183 := bstep (se 1 (by rfl) ⟨1029887, by rfl⟩ : syracuseStep 1373183 = 2059775) B2059775
theorem B1242451 : Blo 610295 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B3930221 : Blo 610295 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B916991 : Blo 610295 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B2064041 : Blo 610295 2064041 := bstep (se 2 (by rfl) ⟨774015, by rfl⟩ : syracuseStep 2064041 = 1548031) B1548031
theorem B1311167 : Blo 610295 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B10716907 : Blo 610295 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B919547 : Blo 610295 919547 := bstep (se 1 (by rfl) ⟨689660, by rfl⟩ : syracuseStep 919547 = 1379321) B1379321
theorem B2071007 : Blo 610295 2071007 := bstep (se 1 (by rfl) ⟨1553255, by rfl⟩ : syracuseStep 2071007 = 3106511) B3106511
theorem B6626405 : Blo 610295 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B5873917 : Blo 610295 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B3485531 : Blo 610295 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B3716455 : Blo 610295 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B1554815 : Blo 610295 1554815 := bstep (se 1 (by rfl) ⟨1166111, by rfl⟩ : syracuseStep 1554815 = 2332223) B2332223
theorem B48351271 : Blo 610295 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B611327 : Blo 610295 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B4971689 : Blo 610295 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B3302131 : Blo 610295 3302131 := bstep (se 1 (by rfl) ⟨2476598, by rfl⟩ : syracuseStep 3302131 = 4953197) B4953197
theorem B12577193 : Blo 610295 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B915455 : Blo 610295 915455 := bstep (se 1 (by rfl) ⟨686591, by rfl⟩ : syracuseStep 915455 = 1373183) B1373183
theorem B2620147 : Blo 610295 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B1376027 : Blo 610295 1376027 := bstep (se 1 (by rfl) ⟨1032020, by rfl⟩ : syracuseStep 1376027 = 2064041) B2064041
theorem B7831889 : Blo 610295 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B14289209 : Blo 610295 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B1380671 : Blo 610295 1380671 := bstep (se 1 (by rfl) ⟨1035503, by rfl⟩ : syracuseStep 1380671 = 2071007) B2071007
theorem B3314459 : Blo 610295 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B4955273 : Blo 610295 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B17670413 : Blo 610295 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B4402841 : Blo 610295 4402841 := bstep (se 2 (by rfl) ⟨1651065, by rfl⟩ : syracuseStep 4402841 = 3302131) B3302131
theorem B64468361 : Blo 610295 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B3493529 : Blo 610295 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B610303 : Blo 610295 610303 := bstep (se 1 (by rfl) ⟨457727, by rfl⟩ : syracuseStep 610303 = 915455) B915455
theorem B1036543 : Blo 610295 1036543 := bstep (se 1 (by rfl) ⟨777407, by rfl⟩ : syracuseStep 1036543 = 1554815) B1554815
theorem B3496445 : Blo 610295 3496445 := bstep (se 3 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 3496445 = 1311167) B1311167
theorem B613031 : Blo 610295 613031 := bstep (se 1 (by rfl) ⟨459773, by rfl⟩ : syracuseStep 613031 = 919547) B919547
theorem B8384795 : Blo 610295 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B2323687 : Blo 610295 2323687 := bstep (se 1 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 2323687 = 3485531) B3485531
theorem B917351 : Blo 610295 917351 := bstep (se 1 (by rfl) ⟨688013, by rfl⟩ : syracuseStep 917351 = 1376027) B1376027
theorem B2329019 : Blo 610295 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B920447 : Blo 610295 920447 := bstep (se 1 (by rfl) ⟨690335, by rfl⟩ : syracuseStep 920447 = 1380671) B1380671
theorem B2330963 : Blo 610295 2330963 := bstep (se 1 (by rfl) ⟨1748222, by rfl⟩ : syracuseStep 2330963 = 3496445) B3496445
theorem B1382057 : Blo 610295 1382057 := bstep (se 2 (by rfl) ⟨518271, by rfl⟩ : syracuseStep 1382057 = 1036543) B1036543
theorem B11740909 : Blo 610295 11740909 := bstep (se 3 (by rfl) ⟨2201420, by rfl⟩ : syracuseStep 11740909 = 4402841) B4402841
theorem B5221259 : Blo 610295 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B11780275 : Blo 610295 11780275 := bstep (se 1 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 11780275 = 17670413) B17670413
theorem B3098249 : Blo 610295 3098249 := bstep (se 2 (by rfl) ⟨1161843, by rfl⟩ : syracuseStep 3098249 = 2323687) B2323687
theorem B5589863 : Blo 610295 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B42978907 : Blo 610295 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B611567 : Blo 610295 611567 := bstep (se 1 (by rfl) ⟨458675, by rfl⟩ : syracuseStep 611567 = 917351) B917351
theorem B9526139 : Blo 610295 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B8838557 : Blo 610295 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B3303515 : Blo 610295 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B2065499 : Blo 610295 2065499 := bstep (se 1 (by rfl) ⟨1549124, by rfl⟩ : syracuseStep 2065499 = 3098249) B3098249
theorem B921371 : Blo 610295 921371 := bstep (se 1 (by rfl) ⟨691028, by rfl⟩ : syracuseStep 921371 = 1382057) B1382057
theorem B3480839 : Blo 610295 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B229220837 : Blo 610295 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B15707033 : Blo 610295 15707033 := bstep (se 2 (by rfl) ⟨5890137, by rfl⟩ : syracuseStep 15707033 = 11780275) B11780275
theorem B1552679 : Blo 610295 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B1553975 : Blo 610295 1553975 := bstep (se 1 (by rfl) ⟨1165481, by rfl⟩ : syracuseStep 1553975 = 2330963) B2330963
theorem B3726575 : Blo 610295 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B613631 : Blo 610295 613631 := bstep (se 1 (by rfl) ⟨460223, by rfl⟩ : syracuseStep 613631 = 920447) B920447
theorem B15654545 : Blo 610295 15654545 := bstep (se 2 (by rfl) ⟨5870454, by rfl⟩ : syracuseStep 15654545 = 11740909) B11740909
theorem B6350759 : Blo 610295 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B5892371 : Blo 610295 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B8809373 : Blo 610295 8809373 := bstep (se 3 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 8809373 = 3303515) B3303515
theorem B1376999 : Blo 610295 1376999 := bstep (se 1 (by rfl) ⟨1032749, by rfl⟩ : syracuseStep 1376999 = 2065499) B2065499
theorem B5872915 : Blo 610295 5872915 := bstep (se 1 (by rfl) ⟨4404686, by rfl⟩ : syracuseStep 5872915 = 8809373) B8809373
theorem B67741429 : Blo 610295 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B10436363 : Blo 610295 10436363 := bstep (se 1 (by rfl) ⟨7827272, by rfl⟩ : syracuseStep 10436363 = 15654545) B15654545
theorem B152813891 : Blo 610295 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B10471355 : Blo 610295 10471355 := bstep (se 1 (by rfl) ⟨7853516, by rfl⟩ : syracuseStep 10471355 = 15707033) B15707033
theorem B1035119 : Blo 610295 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B1035983 : Blo 610295 1035983 := bstep (se 1 (by rfl) ⟨776987, by rfl⟩ : syracuseStep 1035983 = 1553975) B1553975
theorem B614247 : Blo 610295 614247 := bstep (se 1 (by rfl) ⟨460685, by rfl⟩ : syracuseStep 614247 = 921371) B921371
theorem B2484383 : Blo 610295 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B2320559 : Blo 610295 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B3928247 : Blo 610295 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B101875927 : Blo 610295 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B917999 : Blo 610295 917999 := bstep (se 1 (by rfl) ⟨688499, by rfl⟩ : syracuseStep 917999 = 1376999) B1376999
theorem B6980903 : Blo 610295 6980903 := bstep (se 1 (by rfl) ⟨5235677, by rfl⟩ : syracuseStep 6980903 = 10471355) B10471355
theorem B690079 : Blo 610295 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B690655 : Blo 610295 690655 := bstep (se 1 (by rfl) ⟨517991, by rfl⟩ : syracuseStep 690655 = 1035983) B1035983
theorem B6625021 : Blo 610295 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B1547039 : Blo 610295 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B6957575 : Blo 610295 6957575 := bstep (se 1 (by rfl) ⟨5218181, by rfl⟩ : syracuseStep 6957575 = 10436363) B10436363
theorem B90321905 : Blo 610295 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B2618831 : Blo 610295 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B7830553 : Blo 610295 7830553 := bstep (se 2 (by rfl) ⟨2936457, by rfl⟩ : syracuseStep 7830553 = 5872915) B5872915
theorem B4653935 : Blo 610295 4653935 := bstep (se 1 (by rfl) ⟨3490451, by rfl⟩ : syracuseStep 4653935 = 6980903) B6980903
theorem B920105 : Blo 610295 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B920873 : Blo 610295 920873 := bstep (se 2 (by rfl) ⟨345327, by rfl⟩ : syracuseStep 920873 = 690655) B690655
theorem B141333781 : Blo 610295 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B1745887 : Blo 610295 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B135834569 : Blo 610295 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B1031359 : Blo 610295 1031359 := bstep (se 1 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 1031359 = 1547039) B1547039
theorem B4638383 : Blo 610295 4638383 := bstep (se 1 (by rfl) ⟨3478787, by rfl⟩ : syracuseStep 4638383 = 6957575) B6957575
theorem B60214603 : Blo 610295 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B10440737 : Blo 610295 10440737 := bstep (se 2 (by rfl) ⟨3915276, by rfl⟩ : syracuseStep 10440737 = 7830553) B7830553
theorem B611999 : Blo 610295 611999 := bstep (se 1 (by rfl) ⟨458999, by rfl⟩ : syracuseStep 611999 = 917999) B917999
theorem B2327849 : Blo 610295 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B80286137 : Blo 610295 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B3092255 : Blo 610295 3092255 := bstep (se 1 (by rfl) ⟨2319191, by rfl⟩ : syracuseStep 3092255 = 4638383) B4638383
theorem B6960491 : Blo 610295 6960491 := bstep (se 1 (by rfl) ⟨5220368, by rfl⟩ : syracuseStep 6960491 = 10440737) B10440737
theorem B90556379 : Blo 610295 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B3102623 : Blo 610295 3102623 := bstep (se 1 (by rfl) ⟨2326967, by rfl⟩ : syracuseStep 3102623 = 4653935) B4653935
theorem B613403 : Blo 610295 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B613915 : Blo 610295 613915 := bstep (se 1 (by rfl) ⟨460436, by rfl⟩ : syracuseStep 613915 = 920873) B920873
theorem B188445041 : Blo 610295 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B1375145 : Blo 610295 1375145 := bstep (se 2 (by rfl) ⟨515679, by rfl⟩ : syracuseStep 1375145 = 1031359) B1031359
theorem B2068415 : Blo 610295 2068415 := bstep (se 1 (by rfl) ⟨1551311, by rfl⟩ : syracuseStep 2068415 = 3102623) B3102623
theorem B1551899 : Blo 610295 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B60370919 : Blo 610295 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B53524091 : Blo 610295 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B4640327 : Blo 610295 4640327 := bstep (se 1 (by rfl) ⟨3480245, by rfl⟩ : syracuseStep 4640327 = 6960491) B6960491
theorem B2061503 : Blo 610295 2061503 := bstep (se 1 (by rfl) ⟨1546127, by rfl⟩ : syracuseStep 2061503 = 3092255) B3092255
theorem B125630027 : Blo 610295 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B916763 : Blo 610295 916763 := bstep (se 1 (by rfl) ⟨687572, by rfl⟩ : syracuseStep 916763 = 1375145) B1375145
theorem B1378943 : Blo 610295 1378943 := bstep (se 1 (by rfl) ⟨1034207, by rfl⟩ : syracuseStep 1378943 = 2068415) B2068415
theorem B40247279 : Blo 610295 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B3093551 : Blo 610295 3093551 := bstep (se 1 (by rfl) ⟨2320163, by rfl⟩ : syracuseStep 3093551 = 4640327) B4640327
theorem B1034599 : Blo 610295 1034599 := bstep (se 1 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 1034599 = 1551899) B1551899
theorem B611175 : Blo 610295 611175 := bstep (se 1 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 611175 = 916763) B916763
theorem B1374335 : Blo 610295 1374335 := bstep (se 1 (by rfl) ⟨1030751, by rfl⟩ : syracuseStep 1374335 = 2061503) B2061503
theorem B83753351 : Blo 610295 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B35682727 : Blo 610295 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B919295 : Blo 610295 919295 := bstep (se 1 (by rfl) ⟨689471, by rfl⟩ : syracuseStep 919295 = 1378943) B1378943
theorem B1379465 : Blo 610295 1379465 := bstep (se 2 (by rfl) ⟨517299, by rfl⟩ : syracuseStep 1379465 = 1034599) B1034599
theorem B26831519 : Blo 610295 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B47576969 : Blo 610295 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B2062367 : Blo 610295 2062367 := bstep (se 1 (by rfl) ⟨1546775, by rfl⟩ : syracuseStep 2062367 = 3093551) B3093551
theorem B916223 : Blo 610295 916223 := bstep (se 1 (by rfl) ⟨687167, by rfl⟩ : syracuseStep 916223 = 1374335) B1374335
theorem B55835567 : Blo 610295 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B919643 : Blo 610295 919643 := bstep (se 1 (by rfl) ⟨689732, by rfl⟩ : syracuseStep 919643 = 1379465) B1379465
theorem B610815 : Blo 610295 610815 := bstep (se 1 (by rfl) ⟨458111, by rfl⟩ : syracuseStep 610815 = 916223) B916223
theorem B612863 : Blo 610295 612863 := bstep (se 1 (by rfl) ⟨459647, by rfl⟩ : syracuseStep 612863 = 919295) B919295
theorem B17887679 : Blo 610295 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B31717979 : Blo 610295 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B1374911 : Blo 610295 1374911 := bstep (se 1 (by rfl) ⟨1031183, by rfl⟩ : syracuseStep 1374911 = 2062367) B2062367
theorem B37223711 : Blo 610295 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B21145319 : Blo 610295 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B24815807 : Blo 610295 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B613095 : Blo 610295 613095 := bstep (se 1 (by rfl) ⟨459821, by rfl⟩ : syracuseStep 613095 = 919643) B919643
theorem B11925119 : Blo 610295 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B916607 : Blo 610295 916607 := bstep (se 1 (by rfl) ⟨687455, by rfl⟩ : syracuseStep 916607 = 1374911) B1374911
theorem B14096879 : Blo 610295 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B7950079 : Blo 610295 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B611071 : Blo 610295 611071 := bstep (se 1 (by rfl) ⟨458303, by rfl⟩ : syracuseStep 611071 = 916607) B916607
theorem B16543871 : Blo 610295 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B10600105 : Blo 610295 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B11029247 : Blo 610295 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B9397919 : Blo 610295 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B6265279 : Blo 610295 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B14133473 : Blo 610295 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B7352831 : Blo 610295 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B9422315 : Blo 610295 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B4901887 : Blo 610295 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B8353705 : Blo 610295 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B6535849 : Blo 610295 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B6281543 : Blo 610295 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B11138273 : Blo 610295 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B7425515 : Blo 610295 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B4187695 : Blo 610295 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B8714465 : Blo 610295 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B4950343 : Blo 610295 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B5809643 : Blo 610295 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B5583593 : Blo 610295 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B3873095 : Blo 610295 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B6600457 : Blo 610295 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B3722395 : Blo 610295 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B4963193 : Blo 610295 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B8800609 : Blo 610295 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B2582063 : Blo 610295 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B11734145 : Blo 610295 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B1721375 : Blo 610295 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B3308795 : Blo 610295 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B1147583 : Blo 610295 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B2205863 : Blo 610295 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B7822763 : Blo 610295 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5215175 : Blo 610295 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B765055 : Blo 610295 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B1470575 : Blo 610295 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B3476783 : Blo 610295 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B4080293 : Blo 610295 4080293 := bstep (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) B765055
theorem B3921533 : Blo 610295 3921533 := bstep (se 3 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 3921533 = 1470575) B1470575
theorem B2720195 : Blo 610295 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B2317855 : Blo 610295 2317855 := bstep (se 1 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 2317855 = 3476783) B3476783
theorem B2614355 : Blo 610295 2614355 := bstep (se 1 (by rfl) ⟨1960766, by rfl⟩ : syracuseStep 2614355 = 3921533) B3921533
theorem B1742903 : Blo 610295 1742903 := bstep (se 1 (by rfl) ⟨1307177, by rfl⟩ : syracuseStep 1742903 = 2614355) B2614355
theorem B3090473 : Blo 610295 3090473 := bstep (se 2 (by rfl) ⟨1158927, by rfl⟩ : syracuseStep 3090473 = 2317855) B2317855
theorem B1813463 : Blo 610295 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B1161935 : Blo 610295 1161935 := bstep (se 1 (by rfl) ⟨871451, by rfl⟩ : syracuseStep 1161935 = 1742903) B1742903
theorem B2060315 : Blo 610295 2060315 := bstep (se 1 (by rfl) ⟨1545236, by rfl⟩ : syracuseStep 2060315 = 3090473) B3090473
theorem B1208975 : Blo 610295 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B12895733 : Blo 610295 12895733 := bstep (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) B1208975
theorem B774623 : Blo 610295 774623 := bstep (se 1 (by rfl) ⟨580967, by rfl⟩ : syracuseStep 774623 = 1161935) B1161935
theorem B1373543 : Blo 610295 1373543 := bstep (se 1 (by rfl) ⟨1030157, by rfl⟩ : syracuseStep 1373543 = 2060315) B2060315
theorem B2065661 : Blo 610295 2065661 := bstep (se 3 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 2065661 = 774623) B774623
theorem B34388621 : Blo 610295 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B915695 : Blo 610295 915695 := bstep (se 1 (by rfl) ⟨686771, by rfl⟩ : syracuseStep 915695 = 1373543) B1373543
theorem B1377107 : Blo 610295 1377107 := bstep (se 1 (by rfl) ⟨1032830, by rfl⟩ : syracuseStep 1377107 = 2065661) B2065661
theorem B610463 : Blo 610295 610463 := bstep (se 1 (by rfl) ⟨457847, by rfl⟩ : syracuseStep 610463 = 915695) B915695
theorem B22925747 : Blo 610295 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B918071 : Blo 610295 918071 := bstep (se 1 (by rfl) ⟨688553, by rfl⟩ : syracuseStep 918071 = 1377107) B1377107
theorem B15283831 : Blo 610295 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B612047 : Blo 610295 612047 := bstep (se 1 (by rfl) ⟨459035, by rfl⟩ : syracuseStep 612047 = 918071) B918071
theorem B20378441 : Blo 610295 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B13585627 : Blo 610295 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B72456677 : Blo 610295 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B48304451 : Blo 610295 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B32202967 : Blo 610295 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B42937289 : Blo 610295 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B28624859 : Blo 610295 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B19083239 : Blo 610295 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B12722159 : Blo 610295 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B8481439 : Blo 610295 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B11308585 : Blo 610295 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B15078113 : Blo 610295 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B10052075 : Blo 610295 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B6701383 : Blo 610295 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B8935177 : Blo 610295 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B11913569 : Blo 610295 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7942379 : Blo 610295 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B84718709 : Blo 610295 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B56479139 : Blo 610295 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B37652759 : Blo 610295 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B25101839 : Blo 610295 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B16734559 : Blo 610295 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B22312745 : Blo 610295 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B14875163 : Blo 610295 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B9916775 : Blo 610295 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B6611183 : Blo 610295 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B4407455 : Blo 610295 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2938303 : Blo 610295 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B3917737 : Blo 610295 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B5223649 : Blo 610295 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B6964865 : Blo 610295 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B4643243 : Blo 610295 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B3095495 : Blo 610295 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B2063663 : Blo 610295 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B1375775 : Blo 610295 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B917183 : Blo 610295 917183 := bstep (se 1 (by rfl) ⟨687887, by rfl⟩ : syracuseStep 917183 = 1375775) B1375775
theorem B611455 : Blo 610295 611455 := bstep (se 1 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 611455 = 917183) B917183

theorem C0 (j : ℕ) (h1 : 152573 ≤ j) (h2 : j ≤ 153272) : Blo 610295 (4 * j + 3) := by
  interval_cases j
  · exact B610295
  · exact B610299
  · exact B610303
  · exact B610307
  · exact B610311
  · exact B610315
  · exact B610319
  · exact B610323
  · exact B610327
  · exact B610331
  · exact B610335
  · exact B610339
  · exact B610343
  · exact B610347
  · exact B610351
  · exact B610355
  · exact B610359
  · exact B610363
  · exact B610367
  · exact B610371
  · exact B610375
  · exact B610379
  · exact B610383
  · exact B610387
  · exact B610391
  · exact B610395
  · exact B610399
  · exact B610403
  · exact B610407
  · exact B610411
  · exact B610415
  · exact B610419
  · exact B610423
  · exact B610427
  · exact B610431
  · exact B610435
  · exact B610439
  · exact B610443
  · exact B610447
  · exact B610451
  · exact B610455
  · exact B610459
  · exact B610463
  · exact B610467
  · exact B610471
  · exact B610475
  · exact B610479
  · exact B610483
  · exact B610487
  · exact B610491
  · exact B610495
  · exact B610499
  · exact B610503
  · exact B610507
  · exact B610511
  · exact B610515
  · exact B610519
  · exact B610523
  · exact B610527
  · exact B610531
  · exact B610535
  · exact B610539
  · exact B610543
  · exact B610547
  · exact B610551
  · exact B610555
  · exact B610559
  · exact B610563
  · exact B610567
  · exact B610571
  · exact B610575
  · exact B610579
  · exact B610583
  · exact B610587
  · exact B610591
  · exact B610595
  · exact B610599
  · exact B610603
  · exact B610607
  · exact B610611
  · exact B610615
  · exact B610619
  · exact B610623
  · exact B610627
  · exact B610631
  · exact B610635
  · exact B610639
  · exact B610643
  · exact B610647
  · exact B610651
  · exact B610655
  · exact B610659
  · exact B610663
  · exact B610667
  · exact B610671
  · exact B610675
  · exact B610679
  · exact B610683
  · exact B610687
  · exact B610691
  · exact B610695
  · exact B610699
  · exact B610703
  · exact B610707
  · exact B610711
  · exact B610715
  · exact B610719
  · exact B610723
  · exact B610727
  · exact B610731
  · exact B610735
  · exact B610739
  · exact B610743
  · exact B610747
  · exact B610751
  · exact B610755
  · exact B610759
  · exact B610763
  · exact B610767
  · exact B610771
  · exact B610775
  · exact B610779
  · exact B610783
  · exact B610787
  · exact B610791
  · exact B610795
  · exact B610799
  · exact B610803
  · exact B610807
  · exact B610811
  · exact B610815
  · exact B610819
  · exact B610823
  · exact B610827
  · exact B610831
  · exact B610835
  · exact B610839
  · exact B610843
  · exact B610847
  · exact B610851
  · exact B610855
  · exact B610859
  · exact B610863
  · exact B610867
  · exact B610871
  · exact B610875
  · exact B610879
  · exact B610883
  · exact B610887
  · exact B610891
  · exact B610895
  · exact B610899
  · exact B610903
  · exact B610907
  · exact B610911
  · exact B610915
  · exact B610919
  · exact B610923
  · exact B610927
  · exact B610931
  · exact B610935
  · exact B610939
  · exact B610943
  · exact B610947
  · exact B610951
  · exact B610955
  · exact B610959
  · exact B610963
  · exact B610967
  · exact B610971
  · exact B610975
  · exact B610979
  · exact B610983
  · exact B610987
  · exact B610991
  · exact B610995
  · exact B610999
  · exact B611003
  · exact B611007
  · exact B611011
  · exact B611015
  · exact B611019
  · exact B611023
  · exact B611027
  · exact B611031
  · exact B611035
  · exact B611039
  · exact B611043
  · exact B611047
  · exact B611051
  · exact B611055
  · exact B611059
  · exact B611063
  · exact B611067
  · exact B611071
  · exact B611075
  · exact B611079
  · exact B611083
  · exact B611087
  · exact B611091
  · exact B611095
  · exact B611099
  · exact B611103
  · exact B611107
  · exact B611111
  · exact B611115
  · exact B611119
  · exact B611123
  · exact B611127
  · exact B611131
  · exact B611135
  · exact B611139
  · exact B611143
  · exact B611147
  · exact B611151
  · exact B611155
  · exact B611159
  · exact B611163
  · exact B611167
  · exact B611171
  · exact B611175
  · exact B611179
  · exact B611183
  · exact B611187
  · exact B611191
  · exact B611195
  · exact B611199
  · exact B611203
  · exact B611207
  · exact B611211
  · exact B611215
  · exact B611219
  · exact B611223
  · exact B611227
  · exact B611231
  · exact B611235
  · exact B611239
  · exact B611243
  · exact B611247
  · exact B611251
  · exact B611255
  · exact B611259
  · exact B611263
  · exact B611267
  · exact B611271
  · exact B611275
  · exact B611279
  · exact B611283
  · exact B611287
  · exact B611291
  · exact B611295
  · exact B611299
  · exact B611303
  · exact B611307
  · exact B611311
  · exact B611315
  · exact B611319
  · exact B611323
  · exact B611327
  · exact B611331
  · exact B611335
  · exact B611339
  · exact B611343
  · exact B611347
  · exact B611351
  · exact B611355
  · exact B611359
  · exact B611363
  · exact B611367
  · exact B611371
  · exact B611375
  · exact B611379
  · exact B611383
  · exact B611387
  · exact B611391
  · exact B611395
  · exact B611399
  · exact B611403
  · exact B611407
  · exact B611411
  · exact B611415
  · exact B611419
  · exact B611423
  · exact B611427
  · exact B611431
  · exact B611435
  · exact B611439
  · exact B611443
  · exact B611447
  · exact B611451
  · exact B611455
  · exact B611459
  · exact B611463
  · exact B611467
  · exact B611471
  · exact B611475
  · exact B611479
  · exact B611483
  · exact B611487
  · exact B611491
  · exact B611495
  · exact B611499
  · exact B611503
  · exact B611507
  · exact B611511
  · exact B611515
  · exact B611519
  · exact B611523
  · exact B611527
  · exact B611531
  · exact B611535
  · exact B611539
  · exact B611543
  · exact B611547
  · exact B611551
  · exact B611555
  · exact B611559
  · exact B611563
  · exact B611567
  · exact B611571
  · exact B611575
  · exact B611579
  · exact B611583
  · exact B611587
  · exact B611591
  · exact B611595
  · exact B611599
  · exact B611603
  · exact B611607
  · exact B611611
  · exact B611615
  · exact B611619
  · exact B611623
  · exact B611627
  · exact B611631
  · exact B611635
  · exact B611639
  · exact B611643
  · exact B611647
  · exact B611651
  · exact B611655
  · exact B611659
  · exact B611663
  · exact B611667
  · exact B611671
  · exact B611675
  · exact B611679
  · exact B611683
  · exact B611687
  · exact B611691
  · exact B611695
  · exact B611699
  · exact B611703
  · exact B611707
  · exact B611711
  · exact B611715
  · exact B611719
  · exact B611723
  · exact B611727
  · exact B611731
  · exact B611735
  · exact B611739
  · exact B611743
  · exact B611747
  · exact B611751
  · exact B611755
  · exact B611759
  · exact B611763
  · exact B611767
  · exact B611771
  · exact B611775
  · exact B611779
  · exact B611783
  · exact B611787
  · exact B611791
  · exact B611795
  · exact B611799
  · exact B611803
  · exact B611807
  · exact B611811
  · exact B611815
  · exact B611819
  · exact B611823
  · exact B611827
  · exact B611831
  · exact B611835
  · exact B611839
  · exact B611843
  · exact B611847
  · exact B611851
  · exact B611855
  · exact B611859
  · exact B611863
  · exact B611867
  · exact B611871
  · exact B611875
  · exact B611879
  · exact B611883
  · exact B611887
  · exact B611891
  · exact B611895
  · exact B611899
  · exact B611903
  · exact B611907
  · exact B611911
  · exact B611915
  · exact B611919
  · exact B611923
  · exact B611927
  · exact B611931
  · exact B611935
  · exact B611939
  · exact B611943
  · exact B611947
  · exact B611951
  · exact B611955
  · exact B611959
  · exact B611963
  · exact B611967
  · exact B611971
  · exact B611975
  · exact B611979
  · exact B611983
  · exact B611987
  · exact B611991
  · exact B611995
  · exact B611999
  · exact B612003
  · exact B612007
  · exact B612011
  · exact B612015
  · exact B612019
  · exact B612023
  · exact B612027
  · exact B612031
  · exact B612035
  · exact B612039
  · exact B612043
  · exact B612047
  · exact B612051
  · exact B612055
  · exact B612059
  · exact B612063
  · exact B612067
  · exact B612071
  · exact B612075
  · exact B612079
  · exact B612083
  · exact B612087
  · exact B612091
  · exact B612095
  · exact B612099
  · exact B612103
  · exact B612107
  · exact B612111
  · exact B612115
  · exact B612119
  · exact B612123
  · exact B612127
  · exact B612131
  · exact B612135
  · exact B612139
  · exact B612143
  · exact B612147
  · exact B612151
  · exact B612155
  · exact B612159
  · exact B612163
  · exact B612167
  · exact B612171
  · exact B612175
  · exact B612179
  · exact B612183
  · exact B612187
  · exact B612191
  · exact B612195
  · exact B612199
  · exact B612203
  · exact B612207
  · exact B612211
  · exact B612215
  · exact B612219
  · exact B612223
  · exact B612227
  · exact B612231
  · exact B612235
  · exact B612239
  · exact B612243
  · exact B612247
  · exact B612251
  · exact B612255
  · exact B612259
  · exact B612263
  · exact B612267
  · exact B612271
  · exact B612275
  · exact B612279
  · exact B612283
  · exact B612287
  · exact B612291
  · exact B612295
  · exact B612299
  · exact B612303
  · exact B612307
  · exact B612311
  · exact B612315
  · exact B612319
  · exact B612323
  · exact B612327
  · exact B612331
  · exact B612335
  · exact B612339
  · exact B612343
  · exact B612347
  · exact B612351
  · exact B612355
  · exact B612359
  · exact B612363
  · exact B612367
  · exact B612371
  · exact B612375
  · exact B612379
  · exact B612383
  · exact B612387
  · exact B612391
  · exact B612395
  · exact B612399
  · exact B612403
  · exact B612407
  · exact B612411
  · exact B612415
  · exact B612419
  · exact B612423
  · exact B612427
  · exact B612431
  · exact B612435
  · exact B612439
  · exact B612443
  · exact B612447
  · exact B612451
  · exact B612455
  · exact B612459
  · exact B612463
  · exact B612467
  · exact B612471
  · exact B612475
  · exact B612479
  · exact B612483
  · exact B612487
  · exact B612491
  · exact B612495
  · exact B612499
  · exact B612503
  · exact B612507
  · exact B612511
  · exact B612515
  · exact B612519
  · exact B612523
  · exact B612527
  · exact B612531
  · exact B612535
  · exact B612539
  · exact B612543
  · exact B612547
  · exact B612551
  · exact B612555
  · exact B612559
  · exact B612563
  · exact B612567
  · exact B612571
  · exact B612575
  · exact B612579
  · exact B612583
  · exact B612587
  · exact B612591
  · exact B612595
  · exact B612599
  · exact B612603
  · exact B612607
  · exact B612611
  · exact B612615
  · exact B612619
  · exact B612623
  · exact B612627
  · exact B612631
  · exact B612635
  · exact B612639
  · exact B612643
  · exact B612647
  · exact B612651
  · exact B612655
  · exact B612659
  · exact B612663
  · exact B612667
  · exact B612671
  · exact B612675
  · exact B612679
  · exact B612683
  · exact B612687
  · exact B612691
  · exact B612695
  · exact B612699
  · exact B612703
  · exact B612707
  · exact B612711
  · exact B612715
  · exact B612719
  · exact B612723
  · exact B612727
  · exact B612731
  · exact B612735
  · exact B612739
  · exact B612743
  · exact B612747
  · exact B612751
  · exact B612755
  · exact B612759
  · exact B612763
  · exact B612767
  · exact B612771
  · exact B612775
  · exact B612779
  · exact B612783
  · exact B612787
  · exact B612791
  · exact B612795
  · exact B612799
  · exact B612803
  · exact B612807
  · exact B612811
  · exact B612815
  · exact B612819
  · exact B612823
  · exact B612827
  · exact B612831
  · exact B612835
  · exact B612839
  · exact B612843
  · exact B612847
  · exact B612851
  · exact B612855
  · exact B612859
  · exact B612863
  · exact B612867
  · exact B612871
  · exact B612875
  · exact B612879
  · exact B612883
  · exact B612887
  · exact B612891
  · exact B612895
  · exact B612899
  · exact B612903
  · exact B612907
  · exact B612911
  · exact B612915
  · exact B612919
  · exact B612923
  · exact B612927
  · exact B612931
  · exact B612935
  · exact B612939
  · exact B612943
  · exact B612947
  · exact B612951
  · exact B612955
  · exact B612959
  · exact B612963
  · exact B612967
  · exact B612971
  · exact B612975
  · exact B612979
  · exact B612983
  · exact B612987
  · exact B612991
  · exact B612995
  · exact B612999
  · exact B613003
  · exact B613007
  · exact B613011
  · exact B613015
  · exact B613019
  · exact B613023
  · exact B613027
  · exact B613031
  · exact B613035
  · exact B613039
  · exact B613043
  · exact B613047
  · exact B613051
  · exact B613055
  · exact B613059
  · exact B613063
  · exact B613067
  · exact B613071
  · exact B613075
  · exact B613079
  · exact B613083
  · exact B613087
  · exact B613091

theorem C1 (j : ℕ) (h1 : 153273 ≤ j) (h2 : j ≤ 153573) : Blo 610295 (4 * j + 3) := by
  interval_cases j
  · exact B613095
  · exact B613099
  · exact B613103
  · exact B613107
  · exact B613111
  · exact B613115
  · exact B613119
  · exact B613123
  · exact B613127
  · exact B613131
  · exact B613135
  · exact B613139
  · exact B613143
  · exact B613147
  · exact B613151
  · exact B613155
  · exact B613159
  · exact B613163
  · exact B613167
  · exact B613171
  · exact B613175
  · exact B613179
  · exact B613183
  · exact B613187
  · exact B613191
  · exact B613195
  · exact B613199
  · exact B613203
  · exact B613207
  · exact B613211
  · exact B613215
  · exact B613219
  · exact B613223
  · exact B613227
  · exact B613231
  · exact B613235
  · exact B613239
  · exact B613243
  · exact B613247
  · exact B613251
  · exact B613255
  · exact B613259
  · exact B613263
  · exact B613267
  · exact B613271
  · exact B613275
  · exact B613279
  · exact B613283
  · exact B613287
  · exact B613291
  · exact B613295
  · exact B613299
  · exact B613303
  · exact B613307
  · exact B613311
  · exact B613315
  · exact B613319
  · exact B613323
  · exact B613327
  · exact B613331
  · exact B613335
  · exact B613339
  · exact B613343
  · exact B613347
  · exact B613351
  · exact B613355
  · exact B613359
  · exact B613363
  · exact B613367
  · exact B613371
  · exact B613375
  · exact B613379
  · exact B613383
  · exact B613387
  · exact B613391
  · exact B613395
  · exact B613399
  · exact B613403
  · exact B613407
  · exact B613411
  · exact B613415
  · exact B613419
  · exact B613423
  · exact B613427
  · exact B613431
  · exact B613435
  · exact B613439
  · exact B613443
  · exact B613447
  · exact B613451
  · exact B613455
  · exact B613459
  · exact B613463
  · exact B613467
  · exact B613471
  · exact B613475
  · exact B613479
  · exact B613483
  · exact B613487
  · exact B613491
  · exact B613495
  · exact B613499
  · exact B613503
  · exact B613507
  · exact B613511
  · exact B613515
  · exact B613519
  · exact B613523
  · exact B613527
  · exact B613531
  · exact B613535
  · exact B613539
  · exact B613543
  · exact B613547
  · exact B613551
  · exact B613555
  · exact B613559
  · exact B613563
  · exact B613567
  · exact B613571
  · exact B613575
  · exact B613579
  · exact B613583
  · exact B613587
  · exact B613591
  · exact B613595
  · exact B613599
  · exact B613603
  · exact B613607
  · exact B613611
  · exact B613615
  · exact B613619
  · exact B613623
  · exact B613627
  · exact B613631
  · exact B613635
  · exact B613639
  · exact B613643
  · exact B613647
  · exact B613651
  · exact B613655
  · exact B613659
  · exact B613663
  · exact B613667
  · exact B613671
  · exact B613675
  · exact B613679
  · exact B613683
  · exact B613687
  · exact B613691
  · exact B613695
  · exact B613699
  · exact B613703
  · exact B613707
  · exact B613711
  · exact B613715
  · exact B613719
  · exact B613723
  · exact B613727
  · exact B613731
  · exact B613735
  · exact B613739
  · exact B613743
  · exact B613747
  · exact B613751
  · exact B613755
  · exact B613759
  · exact B613763
  · exact B613767
  · exact B613771
  · exact B613775
  · exact B613779
  · exact B613783
  · exact B613787
  · exact B613791
  · exact B613795
  · exact B613799
  · exact B613803
  · exact B613807
  · exact B613811
  · exact B613815
  · exact B613819
  · exact B613823
  · exact B613827
  · exact B613831
  · exact B613835
  · exact B613839
  · exact B613843
  · exact B613847
  · exact B613851
  · exact B613855
  · exact B613859
  · exact B613863
  · exact B613867
  · exact B613871
  · exact B613875
  · exact B613879
  · exact B613883
  · exact B613887
  · exact B613891
  · exact B613895
  · exact B613899
  · exact B613903
  · exact B613907
  · exact B613911
  · exact B613915
  · exact B613919
  · exact B613923
  · exact B613927
  · exact B613931
  · exact B613935
  · exact B613939
  · exact B613943
  · exact B613947
  · exact B613951
  · exact B613955
  · exact B613959
  · exact B613963
  · exact B613967
  · exact B613971
  · exact B613975
  · exact B613979
  · exact B613983
  · exact B613987
  · exact B613991
  · exact B613995
  · exact B613999
  · exact B614003
  · exact B614007
  · exact B614011
  · exact B614015
  · exact B614019
  · exact B614023
  · exact B614027
  · exact B614031
  · exact B614035
  · exact B614039
  · exact B614043
  · exact B614047
  · exact B614051
  · exact B614055
  · exact B614059
  · exact B614063
  · exact B614067
  · exact B614071
  · exact B614075
  · exact B614079
  · exact B614083
  · exact B614087
  · exact B614091
  · exact B614095
  · exact B614099
  · exact B614103
  · exact B614107
  · exact B614111
  · exact B614115
  · exact B614119
  · exact B614123
  · exact B614127
  · exact B614131
  · exact B614135
  · exact B614139
  · exact B614143
  · exact B614147
  · exact B614151
  · exact B614155
  · exact B614159
  · exact B614163
  · exact B614167
  · exact B614171
  · exact B614175
  · exact B614179
  · exact B614183
  · exact B614187
  · exact B614191
  · exact B614195
  · exact B614199
  · exact B614203
  · exact B614207
  · exact B614211
  · exact B614215
  · exact B614219
  · exact B614223
  · exact B614227
  · exact B614231
  · exact B614235
  · exact B614239
  · exact B614243
  · exact B614247
  · exact B614251
  · exact B614255
  · exact B614259
  · exact B614263
  · exact B614267
  · exact B614271
  · exact B614275
  · exact B614279
  · exact B614283
  · exact B614287
  · exact B614291
  · exact B614295

theorem solution (m : ℕ) (hlo : 610295 ≤ m) (hhi : m ≤ 614295) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 152573 ≤ j := by omega
    have hj2 : j ≤ 153573 := by omega
    have hb : Blo 610295 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 153273 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
