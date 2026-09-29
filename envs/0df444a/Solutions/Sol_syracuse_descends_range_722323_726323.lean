-- Prove2me | solution 1 for syracuse_descends_range_722323_726323
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:08.738094+00:00
-- url     : https://prove2.me/submissions/d7073a0d-f925-4a47-b9c3-f8aee521e9ce

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


theorem B1376261 : Blo 722323 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B1835045 : Blo 722323 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B2064437 : Blo 722323 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B2752613 : Blo 722323 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B917669 : Blo 722323 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B917725 : Blo 722323 917725 := bbase (se 3 (by rfl) ⟨172073, by rfl⟩ : syracuseStep 917725 = 344147) (by norm_num)
theorem B1835237 : Blo 722323 1835237 := bbase (se 4 (by rfl) ⟨172053, by rfl⟩ : syracuseStep 1835237 = 344107) (by norm_num)
theorem B917821 : Blo 722323 917821 := bbase (se 3 (by rfl) ⟨172091, by rfl⟩ : syracuseStep 917821 = 344183) (by norm_num)
theorem B917993 : Blo 722323 917993 := bbase (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) (by norm_num)
theorem B918049 : Blo 722323 918049 := bbase (se 2 (by rfl) ⟨344268, by rfl⟩ : syracuseStep 918049 = 688537) (by norm_num)
theorem B1835581 : Blo 722323 1835581 := bbase (se 3 (by rfl) ⟨344171, by rfl⟩ : syracuseStep 1835581 = 688343) (by norm_num)
theorem B1114717 : Blo 722323 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B918145 : Blo 722323 918145 := bbase (se 2 (by rfl) ⟨344304, by rfl⟩ : syracuseStep 918145 = 688609) (by norm_num)
theorem B1835693 : Blo 722323 1835693 := bbase (se 3 (by rfl) ⟨344192, by rfl⟩ : syracuseStep 1835693 = 688385) (by norm_num)
theorem B1671869 : Blo 722323 1671869 := bbase (se 3 (by rfl) ⟨313475, by rfl⟩ : syracuseStep 1671869 = 626951) (by norm_num)
theorem B3670757 : Blo 722323 3670757 := bbase (se 4 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 3670757 = 688267) (by norm_num)
theorem B1377013 : Blo 722323 1377013 := bbase (se 5 (by rfl) ⟨64547, by rfl⟩ : syracuseStep 1377013 = 129095) (by norm_num)
theorem B2065189 : Blo 722323 2065189 := bbase (se 4 (by rfl) ⟨193611, by rfl⟩ : syracuseStep 2065189 = 387223) (by norm_num)
theorem B918317 : Blo 722323 918317 := bbase (se 3 (by rfl) ⟨172184, by rfl⟩ : syracuseStep 918317 = 344369) (by norm_num)
theorem B17662805 : Blo 722323 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B918373 : Blo 722323 918373 := bbase (se 4 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 918373 = 172195) (by norm_num)
theorem B1835885 : Blo 722323 1835885 := bbase (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) (by norm_num)
theorem B1377157 : Blo 722323 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B6783925 : Blo 722323 6783925 := bbase (se 5 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 6783925 = 635993) (by norm_num)
theorem B918469 : Blo 722323 918469 := bbase (se 4 (by rfl) ⟨86106, by rfl⟩ : syracuseStep 918469 = 172213) (by norm_num)
theorem B1377317 : Blo 722323 1377317 := bbase (se 4 (by rfl) ⟨129123, by rfl⟩ : syracuseStep 1377317 = 258247) (by norm_num)
theorem B754741 : Blo 722323 754741 := bbase (se 5 (by rfl) ⟨35378, by rfl⟩ : syracuseStep 754741 = 70757) (by norm_num)
theorem B918641 : Blo 722323 918641 := bbase (se 2 (by rfl) ⟨344490, by rfl⟩ : syracuseStep 918641 = 688981) (by norm_num)
theorem B918697 : Blo 722323 918697 := bbase (se 2 (by rfl) ⟨344511, by rfl⟩ : syracuseStep 918697 = 689023) (by norm_num)
theorem B1377461 : Blo 722323 1377461 := bbase (se 5 (by rfl) ⟨64568, by rfl⟩ : syracuseStep 1377461 = 129137) (by norm_num)
theorem B1836229 : Blo 722323 1836229 := bbase (se 4 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 1836229 = 344293) (by norm_num)
theorem B2753797 : Blo 722323 2753797 := bbase (se 4 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 2753797 = 516337) (by norm_num)
theorem B918793 : Blo 722323 918793 := bbase (se 2 (by rfl) ⟨344547, by rfl⟩ : syracuseStep 918793 = 689095) (by norm_num)
theorem B1836341 : Blo 722323 1836341 := bbase (se 5 (by rfl) ⟨86078, by rfl⟩ : syracuseStep 1836341 = 172157) (by norm_num)
theorem B918965 : Blo 722323 918965 := bbase (se 5 (by rfl) ⟨43076, by rfl⟩ : syracuseStep 918965 = 86153) (by norm_num)
theorem B1377749 : Blo 722323 1377749 := bbase (se 7 (by rfl) ⟨16145, by rfl⟩ : syracuseStep 1377749 = 32291) (by norm_num)
theorem B919021 : Blo 722323 919021 := bbase (se 3 (by rfl) ⟨172316, by rfl⟩ : syracuseStep 919021 = 344633) (by norm_num)
theorem B6194677 : Blo 722323 6194677 := bbase (se 5 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 6194677 = 580751) (by norm_num)
theorem B1836533 : Blo 722323 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B2754101 : Blo 722323 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B919117 : Blo 722323 919117 := bbase (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) (by norm_num)
theorem B1377901 : Blo 722323 1377901 := bbase (se 3 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 1377901 = 516713) (by norm_num)
theorem B1738525 : Blo 722323 1738525 := bbase (se 3 (by rfl) ⟨325973, by rfl⟩ : syracuseStep 1738525 = 651947) (by norm_num)
theorem B952141 : Blo 722323 952141 := bbase (se 3 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 952141 = 357053) (by norm_num)
theorem B1836877 : Blo 722323 1836877 := bbase (se 3 (by rfl) ⟨344414, by rfl⟩ : syracuseStep 1836877 = 688829) (by norm_num)
theorem B1378205 : Blo 722323 1378205 := bbase (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) (by norm_num)
theorem B1836989 : Blo 722323 1836989 := bbase (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) (by norm_num)
theorem B3672053 : Blo 722323 3672053 := bbase (se 5 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 3672053 = 344255) (by norm_num)
theorem B1083485 : Blo 722323 1083485 := bbase (se 3 (by rfl) ⟨203153, by rfl⟩ : syracuseStep 1083485 = 406307) (by norm_num)
theorem B1083509 : Blo 722323 1083509 := bbase (se 5 (by rfl) ⟨50789, by rfl⟩ : syracuseStep 1083509 = 101579) (by norm_num)
theorem B1837181 : Blo 722323 1837181 := bbase (se 3 (by rfl) ⟨344471, by rfl⟩ : syracuseStep 1837181 = 688943) (by norm_num)
theorem B1083533 : Blo 722323 1083533 := bbase (se 3 (by rfl) ⟨203162, by rfl⟩ : syracuseStep 1083533 = 406325) (by norm_num)
theorem B1083557 : Blo 722323 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B1083581 : Blo 722323 1083581 := bbase (se 3 (by rfl) ⟨203171, by rfl⟩ : syracuseStep 1083581 = 406343) (by norm_num)
theorem B1083605 : Blo 722323 1083605 := bbase (se 7 (by rfl) ⟨12698, by rfl⟩ : syracuseStep 1083605 = 25397) (by norm_num)
theorem B1083629 : Blo 722323 1083629 := bbase (se 3 (by rfl) ⟨203180, by rfl⟩ : syracuseStep 1083629 = 406361) (by norm_num)
theorem B1083653 : Blo 722323 1083653 := bbase (se 4 (by rfl) ⟨101592, by rfl⟩ : syracuseStep 1083653 = 203185) (by norm_num)
theorem B10455317 : Blo 722323 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B1083677 : Blo 722323 1083677 := bbase (se 3 (by rfl) ⟨203189, by rfl⟩ : syracuseStep 1083677 = 406379) (by norm_num)
theorem B1739045 : Blo 722323 1739045 := bbase (se 4 (by rfl) ⟨163035, by rfl⟩ : syracuseStep 1739045 = 326071) (by norm_num)
theorem B1083701 : Blo 722323 1083701 := bbase (se 5 (by rfl) ⟨50798, by rfl⟩ : syracuseStep 1083701 = 101597) (by norm_num)
theorem B3475781 : Blo 722323 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B1083725 : Blo 722323 1083725 := bbase (se 3 (by rfl) ⟨203198, by rfl⟩ : syracuseStep 1083725 = 406397) (by norm_num)
theorem B1083749 : Blo 722323 1083749 := bbase (se 4 (by rfl) ⟨101601, by rfl⟩ : syracuseStep 1083749 = 203203) (by norm_num)
theorem B1083773 : Blo 722323 1083773 := bbase (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) (by norm_num)
theorem B1739141 : Blo 722323 1739141 := bbase (se 4 (by rfl) ⟨163044, by rfl⟩ : syracuseStep 1739141 = 326089) (by norm_num)
theorem B1083797 : Blo 722323 1083797 := bbase (se 6 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 1083797 = 50803) (by norm_num)
theorem B1083821 : Blo 722323 1083821 := bbase (se 3 (by rfl) ⟨203216, by rfl⟩ : syracuseStep 1083821 = 406433) (by norm_num)
theorem B1083845 : Blo 722323 1083845 := bbase (se 4 (by rfl) ⟨101610, by rfl⟩ : syracuseStep 1083845 = 203221) (by norm_num)
theorem B1837525 : Blo 722323 1837525 := bbase (se 7 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 1837525 = 43067) (by norm_num)
theorem B1083869 : Blo 722323 1083869 := bbase (se 3 (by rfl) ⟨203225, by rfl⟩ : syracuseStep 1083869 = 406451) (by norm_num)
theorem B1083893 : Blo 722323 1083893 := bbase (se 5 (by rfl) ⟨50807, by rfl⟩ : syracuseStep 1083893 = 101615) (by norm_num)
theorem B1083917 : Blo 722323 1083917 := bbase (se 3 (by rfl) ⟨203234, by rfl⟩ : syracuseStep 1083917 = 406469) (by norm_num)
theorem B1083941 : Blo 722323 1083941 := bbase (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) (by norm_num)
theorem B1083965 : Blo 722323 1083965 := bbase (se 3 (by rfl) ⟨203243, by rfl⟩ : syracuseStep 1083965 = 406487) (by norm_num)
theorem B1837637 : Blo 722323 1837637 := bbase (se 4 (by rfl) ⟨172278, by rfl⟩ : syracuseStep 1837637 = 344557) (by norm_num)
theorem B1083989 : Blo 722323 1083989 := bbase (se 8 (by rfl) ⟨6351, by rfl⟩ : syracuseStep 1083989 = 12703) (by norm_num)
theorem B1084013 : Blo 722323 1084013 := bbase (se 3 (by rfl) ⟨203252, by rfl⟩ : syracuseStep 1084013 = 406505) (by norm_num)
theorem B1084037 : Blo 722323 1084037 := bbase (se 4 (by rfl) ⟨101628, by rfl⟩ : syracuseStep 1084037 = 203257) (by norm_num)
theorem B1084061 : Blo 722323 1084061 := bbase (se 3 (by rfl) ⟨203261, by rfl⟩ : syracuseStep 1084061 = 406523) (by norm_num)
theorem B1084085 : Blo 722323 1084085 := bbase (se 5 (by rfl) ⟨50816, by rfl⟩ : syracuseStep 1084085 = 101633) (by norm_num)
theorem B1084109 : Blo 722323 1084109 := bbase (se 3 (by rfl) ⟨203270, by rfl⟩ : syracuseStep 1084109 = 406541) (by norm_num)
theorem B1084133 : Blo 722323 1084133 := bbase (se 4 (by rfl) ⟨101637, by rfl⟩ : syracuseStep 1084133 = 203275) (by norm_num)
theorem B1084157 : Blo 722323 1084157 := bbase (se 3 (by rfl) ⟨203279, by rfl⟩ : syracuseStep 1084157 = 406559) (by norm_num)
theorem B1837829 : Blo 722323 1837829 := bbase (se 4 (by rfl) ⟨172296, by rfl⟩ : syracuseStep 1837829 = 344593) (by norm_num)
theorem B1084181 : Blo 722323 1084181 := bbase (se 6 (by rfl) ⟨25410, by rfl⟩ : syracuseStep 1084181 = 50821) (by norm_num)
theorem B1084205 : Blo 722323 1084205 := bbase (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) (by norm_num)
theorem B1084229 : Blo 722323 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B1542989 : Blo 722323 1542989 := bbase (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) (by norm_num)
theorem B1542997 : Blo 722323 1542997 := bbase (se 9 (by rfl) ⟨4520, by rfl⟩ : syracuseStep 1542997 = 9041) (by norm_num)
theorem B1084253 : Blo 722323 1084253 := bbase (se 3 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 1084253 = 406595) (by norm_num)
theorem B1084277 : Blo 722323 1084277 := bbase (se 5 (by rfl) ⟨50825, by rfl⟩ : syracuseStep 1084277 = 101651) (by norm_num)
theorem B1084301 : Blo 722323 1084301 := bbase (se 3 (by rfl) ⟨203306, by rfl⟩ : syracuseStep 1084301 = 406613) (by norm_num)
theorem B1084325 : Blo 722323 1084325 := bbase (se 4 (by rfl) ⟨101655, by rfl⟩ : syracuseStep 1084325 = 203311) (by norm_num)
theorem B1084349 : Blo 722323 1084349 := bbase (se 3 (by rfl) ⟨203315, by rfl⟩ : syracuseStep 1084349 = 406631) (by norm_num)
theorem B1084373 : Blo 722323 1084373 := bbase (se 7 (by rfl) ⟨12707, by rfl⟩ : syracuseStep 1084373 = 25415) (by norm_num)
theorem B1084397 : Blo 722323 1084397 := bbase (se 3 (by rfl) ⟨203324, by rfl⟩ : syracuseStep 1084397 = 406649) (by norm_num)
theorem B1084421 : Blo 722323 1084421 := bbase (se 4 (by rfl) ⟨101664, by rfl⟩ : syracuseStep 1084421 = 203329) (by norm_num)
theorem B1084445 : Blo 722323 1084445 := bbase (se 3 (by rfl) ⟨203333, by rfl⟩ : syracuseStep 1084445 = 406667) (by norm_num)
theorem B1084469 : Blo 722323 1084469 := bbase (se 5 (by rfl) ⟨50834, by rfl⟩ : syracuseStep 1084469 = 101669) (by norm_num)
theorem B1084493 : Blo 722323 1084493 := bbase (se 3 (by rfl) ⟨203342, by rfl⟩ : syracuseStep 1084493 = 406685) (by norm_num)
theorem B1838173 : Blo 722323 1838173 := bbase (se 3 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 1838173 = 689315) (by norm_num)
theorem B1084517 : Blo 722323 1084517 := bbase (se 4 (by rfl) ⟨101673, by rfl⟩ : syracuseStep 1084517 = 203347) (by norm_num)
theorem B1084541 : Blo 722323 1084541 := bbase (se 3 (by rfl) ⟨203351, by rfl⟩ : syracuseStep 1084541 = 406703) (by norm_num)
theorem B1084565 : Blo 722323 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B1084589 : Blo 722323 1084589 := bbase (se 3 (by rfl) ⟨203360, by rfl⟩ : syracuseStep 1084589 = 406721) (by norm_num)
theorem B1084613 : Blo 722323 1084613 := bbase (se 4 (by rfl) ⟨101682, by rfl⟩ : syracuseStep 1084613 = 203365) (by norm_num)
theorem B1838285 : Blo 722323 1838285 := bbase (se 3 (by rfl) ⟨344678, by rfl⟩ : syracuseStep 1838285 = 689357) (by norm_num)
theorem B1084637 : Blo 722323 1084637 := bbase (se 3 (by rfl) ⟨203369, by rfl⟩ : syracuseStep 1084637 = 406739) (by norm_num)
theorem B1084661 : Blo 722323 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B3673349 : Blo 722323 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B1084685 : Blo 722323 1084685 := bbase (se 3 (by rfl) ⟨203378, by rfl⟩ : syracuseStep 1084685 = 406757) (by norm_num)
theorem B1084709 : Blo 722323 1084709 := bbase (se 4 (by rfl) ⟨101691, by rfl⟩ : syracuseStep 1084709 = 203383) (by norm_num)
theorem B1084733 : Blo 722323 1084733 := bbase (se 3 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 1084733 = 406775) (by norm_num)
theorem B1084757 : Blo 722323 1084757 := bbase (se 11 (by rfl) ⟨794, by rfl⟩ : syracuseStep 1084757 = 1589) (by norm_num)
theorem B1084781 : Blo 722323 1084781 := bbase (se 3 (by rfl) ⟨203396, by rfl⟩ : syracuseStep 1084781 = 406793) (by norm_num)
theorem B1084805 : Blo 722323 1084805 := bbase (se 4 (by rfl) ⟨101700, by rfl⟩ : syracuseStep 1084805 = 203401) (by norm_num)
theorem B1838477 : Blo 722323 1838477 := bbase (se 3 (by rfl) ⟨344714, by rfl⟩ : syracuseStep 1838477 = 689429) (by norm_num)
theorem B1084829 : Blo 722323 1084829 := bbase (se 3 (by rfl) ⟨203405, by rfl⟩ : syracuseStep 1084829 = 406811) (by norm_num)
theorem B1084853 : Blo 722323 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B6196661 : Blo 722323 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B1084877 : Blo 722323 1084877 := bbase (se 3 (by rfl) ⟨203414, by rfl⟩ : syracuseStep 1084877 = 406829) (by norm_num)
theorem B1084901 : Blo 722323 1084901 := bbase (se 4 (by rfl) ⟨101709, by rfl⟩ : syracuseStep 1084901 = 203419) (by norm_num)
theorem B1084925 : Blo 722323 1084925 := bbase (se 3 (by rfl) ⟨203423, by rfl⟩ : syracuseStep 1084925 = 406847) (by norm_num)
theorem B1084949 : Blo 722323 1084949 := bbase (se 6 (by rfl) ⟨25428, by rfl⟩ : syracuseStep 1084949 = 50857) (by norm_num)
theorem B1084973 : Blo 722323 1084973 := bbase (se 3 (by rfl) ⟨203432, by rfl⟩ : syracuseStep 1084973 = 406865) (by norm_num)
theorem B1084997 : Blo 722323 1084997 := bbase (se 4 (by rfl) ⟨101718, by rfl⟩ : syracuseStep 1084997 = 203437) (by norm_num)
theorem B2068037 : Blo 722323 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B1085021 : Blo 722323 1085021 := bbase (se 3 (by rfl) ⟨203441, by rfl⟩ : syracuseStep 1085021 = 406883) (by norm_num)
theorem B1085045 : Blo 722323 1085045 := bbase (se 5 (by rfl) ⟨50861, by rfl⟩ : syracuseStep 1085045 = 101723) (by norm_num)
theorem B2756213 : Blo 722323 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B3477125 : Blo 722323 3477125 := bbase (se 4 (by rfl) ⟨325980, by rfl⟩ : syracuseStep 3477125 = 651961) (by norm_num)
theorem B1085069 : Blo 722323 1085069 := bbase (se 3 (by rfl) ⟨203450, by rfl⟩ : syracuseStep 1085069 = 406901) (by norm_num)
theorem B1085093 : Blo 722323 1085093 := bbase (se 4 (by rfl) ⟨101727, by rfl⟩ : syracuseStep 1085093 = 203455) (by norm_num)
theorem B1085117 : Blo 722323 1085117 := bbase (se 3 (by rfl) ⟨203459, by rfl⟩ : syracuseStep 1085117 = 406919) (by norm_num)
theorem B1740485 : Blo 722323 1740485 := bbase (se 4 (by rfl) ⟨163170, by rfl⟩ : syracuseStep 1740485 = 326341) (by norm_num)
theorem B1085141 : Blo 722323 1085141 := bbase (se 7 (by rfl) ⟨12716, by rfl⟩ : syracuseStep 1085141 = 25433) (by norm_num)
theorem B4132565 : Blo 722323 4132565 := bbase (se 7 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 4132565 = 96857) (by norm_num)
theorem B1085165 : Blo 722323 1085165 := bbase (se 3 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 1085165 = 406937) (by norm_num)
theorem B1085189 : Blo 722323 1085189 := bbase (se 4 (by rfl) ⟨101736, by rfl⟩ : syracuseStep 1085189 = 203473) (by norm_num)
theorem B1085213 : Blo 722323 1085213 := bbase (se 3 (by rfl) ⟨203477, by rfl⟩ : syracuseStep 1085213 = 406955) (by norm_num)
theorem B1085237 : Blo 722323 1085237 := bbase (se 5 (by rfl) ⟨50870, by rfl⟩ : syracuseStep 1085237 = 101741) (by norm_num)
theorem B1085261 : Blo 722323 1085261 := bbase (se 3 (by rfl) ⟨203486, by rfl⟩ : syracuseStep 1085261 = 406973) (by norm_num)
theorem B1085285 : Blo 722323 1085285 := bbase (se 4 (by rfl) ⟨101745, by rfl⟩ : syracuseStep 1085285 = 203491) (by norm_num)
theorem B1085309 : Blo 722323 1085309 := bbase (se 3 (by rfl) ⟨203495, by rfl⟩ : syracuseStep 1085309 = 406991) (by norm_num)
theorem B1085333 : Blo 722323 1085333 := bbase (se 6 (by rfl) ⟨25437, by rfl⟩ : syracuseStep 1085333 = 50875) (by norm_num)
theorem B2756501 : Blo 722323 2756501 := bbase (se 6 (by rfl) ⟨64605, by rfl⟩ : syracuseStep 2756501 = 129211) (by norm_num)
theorem B1085357 : Blo 722323 1085357 := bbase (se 3 (by rfl) ⟨203504, by rfl⟩ : syracuseStep 1085357 = 407009) (by norm_num)
theorem B1544125 : Blo 722323 1544125 := bbase (se 3 (by rfl) ⟨289523, by rfl⟩ : syracuseStep 1544125 = 579047) (by norm_num)
theorem B1085381 : Blo 722323 1085381 := bbase (se 4 (by rfl) ⟨101754, by rfl⟩ : syracuseStep 1085381 = 203509) (by norm_num)
theorem B1085405 : Blo 722323 1085405 := bbase (se 3 (by rfl) ⟨203513, by rfl⟩ : syracuseStep 1085405 = 407027) (by norm_num)
theorem B1085429 : Blo 722323 1085429 := bbase (se 5 (by rfl) ⟨50879, by rfl⟩ : syracuseStep 1085429 = 101759) (by norm_num)
theorem B1085453 : Blo 722323 1085453 := bbase (se 3 (by rfl) ⟨203522, by rfl⟩ : syracuseStep 1085453 = 407045) (by norm_num)
theorem B1085477 : Blo 722323 1085477 := bbase (se 4 (by rfl) ⟨101763, by rfl⟩ : syracuseStep 1085477 = 203527) (by norm_num)
theorem B1085501 : Blo 722323 1085501 := bbase (se 3 (by rfl) ⟨203531, by rfl⟩ : syracuseStep 1085501 = 407063) (by norm_num)
theorem B1085525 : Blo 722323 1085525 := bbase (se 8 (by rfl) ⟨6360, by rfl⟩ : syracuseStep 1085525 = 12721) (by norm_num)
theorem B1085549 : Blo 722323 1085549 := bbase (se 3 (by rfl) ⟨203540, by rfl⟩ : syracuseStep 1085549 = 407081) (by norm_num)
theorem B1085573 : Blo 722323 1085573 := bbase (se 4 (by rfl) ⟨101772, by rfl⟩ : syracuseStep 1085573 = 203545) (by norm_num)
theorem B1085597 : Blo 722323 1085597 := bbase (se 3 (by rfl) ⟨203549, by rfl⟩ : syracuseStep 1085597 = 407099) (by norm_num)
theorem B1085621 : Blo 722323 1085621 := bbase (se 5 (by rfl) ⟨50888, by rfl⟩ : syracuseStep 1085621 = 101777) (by norm_num)
theorem B1085645 : Blo 722323 1085645 := bbase (se 3 (by rfl) ⟨203558, by rfl⟩ : syracuseStep 1085645 = 407117) (by norm_num)
theorem B4526293 : Blo 722323 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B1085669 : Blo 722323 1085669 := bbase (se 4 (by rfl) ⟨101781, by rfl⟩ : syracuseStep 1085669 = 203563) (by norm_num)
theorem B1085693 : Blo 722323 1085693 := bbase (se 3 (by rfl) ⟨203567, by rfl⟩ : syracuseStep 1085693 = 407135) (by norm_num)
theorem B1085717 : Blo 722323 1085717 := bbase (se 6 (by rfl) ⟨25446, by rfl⟩ : syracuseStep 1085717 = 50893) (by norm_num)
theorem B1085741 : Blo 722323 1085741 := bbase (se 3 (by rfl) ⟨203576, by rfl⟩ : syracuseStep 1085741 = 407153) (by norm_num)
theorem B1544501 : Blo 722323 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B1085765 : Blo 722323 1085765 := bbase (se 4 (by rfl) ⟨101790, by rfl⟩ : syracuseStep 1085765 = 203581) (by norm_num)
theorem B1085789 : Blo 722323 1085789 := bbase (se 3 (by rfl) ⟨203585, by rfl⟩ : syracuseStep 1085789 = 407171) (by norm_num)
theorem B1085813 : Blo 722323 1085813 := bbase (se 5 (by rfl) ⟨50897, by rfl⟩ : syracuseStep 1085813 = 101795) (by norm_num)
theorem B1085837 : Blo 722323 1085837 := bbase (se 3 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 1085837 = 407189) (by norm_num)
theorem B1085861 : Blo 722323 1085861 := bbase (se 4 (by rfl) ⟨101799, by rfl⟩ : syracuseStep 1085861 = 203599) (by norm_num)
theorem B1085885 : Blo 722323 1085885 := bbase (se 3 (by rfl) ⟨203603, by rfl⟩ : syracuseStep 1085885 = 407207) (by norm_num)
theorem B1085909 : Blo 722323 1085909 := bbase (se 7 (by rfl) ⟨12725, by rfl⟩ : syracuseStep 1085909 = 25451) (by norm_num)
theorem B1085933 : Blo 722323 1085933 := bbase (se 3 (by rfl) ⟨203612, by rfl⟩ : syracuseStep 1085933 = 407225) (by norm_num)
theorem B1085957 : Blo 722323 1085957 := bbase (se 4 (by rfl) ⟨101808, by rfl⟩ : syracuseStep 1085957 = 203617) (by norm_num)
theorem B2789893 : Blo 722323 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B3674645 : Blo 722323 3674645 := bbase (se 6 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 3674645 = 172249) (by norm_num)
theorem B1085981 : Blo 722323 1085981 := bbase (se 3 (by rfl) ⟨203621, by rfl⟩ : syracuseStep 1085981 = 407243) (by norm_num)
theorem B1086005 : Blo 722323 1086005 := bbase (se 5 (by rfl) ⟨50906, by rfl⟩ : syracuseStep 1086005 = 101813) (by norm_num)
theorem B1086029 : Blo 722323 1086029 := bbase (se 3 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 1086029 = 407261) (by norm_num)
theorem B1086053 : Blo 722323 1086053 := bbase (se 4 (by rfl) ⟨101817, by rfl⟩ : syracuseStep 1086053 = 203635) (by norm_num)
theorem B1086077 : Blo 722323 1086077 := bbase (se 3 (by rfl) ⟨203639, by rfl⟩ : syracuseStep 1086077 = 407279) (by norm_num)
theorem B1086101 : Blo 722323 1086101 := bbase (se 6 (by rfl) ⟨25455, by rfl⟩ : syracuseStep 1086101 = 50911) (by norm_num)
theorem B5509781 : Blo 722323 5509781 := bbase (se 6 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 5509781 = 258271) (by norm_num)
theorem B1086125 : Blo 722323 1086125 := bbase (se 3 (by rfl) ⟨203648, by rfl⟩ : syracuseStep 1086125 = 407297) (by norm_num)
theorem B5083829 : Blo 722323 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B1086149 : Blo 722323 1086149 := bbase (se 4 (by rfl) ⟨101826, by rfl⟩ : syracuseStep 1086149 = 203653) (by norm_num)
theorem B1086173 : Blo 722323 1086173 := bbase (se 3 (by rfl) ⟨203657, by rfl⟩ : syracuseStep 1086173 = 407315) (by norm_num)
theorem B1086197 : Blo 722323 1086197 := bbase (se 5 (by rfl) ⟨50915, by rfl⟩ : syracuseStep 1086197 = 101831) (by norm_num)
theorem B1086221 : Blo 722323 1086221 := bbase (se 3 (by rfl) ⟨203666, by rfl⟩ : syracuseStep 1086221 = 407333) (by norm_num)
theorem B1086245 : Blo 722323 1086245 := bbase (se 4 (by rfl) ⟨101835, by rfl⟩ : syracuseStep 1086245 = 203671) (by norm_num)
theorem B1086269 : Blo 722323 1086269 := bbase (se 3 (by rfl) ⟨203675, by rfl⟩ : syracuseStep 1086269 = 407351) (by norm_num)
theorem B1086293 : Blo 722323 1086293 := bbase (se 9 (by rfl) ⟨3182, by rfl⟩ : syracuseStep 1086293 = 6365) (by norm_num)
theorem B8262485 : Blo 722323 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B1086317 : Blo 722323 1086317 := bbase (se 3 (by rfl) ⟨203684, by rfl⟩ : syracuseStep 1086317 = 407369) (by norm_num)
theorem B1086341 : Blo 722323 1086341 := bbase (se 4 (by rfl) ⟨101844, by rfl⟩ : syracuseStep 1086341 = 203689) (by norm_num)
theorem B1086365 : Blo 722323 1086365 := bbase (se 3 (by rfl) ⟨203693, by rfl⟩ : syracuseStep 1086365 = 407387) (by norm_num)
theorem B1086389 : Blo 722323 1086389 := bbase (se 5 (by rfl) ⟨50924, by rfl⟩ : syracuseStep 1086389 = 101849) (by norm_num)
theorem B1086413 : Blo 722323 1086413 := bbase (se 3 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 1086413 = 407405) (by norm_num)
theorem B1086437 : Blo 722323 1086437 := bbase (se 4 (by rfl) ⟨101853, by rfl⟩ : syracuseStep 1086437 = 203707) (by norm_num)
theorem B1086461 : Blo 722323 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B1086485 : Blo 722323 1086485 := bbase (se 6 (by rfl) ⟨25464, by rfl⟩ : syracuseStep 1086485 = 50929) (by norm_num)
theorem B1086509 : Blo 722323 1086509 := bbase (se 3 (by rfl) ⟨203720, by rfl⟩ : syracuseStep 1086509 = 407441) (by norm_num)
theorem B2757685 : Blo 722323 2757685 := bbase (se 5 (by rfl) ⟨129266, by rfl⟩ : syracuseStep 2757685 = 258533) (by norm_num)
theorem B1086533 : Blo 722323 1086533 := bbase (se 4 (by rfl) ⟨101862, by rfl⟩ : syracuseStep 1086533 = 203725) (by norm_num)
theorem B1086557 : Blo 722323 1086557 := bbase (se 3 (by rfl) ⟨203729, by rfl⟩ : syracuseStep 1086557 = 407459) (by norm_num)
theorem B1086581 : Blo 722323 1086581 := bbase (se 5 (by rfl) ⟨50933, by rfl⟩ : syracuseStep 1086581 = 101867) (by norm_num)
theorem B1086605 : Blo 722323 1086605 := bbase (se 3 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 1086605 = 407477) (by norm_num)
theorem B1086629 : Blo 722323 1086629 := bbase (se 4 (by rfl) ⟨101871, by rfl⟩ : syracuseStep 1086629 = 203743) (by norm_num)
theorem B1086653 : Blo 722323 1086653 := bbase (se 3 (by rfl) ⟨203747, by rfl⟩ : syracuseStep 1086653 = 407495) (by norm_num)
theorem B1086677 : Blo 722323 1086677 := bbase (se 7 (by rfl) ⟨12734, by rfl⟩ : syracuseStep 1086677 = 25469) (by norm_num)
theorem B824537 : Blo 722323 824537 := bbase (se 2 (by rfl) ⟨309201, by rfl⟩ : syracuseStep 824537 = 618403) (by norm_num)
theorem B1086701 : Blo 722323 1086701 := bbase (se 3 (by rfl) ⟨203756, by rfl⟩ : syracuseStep 1086701 = 407513) (by norm_num)
theorem B1086725 : Blo 722323 1086725 := bbase (se 4 (by rfl) ⟨101880, by rfl⟩ : syracuseStep 1086725 = 203761) (by norm_num)
theorem B1086749 : Blo 722323 1086749 := bbase (se 3 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 1086749 = 407531) (by norm_num)
theorem B1086773 : Blo 722323 1086773 := bbase (se 5 (by rfl) ⟨50942, by rfl⟩ : syracuseStep 1086773 = 101885) (by norm_num)
theorem B1086797 : Blo 722323 1086797 := bbase (se 3 (by rfl) ⟨203774, by rfl⟩ : syracuseStep 1086797 = 407549) (by norm_num)
theorem B1086821 : Blo 722323 1086821 := bbase (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) (by norm_num)
theorem B1086845 : Blo 722323 1086845 := bbase (se 3 (by rfl) ⟨203783, by rfl⟩ : syracuseStep 1086845 = 407567) (by norm_num)
theorem B1086869 : Blo 722323 1086869 := bbase (se 6 (by rfl) ⟨25473, by rfl⟩ : syracuseStep 1086869 = 50947) (by norm_num)
theorem B1086893 : Blo 722323 1086893 := bbase (se 3 (by rfl) ⟨203792, by rfl⟩ : syracuseStep 1086893 = 407585) (by norm_num)
theorem B1086917 : Blo 722323 1086917 := bbase (se 4 (by rfl) ⟨101898, by rfl⟩ : syracuseStep 1086917 = 203797) (by norm_num)
theorem B6952405 : Blo 722323 6952405 := bbase (se 7 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 6952405 = 162947) (by norm_num)
theorem B1086941 : Blo 722323 1086941 := bbase (se 3 (by rfl) ⟨203801, by rfl⟩ : syracuseStep 1086941 = 407603) (by norm_num)
theorem B1086965 : Blo 722323 1086965 := bbase (se 5 (by rfl) ⟨50951, by rfl⟩ : syracuseStep 1086965 = 101903) (by norm_num)
theorem B1086989 : Blo 722323 1086989 := bbase (se 3 (by rfl) ⟨203810, by rfl⟩ : syracuseStep 1086989 = 407621) (by norm_num)
theorem B1087013 : Blo 722323 1087013 := bbase (se 4 (by rfl) ⟨101907, by rfl⟩ : syracuseStep 1087013 = 203815) (by norm_num)
theorem B1087037 : Blo 722323 1087037 := bbase (se 3 (by rfl) ⟨203819, by rfl⟩ : syracuseStep 1087037 = 407639) (by norm_num)
theorem B3479125 : Blo 722323 3479125 := bbase (se 8 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 3479125 = 40771) (by norm_num)
theorem B1087061 : Blo 722323 1087061 := bbase (se 8 (by rfl) ⟨6369, by rfl⟩ : syracuseStep 1087061 = 12739) (by norm_num)
theorem B1087085 : Blo 722323 1087085 := bbase (se 3 (by rfl) ⟨203828, by rfl⟩ : syracuseStep 1087085 = 407657) (by norm_num)
theorem B1087109 : Blo 722323 1087109 := bbase (se 4 (by rfl) ⟨101916, by rfl⟩ : syracuseStep 1087109 = 203833) (by norm_num)
theorem B1742485 : Blo 722323 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B1087133 : Blo 722323 1087133 := bbase (se 3 (by rfl) ⟨203837, by rfl⟩ : syracuseStep 1087133 = 407675) (by norm_num)
theorem B1087157 : Blo 722323 1087157 := bbase (se 5 (by rfl) ⟨50960, by rfl⟩ : syracuseStep 1087157 = 101921) (by norm_num)
theorem B1087181 : Blo 722323 1087181 := bbase (se 3 (by rfl) ⟨203846, by rfl⟩ : syracuseStep 1087181 = 407693) (by norm_num)
theorem B1087205 : Blo 722323 1087205 := bbase (se 4 (by rfl) ⟨101925, by rfl⟩ : syracuseStep 1087205 = 203851) (by norm_num)
theorem B1087229 : Blo 722323 1087229 := bbase (se 3 (by rfl) ⟨203855, by rfl⟩ : syracuseStep 1087229 = 407711) (by norm_num)
theorem B1087253 : Blo 722323 1087253 := bbase (se 6 (by rfl) ⟨25482, by rfl⟩ : syracuseStep 1087253 = 50965) (by norm_num)
theorem B1742629 : Blo 722323 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B3675941 : Blo 722323 3675941 := bbase (se 4 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 3675941 = 689239) (by norm_num)
theorem B1087277 : Blo 722323 1087277 := bbase (se 3 (by rfl) ⟨203864, by rfl⟩ : syracuseStep 1087277 = 407729) (by norm_num)
theorem B1087301 : Blo 722323 1087301 := bbase (se 4 (by rfl) ⟨101934, by rfl⟩ : syracuseStep 1087301 = 203869) (by norm_num)
theorem B1087325 : Blo 722323 1087325 := bbase (se 3 (by rfl) ⟨203873, by rfl⟩ : syracuseStep 1087325 = 407747) (by norm_num)
theorem B1087349 : Blo 722323 1087349 := bbase (se 5 (by rfl) ⟨50969, by rfl⟩ : syracuseStep 1087349 = 101939) (by norm_num)
theorem B1087373 : Blo 722323 1087373 := bbase (se 3 (by rfl) ⟨203882, by rfl⟩ : syracuseStep 1087373 = 407765) (by norm_num)
theorem B1546141 : Blo 722323 1546141 := bbase (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) (by norm_num)
theorem B1087397 : Blo 722323 1087397 := bbase (se 4 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 1087397 = 203887) (by norm_num)
theorem B1087421 : Blo 722323 1087421 := bbase (se 3 (by rfl) ⟨203891, by rfl⟩ : syracuseStep 1087421 = 407783) (by norm_num)
theorem B9050069 : Blo 722323 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B1087445 : Blo 722323 1087445 := bbase (se 7 (by rfl) ⟨12743, by rfl⟩ : syracuseStep 1087445 = 25487) (by norm_num)
theorem B1087469 : Blo 722323 1087469 := bbase (se 3 (by rfl) ⟨203900, by rfl⟩ : syracuseStep 1087469 = 407801) (by norm_num)
theorem B1087493 : Blo 722323 1087493 := bbase (se 4 (by rfl) ⟨101952, by rfl⟩ : syracuseStep 1087493 = 203905) (by norm_num)
theorem B1087517 : Blo 722323 1087517 := bbase (se 3 (by rfl) ⟨203909, by rfl⟩ : syracuseStep 1087517 = 407819) (by norm_num)
theorem B1087541 : Blo 722323 1087541 := bbase (se 5 (by rfl) ⟨50978, by rfl⟩ : syracuseStep 1087541 = 101957) (by norm_num)
theorem B1087565 : Blo 722323 1087565 := bbase (se 3 (by rfl) ⟨203918, by rfl⟩ : syracuseStep 1087565 = 407837) (by norm_num)
theorem B1087589 : Blo 722323 1087589 := bbase (se 4 (by rfl) ⟨101961, by rfl⟩ : syracuseStep 1087589 = 203923) (by norm_num)
theorem B4954229 : Blo 722323 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B1087613 : Blo 722323 1087613 := bbase (se 3 (by rfl) ⟨203927, by rfl⟩ : syracuseStep 1087613 = 407855) (by norm_num)
theorem B1087637 : Blo 722323 1087637 := bbase (se 6 (by rfl) ⟨25491, by rfl⟩ : syracuseStep 1087637 = 50983) (by norm_num)
theorem B3184805 : Blo 722323 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B1087661 : Blo 722323 1087661 := bbase (se 3 (by rfl) ⟨203936, by rfl⟩ : syracuseStep 1087661 = 407873) (by norm_num)
theorem B4397237 : Blo 722323 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B1087685 : Blo 722323 1087685 := bbase (se 4 (by rfl) ⟨101970, by rfl⟩ : syracuseStep 1087685 = 203941) (by norm_num)
theorem B1087709 : Blo 722323 1087709 := bbase (se 3 (by rfl) ⟨203945, by rfl⟩ : syracuseStep 1087709 = 407891) (by norm_num)
theorem B1087733 : Blo 722323 1087733 := bbase (se 5 (by rfl) ⟨50987, by rfl⟩ : syracuseStep 1087733 = 101975) (by norm_num)
theorem B1087757 : Blo 722323 1087757 := bbase (se 3 (by rfl) ⟨203954, by rfl⟩ : syracuseStep 1087757 = 407909) (by norm_num)
theorem B1087781 : Blo 722323 1087781 := bbase (se 4 (by rfl) ⟨101979, by rfl⟩ : syracuseStep 1087781 = 203959) (by norm_num)
theorem B1087805 : Blo 722323 1087805 := bbase (se 3 (by rfl) ⟨203963, by rfl⟩ : syracuseStep 1087805 = 407927) (by norm_num)
theorem B3086677 : Blo 722323 3086677 := bbase (se 10 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 3086677 = 9043) (by norm_num)
theorem B1087829 : Blo 722323 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B1087853 : Blo 722323 1087853 := bbase (se 3 (by rfl) ⟨203972, by rfl⟩ : syracuseStep 1087853 = 407945) (by norm_num)
theorem B1087877 : Blo 722323 1087877 := bbase (se 4 (by rfl) ⟨101988, by rfl⟩ : syracuseStep 1087877 = 203977) (by norm_num)
theorem B1743245 : Blo 722323 1743245 := bbase (se 3 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 1743245 = 653717) (by norm_num)
theorem B1087901 : Blo 722323 1087901 := bbase (se 3 (by rfl) ⟨203981, by rfl⟩ : syracuseStep 1087901 = 407963) (by norm_num)
theorem B1218989 : Blo 722323 1218989 := bbase (se 3 (by rfl) ⟨228560, by rfl⟩ : syracuseStep 1218989 = 457121) (by norm_num)
theorem B1087925 : Blo 722323 1087925 := bbase (se 5 (by rfl) ⟨50996, by rfl⟩ : syracuseStep 1087925 = 101993) (by norm_num)
theorem B1087949 : Blo 722323 1087949 := bbase (se 3 (by rfl) ⟨203990, by rfl⟩ : syracuseStep 1087949 = 407981) (by norm_num)
theorem B1087973 : Blo 722323 1087973 := bbase (se 4 (by rfl) ⟨101997, by rfl⟩ : syracuseStep 1087973 = 203995) (by norm_num)
theorem B1087997 : Blo 722323 1087997 := bbase (se 3 (by rfl) ⟨203999, by rfl⟩ : syracuseStep 1087997 = 407999) (by norm_num)
theorem B1088021 : Blo 722323 1088021 := bbase (se 6 (by rfl) ⟨25500, by rfl⟩ : syracuseStep 1088021 = 51001) (by norm_num)
theorem B1219117 : Blo 722323 1219117 := bbase (se 3 (by rfl) ⟨228584, by rfl⟩ : syracuseStep 1219117 = 457169) (by norm_num)
theorem B1088045 : Blo 722323 1088045 := bbase (se 3 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 1088045 = 408017) (by norm_num)
theorem B1088069 : Blo 722323 1088069 := bbase (se 4 (by rfl) ⟨102006, by rfl⟩ : syracuseStep 1088069 = 204013) (by norm_num)
theorem B1088093 : Blo 722323 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B1088117 : Blo 722323 1088117 := bbase (se 5 (by rfl) ⟨51005, by rfl⟩ : syracuseStep 1088117 = 102011) (by norm_num)
theorem B1219205 : Blo 722323 1219205 := bbase (se 4 (by rfl) ⟨114300, by rfl⟩ : syracuseStep 1219205 = 228601) (by norm_num)
theorem B1088141 : Blo 722323 1088141 := bbase (se 3 (by rfl) ⟨204026, by rfl⟩ : syracuseStep 1088141 = 408053) (by norm_num)
theorem B1088165 : Blo 722323 1088165 := bbase (se 4 (by rfl) ⟨102015, by rfl⟩ : syracuseStep 1088165 = 204031) (by norm_num)
theorem B1088189 : Blo 722323 1088189 := bbase (se 3 (by rfl) ⟨204035, by rfl⟩ : syracuseStep 1088189 = 408071) (by norm_num)
theorem B1088213 : Blo 722323 1088213 := bbase (se 7 (by rfl) ⟨12752, by rfl⟩ : syracuseStep 1088213 = 25505) (by norm_num)
theorem B1743581 : Blo 722323 1743581 := bbase (se 3 (by rfl) ⟨326921, by rfl⟩ : syracuseStep 1743581 = 653843) (by norm_num)
theorem B1088237 : Blo 722323 1088237 := bbase (se 3 (by rfl) ⟨204044, by rfl⟩ : syracuseStep 1088237 = 408089) (by norm_num)
theorem B1219333 : Blo 722323 1219333 := bbase (se 4 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 1219333 = 228625) (by norm_num)
theorem B1088261 : Blo 722323 1088261 := bbase (se 4 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 1088261 = 204049) (by norm_num)
theorem B1547029 : Blo 722323 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B1088285 : Blo 722323 1088285 := bbase (se 3 (by rfl) ⟨204053, by rfl⟩ : syracuseStep 1088285 = 408107) (by norm_num)
theorem B1088309 : Blo 722323 1088309 := bbase (se 5 (by rfl) ⟨51014, by rfl⟩ : syracuseStep 1088309 = 102029) (by norm_num)
theorem B1743677 : Blo 722323 1743677 := bbase (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) (by norm_num)
theorem B1088333 : Blo 722323 1088333 := bbase (se 3 (by rfl) ⟨204062, by rfl⟩ : syracuseStep 1088333 = 408125) (by norm_num)
theorem B1219421 : Blo 722323 1219421 := bbase (se 3 (by rfl) ⟨228641, by rfl⟩ : syracuseStep 1219421 = 457283) (by norm_num)
theorem B1088357 : Blo 722323 1088357 := bbase (se 4 (by rfl) ⟨102033, by rfl⟩ : syracuseStep 1088357 = 204067) (by norm_num)
theorem B1088381 : Blo 722323 1088381 := bbase (se 3 (by rfl) ⟨204071, by rfl⟩ : syracuseStep 1088381 = 408143) (by norm_num)
theorem B1088405 : Blo 722323 1088405 := bbase (se 6 (by rfl) ⟨25509, by rfl⟩ : syracuseStep 1088405 = 51019) (by norm_num)
theorem B1088429 : Blo 722323 1088429 := bbase (se 3 (by rfl) ⟨204080, by rfl⟩ : syracuseStep 1088429 = 408161) (by norm_num)
theorem B1088453 : Blo 722323 1088453 := bbase (se 4 (by rfl) ⟨102042, by rfl⟩ : syracuseStep 1088453 = 204085) (by norm_num)
theorem B1219549 : Blo 722323 1219549 := bbase (se 3 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 1219549 = 457331) (by norm_num)
theorem B1088477 : Blo 722323 1088477 := bbase (se 3 (by rfl) ⟨204089, by rfl⟩ : syracuseStep 1088477 = 408179) (by norm_num)
theorem B1088501 : Blo 722323 1088501 := bbase (se 5 (by rfl) ⟨51023, by rfl⟩ : syracuseStep 1088501 = 102047) (by norm_num)
theorem B1743869 : Blo 722323 1743869 := bbase (se 3 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 1743869 = 653951) (by norm_num)
theorem B1088525 : Blo 722323 1088525 := bbase (se 3 (by rfl) ⟨204098, by rfl⟩ : syracuseStep 1088525 = 408197) (by norm_num)
theorem B1088549 : Blo 722323 1088549 := bbase (se 4 (by rfl) ⟨102051, by rfl⟩ : syracuseStep 1088549 = 204103) (by norm_num)
theorem B1219637 : Blo 722323 1219637 := bbase (se 5 (by rfl) ⟨57170, by rfl⟩ : syracuseStep 1219637 = 114341) (by norm_num)
theorem B1088573 : Blo 722323 1088573 := bbase (se 3 (by rfl) ⟨204107, by rfl⟩ : syracuseStep 1088573 = 408215) (by norm_num)
theorem B1088597 : Blo 722323 1088597 := bbase (se 8 (by rfl) ⟨6378, by rfl⟩ : syracuseStep 1088597 = 12757) (by norm_num)
theorem B1088621 : Blo 722323 1088621 := bbase (se 3 (by rfl) ⟨204116, by rfl⟩ : syracuseStep 1088621 = 408233) (by norm_num)
theorem B1088645 : Blo 722323 1088645 := bbase (se 4 (by rfl) ⟨102060, by rfl⟩ : syracuseStep 1088645 = 204121) (by norm_num)
theorem B1088669 : Blo 722323 1088669 := bbase (se 3 (by rfl) ⟨204125, by rfl⟩ : syracuseStep 1088669 = 408251) (by norm_num)
theorem B1219765 : Blo 722323 1219765 := bbase (se 5 (by rfl) ⟨57176, by rfl⟩ : syracuseStep 1219765 = 114353) (by norm_num)
theorem B1088693 : Blo 722323 1088693 := bbase (se 5 (by rfl) ⟨51032, by rfl⟩ : syracuseStep 1088693 = 102065) (by norm_num)
theorem B1088717 : Blo 722323 1088717 := bbase (se 3 (by rfl) ⟨204134, by rfl⟩ : syracuseStep 1088717 = 408269) (by norm_num)
theorem B1088741 : Blo 722323 1088741 := bbase (se 4 (by rfl) ⟨102069, by rfl⟩ : syracuseStep 1088741 = 204139) (by norm_num)
theorem B1088765 : Blo 722323 1088765 := bbase (se 3 (by rfl) ⟨204143, by rfl⟩ : syracuseStep 1088765 = 408287) (by norm_num)
theorem B1547525 : Blo 722323 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B1219853 : Blo 722323 1219853 := bbase (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) (by norm_num)
theorem B1088789 : Blo 722323 1088789 := bbase (se 6 (by rfl) ⟨25518, by rfl⟩ : syracuseStep 1088789 = 51037) (by norm_num)
theorem B1088813 : Blo 722323 1088813 := bbase (se 3 (by rfl) ⟨204152, by rfl⟩ : syracuseStep 1088813 = 408305) (by norm_num)
theorem B1088837 : Blo 722323 1088837 := bbase (se 4 (by rfl) ⟨102078, by rfl⟩ : syracuseStep 1088837 = 204157) (by norm_num)
theorem B1088861 : Blo 722323 1088861 := bbase (se 3 (by rfl) ⟨204161, by rfl⟩ : syracuseStep 1088861 = 408323) (by norm_num)
theorem B1088885 : Blo 722323 1088885 := bbase (se 5 (by rfl) ⟨51041, by rfl⟩ : syracuseStep 1088885 = 102083) (by norm_num)
theorem B1219981 : Blo 722323 1219981 := bbase (se 3 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 1219981 = 457493) (by norm_num)
theorem B1088909 : Blo 722323 1088909 := bbase (se 3 (by rfl) ⟨204170, by rfl⟩ : syracuseStep 1088909 = 408341) (by norm_num)
theorem B10722709 : Blo 722323 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B826777 : Blo 722323 826777 := bbase (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) (by norm_num)
theorem B826781 : Blo 722323 826781 := bbase (se 3 (by rfl) ⟨155021, by rfl⟩ : syracuseStep 826781 = 310043) (by norm_num)
theorem B1088933 : Blo 722323 1088933 := bbase (se 4 (by rfl) ⟨102087, by rfl⟩ : syracuseStep 1088933 = 204175) (by norm_num)
theorem B1088957 : Blo 722323 1088957 := bbase (se 3 (by rfl) ⟨204179, by rfl⟩ : syracuseStep 1088957 = 408359) (by norm_num)
theorem B1088981 : Blo 722323 1088981 := bbase (se 7 (by rfl) ⟨12761, by rfl⟩ : syracuseStep 1088981 = 25523) (by norm_num)
theorem B1220069 : Blo 722323 1220069 := bbase (se 4 (by rfl) ⟨114381, by rfl⟩ : syracuseStep 1220069 = 228763) (by norm_num)
theorem B1089005 : Blo 722323 1089005 := bbase (se 3 (by rfl) ⟨204188, by rfl⟩ : syracuseStep 1089005 = 408377) (by norm_num)
theorem B1089029 : Blo 722323 1089029 := bbase (se 4 (by rfl) ⟨102096, by rfl⟩ : syracuseStep 1089029 = 204193) (by norm_num)
theorem B1089053 : Blo 722323 1089053 := bbase (se 3 (by rfl) ⟨204197, by rfl⟩ : syracuseStep 1089053 = 408395) (by norm_num)
theorem B1089077 : Blo 722323 1089077 := bbase (se 5 (by rfl) ⟨51050, by rfl⟩ : syracuseStep 1089077 = 102101) (by norm_num)
theorem B1089101 : Blo 722323 1089101 := bbase (se 3 (by rfl) ⟨204206, by rfl⟩ : syracuseStep 1089101 = 408413) (by norm_num)
theorem B1220197 : Blo 722323 1220197 := bbase (se 4 (by rfl) ⟨114393, by rfl⟩ : syracuseStep 1220197 = 228787) (by norm_num)
theorem B1089125 : Blo 722323 1089125 := bbase (se 4 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 1089125 = 204211) (by norm_num)
theorem B1089149 : Blo 722323 1089149 := bbase (se 3 (by rfl) ⟨204215, by rfl⟩ : syracuseStep 1089149 = 408431) (by norm_num)
theorem B1089173 : Blo 722323 1089173 := bbase (se 6 (by rfl) ⟨25527, by rfl⟩ : syracuseStep 1089173 = 51055) (by norm_num)
theorem B1089197 : Blo 722323 1089197 := bbase (se 3 (by rfl) ⟨204224, by rfl⟩ : syracuseStep 1089197 = 408449) (by norm_num)
theorem B1220285 : Blo 722323 1220285 := bbase (se 3 (by rfl) ⟨228803, by rfl⟩ : syracuseStep 1220285 = 457607) (by norm_num)
theorem B1089221 : Blo 722323 1089221 := bbase (se 4 (by rfl) ⟨102114, by rfl⟩ : syracuseStep 1089221 = 204229) (by norm_num)
theorem B1089245 : Blo 722323 1089245 := bbase (se 3 (by rfl) ⟨204233, by rfl⟩ : syracuseStep 1089245 = 408467) (by norm_num)
theorem B1089269 : Blo 722323 1089269 := bbase (se 5 (by rfl) ⟨51059, by rfl⟩ : syracuseStep 1089269 = 102119) (by norm_num)
theorem B1089293 : Blo 722323 1089293 := bbase (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) (by norm_num)
theorem B3088165 : Blo 722323 3088165 := bbase (se 4 (by rfl) ⟨289515, by rfl⟩ : syracuseStep 3088165 = 579031) (by norm_num)
theorem B1089317 : Blo 722323 1089317 := bbase (se 4 (by rfl) ⟨102123, by rfl⟩ : syracuseStep 1089317 = 204247) (by norm_num)
theorem B3088181 : Blo 722323 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B1220413 : Blo 722323 1220413 := bbase (se 3 (by rfl) ⟨228827, by rfl⟩ : syracuseStep 1220413 = 457655) (by norm_num)
theorem B1089341 : Blo 722323 1089341 := bbase (se 3 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 1089341 = 408503) (by norm_num)
theorem B1089365 : Blo 722323 1089365 := bbase (se 9 (by rfl) ⟨3191, by rfl⟩ : syracuseStep 1089365 = 6383) (by norm_num)
theorem B2236261 : Blo 722323 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B1089389 : Blo 722323 1089389 := bbase (se 3 (by rfl) ⟨204260, by rfl⟩ : syracuseStep 1089389 = 408521) (by norm_num)
theorem B1089413 : Blo 722323 1089413 := bbase (se 4 (by rfl) ⟨102132, by rfl⟩ : syracuseStep 1089413 = 204265) (by norm_num)
theorem B1220501 : Blo 722323 1220501 := bbase (se 6 (by rfl) ⟨28605, by rfl⟩ : syracuseStep 1220501 = 57211) (by norm_num)
theorem B1089437 : Blo 722323 1089437 := bbase (se 3 (by rfl) ⟨204269, by rfl⟩ : syracuseStep 1089437 = 408539) (by norm_num)
theorem B1089461 : Blo 722323 1089461 := bbase (se 5 (by rfl) ⟨51068, by rfl⟩ : syracuseStep 1089461 = 102137) (by norm_num)
theorem B1089485 : Blo 722323 1089485 := bbase (se 3 (by rfl) ⟨204278, by rfl⟩ : syracuseStep 1089485 = 408557) (by norm_num)
theorem B794629 : Blo 722323 794629 := bbase (se 4 (by rfl) ⟨74496, by rfl⟩ : syracuseStep 794629 = 148993) (by norm_num)
theorem B1220629 : Blo 722323 1220629 := bbase (se 6 (by rfl) ⟨28608, by rfl⟩ : syracuseStep 1220629 = 57217) (by norm_num)
theorem B1548389 : Blo 722323 1548389 := bbase (se 4 (by rfl) ⟨145161, by rfl⟩ : syracuseStep 1548389 = 290323) (by norm_num)
theorem B1220717 : Blo 722323 1220717 := bbase (se 3 (by rfl) ⟨228884, by rfl⟩ : syracuseStep 1220717 = 457769) (by norm_num)
theorem B1745021 : Blo 722323 1745021 := bbase (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) (by norm_num)
theorem B1220845 : Blo 722323 1220845 := bbase (se 3 (by rfl) ⟨228908, by rfl⟩ : syracuseStep 1220845 = 457817) (by norm_num)
theorem B6955253 : Blo 722323 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B1548533 : Blo 722323 1548533 := bbase (se 5 (by rfl) ⟨72587, by rfl⟩ : syracuseStep 1548533 = 145175) (by norm_num)
theorem B827653 : Blo 722323 827653 := bbase (se 4 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 827653 = 155185) (by norm_num)
theorem B1220933 : Blo 722323 1220933 := bbase (se 4 (by rfl) ⟨114462, by rfl⟩ : syracuseStep 1220933 = 228925) (by norm_num)
theorem B2203973 : Blo 722323 2203973 := bbase (se 4 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 2203973 = 413245) (by norm_num)
theorem B1221061 : Blo 722323 1221061 := bbase (se 4 (by rfl) ⟨114474, by rfl⟩ : syracuseStep 1221061 = 228949) (by norm_num)
theorem B1221149 : Blo 722323 1221149 := bbase (se 3 (by rfl) ⟨228965, by rfl⟩ : syracuseStep 1221149 = 457931) (by norm_num)
theorem B1221277 : Blo 722323 1221277 := bbase (se 3 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 1221277 = 457979) (by norm_num)
theorem B1221365 : Blo 722323 1221365 := bbase (se 5 (by rfl) ⟨57251, by rfl⟩ : syracuseStep 1221365 = 114503) (by norm_num)
theorem B1221493 : Blo 722323 1221493 := bbase (se 5 (by rfl) ⟨57257, by rfl⟩ : syracuseStep 1221493 = 114515) (by norm_num)
theorem B1221581 : Blo 722323 1221581 := bbase (se 3 (by rfl) ⟨229046, by rfl⟩ : syracuseStep 1221581 = 458093) (by norm_num)
theorem B1549277 : Blo 722323 1549277 := bbase (se 3 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 1549277 = 580979) (by norm_num)
theorem B1221709 : Blo 722323 1221709 := bbase (se 3 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 1221709 = 458141) (by norm_num)
theorem B1221797 : Blo 722323 1221797 := bbase (se 4 (by rfl) ⟨114543, by rfl⟩ : syracuseStep 1221797 = 229087) (by norm_num)
theorem B3712229 : Blo 722323 3712229 := bbase (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) (by norm_num)
theorem B1221925 : Blo 722323 1221925 := bbase (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) (by norm_num)
theorem B1222013 : Blo 722323 1222013 := bbase (se 3 (by rfl) ⟨229127, by rfl⟩ : syracuseStep 1222013 = 458255) (by norm_num)
theorem B2860469 : Blo 722323 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B1222141 : Blo 722323 1222141 := bbase (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) (by norm_num)
theorem B927265 : Blo 722323 927265 := bbase (se 2 (by rfl) ⟨347724, by rfl⟩ : syracuseStep 927265 = 695449) (by norm_num)
theorem B1648181 : Blo 722323 1648181 := bbase (se 5 (by rfl) ⟨77258, by rfl⟩ : syracuseStep 1648181 = 154517) (by norm_num)
theorem B1222229 : Blo 722323 1222229 := bbase (se 8 (by rfl) ⟨7161, by rfl⟩ : syracuseStep 1222229 = 14323) (by norm_num)
theorem B1550029 : Blo 722323 1550029 := bbase (se 3 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 1550029 = 581261) (by norm_num)
theorem B1222357 : Blo 722323 1222357 := bbase (se 7 (by rfl) ⟨14324, by rfl⟩ : syracuseStep 1222357 = 28649) (by norm_num)
theorem B1189621 : Blo 722323 1189621 := bbase (se 5 (by rfl) ⟨55763, by rfl⟩ : syracuseStep 1189621 = 111527) (by norm_num)
theorem B1222445 : Blo 722323 1222445 := bbase (se 3 (by rfl) ⟨229208, by rfl⟩ : syracuseStep 1222445 = 458417) (by norm_num)
theorem B6596437 : Blo 722323 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B1550173 : Blo 722323 1550173 := bbase (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) (by norm_num)
theorem B1222573 : Blo 722323 1222573 := bbase (se 3 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 1222573 = 458465) (by norm_num)
theorem B3090437 : Blo 722323 3090437 := bbase (se 4 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 3090437 = 579457) (by norm_num)
theorem B1222661 : Blo 722323 1222661 := bbase (se 4 (by rfl) ⟨114624, by rfl⟩ : syracuseStep 1222661 = 229249) (by norm_num)
theorem B1222789 : Blo 722323 1222789 := bbase (se 4 (by rfl) ⟨114636, by rfl⟩ : syracuseStep 1222789 = 229273) (by norm_num)
theorem B3582133 : Blo 722323 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B1550549 : Blo 722323 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B1222877 : Blo 722323 1222877 := bbase (se 3 (by rfl) ⟨229289, by rfl⟩ : syracuseStep 1222877 = 458579) (by norm_num)
theorem B11741525 : Blo 722323 11741525 := bbase (se 10 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 11741525 = 34399) (by norm_num)
theorem B1223005 : Blo 722323 1223005 := bbase (se 3 (by rfl) ⟨229313, by rfl⟩ : syracuseStep 1223005 = 458627) (by norm_num)
theorem B1223093 : Blo 722323 1223093 := bbase (se 5 (by rfl) ⟨57332, by rfl⟩ : syracuseStep 1223093 = 114665) (by norm_num)
theorem B1157581 : Blo 722323 1157581 := bbase (se 3 (by rfl) ⟨217046, by rfl⟩ : syracuseStep 1157581 = 434093) (by norm_num)
theorem B1223221 : Blo 722323 1223221 := bbase (se 5 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 1223221 = 114677) (by norm_num)
theorem B1550917 : Blo 722323 1550917 := bbase (se 4 (by rfl) ⟨145398, by rfl⟩ : syracuseStep 1550917 = 290797) (by norm_num)
theorem B1223309 : Blo 722323 1223309 := bbase (se 3 (by rfl) ⟨229370, by rfl⟩ : syracuseStep 1223309 = 458741) (by norm_num)
theorem B1223437 : Blo 722323 1223437 := bbase (se 3 (by rfl) ⟨229394, by rfl⟩ : syracuseStep 1223437 = 458789) (by norm_num)
theorem B928609 : Blo 722323 928609 := bbase (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) (by norm_num)
theorem B1223525 : Blo 722323 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B2206597 : Blo 722323 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B1223653 : Blo 722323 1223653 := bbase (se 4 (by rfl) ⟨114717, by rfl⟩ : syracuseStep 1223653 = 229435) (by norm_num)
theorem B1158133 : Blo 722323 1158133 := bbase (se 5 (by rfl) ⟨54287, by rfl⟩ : syracuseStep 1158133 = 108575) (by norm_num)
theorem B1223741 : Blo 722323 1223741 := bbase (se 3 (by rfl) ⟨229451, by rfl⟩ : syracuseStep 1223741 = 458903) (by norm_num)
theorem B732241 : Blo 722323 732241 := bbase (se 2 (by rfl) ⟨274590, by rfl⟩ : syracuseStep 732241 = 549181) (by norm_num)
theorem B1223869 : Blo 722323 1223869 := bbase (se 3 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 1223869 = 458951) (by norm_num)
theorem B1158389 : Blo 722323 1158389 := bbase (se 5 (by rfl) ⟨54299, by rfl⟩ : syracuseStep 1158389 = 108599) (by norm_num)
theorem B1649933 : Blo 722323 1649933 := bbase (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) (by norm_num)
theorem B1223957 : Blo 722323 1223957 := bbase (se 6 (by rfl) ⟨28686, by rfl⟩ : syracuseStep 1223957 = 57373) (by norm_num)
theorem B5221685 : Blo 722323 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B3485045 : Blo 722323 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B1224085 : Blo 722323 1224085 := bbase (se 6 (by rfl) ⟨28689, by rfl⟩ : syracuseStep 1224085 = 57379) (by norm_num)
theorem B1224173 : Blo 722323 1224173 := bbase (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) (by norm_num)
theorem B1224301 : Blo 722323 1224301 := bbase (se 3 (by rfl) ⟨229556, by rfl⟩ : syracuseStep 1224301 = 459113) (by norm_num)
theorem B1224389 : Blo 722323 1224389 := bbase (se 4 (by rfl) ⟨114786, by rfl⟩ : syracuseStep 1224389 = 229573) (by norm_num)
theorem B1224517 : Blo 722323 1224517 := bbase (se 4 (by rfl) ⟨114798, by rfl⟩ : syracuseStep 1224517 = 229597) (by norm_num)
theorem B1224605 : Blo 722323 1224605 := bbase (se 3 (by rfl) ⟨229613, by rfl⟩ : syracuseStep 1224605 = 459227) (by norm_num)
theorem B1159093 : Blo 722323 1159093 := bbase (se 5 (by rfl) ⟨54332, by rfl⟩ : syracuseStep 1159093 = 108665) (by norm_num)
theorem B3715013 : Blo 722323 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B1224733 : Blo 722323 1224733 := bbase (se 3 (by rfl) ⟨229637, by rfl⟩ : syracuseStep 1224733 = 459275) (by norm_num)
theorem B1224821 : Blo 722323 1224821 := bbase (se 5 (by rfl) ⟨57413, by rfl⟩ : syracuseStep 1224821 = 114827) (by norm_num)
theorem B733421 : Blo 722323 733421 := bbase (se 3 (by rfl) ⟨137516, by rfl⟩ : syracuseStep 733421 = 275033) (by norm_num)
theorem B1224949 : Blo 722323 1224949 := bbase (se 5 (by rfl) ⟨57419, by rfl⟩ : syracuseStep 1224949 = 114839) (by norm_num)
theorem B1225037 : Blo 722323 1225037 := bbase (se 3 (by rfl) ⟨229694, by rfl⟩ : syracuseStep 1225037 = 459389) (by norm_num)
theorem B1159517 : Blo 722323 1159517 := bbase (se 3 (by rfl) ⟨217409, by rfl⟩ : syracuseStep 1159517 = 434819) (by norm_num)
theorem B1028477 : Blo 722323 1028477 := bbase (se 3 (by rfl) ⟨192839, by rfl⟩ : syracuseStep 1028477 = 385679) (by norm_num)
theorem B13250965 : Blo 722323 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B2929061 : Blo 722323 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B1225165 : Blo 722323 1225165 := bbase (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) (by norm_num)
theorem B1225253 : Blo 722323 1225253 := bbase (se 4 (by rfl) ⟨114867, by rfl⟩ : syracuseStep 1225253 = 229735) (by norm_num)
theorem B1159805 : Blo 722323 1159805 := bbase (se 3 (by rfl) ⟨217463, by rfl⟩ : syracuseStep 1159805 = 434927) (by norm_num)
theorem B1225381 : Blo 722323 1225381 := bbase (se 4 (by rfl) ⟨114879, by rfl⟩ : syracuseStep 1225381 = 229759) (by norm_num)
theorem B766657 : Blo 722323 766657 := bbase (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) (by norm_num)
theorem B1651445 : Blo 722323 1651445 := bbase (se 5 (by rfl) ⟨77411, by rfl⟩ : syracuseStep 1651445 = 154823) (by norm_num)
theorem B1225469 : Blo 722323 1225469 := bbase (se 3 (by rfl) ⟨229775, by rfl⟩ : syracuseStep 1225469 = 459551) (by norm_num)
theorem B1160029 : Blo 722323 1160029 := bbase (se 3 (by rfl) ⟨217505, by rfl⟩ : syracuseStep 1160029 = 435011) (by norm_num)
theorem B1225597 : Blo 722323 1225597 := bbase (se 3 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 1225597 = 459599) (by norm_num)
theorem B734089 : Blo 722323 734089 := bbase (se 2 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 734089 = 550567) (by norm_num)
theorem B734105 : Blo 722323 734105 := bbase (se 2 (by rfl) ⟨275289, by rfl⟩ : syracuseStep 734105 = 550579) (by norm_num)
theorem B1029029 : Blo 722323 1029029 := bbase (se 4 (by rfl) ⟨96471, by rfl⟩ : syracuseStep 1029029 = 192943) (by norm_num)
theorem B4633685 : Blo 722323 4633685 := bbase (se 8 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 4633685 = 54301) (by norm_num)
theorem B2438261 : Blo 722323 2438261 := bbase (se 5 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 2438261 = 228587) (by norm_num)
theorem B5027093 : Blo 722323 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B9385237 : Blo 722323 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B734653 : Blo 722323 734653 := bbase (se 3 (by rfl) ⟨137747, by rfl⟩ : syracuseStep 734653 = 275495) (by norm_num)
theorem B1258973 : Blo 722323 1258973 := bbase (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) (by norm_num)
theorem B2438693 : Blo 722323 2438693 := bbase (se 4 (by rfl) ⟨228627, by rfl⟩ : syracuseStep 2438693 = 457255) (by norm_num)
theorem B1652285 : Blo 722323 1652285 := bbase (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) (by norm_num)
theorem B1029781 : Blo 722323 1029781 := bbase (se 6 (by rfl) ⟨24135, by rfl⟩ : syracuseStep 1029781 = 48271) (by norm_num)
theorem B734933 : Blo 722323 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B5486453 : Blo 722323 5486453 := bbase (se 5 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 5486453 = 514355) (by norm_num)
theorem B3094469 : Blo 722323 3094469 := bbase (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) (by norm_num)
theorem B1161157 : Blo 722323 1161157 := bbase (se 4 (by rfl) ⟨108858, by rfl⟩ : syracuseStep 1161157 = 217717) (by norm_num)
theorem B2439125 : Blo 722323 2439125 := bbase (se 7 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 2439125 = 57167) (by norm_num)
theorem B735193 : Blo 722323 735193 := bbase (se 2 (by rfl) ⟨275697, by rfl⟩ : syracuseStep 735193 = 551395) (by norm_num)
theorem B5224661 : Blo 722323 5224661 := bbase (se 7 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 5224661 = 122453) (by norm_num)
theorem B735517 : Blo 722323 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B735565 : Blo 722323 735565 := bbase (se 3 (by rfl) ⟨137918, by rfl⟩ : syracuseStep 735565 = 275837) (by norm_num)
theorem B2439557 : Blo 722323 2439557 := bbase (se 4 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 2439557 = 457417) (by norm_num)
theorem B1161605 : Blo 722323 1161605 := bbase (se 4 (by rfl) ⟨108900, by rfl⟩ : syracuseStep 1161605 = 217801) (by norm_num)
theorem B1030573 : Blo 722323 1030573 := bbase (se 3 (by rfl) ⟨193232, by rfl⟩ : syracuseStep 1030573 = 386465) (by norm_num)
theorem B3488197 : Blo 722323 3488197 := bbase (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) (by norm_num)
theorem B3357317 : Blo 722323 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B1784533 : Blo 722323 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B1030909 : Blo 722323 1030909 := bbase (se 3 (by rfl) ⟨193295, by rfl⟩ : syracuseStep 1030909 = 386591) (by norm_num)
theorem B1325821 : Blo 722323 1325821 := bbase (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) (by norm_num)
theorem B6175541 : Blo 722323 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B2439989 : Blo 722323 2439989 := bbase (se 5 (by rfl) ⟨114374, by rfl⟩ : syracuseStep 2439989 = 228749) (by norm_num)
theorem B2931653 : Blo 722323 2931653 := bbase (se 4 (by rfl) ⟨274842, by rfl⟩ : syracuseStep 2931653 = 549685) (by norm_num)
theorem B1031125 : Blo 722323 1031125 := bbase (se 7 (by rfl) ⟨12083, by rfl⟩ : syracuseStep 1031125 = 24167) (by norm_num)
theorem B1653853 : Blo 722323 1653853 := bbase (se 3 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 1653853 = 620195) (by norm_num)
theorem B2440421 : Blo 722323 2440421 := bbase (se 4 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 2440421 = 457579) (by norm_num)
theorem B1031501 : Blo 722323 1031501 := bbase (se 3 (by rfl) ⟨193406, by rfl⟩ : syracuseStep 1031501 = 386813) (by norm_num)
theorem B11124053 : Blo 722323 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B2440853 : Blo 722323 2440853 := bbase (se 6 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 2440853 = 114415) (by norm_num)
theorem B868009 : Blo 722323 868009 := bbase (se 2 (by rfl) ⟨325503, by rfl⟩ : syracuseStep 868009 = 651007) (by norm_num)
theorem B3096245 : Blo 722323 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B1163117 : Blo 722323 1163117 := bbase (se 3 (by rfl) ⟨218084, by rfl⟩ : syracuseStep 1163117 = 436169) (by norm_num)
theorem B1163245 : Blo 722323 1163245 := bbase (se 3 (by rfl) ⟨218108, by rfl⟩ : syracuseStep 1163245 = 436217) (by norm_num)
theorem B2441285 : Blo 722323 2441285 := bbase (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) (by norm_num)
theorem B4636885 : Blo 722323 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B2441717 : Blo 722323 2441717 := bbase (se 5 (by rfl) ⟨114455, by rfl⟩ : syracuseStep 2441717 = 228911) (by norm_num)
theorem B868897 : Blo 722323 868897 := bbase (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) (by norm_num)
theorem B3097237 : Blo 722323 3097237 := bbase (se 6 (by rfl) ⟨72591, by rfl⟩ : syracuseStep 3097237 = 145183) (by norm_num)
theorem B836249 : Blo 722323 836249 := bbase (se 2 (by rfl) ⟨313593, by rfl⟩ : syracuseStep 836249 = 627187) (by norm_num)
theorem B1032925 : Blo 722323 1032925 := bbase (se 3 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 1032925 = 387347) (by norm_num)
theorem B2474869 : Blo 722323 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B2442149 : Blo 722323 2442149 := bbase (se 4 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 2442149 = 457903) (by norm_num)
theorem B1098677 : Blo 722323 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B2933941 : Blo 722323 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1033517 : Blo 722323 1033517 := bbase (se 3 (by rfl) ⟨193784, by rfl⟩ : syracuseStep 1033517 = 387569) (by norm_num)
theorem B2934085 : Blo 722323 2934085 := bbase (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) (by norm_num)
theorem B2442581 : Blo 722323 2442581 := bbase (se 12 (by rfl) ⟨894, by rfl⟩ : syracuseStep 2442581 = 1789) (by norm_num)
theorem B1033597 : Blo 722323 1033597 := bbase (se 3 (by rfl) ⟨193799, by rfl⟩ : syracuseStep 1033597 = 387599) (by norm_num)
theorem B1033717 : Blo 722323 1033717 := bbase (se 5 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 1033717 = 96911) (by norm_num)
theorem B3720725 : Blo 722323 3720725 := bbase (se 6 (by rfl) ⟨87204, by rfl⟩ : syracuseStep 3720725 = 174409) (by norm_num)
theorem B869945 : Blo 722323 869945 := bbase (se 2 (by rfl) ⟨326229, by rfl⟩ : syracuseStep 869945 = 652459) (by norm_num)
theorem B1033813 : Blo 722323 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B6178517 : Blo 722323 6178517 := bbase (se 7 (by rfl) ⟨72404, by rfl⟩ : syracuseStep 6178517 = 144809) (by norm_num)
theorem B2443013 : Blo 722323 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B2475845 : Blo 722323 2475845 := bbase (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) (by norm_num)
theorem B771977 : Blo 722323 771977 := bbase (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) (by norm_num)
theorem B870301 : Blo 722323 870301 := bbase (se 3 (by rfl) ⟨163181, by rfl⟩ : syracuseStep 870301 = 326363) (by norm_num)
theorem B3917909 : Blo 722323 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B870493 : Blo 722323 870493 := bbase (se 3 (by rfl) ⟨163217, by rfl⟩ : syracuseStep 870493 = 326435) (by norm_num)
theorem B4180085 : Blo 722323 4180085 := bbase (se 5 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 4180085 = 391883) (by norm_num)
theorem B2443445 : Blo 722323 2443445 := bbase (se 5 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 2443445 = 229073) (by norm_num)
theorem B870637 : Blo 722323 870637 := bbase (se 3 (by rfl) ⟨163244, by rfl⟩ : syracuseStep 870637 = 326489) (by norm_num)
theorem B772421 : Blo 722323 772421 := bbase (se 4 (by rfl) ⟨72414, by rfl⟩ : syracuseStep 772421 = 144829) (by norm_num)
theorem B2574773 : Blo 722323 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B4180405 : Blo 722323 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B772669 : Blo 722323 772669 := bbase (se 3 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 772669 = 289751) (by norm_num)
theorem B3820117 : Blo 722323 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B2443877 : Blo 722323 2443877 := bbase (se 4 (by rfl) ⟨229113, by rfl⟩ : syracuseStep 2443877 = 458227) (by norm_num)
theorem B1100477 : Blo 722323 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B1395533 : Blo 722323 1395533 := bbase (se 3 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 1395533 = 523325) (by norm_num)
theorem B4410325 : Blo 722323 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B773101 : Blo 722323 773101 := bbase (se 3 (by rfl) ⟨144956, by rfl⟩ : syracuseStep 773101 = 289913) (by norm_num)
theorem B2444309 : Blo 722323 2444309 := bbase (se 6 (by rfl) ⟨57288, by rfl⟩ : syracuseStep 2444309 = 114577) (by norm_num)
theorem B773173 : Blo 722323 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B1625237 : Blo 722323 1625237 := bbase (se 6 (by rfl) ⟨38091, by rfl⟩ : syracuseStep 1625237 = 76183) (by norm_num)
theorem B1625309 : Blo 722323 1625309 := bbase (se 3 (by rfl) ⟨304745, by rfl⟩ : syracuseStep 1625309 = 609491) (by norm_num)
theorem B1101061 : Blo 722323 1101061 := bbase (se 4 (by rfl) ⟨103224, by rfl⟩ : syracuseStep 1101061 = 206449) (by norm_num)
theorem B1625381 : Blo 722323 1625381 := bbase (se 4 (by rfl) ⟨152379, by rfl⟩ : syracuseStep 1625381 = 304759) (by norm_num)
theorem B1625453 : Blo 722323 1625453 := bbase (se 3 (by rfl) ⟨304772, by rfl⟩ : syracuseStep 1625453 = 609545) (by norm_num)
theorem B773545 : Blo 722323 773545 := bbase (se 2 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 773545 = 580159) (by norm_num)
theorem B1625525 : Blo 722323 1625525 := bbase (se 5 (by rfl) ⟨76196, by rfl⟩ : syracuseStep 1625525 = 152393) (by norm_num)
theorem B2444741 : Blo 722323 2444741 := bbase (se 4 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 2444741 = 458389) (by norm_num)
theorem B1101269 : Blo 722323 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B1625597 : Blo 722323 1625597 := bbase (se 3 (by rfl) ⟨304799, by rfl⟩ : syracuseStep 1625597 = 609599) (by norm_num)
theorem B1625669 : Blo 722323 1625669 := bbase (se 4 (by rfl) ⟨152406, by rfl⟩ : syracuseStep 1625669 = 304813) (by norm_num)
theorem B1625741 : Blo 722323 1625741 := bbase (se 3 (by rfl) ⟨304826, by rfl⟩ : syracuseStep 1625741 = 609653) (by norm_num)
theorem B1953461 : Blo 722323 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B1855157 : Blo 722323 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B1625813 : Blo 722323 1625813 := bbase (se 7 (by rfl) ⟨19052, by rfl⟩ : syracuseStep 1625813 = 38105) (by norm_num)
theorem B872165 : Blo 722323 872165 := bbase (se 4 (by rfl) ⟨81765, by rfl⟩ : syracuseStep 872165 = 163531) (by norm_num)
theorem B1625885 : Blo 722323 1625885 := bbase (se 3 (by rfl) ⟨304853, by rfl⟩ : syracuseStep 1625885 = 609707) (by norm_num)
theorem B773921 : Blo 722323 773921 := bbase (se 2 (by rfl) ⟨290220, by rfl⟩ : syracuseStep 773921 = 580441) (by norm_num)
theorem B1625957 : Blo 722323 1625957 := bbase (se 4 (by rfl) ⟨152433, by rfl⟩ : syracuseStep 1625957 = 304867) (by norm_num)
theorem B773993 : Blo 722323 773993 := bbase (se 2 (by rfl) ⟨290247, by rfl⟩ : syracuseStep 773993 = 580495) (by norm_num)
theorem B2445173 : Blo 722323 2445173 := bbase (se 5 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 2445173 = 229235) (by norm_num)
theorem B1626029 : Blo 722323 1626029 := bbase (se 3 (by rfl) ⟨304880, by rfl⟩ : syracuseStep 1626029 = 609761) (by norm_num)
theorem B1626101 : Blo 722323 1626101 := bbase (se 5 (by rfl) ⟨76223, by rfl⟩ : syracuseStep 1626101 = 152447) (by norm_num)
theorem B872473 : Blo 722323 872473 := bbase (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) (by norm_num)
theorem B774181 : Blo 722323 774181 := bbase (se 4 (by rfl) ⟨72579, by rfl⟩ : syracuseStep 774181 = 145159) (by norm_num)
theorem B1626173 : Blo 722323 1626173 := bbase (se 3 (by rfl) ⟨304907, by rfl⟩ : syracuseStep 1626173 = 609815) (by norm_num)
theorem B3657797 : Blo 722323 3657797 := bbase (se 4 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 3657797 = 685837) (by norm_num)
theorem B872569 : Blo 722323 872569 := bbase (se 2 (by rfl) ⟨327213, by rfl⟩ : syracuseStep 872569 = 654427) (by norm_num)
theorem B1626245 : Blo 722323 1626245 := bbase (se 4 (by rfl) ⟨152460, by rfl⟩ : syracuseStep 1626245 = 304921) (by norm_num)
theorem B1626317 : Blo 722323 1626317 := bbase (se 3 (by rfl) ⟨304934, by rfl⟩ : syracuseStep 1626317 = 609869) (by norm_num)
theorem B774365 : Blo 722323 774365 := bbase (se 3 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 774365 = 290387) (by norm_num)
theorem B1626389 : Blo 722323 1626389 := bbase (se 6 (by rfl) ⟨38118, by rfl⟩ : syracuseStep 1626389 = 76237) (by norm_num)
theorem B2445605 : Blo 722323 2445605 := bbase (se 4 (by rfl) ⟨229275, by rfl⟩ : syracuseStep 2445605 = 458551) (by norm_num)
theorem B1626461 : Blo 722323 1626461 := bbase (se 3 (by rfl) ⟨304961, by rfl⟩ : syracuseStep 1626461 = 609923) (by norm_num)
theorem B1626533 : Blo 722323 1626533 := bbase (se 4 (by rfl) ⟨152487, by rfl⟩ : syracuseStep 1626533 = 304975) (by norm_num)
theorem B1626605 : Blo 722323 1626605 := bbase (se 3 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 1626605 = 609977) (by norm_num)
theorem B1102325 : Blo 722323 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B1626677 : Blo 722323 1626677 := bbase (se 5 (by rfl) ⟨76250, by rfl⟩ : syracuseStep 1626677 = 152501) (by norm_num)
theorem B1626749 : Blo 722323 1626749 := bbase (se 3 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 1626749 = 610031) (by norm_num)
theorem B1626821 : Blo 722323 1626821 := bbase (se 4 (by rfl) ⟨152514, by rfl⟩ : syracuseStep 1626821 = 305029) (by norm_num)
theorem B2446037 : Blo 722323 2446037 := bbase (se 7 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 2446037 = 57329) (by norm_num)
theorem B7951061 : Blo 722323 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B1626893 : Blo 722323 1626893 := bbase (se 3 (by rfl) ⟨305042, by rfl⟩ : syracuseStep 1626893 = 610085) (by norm_num)
theorem B4117301 : Blo 722323 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B1626965 : Blo 722323 1626965 := bbase (se 9 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 1626965 = 9533) (by norm_num)
theorem B1627037 : Blo 722323 1627037 := bbase (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) (by norm_num)
theorem B775117 : Blo 722323 775117 := bbase (se 3 (by rfl) ⟨145334, by rfl⟩ : syracuseStep 775117 = 290669) (by norm_num)
theorem B1627109 : Blo 722323 1627109 := bbase (se 4 (by rfl) ⟨152541, by rfl⟩ : syracuseStep 1627109 = 305083) (by norm_num)
theorem B775189 : Blo 722323 775189 := bbase (se 6 (by rfl) ⟨18168, by rfl⟩ : syracuseStep 775189 = 36337) (by norm_num)
theorem B1627181 : Blo 722323 1627181 := bbase (se 3 (by rfl) ⟨305096, by rfl⟩ : syracuseStep 1627181 = 610193) (by norm_num)
theorem B1627253 : Blo 722323 1627253 := bbase (se 5 (by rfl) ⟨76277, by rfl⟩ : syracuseStep 1627253 = 152555) (by norm_num)
theorem B2446469 : Blo 722323 2446469 := bbase (se 4 (by rfl) ⟨229356, by rfl⟩ : syracuseStep 2446469 = 458713) (by norm_num)
theorem B1627325 : Blo 722323 1627325 := bbase (se 3 (by rfl) ⟨305123, by rfl⟩ : syracuseStep 1627325 = 610247) (by norm_num)
theorem B775369 : Blo 722323 775369 := bbase (se 2 (by rfl) ⟨290763, by rfl⟩ : syracuseStep 775369 = 581527) (by norm_num)
theorem B1627397 : Blo 722323 1627397 := bbase (se 4 (by rfl) ⟨152568, by rfl⟩ : syracuseStep 1627397 = 305137) (by norm_num)
theorem B2315573 : Blo 722323 2315573 := bbase (se 5 (by rfl) ⟨108542, by rfl⟩ : syracuseStep 2315573 = 217085) (by norm_num)
theorem B1627469 : Blo 722323 1627469 := bbase (se 3 (by rfl) ⟨305150, by rfl⟩ : syracuseStep 1627469 = 610301) (by norm_num)
theorem B3659093 : Blo 722323 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B1627541 : Blo 722323 1627541 := bbase (se 6 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 1627541 = 76291) (by norm_num)
theorem B1955269 : Blo 722323 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B5494229 : Blo 722323 5494229 := bbase (se 7 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 5494229 = 128771) (by norm_num)
theorem B1627613 : Blo 722323 1627613 := bbase (se 3 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 1627613 = 610355) (by norm_num)
theorem B1627685 : Blo 722323 1627685 := bbase (se 4 (by rfl) ⟨152595, by rfl⟩ : syracuseStep 1627685 = 305191) (by norm_num)
theorem B3102245 : Blo 722323 3102245 := bbase (se 4 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 3102245 = 581671) (by norm_num)
theorem B2446901 : Blo 722323 2446901 := bbase (se 5 (by rfl) ⟨114698, by rfl⟩ : syracuseStep 2446901 = 229397) (by norm_num)
theorem B1627757 : Blo 722323 1627757 := bbase (se 3 (by rfl) ⟨305204, by rfl⟩ : syracuseStep 1627757 = 610409) (by norm_num)
theorem B1627829 : Blo 722323 1627829 := bbase (se 5 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 1627829 = 152609) (by norm_num)
theorem B1627901 : Blo 722323 1627901 := bbase (se 3 (by rfl) ⟨305231, by rfl⟩ : syracuseStep 1627901 = 610463) (by norm_num)
theorem B1627973 : Blo 722323 1627973 := bbase (se 4 (by rfl) ⟨152622, by rfl⟩ : syracuseStep 1627973 = 305245) (by norm_num)
theorem B1628045 : Blo 722323 1628045 := bbase (se 3 (by rfl) ⟨305258, by rfl⟩ : syracuseStep 1628045 = 610517) (by norm_num)
theorem B4118485 : Blo 722323 4118485 := bbase (se 7 (by rfl) ⟨48263, by rfl⟩ : syracuseStep 4118485 = 96527) (by norm_num)
theorem B1628117 : Blo 722323 1628117 := bbase (se 7 (by rfl) ⟨19079, by rfl⟩ : syracuseStep 1628117 = 38159) (by norm_num)
theorem B2447333 : Blo 722323 2447333 := bbase (se 4 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 2447333 = 458875) (by norm_num)
theorem B1628189 : Blo 722323 1628189 := bbase (se 3 (by rfl) ⟨305285, by rfl⟩ : syracuseStep 1628189 = 610571) (by norm_num)
theorem B1103957 : Blo 722323 1103957 := bbase (se 8 (by rfl) ⟨6468, by rfl⟩ : syracuseStep 1103957 = 12937) (by norm_num)
theorem B1628261 : Blo 722323 1628261 := bbase (se 4 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 1628261 = 305299) (by norm_num)
theorem B4642933 : Blo 722323 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B5232757 : Blo 722323 5232757 := bbase (se 5 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 5232757 = 490571) (by norm_num)
theorem B1628333 : Blo 722323 1628333 := bbase (se 3 (by rfl) ⟨305312, by rfl⟩ : syracuseStep 1628333 = 610625) (by norm_num)
theorem B1104077 : Blo 722323 1104077 := bbase (se 3 (by rfl) ⟨207014, by rfl⟩ : syracuseStep 1104077 = 414029) (by norm_num)
theorem B1628405 : Blo 722323 1628405 := bbase (se 5 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 1628405 = 152663) (by norm_num)
theorem B1628477 : Blo 722323 1628477 := bbase (se 3 (by rfl) ⟨305339, by rfl⟩ : syracuseStep 1628477 = 610679) (by norm_num)
theorem B1628549 : Blo 722323 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B2447765 : Blo 722323 2447765 := bbase (se 6 (by rfl) ⟨57369, by rfl⟩ : syracuseStep 2447765 = 114739) (by norm_num)
theorem B1628621 : Blo 722323 1628621 := bbase (se 3 (by rfl) ⟨305366, by rfl⟩ : syracuseStep 1628621 = 610733) (by norm_num)
theorem B1628693 : Blo 722323 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B1858085 : Blo 722323 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B2316853 : Blo 722323 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B1628765 : Blo 722323 1628765 := bbase (se 3 (by rfl) ⟨305393, by rfl⟩ : syracuseStep 1628765 = 610787) (by norm_num)
theorem B3660389 : Blo 722323 3660389 := bbase (se 4 (by rfl) ⟨343161, by rfl⟩ : syracuseStep 3660389 = 686323) (by norm_num)
theorem B1628837 : Blo 722323 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B1628909 : Blo 722323 1628909 := bbase (se 3 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 1628909 = 610841) (by norm_num)
theorem B1628981 : Blo 722323 1628981 := bbase (se 5 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 1628981 = 152717) (by norm_num)
theorem B2448197 : Blo 722323 2448197 := bbase (se 4 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 2448197 = 459037) (by norm_num)
theorem B1629053 : Blo 722323 1629053 := bbase (se 3 (by rfl) ⟨305447, by rfl⟩ : syracuseStep 1629053 = 610895) (by norm_num)
theorem B1465285 : Blo 722323 1465285 := bbase (se 4 (by rfl) ⟨137370, by rfl⟩ : syracuseStep 1465285 = 274741) (by norm_num)
theorem B1629125 : Blo 722323 1629125 := bbase (se 4 (by rfl) ⟨152730, by rfl⟩ : syracuseStep 1629125 = 305461) (by norm_num)
theorem B1629197 : Blo 722323 1629197 := bbase (se 3 (by rfl) ⟨305474, by rfl⟩ : syracuseStep 1629197 = 610949) (by norm_num)
theorem B1629269 : Blo 722323 1629269 := bbase (se 8 (by rfl) ⟨9546, by rfl⟩ : syracuseStep 1629269 = 19093) (by norm_num)
theorem B2939989 : Blo 722323 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B1629341 : Blo 722323 1629341 := bbase (se 3 (by rfl) ⟨305501, by rfl⟩ : syracuseStep 1629341 = 611003) (by norm_num)
theorem B1629413 : Blo 722323 1629413 := bbase (se 4 (by rfl) ⟨152757, by rfl⟩ : syracuseStep 1629413 = 305515) (by norm_num)
theorem B2448629 : Blo 722323 2448629 := bbase (se 5 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 2448629 = 229559) (by norm_num)
theorem B1301789 : Blo 722323 1301789 := bbase (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) (by norm_num)
theorem B1629485 : Blo 722323 1629485 := bbase (se 3 (by rfl) ⟨305528, by rfl⟩ : syracuseStep 1629485 = 611057) (by norm_num)
theorem B1629557 : Blo 722323 1629557 := bbase (se 5 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 1629557 = 152771) (by norm_num)
theorem B1564085 : Blo 722323 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B1629629 : Blo 722323 1629629 := bbase (se 3 (by rfl) ⟨305555, by rfl⟩ : syracuseStep 1629629 = 611111) (by norm_num)
theorem B1629701 : Blo 722323 1629701 := bbase (se 4 (by rfl) ⟨152784, by rfl⟩ : syracuseStep 1629701 = 305569) (by norm_num)
theorem B1629773 : Blo 722323 1629773 := bbase (se 3 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 1629773 = 611165) (by norm_num)
theorem B1236613 : Blo 722323 1236613 := bbase (se 4 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 1236613 = 231865) (by norm_num)
theorem B1629845 : Blo 722323 1629845 := bbase (se 6 (by rfl) ⟨38199, by rfl⟩ : syracuseStep 1629845 = 76399) (by norm_num)
theorem B2449061 : Blo 722323 2449061 := bbase (se 4 (by rfl) ⟨229599, by rfl⟩ : syracuseStep 2449061 = 459199) (by norm_num)
theorem B1629917 : Blo 722323 1629917 := bbase (se 3 (by rfl) ⟨305609, by rfl⟩ : syracuseStep 1629917 = 611219) (by norm_num)
theorem B6610709 : Blo 722323 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B745249 : Blo 722323 745249 := bbase (se 2 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 745249 = 558937) (by norm_num)
theorem B1629989 : Blo 722323 1629989 := bbase (se 4 (by rfl) ⟨152811, by rfl⟩ : syracuseStep 1629989 = 305623) (by norm_num)
theorem B3137381 : Blo 722323 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B1630061 : Blo 722323 1630061 := bbase (se 3 (by rfl) ⟨305636, by rfl⟩ : syracuseStep 1630061 = 611273) (by norm_num)
theorem B3661685 : Blo 722323 3661685 := bbase (se 5 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 3661685 = 343283) (by norm_num)
theorem B2318213 : Blo 722323 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B4120469 : Blo 722323 4120469 := bbase (se 6 (by rfl) ⟨96573, by rfl⟩ : syracuseStep 4120469 = 193147) (by norm_num)
theorem B1630133 : Blo 722323 1630133 := bbase (se 5 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 1630133 = 152825) (by norm_num)
theorem B1630205 : Blo 722323 1630205 := bbase (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) (by norm_num)
theorem B2318341 : Blo 722323 2318341 := bbase (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) (by norm_num)
theorem B1630277 : Blo 722323 1630277 := bbase (se 4 (by rfl) ⟨152838, by rfl⟩ : syracuseStep 1630277 = 305677) (by norm_num)
theorem B2449493 : Blo 722323 2449493 := bbase (se 8 (by rfl) ⟨14352, by rfl⟩ : syracuseStep 2449493 = 28705) (by norm_num)
theorem B1630349 : Blo 722323 1630349 := bbase (se 3 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 1630349 = 611381) (by norm_num)
theorem B1630421 : Blo 722323 1630421 := bbase (se 7 (by rfl) ⟨19106, by rfl⟩ : syracuseStep 1630421 = 38213) (by norm_num)
theorem B2744549 : Blo 722323 2744549 := bbase (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) (by norm_num)
theorem B2318597 : Blo 722323 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B1630493 : Blo 722323 1630493 := bbase (se 3 (by rfl) ⟨305717, by rfl⟩ : syracuseStep 1630493 = 611435) (by norm_num)
theorem B1630565 : Blo 722323 1630565 := bbase (se 4 (by rfl) ⟨152865, by rfl⟩ : syracuseStep 1630565 = 305731) (by norm_num)
theorem B1630637 : Blo 722323 1630637 := bbase (se 3 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 1630637 = 611489) (by norm_num)
theorem B1630709 : Blo 722323 1630709 := bbase (se 5 (by rfl) ⟨76439, by rfl⟩ : syracuseStep 1630709 = 152879) (by norm_num)
theorem B2744837 : Blo 722323 2744837 := bbase (se 4 (by rfl) ⟨257328, by rfl⟩ : syracuseStep 2744837 = 514657) (by norm_num)
theorem B2449925 : Blo 722323 2449925 := bbase (se 4 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 2449925 = 459361) (by norm_num)
theorem B1630781 : Blo 722323 1630781 := bbase (se 3 (by rfl) ⟨305771, by rfl⟩ : syracuseStep 1630781 = 611543) (by norm_num)
theorem B1630853 : Blo 722323 1630853 := bbase (se 4 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 1630853 = 305785) (by norm_num)
theorem B1630925 : Blo 722323 1630925 := bbase (se 3 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 1630925 = 611597) (by norm_num)
theorem B1630997 : Blo 722323 1630997 := bbase (se 6 (by rfl) ⟨38226, by rfl⟩ : syracuseStep 1630997 = 76453) (by norm_num)
theorem B1467173 : Blo 722323 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B1631069 : Blo 722323 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B4645781 : Blo 722323 4645781 := bbase (se 6 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 4645781 = 217771) (by norm_num)
theorem B1631141 : Blo 722323 1631141 := bbase (se 4 (by rfl) ⟨152919, by rfl⟩ : syracuseStep 1631141 = 305839) (by norm_num)
theorem B2450357 : Blo 722323 2450357 := bbase (se 5 (by rfl) ⟨114860, by rfl⟩ : syracuseStep 2450357 = 229721) (by norm_num)
theorem B1631213 : Blo 722323 1631213 := bbase (se 3 (by rfl) ⟨305852, by rfl⟩ : syracuseStep 1631213 = 611705) (by norm_num)
theorem B1631285 : Blo 722323 1631285 := bbase (se 5 (by rfl) ⟨76466, by rfl⟩ : syracuseStep 1631285 = 152933) (by norm_num)
theorem B943193 : Blo 722323 943193 := bbase (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) (by norm_num)
theorem B1631357 : Blo 722323 1631357 := bbase (se 3 (by rfl) ⟨305879, by rfl⟩ : syracuseStep 1631357 = 611759) (by norm_num)
theorem B3662981 : Blo 722323 3662981 := bbase (se 4 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 3662981 = 686809) (by norm_num)
theorem B1631429 : Blo 722323 1631429 := bbase (se 4 (by rfl) ⟨152946, by rfl⟩ : syracuseStep 1631429 = 305893) (by norm_num)
theorem B1631501 : Blo 722323 1631501 := bbase (se 3 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 1631501 = 611813) (by norm_num)
theorem B2057557 : Blo 722323 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B1631573 : Blo 722323 1631573 := bbase (se 12 (by rfl) ⟨597, by rfl⟩ : syracuseStep 1631573 = 1195) (by norm_num)
theorem B1467749 : Blo 722323 1467749 := bbase (se 4 (by rfl) ⟨137601, by rfl⟩ : syracuseStep 1467749 = 275203) (by norm_num)
theorem B2450789 : Blo 722323 2450789 := bbase (se 4 (by rfl) ⟨229761, by rfl⟩ : syracuseStep 2450789 = 459523) (by norm_num)
theorem B1631645 : Blo 722323 1631645 := bbase (se 3 (by rfl) ⟨305933, by rfl⟩ : syracuseStep 1631645 = 611867) (by norm_num)
theorem B1631717 : Blo 722323 1631717 := bbase (se 4 (by rfl) ⟨152973, by rfl⟩ : syracuseStep 1631717 = 305947) (by norm_num)
theorem B2057717 : Blo 722323 2057717 := bbase (se 5 (by rfl) ⟨96455, by rfl⟩ : syracuseStep 2057717 = 192911) (by norm_num)
theorem B1631789 : Blo 722323 1631789 := bbase (se 3 (by rfl) ⟨305960, by rfl⟩ : syracuseStep 1631789 = 611921) (by norm_num)
theorem B812641 : Blo 722323 812641 := bbase (se 2 (by rfl) ⟨304740, by rfl⟩ : syracuseStep 812641 = 609481) (by norm_num)
theorem B1828453 : Blo 722323 1828453 := bbase (se 4 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 1828453 = 342835) (by norm_num)
theorem B1631861 : Blo 722323 1631861 := bbase (se 5 (by rfl) ⟨76493, by rfl⟩ : syracuseStep 1631861 = 152987) (by norm_num)
theorem B812677 : Blo 722323 812677 := bbase (se 4 (by rfl) ⟨76188, by rfl⟩ : syracuseStep 812677 = 152377) (by norm_num)
theorem B2746021 : Blo 722323 2746021 := bbase (se 4 (by rfl) ⟨257439, by rfl⟩ : syracuseStep 2746021 = 514879) (by norm_num)
theorem B812713 : Blo 722323 812713 := bbase (se 2 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 812713 = 609535) (by norm_num)
theorem B1631933 : Blo 722323 1631933 := bbase (se 3 (by rfl) ⟨305987, by rfl⟩ : syracuseStep 1631933 = 611975) (by norm_num)
theorem B812749 : Blo 722323 812749 := bbase (se 3 (by rfl) ⟨152390, by rfl⟩ : syracuseStep 812749 = 304781) (by norm_num)
theorem B1828565 : Blo 722323 1828565 := bbase (se 7 (by rfl) ⟨21428, by rfl⟩ : syracuseStep 1828565 = 42857) (by norm_num)
theorem B2057957 : Blo 722323 2057957 := bbase (se 4 (by rfl) ⟨192933, by rfl⟩ : syracuseStep 2057957 = 385867) (by norm_num)
theorem B812785 : Blo 722323 812785 := bbase (se 2 (by rfl) ⟨304794, by rfl⟩ : syracuseStep 812785 = 609589) (by norm_num)
theorem B1632005 : Blo 722323 1632005 := bbase (se 4 (by rfl) ⟨153000, by rfl⟩ : syracuseStep 1632005 = 306001) (by norm_num)
theorem B1238797 : Blo 722323 1238797 := bbase (se 3 (by rfl) ⟨232274, by rfl⟩ : syracuseStep 1238797 = 464549) (by norm_num)
theorem B812821 : Blo 722323 812821 := bbase (se 6 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 812821 = 38101) (by norm_num)
theorem B2451221 : Blo 722323 2451221 := bbase (se 6 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 2451221 = 114901) (by norm_num)
theorem B943913 : Blo 722323 943913 := bbase (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) (by norm_num)
theorem B812857 : Blo 722323 812857 := bbase (se 2 (by rfl) ⟨304821, by rfl⟩ : syracuseStep 812857 = 609643) (by norm_num)
theorem B1632077 : Blo 722323 1632077 := bbase (se 3 (by rfl) ⟨306014, by rfl⟩ : syracuseStep 1632077 = 612029) (by norm_num)
theorem B812893 : Blo 722323 812893 := bbase (se 3 (by rfl) ⟨152417, by rfl⟩ : syracuseStep 812893 = 304835) (by norm_num)
theorem B812929 : Blo 722323 812929 := bbase (se 2 (by rfl) ⟨304848, by rfl⟩ : syracuseStep 812929 = 609697) (by norm_num)
theorem B1828757 : Blo 722323 1828757 := bbase (se 6 (by rfl) ⟨42861, by rfl⟩ : syracuseStep 1828757 = 85723) (by norm_num)
theorem B1468309 : Blo 722323 1468309 := bbase (se 6 (by rfl) ⟨34413, by rfl⟩ : syracuseStep 1468309 = 68827) (by norm_num)
theorem B1632149 : Blo 722323 1632149 := bbase (se 6 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 1632149 = 76507) (by norm_num)
theorem B812965 : Blo 722323 812965 := bbase (se 4 (by rfl) ⟨76215, by rfl⟩ : syracuseStep 812965 = 152431) (by norm_num)
theorem B2058149 : Blo 722323 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B813001 : Blo 722323 813001 := bbase (se 2 (by rfl) ⟨304875, by rfl⟩ : syracuseStep 813001 = 609751) (by norm_num)
theorem B2746325 : Blo 722323 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B1632221 : Blo 722323 1632221 := bbase (se 3 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 1632221 = 612083) (by norm_num)
theorem B813037 : Blo 722323 813037 := bbase (se 3 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 813037 = 304889) (by norm_num)
theorem B813073 : Blo 722323 813073 := bbase (se 2 (by rfl) ⟨304902, by rfl⟩ : syracuseStep 813073 = 609805) (by norm_num)
theorem B1632293 : Blo 722323 1632293 := bbase (se 4 (by rfl) ⟨153027, by rfl⟩ : syracuseStep 1632293 = 306055) (by norm_num)
theorem B813109 : Blo 722323 813109 := bbase (se 5 (by rfl) ⟨38114, by rfl⟩ : syracuseStep 813109 = 76229) (by norm_num)
theorem B4122677 : Blo 722323 4122677 := bbase (se 5 (by rfl) ⟨193250, by rfl⟩ : syracuseStep 4122677 = 386501) (by norm_num)
theorem B813145 : Blo 722323 813145 := bbase (se 2 (by rfl) ⟨304929, by rfl⟩ : syracuseStep 813145 = 609859) (by norm_num)
theorem B1632365 : Blo 722323 1632365 := bbase (se 3 (by rfl) ⟨306068, by rfl⟩ : syracuseStep 1632365 = 612137) (by norm_num)
theorem B813181 : Blo 722323 813181 := bbase (se 3 (by rfl) ⟨152471, by rfl⟩ : syracuseStep 813181 = 304943) (by norm_num)
theorem B813217 : Blo 722323 813217 := bbase (se 2 (by rfl) ⟨304956, by rfl⟩ : syracuseStep 813217 = 609913) (by norm_num)
theorem B1632437 : Blo 722323 1632437 := bbase (se 5 (by rfl) ⟨76520, by rfl⟩ : syracuseStep 1632437 = 153041) (by norm_num)
theorem B813253 : Blo 722323 813253 := bbase (se 4 (by rfl) ⟨76242, by rfl⟩ : syracuseStep 813253 = 152485) (by norm_num)
theorem B2091221 : Blo 722323 2091221 := bbase (se 7 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 2091221 = 49013) (by norm_num)
theorem B813289 : Blo 722323 813289 := bbase (se 2 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 813289 = 609967) (by norm_num)
theorem B1829101 : Blo 722323 1829101 := bbase (se 3 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 1829101 = 685913) (by norm_num)
theorem B1632509 : Blo 722323 1632509 := bbase (se 3 (by rfl) ⟨306095, by rfl⟩ : syracuseStep 1632509 = 612191) (by norm_num)
theorem B813325 : Blo 722323 813325 := bbase (se 3 (by rfl) ⟨152498, by rfl⟩ : syracuseStep 813325 = 304997) (by norm_num)
theorem B813361 : Blo 722323 813361 := bbase (se 2 (by rfl) ⟨305010, by rfl⟩ : syracuseStep 813361 = 610021) (by norm_num)
theorem B1632581 : Blo 722323 1632581 := bbase (se 4 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 1632581 = 306109) (by norm_num)
theorem B813397 : Blo 722323 813397 := bbase (se 10 (by rfl) ⟨1191, by rfl⟩ : syracuseStep 813397 = 2383) (by norm_num)
theorem B1829213 : Blo 722323 1829213 := bbase (se 3 (by rfl) ⟨342977, by rfl⟩ : syracuseStep 1829213 = 685955) (by norm_num)
theorem B813433 : Blo 722323 813433 := bbase (se 2 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 813433 = 610075) (by norm_num)
theorem B1632653 : Blo 722323 1632653 := bbase (se 3 (by rfl) ⟨306122, by rfl⟩ : syracuseStep 1632653 = 612245) (by norm_num)
theorem B3664277 : Blo 722323 3664277 := bbase (se 6 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 3664277 = 171763) (by norm_num)
theorem B813469 : Blo 722323 813469 := bbase (se 3 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 813469 = 305051) (by norm_num)
theorem B813505 : Blo 722323 813505 := bbase (se 2 (by rfl) ⟨305064, by rfl⟩ : syracuseStep 813505 = 610129) (by norm_num)
theorem B1632725 : Blo 722323 1632725 := bbase (se 7 (by rfl) ⟨19133, by rfl⟩ : syracuseStep 1632725 = 38267) (by norm_num)
theorem B813541 : Blo 722323 813541 := bbase (se 4 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 813541 = 152539) (by norm_num)
theorem B813577 : Blo 722323 813577 := bbase (se 2 (by rfl) ⟨305091, by rfl⟩ : syracuseStep 813577 = 610183) (by norm_num)
theorem B1698317 : Blo 722323 1698317 := bbase (se 3 (by rfl) ⟨318434, by rfl⟩ : syracuseStep 1698317 = 636869) (by norm_num)
theorem B1829405 : Blo 722323 1829405 := bbase (se 3 (by rfl) ⟨343013, by rfl⟩ : syracuseStep 1829405 = 686027) (by norm_num)
theorem B1632797 : Blo 722323 1632797 := bbase (se 3 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 1632797 = 612299) (by norm_num)
theorem B813613 : Blo 722323 813613 := bbase (se 3 (by rfl) ⟨152552, by rfl⟩ : syracuseStep 813613 = 305105) (by norm_num)
theorem B813649 : Blo 722323 813649 := bbase (se 2 (by rfl) ⟨305118, by rfl⟩ : syracuseStep 813649 = 610237) (by norm_num)
theorem B1632869 : Blo 722323 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B813685 : Blo 722323 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B2321045 : Blo 722323 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B813721 : Blo 722323 813721 := bbase (se 2 (by rfl) ⟨305145, by rfl⟩ : syracuseStep 813721 = 610291) (by norm_num)
theorem B1632941 : Blo 722323 1632941 := bbase (se 3 (by rfl) ⟨306176, by rfl⟩ : syracuseStep 1632941 = 612353) (by norm_num)
theorem B813757 : Blo 722323 813757 := bbase (se 3 (by rfl) ⟨152579, by rfl⟩ : syracuseStep 813757 = 305159) (by norm_num)
theorem B2943685 : Blo 722323 2943685 := bbase (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) (by norm_num)
theorem B813793 : Blo 722323 813793 := bbase (se 2 (by rfl) ⟨305172, by rfl⟩ : syracuseStep 813793 = 610345) (by norm_num)
theorem B1633013 : Blo 722323 1633013 := bbase (se 5 (by rfl) ⟨76547, by rfl⟩ : syracuseStep 1633013 = 153095) (by norm_num)
theorem B813829 : Blo 722323 813829 := bbase (se 4 (by rfl) ⟨76296, by rfl⟩ : syracuseStep 813829 = 152593) (by norm_num)
theorem B813865 : Blo 722323 813865 := bbase (se 2 (by rfl) ⟨305199, by rfl⟩ : syracuseStep 813865 = 610399) (by norm_num)
theorem B1633085 : Blo 722323 1633085 := bbase (se 3 (by rfl) ⟨306203, by rfl⟩ : syracuseStep 1633085 = 612407) (by norm_num)
theorem B813901 : Blo 722323 813901 := bbase (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) (by norm_num)
theorem B813937 : Blo 722323 813937 := bbase (se 2 (by rfl) ⟨305226, by rfl⟩ : syracuseStep 813937 = 610453) (by norm_num)
theorem B1829749 : Blo 722323 1829749 := bbase (se 5 (by rfl) ⟨85769, by rfl⟩ : syracuseStep 1829749 = 171539) (by norm_num)
theorem B2059141 : Blo 722323 2059141 := bbase (se 4 (by rfl) ⟨193044, by rfl⟩ : syracuseStep 2059141 = 386089) (by norm_num)
theorem B1633157 : Blo 722323 1633157 := bbase (se 4 (by rfl) ⟨153108, by rfl⟩ : syracuseStep 1633157 = 306217) (by norm_num)
theorem B813973 : Blo 722323 813973 := bbase (se 6 (by rfl) ⟨19077, by rfl⟩ : syracuseStep 813973 = 38155) (by norm_num)
theorem B814009 : Blo 722323 814009 := bbase (se 2 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 814009 = 610507) (by norm_num)
theorem B1043389 : Blo 722323 1043389 := bbase (se 3 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 1043389 = 391271) (by norm_num)
theorem B1960901 : Blo 722323 1960901 := bbase (se 4 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 1960901 = 367669) (by norm_num)
theorem B3533765 : Blo 722323 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B1633229 : Blo 722323 1633229 := bbase (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) (by norm_num)
theorem B814045 : Blo 722323 814045 := bbase (se 3 (by rfl) ⟨152633, by rfl⟩ : syracuseStep 814045 = 305267) (by norm_num)
theorem B1829861 : Blo 722323 1829861 := bbase (se 4 (by rfl) ⟨171549, by rfl⟩ : syracuseStep 1829861 = 343099) (by norm_num)
theorem B814081 : Blo 722323 814081 := bbase (se 2 (by rfl) ⟨305280, by rfl⟩ : syracuseStep 814081 = 610561) (by norm_num)
theorem B1633301 : Blo 722323 1633301 := bbase (se 6 (by rfl) ⟨38280, by rfl⟩ : syracuseStep 1633301 = 76561) (by norm_num)
theorem B814117 : Blo 722323 814117 := bbase (se 4 (by rfl) ⟨76323, by rfl⟩ : syracuseStep 814117 = 152647) (by norm_num)
theorem B1469477 : Blo 722323 1469477 := bbase (se 4 (by rfl) ⟨137763, by rfl⟩ : syracuseStep 1469477 = 275527) (by norm_num)
theorem B814153 : Blo 722323 814153 := bbase (se 2 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 814153 = 610615) (by norm_num)
theorem B6974549 : Blo 722323 6974549 := bbase (se 8 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 6974549 = 81733) (by norm_num)
theorem B1633373 : Blo 722323 1633373 := bbase (se 3 (by rfl) ⟨306257, by rfl⟩ : syracuseStep 1633373 = 612515) (by norm_num)
theorem B814189 : Blo 722323 814189 := bbase (se 3 (by rfl) ⟨152660, by rfl⟩ : syracuseStep 814189 = 305321) (by norm_num)
theorem B814225 : Blo 722323 814225 := bbase (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) (by norm_num)
theorem B1830053 : Blo 722323 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B1633445 : Blo 722323 1633445 := bbase (se 4 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 1633445 = 306271) (by norm_num)
theorem B814261 : Blo 722323 814261 := bbase (se 5 (by rfl) ⟨38168, by rfl⟩ : syracuseStep 814261 = 76337) (by norm_num)
theorem B1371325 : Blo 722323 1371325 := bbase (se 3 (by rfl) ⟨257123, by rfl⟩ : syracuseStep 1371325 = 514247) (by norm_num)
theorem B814297 : Blo 722323 814297 := bbase (se 2 (by rfl) ⟨305361, by rfl⟩ : syracuseStep 814297 = 610723) (by norm_num)
theorem B1633517 : Blo 722323 1633517 := bbase (se 3 (by rfl) ⟨306284, by rfl⟩ : syracuseStep 1633517 = 612569) (by norm_num)
theorem B814333 : Blo 722323 814333 := bbase (se 3 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 814333 = 305375) (by norm_num)
theorem B814369 : Blo 722323 814369 := bbase (se 2 (by rfl) ⟨305388, by rfl⟩ : syracuseStep 814369 = 610777) (by norm_num)
theorem B1633589 : Blo 722323 1633589 := bbase (se 5 (by rfl) ⟨76574, by rfl⟩ : syracuseStep 1633589 = 153149) (by norm_num)
theorem B814405 : Blo 722323 814405 := bbase (se 4 (by rfl) ⟨76350, by rfl⟩ : syracuseStep 814405 = 152701) (by norm_num)
theorem B1371485 : Blo 722323 1371485 := bbase (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) (by norm_num)
theorem B814441 : Blo 722323 814441 := bbase (se 2 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 814441 = 610831) (by norm_num)
theorem B1633661 : Blo 722323 1633661 := bbase (se 3 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 1633661 = 612623) (by norm_num)
theorem B814477 : Blo 722323 814477 := bbase (se 3 (by rfl) ⟨152714, by rfl⟩ : syracuseStep 814477 = 305429) (by norm_num)
theorem B2616725 : Blo 722323 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B814513 : Blo 722323 814513 := bbase (se 2 (by rfl) ⟨305442, by rfl⟩ : syracuseStep 814513 = 610885) (by norm_num)
theorem B1633733 : Blo 722323 1633733 := bbase (se 4 (by rfl) ⟨153162, by rfl⟩ : syracuseStep 1633733 = 306325) (by norm_num)
theorem B814549 : Blo 722323 814549 := bbase (se 7 (by rfl) ⟨9545, by rfl⟩ : syracuseStep 814549 = 19091) (by norm_num)
theorem B1371629 : Blo 722323 1371629 := bbase (se 3 (by rfl) ⟨257180, by rfl⟩ : syracuseStep 1371629 = 514361) (by norm_num)
theorem B814585 : Blo 722323 814585 := bbase (se 2 (by rfl) ⟨305469, by rfl⟩ : syracuseStep 814585 = 610939) (by norm_num)
theorem B1830397 : Blo 722323 1830397 := bbase (se 3 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 1830397 = 686399) (by norm_num)
theorem B880141 : Blo 722323 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B1633805 : Blo 722323 1633805 := bbase (se 3 (by rfl) ⟨306338, by rfl⟩ : syracuseStep 1633805 = 612677) (by norm_num)
theorem B814621 : Blo 722323 814621 := bbase (se 3 (by rfl) ⟨152741, by rfl⟩ : syracuseStep 814621 = 305483) (by norm_num)
theorem B814657 : Blo 722323 814657 := bbase (se 2 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 814657 = 610993) (by norm_num)
theorem B1633877 : Blo 722323 1633877 := bbase (se 8 (by rfl) ⟨9573, by rfl⟩ : syracuseStep 1633877 = 19147) (by norm_num)
theorem B781921 : Blo 722323 781921 := bbase (se 2 (by rfl) ⟨293220, by rfl⟩ : syracuseStep 781921 = 586441) (by norm_num)
theorem B814693 : Blo 722323 814693 := bbase (se 4 (by rfl) ⟨76377, by rfl⟩ : syracuseStep 814693 = 152755) (by norm_num)
theorem B1830509 : Blo 722323 1830509 := bbase (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) (by norm_num)
theorem B814729 : Blo 722323 814729 := bbase (se 2 (by rfl) ⟨305523, by rfl⟩ : syracuseStep 814729 = 611047) (by norm_num)
theorem B1044109 : Blo 722323 1044109 := bbase (se 3 (by rfl) ⟨195770, by rfl⟩ : syracuseStep 1044109 = 391541) (by norm_num)
theorem B1633949 : Blo 722323 1633949 := bbase (se 3 (by rfl) ⟨306365, by rfl⟩ : syracuseStep 1633949 = 612731) (by norm_num)
theorem B3665573 : Blo 722323 3665573 := bbase (se 4 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 3665573 = 687295) (by norm_num)
theorem B814765 : Blo 722323 814765 := bbase (se 3 (by rfl) ⟨152768, by rfl⟩ : syracuseStep 814765 = 305537) (by norm_num)
theorem B814801 : Blo 722323 814801 := bbase (se 2 (by rfl) ⟨305550, by rfl⟩ : syracuseStep 814801 = 611101) (by norm_num)
theorem B1634021 : Blo 722323 1634021 := bbase (se 4 (by rfl) ⟨153189, by rfl⟩ : syracuseStep 1634021 = 306379) (by norm_num)
theorem B814837 : Blo 722323 814837 := bbase (se 5 (by rfl) ⟨38195, by rfl⟩ : syracuseStep 814837 = 76391) (by norm_num)
theorem B1240829 : Blo 722323 1240829 := bbase (se 3 (by rfl) ⟨232655, by rfl⟩ : syracuseStep 1240829 = 465311) (by norm_num)
theorem B1371917 : Blo 722323 1371917 := bbase (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) (by norm_num)
theorem B814873 : Blo 722323 814873 := bbase (se 2 (by rfl) ⟨305577, by rfl⟩ : syracuseStep 814873 = 611155) (by norm_num)
theorem B1830701 : Blo 722323 1830701 := bbase (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) (by norm_num)
theorem B1634093 : Blo 722323 1634093 := bbase (se 3 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 1634093 = 612785) (by norm_num)
theorem B782129 : Blo 722323 782129 := bbase (se 2 (by rfl) ⟨293298, by rfl⟩ : syracuseStep 782129 = 586597) (by norm_num)
theorem B814909 : Blo 722323 814909 := bbase (se 3 (by rfl) ⟨152795, by rfl⟩ : syracuseStep 814909 = 305591) (by norm_num)
theorem B814945 : Blo 722323 814945 := bbase (se 2 (by rfl) ⟨305604, by rfl⟩ : syracuseStep 814945 = 611209) (by norm_num)
theorem B1634165 : Blo 722323 1634165 := bbase (se 5 (by rfl) ⟨76601, by rfl⟩ : syracuseStep 1634165 = 153203) (by norm_num)
theorem B814981 : Blo 722323 814981 := bbase (se 4 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 814981 = 152809) (by norm_num)
theorem B978845 : Blo 722323 978845 := bbase (se 3 (by rfl) ⟨183533, by rfl⟩ : syracuseStep 978845 = 367067) (by norm_num)
theorem B1372069 : Blo 722323 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B815017 : Blo 722323 815017 := bbase (se 2 (by rfl) ⟨305631, by rfl⟩ : syracuseStep 815017 = 611263) (by norm_num)
theorem B815053 : Blo 722323 815053 := bbase (se 3 (by rfl) ⟨152822, by rfl⟩ : syracuseStep 815053 = 305645) (by norm_num)
theorem B2060245 : Blo 722323 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B2322389 : Blo 722323 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B815089 : Blo 722323 815089 := bbase (se 2 (by rfl) ⟨305658, by rfl⟩ : syracuseStep 815089 = 611317) (by norm_num)
theorem B2748437 : Blo 722323 2748437 := bbase (se 6 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 2748437 = 128833) (by norm_num)
theorem B815125 : Blo 722323 815125 := bbase (se 6 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 815125 = 38209) (by norm_num)
theorem B815161 : Blo 722323 815161 := bbase (se 2 (by rfl) ⟨305685, by rfl⟩ : syracuseStep 815161 = 611371) (by norm_num)
theorem B815197 : Blo 722323 815197 := bbase (se 3 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 815197 = 305699) (by norm_num)
theorem B782441 : Blo 722323 782441 := bbase (se 2 (by rfl) ⟨293415, by rfl⟩ : syracuseStep 782441 = 586831) (by norm_num)
theorem B815233 : Blo 722323 815233 := bbase (se 2 (by rfl) ⟨305712, by rfl⟩ : syracuseStep 815233 = 611425) (by norm_num)
theorem B1831045 : Blo 722323 1831045 := bbase (se 4 (by rfl) ⟨171660, by rfl⟩ : syracuseStep 1831045 = 343321) (by norm_num)
theorem B815269 : Blo 722323 815269 := bbase (se 4 (by rfl) ⟨76431, by rfl⟩ : syracuseStep 815269 = 152863) (by norm_num)
theorem B815305 : Blo 722323 815305 := bbase (se 2 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 815305 = 611479) (by norm_num)
theorem B1372373 : Blo 722323 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B815341 : Blo 722323 815341 := bbase (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) (by norm_num)
theorem B1831157 : Blo 722323 1831157 := bbase (se 5 (by rfl) ⟨85835, by rfl⟩ : syracuseStep 1831157 = 171671) (by norm_num)
theorem B815377 : Blo 722323 815377 := bbase (se 2 (by rfl) ⟨305766, by rfl⟩ : syracuseStep 815377 = 611533) (by norm_num)
theorem B2748725 : Blo 722323 2748725 := bbase (se 5 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 2748725 = 257693) (by norm_num)
theorem B815413 : Blo 722323 815413 := bbase (se 5 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 815413 = 76445) (by norm_num)
theorem B815449 : Blo 722323 815449 := bbase (se 2 (by rfl) ⟨305793, by rfl⟩ : syracuseStep 815449 = 611587) (by norm_num)
theorem B815485 : Blo 722323 815485 := bbase (se 3 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 815485 = 305807) (by norm_num)
theorem B815521 : Blo 722323 815521 := bbase (se 2 (by rfl) ⟨305820, by rfl⟩ : syracuseStep 815521 = 611641) (by norm_num)
theorem B1831349 : Blo 722323 1831349 := bbase (se 5 (by rfl) ⟨85844, by rfl⟩ : syracuseStep 1831349 = 171689) (by norm_num)
theorem B979381 : Blo 722323 979381 := bbase (se 5 (by rfl) ⟨45908, by rfl⟩ : syracuseStep 979381 = 91817) (by norm_num)
theorem B815557 : Blo 722323 815557 := bbase (se 4 (by rfl) ⟨76458, by rfl⟩ : syracuseStep 815557 = 152917) (by norm_num)
theorem B815593 : Blo 722323 815593 := bbase (se 2 (by rfl) ⟨305847, by rfl⟩ : syracuseStep 815593 = 611695) (by norm_num)
theorem B815629 : Blo 722323 815629 := bbase (se 3 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 815629 = 305861) (by norm_num)
theorem B815665 : Blo 722323 815665 := bbase (se 2 (by rfl) ⟨305874, by rfl⟩ : syracuseStep 815665 = 611749) (by norm_num)
theorem B815701 : Blo 722323 815701 := bbase (se 8 (by rfl) ⟨4779, by rfl⟩ : syracuseStep 815701 = 9559) (by norm_num)
theorem B815737 : Blo 722323 815737 := bbase (se 2 (by rfl) ⟨305901, by rfl⟩ : syracuseStep 815737 = 611803) (by norm_num)
theorem B815773 : Blo 722323 815773 := bbase (se 3 (by rfl) ⟨152957, by rfl⟩ : syracuseStep 815773 = 305915) (by norm_num)
theorem B815809 : Blo 722323 815809 := bbase (se 2 (by rfl) ⟨305928, by rfl⟩ : syracuseStep 815809 = 611857) (by norm_num)
theorem B815845 : Blo 722323 815845 := bbase (se 4 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 815845 = 152971) (by norm_num)
theorem B815881 : Blo 722323 815881 := bbase (se 2 (by rfl) ⟨305955, by rfl⟩ : syracuseStep 815881 = 611911) (by norm_num)
theorem B1831693 : Blo 722323 1831693 := bbase (se 3 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 1831693 = 686885) (by norm_num)
theorem B881425 : Blo 722323 881425 := bbase (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) (by norm_num)
theorem B1176365 : Blo 722323 1176365 := bbase (se 3 (by rfl) ⟨220568, by rfl⟩ : syracuseStep 1176365 = 441137) (by norm_num)
theorem B815917 : Blo 722323 815917 := bbase (se 3 (by rfl) ⟨152984, by rfl⟩ : syracuseStep 815917 = 305969) (by norm_num)
theorem B1471277 : Blo 722323 1471277 := bbase (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) (by norm_num)
theorem B914257 : Blo 722323 914257 := bbase (se 2 (by rfl) ⟨342846, by rfl⟩ : syracuseStep 914257 = 685693) (by norm_num)
theorem B815953 : Blo 722323 815953 := bbase (se 2 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 815953 = 611965) (by norm_num)
theorem B1045333 : Blo 722323 1045333 := bbase (se 9 (by rfl) ⟨3062, by rfl⟩ : syracuseStep 1045333 = 6125) (by norm_num)
theorem B815989 : Blo 722323 815989 := bbase (se 5 (by rfl) ⟨38249, by rfl⟩ : syracuseStep 815989 = 76499) (by norm_num)
theorem B1831805 : Blo 722323 1831805 := bbase (se 3 (by rfl) ⟨343463, by rfl⟩ : syracuseStep 1831805 = 686927) (by norm_num)
theorem B816025 : Blo 722323 816025 := bbase (se 2 (by rfl) ⟨306009, by rfl⟩ : syracuseStep 816025 = 612019) (by norm_num)
theorem B1307549 : Blo 722323 1307549 := bbase (se 3 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 1307549 = 490331) (by norm_num)
theorem B3666869 : Blo 722323 3666869 := bbase (se 5 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 3666869 = 343769) (by norm_num)
theorem B816061 : Blo 722323 816061 := bbase (se 3 (by rfl) ⟨153011, by rfl⟩ : syracuseStep 816061 = 306023) (by norm_num)
theorem B1373125 : Blo 722323 1373125 := bbase (se 4 (by rfl) ⟨128730, by rfl⟩ : syracuseStep 1373125 = 257461) (by norm_num)
theorem B816097 : Blo 722323 816097 := bbase (se 2 (by rfl) ⟨306036, by rfl⟩ : syracuseStep 816097 = 612073) (by norm_num)
theorem B914429 : Blo 722323 914429 := bbase (se 3 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 914429 = 342911) (by norm_num)
theorem B816133 : Blo 722323 816133 := bbase (se 4 (by rfl) ⟨76512, by rfl⟩ : syracuseStep 816133 = 153025) (by norm_num)
theorem B816169 : Blo 722323 816169 := bbase (se 2 (by rfl) ⟨306063, by rfl⟩ : syracuseStep 816169 = 612127) (by norm_num)
theorem B1242157 : Blo 722323 1242157 := bbase (se 3 (by rfl) ⟨232904, by rfl⟩ : syracuseStep 1242157 = 465809) (by norm_num)
theorem B914485 : Blo 722323 914485 := bbase (se 5 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 914485 = 85733) (by norm_num)
theorem B5502005 : Blo 722323 5502005 := bbase (se 5 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 5502005 = 515813) (by norm_num)
theorem B1831997 : Blo 722323 1831997 := bbase (se 3 (by rfl) ⟨343499, by rfl⟩ : syracuseStep 1831997 = 686999) (by norm_num)
theorem B816205 : Blo 722323 816205 := bbase (se 3 (by rfl) ⟨153038, by rfl⟩ : syracuseStep 816205 = 306077) (by norm_num)
theorem B1373269 : Blo 722323 1373269 := bbase (se 8 (by rfl) ⟨8046, by rfl⟩ : syracuseStep 1373269 = 16093) (by norm_num)
theorem B816241 : Blo 722323 816241 := bbase (se 2 (by rfl) ⟨306090, by rfl⟩ : syracuseStep 816241 = 612181) (by norm_num)
theorem B914581 : Blo 722323 914581 := bbase (se 6 (by rfl) ⟨21435, by rfl⟩ : syracuseStep 914581 = 42871) (by norm_num)
theorem B816277 : Blo 722323 816277 := bbase (se 6 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 816277 = 38263) (by norm_num)
theorem B816313 : Blo 722323 816313 := bbase (se 2 (by rfl) ⟨306117, by rfl⟩ : syracuseStep 816313 = 612235) (by norm_num)
theorem B816349 : Blo 722323 816349 := bbase (se 3 (by rfl) ⟨153065, by rfl⟩ : syracuseStep 816349 = 306131) (by norm_num)
theorem B1373429 : Blo 722323 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B816385 : Blo 722323 816385 := bbase (se 2 (by rfl) ⟨306144, by rfl⟩ : syracuseStep 816385 = 612289) (by norm_num)
theorem B816421 : Blo 722323 816421 := bbase (se 4 (by rfl) ⟨76539, by rfl⟩ : syracuseStep 816421 = 153079) (by norm_num)
theorem B914753 : Blo 722323 914753 := bbase (se 2 (by rfl) ⟨343032, by rfl⟩ : syracuseStep 914753 = 686065) (by norm_num)
theorem B816457 : Blo 722323 816457 := bbase (se 2 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 816457 = 612343) (by norm_num)
theorem B816493 : Blo 722323 816493 := bbase (se 3 (by rfl) ⟨153092, by rfl⟩ : syracuseStep 816493 = 306185) (by norm_num)
theorem B914809 : Blo 722323 914809 := bbase (se 2 (by rfl) ⟨343053, by rfl⟩ : syracuseStep 914809 = 686107) (by norm_num)
theorem B1373573 : Blo 722323 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B816529 : Blo 722323 816529 := bbase (se 2 (by rfl) ⟨306198, by rfl⟩ : syracuseStep 816529 = 612397) (by norm_num)
theorem B1832341 : Blo 722323 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B2061749 : Blo 722323 2061749 := bbase (se 5 (by rfl) ⟨96644, by rfl⟩ : syracuseStep 2061749 = 193289) (by norm_num)
theorem B816565 : Blo 722323 816565 := bbase (se 5 (by rfl) ⟨38276, by rfl⟩ : syracuseStep 816565 = 76553) (by norm_num)
theorem B2749909 : Blo 722323 2749909 := bbase (se 7 (by rfl) ⟨32225, by rfl⟩ : syracuseStep 2749909 = 64451) (by norm_num)
theorem B914905 : Blo 722323 914905 := bbase (se 2 (by rfl) ⟨343089, by rfl⟩ : syracuseStep 914905 = 686179) (by norm_num)
theorem B816601 : Blo 722323 816601 := bbase (se 2 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 816601 = 612451) (by norm_num)
theorem B816637 : Blo 722323 816637 := bbase (se 3 (by rfl) ⟨153119, by rfl⟩ : syracuseStep 816637 = 306239) (by norm_num)
theorem B1832453 : Blo 722323 1832453 := bbase (se 4 (by rfl) ⟨171792, by rfl⟩ : syracuseStep 1832453 = 343585) (by norm_num)
theorem B816673 : Blo 722323 816673 := bbase (se 2 (by rfl) ⟨306252, by rfl⟩ : syracuseStep 816673 = 612505) (by norm_num)
theorem B816709 : Blo 722323 816709 := bbase (se 4 (by rfl) ⟨76566, by rfl⟩ : syracuseStep 816709 = 153133) (by norm_num)
theorem B980581 : Blo 722323 980581 := bbase (se 4 (by rfl) ⟨91929, by rfl⟩ : syracuseStep 980581 = 183859) (by norm_num)
theorem B816745 : Blo 722323 816745 := bbase (se 2 (by rfl) ⟨306279, by rfl⟩ : syracuseStep 816745 = 612559) (by norm_num)
theorem B915077 : Blo 722323 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B816781 : Blo 722323 816781 := bbase (se 3 (by rfl) ⟨153146, by rfl⟩ : syracuseStep 816781 = 306293) (by norm_num)
theorem B1373861 : Blo 722323 1373861 := bbase (se 4 (by rfl) ⟨128799, by rfl⟩ : syracuseStep 1373861 = 257599) (by norm_num)
theorem B816817 : Blo 722323 816817 := bbase (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) (by norm_num)
theorem B5961397 : Blo 722323 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B915133 : Blo 722323 915133 := bbase (se 3 (by rfl) ⟨171587, by rfl⟩ : syracuseStep 915133 = 343175) (by norm_num)
theorem B1832645 : Blo 722323 1832645 := bbase (se 4 (by rfl) ⟨171810, by rfl⟩ : syracuseStep 1832645 = 343621) (by norm_num)
theorem B816853 : Blo 722323 816853 := bbase (se 7 (by rfl) ⟨9572, by rfl⟩ : syracuseStep 816853 = 19145) (by norm_num)
theorem B816889 : Blo 722323 816889 := bbase (se 2 (by rfl) ⟨306333, by rfl⟩ : syracuseStep 816889 = 612667) (by norm_num)
theorem B2750213 : Blo 722323 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B2782997 : Blo 722323 2782997 := bbase (se 6 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 2782997 = 130453) (by norm_num)
theorem B915229 : Blo 722323 915229 := bbase (se 3 (by rfl) ⟨171605, by rfl⟩ : syracuseStep 915229 = 343211) (by norm_num)
theorem B816925 : Blo 722323 816925 := bbase (se 3 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 816925 = 306347) (by norm_num)
theorem B1374013 : Blo 722323 1374013 := bbase (se 3 (by rfl) ⟨257627, by rfl⟩ : syracuseStep 1374013 = 515255) (by norm_num)
theorem B816961 : Blo 722323 816961 := bbase (se 2 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 816961 = 612721) (by norm_num)
theorem B816997 : Blo 722323 816997 := bbase (se 4 (by rfl) ⟨76593, by rfl⟩ : syracuseStep 816997 = 153187) (by norm_num)
theorem B980861 : Blo 722323 980861 := bbase (se 3 (by rfl) ⟨183911, by rfl⟩ : syracuseStep 980861 = 367823) (by norm_num)
theorem B817033 : Blo 722323 817033 := bbase (se 2 (by rfl) ⟨306387, by rfl⟩ : syracuseStep 817033 = 612775) (by norm_num)
theorem B2324389 : Blo 722323 2324389 := bbase (se 4 (by rfl) ⟨217911, by rfl⟩ : syracuseStep 2324389 = 435823) (by norm_num)
theorem B817069 : Blo 722323 817069 := bbase (se 3 (by rfl) ⟨153200, by rfl⟩ : syracuseStep 817069 = 306401) (by norm_num)
theorem B915401 : Blo 722323 915401 := bbase (se 2 (by rfl) ⟨343275, by rfl⟩ : syracuseStep 915401 = 686551) (by norm_num)
theorem B817105 : Blo 722323 817105 := bbase (se 2 (by rfl) ⟨306414, by rfl⟩ : syracuseStep 817105 = 612829) (by norm_num)
theorem B915457 : Blo 722323 915457 := bbase (se 2 (by rfl) ⟨343296, by rfl⟩ : syracuseStep 915457 = 686593) (by norm_num)
theorem B1832989 : Blo 722323 1832989 := bbase (se 3 (by rfl) ⟨343685, by rfl⟩ : syracuseStep 1832989 = 687371) (by norm_num)
theorem B915553 : Blo 722323 915553 := bbase (se 2 (by rfl) ⟨343332, by rfl⟩ : syracuseStep 915553 = 686665) (by norm_num)
theorem B1374317 : Blo 722323 1374317 := bbase (se 3 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 1374317 = 515369) (by norm_num)
theorem B1833101 : Blo 722323 1833101 := bbase (se 3 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 1833101 = 687413) (by norm_num)
theorem B3668165 : Blo 722323 3668165 := bbase (se 4 (by rfl) ⟨343890, by rfl⟩ : syracuseStep 3668165 = 687781) (by norm_num)
theorem B3471589 : Blo 722323 3471589 := bbase (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) (by norm_num)
theorem B915725 : Blo 722323 915725 := bbase (se 3 (by rfl) ⟨171698, by rfl⟩ : syracuseStep 915725 = 343397) (by norm_num)
theorem B915781 : Blo 722323 915781 := bbase (se 4 (by rfl) ⟨85854, by rfl⟩ : syracuseStep 915781 = 171709) (by norm_num)
theorem B1833293 : Blo 722323 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B915877 : Blo 722323 915877 := bbase (se 4 (by rfl) ⟨85863, by rfl⟩ : syracuseStep 915877 = 171727) (by norm_num)
theorem B981445 : Blo 722323 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B916049 : Blo 722323 916049 := bbase (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) (by norm_num)
theorem B981613 : Blo 722323 981613 := bbase (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) (by norm_num)
theorem B916105 : Blo 722323 916105 := bbase (se 2 (by rfl) ⟨343539, by rfl⟩ : syracuseStep 916105 = 687079) (by norm_num)
theorem B1833637 : Blo 722323 1833637 := bbase (se 4 (by rfl) ⟨171903, by rfl⟩ : syracuseStep 1833637 = 343807) (by norm_num)
theorem B916201 : Blo 722323 916201 := bbase (se 2 (by rfl) ⟨343575, by rfl⟩ : syracuseStep 916201 = 687151) (by norm_num)
theorem B1833749 : Blo 722323 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1178389 : Blo 722323 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B3144485 : Blo 722323 3144485 := bbase (se 4 (by rfl) ⟨294795, by rfl⟩ : syracuseStep 3144485 = 589591) (by norm_num)
theorem B1375069 : Blo 722323 1375069 := bbase (se 3 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 1375069 = 515651) (by norm_num)
theorem B916373 : Blo 722323 916373 := bbase (se 6 (by rfl) ⟨21477, by rfl⟩ : syracuseStep 916373 = 42955) (by norm_num)
theorem B916429 : Blo 722323 916429 := bbase (se 3 (by rfl) ⟨171830, by rfl⟩ : syracuseStep 916429 = 343661) (by norm_num)
theorem B1833941 : Blo 722323 1833941 := bbase (se 7 (by rfl) ⟨21491, by rfl⟩ : syracuseStep 1833941 = 42983) (by norm_num)
theorem B2063333 : Blo 722323 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B1375213 : Blo 722323 1375213 := bbase (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) (by norm_num)
theorem B916525 : Blo 722323 916525 := bbase (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) (by norm_num)
theorem B1735757 : Blo 722323 1735757 := bbase (se 3 (by rfl) ⟨325454, by rfl⟩ : syracuseStep 1735757 = 650909) (by norm_num)
theorem B1375373 : Blo 722323 1375373 := bbase (se 3 (by rfl) ⟨257882, by rfl⟩ : syracuseStep 1375373 = 515765) (by norm_num)
theorem B916697 : Blo 722323 916697 := bbase (se 2 (by rfl) ⟨343761, by rfl⟩ : syracuseStep 916697 = 687523) (by norm_num)
theorem B916753 : Blo 722323 916753 := bbase (se 2 (by rfl) ⟨343782, by rfl⟩ : syracuseStep 916753 = 687565) (by norm_num)
theorem B1375517 : Blo 722323 1375517 := bbase (se 3 (by rfl) ⟨257909, by rfl⟩ : syracuseStep 1375517 = 515819) (by norm_num)
theorem B1834285 : Blo 722323 1834285 := bbase (se 3 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 1834285 = 687857) (by norm_num)
theorem B916849 : Blo 722323 916849 := bbase (se 2 (by rfl) ⟨343818, by rfl⟩ : syracuseStep 916849 = 687637) (by norm_num)
theorem B1834397 : Blo 722323 1834397 := bbase (se 3 (by rfl) ⟨343949, by rfl⟩ : syracuseStep 1834397 = 687899) (by norm_num)
theorem B3669461 : Blo 722323 3669461 := bbase (se 7 (by rfl) ⟨43001, by rfl⟩ : syracuseStep 3669461 = 86003) (by norm_num)
theorem B917021 : Blo 722323 917021 := bbase (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) (by norm_num)
theorem B1375805 : Blo 722323 1375805 := bbase (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) (by norm_num)
theorem B917077 : Blo 722323 917077 := bbase (se 8 (by rfl) ⟨5373, by rfl⟩ : syracuseStep 917077 = 10747) (by norm_num)
theorem B1834589 : Blo 722323 1834589 := bbase (se 3 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 1834589 = 687971) (by norm_num)
theorem B2064005 : Blo 722323 2064005 := bbase (se 4 (by rfl) ⟨193500, by rfl⟩ : syracuseStep 2064005 = 387001) (by norm_num)
theorem B4947605 : Blo 722323 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B917173 : Blo 722323 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B1375957 : Blo 722323 1375957 := bbase (se 7 (by rfl) ⟨16124, by rfl⟩ : syracuseStep 1375957 = 32249) (by norm_num)
theorem B2752325 : Blo 722323 2752325 := bbase (se 4 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 2752325 = 516061) (by norm_num)
theorem B917345 : Blo 722323 917345 := bbase (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) (by norm_num)
theorem B917401 : Blo 722323 917401 := bbase (se 2 (by rfl) ⟨344025, by rfl⟩ : syracuseStep 917401 = 688051) (by norm_num)
theorem B1834933 : Blo 722323 1834933 := bbase (se 5 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 1834933 = 172025) (by norm_num)
theorem B917497 : Blo 722323 917497 := bbase (se 2 (by rfl) ⟨344061, by rfl⟩ : syracuseStep 917497 = 688123) (by norm_num)
theorem B917507 : Blo 722323 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B1376291 : Blo 722323 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B1835075 : Blo 722323 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B4128965 : Blo 722323 4128965 := bstep (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) B774181
theorem B4653389 : Blo 722323 4653389 := bstep (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) B1745021
theorem B1114579 : Blo 722323 1114579 := bstep (se 1 (by rfl) ⟨835934, by rfl⟩ : syracuseStep 1114579 = 1671869) B1671869
theorem B2064973 : Blo 722323 2064973 := bstep (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) B774365
theorem B918211 : Blo 722323 918211 := bstep (se 1 (by rfl) ⟨688658, by rfl⟩ : syracuseStep 918211 = 1377317) B1377317
theorem B918307 : Blo 722323 918307 := bstep (se 1 (by rfl) ⟨688730, by rfl⟩ : syracuseStep 918307 = 1377461) B1377461
theorem B4129649 : Blo 722323 4129649 := bstep (se 2 (by rfl) ⟨1548618, by rfl⟩ : syracuseStep 4129649 = 3097237) B3097237
theorem B19104709 : Blo 722323 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1377233 : Blo 722323 1377233 := bstep (se 2 (by rfl) ⟨516462, by rfl⟩ : syracuseStep 1377233 = 1032925) B1032925
theorem B1836017 : Blo 722323 1836017 := bstep (se 2 (by rfl) ⟨688506, by rfl⟩ : syracuseStep 1836017 = 1377013) B1377013
theorem B1836067 : Blo 722323 1836067 := bstep (se 1 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 1836067 = 2754101) B2754101
theorem B2753585 : Blo 722323 2753585 := bstep (se 2 (by rfl) ⟨1032594, by rfl⟩ : syracuseStep 2753585 = 2065189) B2065189
theorem B1836209 : Blo 722323 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B18515141 : Blo 722323 18515141 := bstep (se 4 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 18515141 = 3471589) B3471589
theorem B9045233 : Blo 722323 9045233 := bstep (se 2 (by rfl) ⟨3391962, by rfl⟩ : syracuseStep 9045233 = 6783925) B6783925
theorem B918803 : Blo 722323 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B722323 : Blo 722323 722323 := bstep (se 1 (by rfl) ⟨541742, by rfl⟩ : syracuseStep 722323 = 1083485) B1083485
theorem B722339 : Blo 722323 722339 := bstep (se 1 (by rfl) ⟨541754, by rfl⟩ : syracuseStep 722339 = 1083509) B1083509
theorem B2786723 : Blo 722323 2786723 := bstep (se 1 (by rfl) ⟨2090042, by rfl⟩ : syracuseStep 2786723 = 4180085) B4180085
theorem B722355 : Blo 722323 722355 := bstep (se 1 (by rfl) ⟨541766, by rfl⟩ : syracuseStep 722355 = 1083533) B1083533
theorem B722371 : Blo 722323 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B722387 : Blo 722323 722387 := bstep (se 1 (by rfl) ⟨541790, by rfl⟩ : syracuseStep 722387 = 1083581) B1083581
theorem B722403 : Blo 722323 722403 := bstep (se 1 (by rfl) ⟨541802, by rfl⟩ : syracuseStep 722403 = 1083605) B1083605
theorem B722419 : Blo 722323 722419 := bstep (se 1 (by rfl) ⟨541814, by rfl⟩ : syracuseStep 722419 = 1083629) B1083629
theorem B722435 : Blo 722323 722435 := bstep (se 1 (by rfl) ⟨541826, by rfl⟩ : syracuseStep 722435 = 1083653) B1083653
theorem B722451 : Blo 722323 722451 := bstep (se 1 (by rfl) ⟨541838, by rfl⟩ : syracuseStep 722451 = 1083677) B1083677
theorem B722467 : Blo 722323 722467 := bstep (se 1 (by rfl) ⟨541850, by rfl⟩ : syracuseStep 722467 = 1083701) B1083701
theorem B722483 : Blo 722323 722483 := bstep (se 1 (by rfl) ⟨541862, by rfl⟩ : syracuseStep 722483 = 1083725) B1083725
theorem B722499 : Blo 722323 722499 := bstep (se 1 (by rfl) ⟨541874, by rfl⟩ : syracuseStep 722499 = 1083749) B1083749
theorem B722515 : Blo 722323 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B722531 : Blo 722323 722531 := bstep (se 1 (by rfl) ⟨541898, by rfl⟩ : syracuseStep 722531 = 1083797) B1083797
theorem B722547 : Blo 722323 722547 := bstep (se 1 (by rfl) ⟨541910, by rfl⟩ : syracuseStep 722547 = 1083821) B1083821
theorem B722563 : Blo 722323 722563 := bstep (se 1 (by rfl) ⟨541922, by rfl⟩ : syracuseStep 722563 = 1083845) B1083845
theorem B722579 : Blo 722323 722579 := bstep (se 1 (by rfl) ⟨541934, by rfl⟩ : syracuseStep 722579 = 1083869) B1083869
theorem B722595 : Blo 722323 722595 := bstep (se 1 (by rfl) ⟨541946, by rfl⟩ : syracuseStep 722595 = 1083893) B1083893
theorem B3671729 : Blo 722323 3671729 := bstep (se 2 (by rfl) ⟨1376898, by rfl⟩ : syracuseStep 3671729 = 2753797) B2753797
theorem B722611 : Blo 722323 722611 := bstep (se 1 (by rfl) ⟨541958, by rfl⟩ : syracuseStep 722611 = 1083917) B1083917
theorem B722627 : Blo 722323 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B722643 : Blo 722323 722643 := bstep (se 1 (by rfl) ⟨541982, by rfl⟩ : syracuseStep 722643 = 1083965) B1083965
theorem B722659 : Blo 722323 722659 := bstep (se 1 (by rfl) ⟨541994, by rfl⟩ : syracuseStep 722659 = 1083989) B1083989
theorem B722675 : Blo 722323 722675 := bstep (se 1 (by rfl) ⟨542006, by rfl⟩ : syracuseStep 722675 = 1084013) B1084013
theorem B722691 : Blo 722323 722691 := bstep (se 1 (by rfl) ⟨542018, by rfl⟩ : syracuseStep 722691 = 1084037) B1084037
theorem B722707 : Blo 722323 722707 := bstep (se 1 (by rfl) ⟨542030, by rfl⟩ : syracuseStep 722707 = 1084061) B1084061
theorem B722723 : Blo 722323 722723 := bstep (se 1 (by rfl) ⟨542042, by rfl⟩ : syracuseStep 722723 = 1084085) B1084085
theorem B722739 : Blo 722323 722739 := bstep (se 1 (by rfl) ⟨542054, by rfl⟩ : syracuseStep 722739 = 1084109) B1084109
theorem B722755 : Blo 722323 722755 := bstep (se 1 (by rfl) ⟨542066, by rfl⟩ : syracuseStep 722755 = 1084133) B1084133
theorem B1378129 : Blo 722323 1378129 := bstep (se 2 (by rfl) ⟨516798, by rfl⟩ : syracuseStep 1378129 = 1033597) B1033597
theorem B722771 : Blo 722323 722771 := bstep (se 1 (by rfl) ⟨542078, by rfl⟩ : syracuseStep 722771 = 1084157) B1084157
theorem B722787 : Blo 722323 722787 := bstep (se 1 (by rfl) ⟨542090, by rfl⟩ : syracuseStep 722787 = 1084181) B1084181
theorem B722803 : Blo 722323 722803 := bstep (se 1 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 722803 = 1084205) B1084205
theorem B722819 : Blo 722323 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B21202829 : Blo 722323 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B722835 : Blo 722323 722835 := bstep (se 1 (by rfl) ⟨542126, by rfl⟩ : syracuseStep 722835 = 1084253) B1084253
theorem B722851 : Blo 722323 722851 := bstep (se 1 (by rfl) ⟨542138, by rfl⟩ : syracuseStep 722851 = 1084277) B1084277
theorem B722867 : Blo 722323 722867 := bstep (se 1 (by rfl) ⟨542150, by rfl⟩ : syracuseStep 722867 = 1084301) B1084301
theorem B722883 : Blo 722323 722883 := bstep (se 1 (by rfl) ⟨542162, by rfl⟩ : syracuseStep 722883 = 1084325) B1084325
theorem B722899 : Blo 722323 722899 := bstep (se 1 (by rfl) ⟨542174, by rfl⟩ : syracuseStep 722899 = 1084349) B1084349
theorem B722915 : Blo 722323 722915 := bstep (se 1 (by rfl) ⟨542186, by rfl⟩ : syracuseStep 722915 = 1084373) B1084373
theorem B8259569 : Blo 722323 8259569 := bstep (se 2 (by rfl) ⟨3097338, by rfl⟩ : syracuseStep 8259569 = 6194677) B6194677
theorem B722931 : Blo 722323 722931 := bstep (se 1 (by rfl) ⟨542198, by rfl⟩ : syracuseStep 722931 = 1084397) B1084397
theorem B1378289 : Blo 722323 1378289 := bstep (se 2 (by rfl) ⟨516858, by rfl⟩ : syracuseStep 1378289 = 1033717) B1033717
theorem B722947 : Blo 722323 722947 := bstep (se 1 (by rfl) ⟨542210, by rfl⟩ : syracuseStep 722947 = 1084421) B1084421
theorem B722963 : Blo 722323 722963 := bstep (se 1 (by rfl) ⟨542222, by rfl⟩ : syracuseStep 722963 = 1084445) B1084445
theorem B722979 : Blo 722323 722979 := bstep (se 1 (by rfl) ⟨542234, by rfl⟩ : syracuseStep 722979 = 1084469) B1084469
theorem B722995 : Blo 722323 722995 := bstep (se 1 (by rfl) ⟨542246, by rfl⟩ : syracuseStep 722995 = 1084493) B1084493
theorem B723011 : Blo 722323 723011 := bstep (se 1 (by rfl) ⟨542258, by rfl⟩ : syracuseStep 723011 = 1084517) B1084517
theorem B723027 : Blo 722323 723027 := bstep (se 1 (by rfl) ⟨542270, by rfl⟩ : syracuseStep 723027 = 1084541) B1084541
theorem B1083491 : Blo 722323 1083491 := bstep (se 1 (by rfl) ⟨812618, by rfl⟩ : syracuseStep 1083491 = 1625237) B1625237
theorem B723043 : Blo 722323 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B723059 : Blo 722323 723059 := bstep (se 1 (by rfl) ⟨542294, by rfl⟩ : syracuseStep 723059 = 1084589) B1084589
theorem B1083521 : Blo 722323 1083521 := bstep (se 2 (by rfl) ⟨406320, by rfl⟩ : syracuseStep 1083521 = 812641) B812641
theorem B723075 : Blo 722323 723075 := bstep (se 1 (by rfl) ⟨542306, by rfl⟩ : syracuseStep 723075 = 1084613) B1084613
theorem B1837201 : Blo 722323 1837201 := bstep (se 2 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 1837201 = 1377901) B1377901
theorem B1083539 : Blo 722323 1083539 := bstep (se 1 (by rfl) ⟨812654, by rfl⟩ : syracuseStep 1083539 = 1625309) B1625309
theorem B723091 : Blo 722323 723091 := bstep (se 1 (by rfl) ⟨542318, by rfl⟩ : syracuseStep 723091 = 1084637) B1084637
theorem B723107 : Blo 722323 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B1083569 : Blo 722323 1083569 := bstep (se 2 (by rfl) ⟨406338, by rfl⟩ : syracuseStep 1083569 = 812677) B812677
theorem B723123 : Blo 722323 723123 := bstep (se 1 (by rfl) ⟨542342, by rfl⟩ : syracuseStep 723123 = 1084685) B1084685
theorem B1083587 : Blo 722323 1083587 := bstep (se 1 (by rfl) ⟨812690, by rfl⟩ : syracuseStep 1083587 = 1625381) B1625381
theorem B723139 : Blo 722323 723139 := bstep (se 1 (by rfl) ⟨542354, by rfl⟩ : syracuseStep 723139 = 1084709) B1084709
theorem B723155 : Blo 722323 723155 := bstep (se 1 (by rfl) ⟨542366, by rfl⟩ : syracuseStep 723155 = 1084733) B1084733
theorem B1083617 : Blo 722323 1083617 := bstep (se 2 (by rfl) ⟨406356, by rfl⟩ : syracuseStep 1083617 = 812713) B812713
theorem B723171 : Blo 722323 723171 := bstep (se 1 (by rfl) ⟨542378, by rfl⟩ : syracuseStep 723171 = 1084757) B1084757
theorem B1083635 : Blo 722323 1083635 := bstep (se 1 (by rfl) ⟨812726, by rfl⟩ : syracuseStep 1083635 = 1625453) B1625453
theorem B723187 : Blo 722323 723187 := bstep (se 1 (by rfl) ⟨542390, by rfl⟩ : syracuseStep 723187 = 1084781) B1084781
theorem B723203 : Blo 722323 723203 := bstep (se 1 (by rfl) ⟨542402, by rfl⟩ : syracuseStep 723203 = 1084805) B1084805
theorem B1083665 : Blo 722323 1083665 := bstep (se 2 (by rfl) ⟨406374, by rfl⟩ : syracuseStep 1083665 = 812749) B812749
theorem B2066705 : Blo 722323 2066705 := bstep (se 2 (by rfl) ⟨775014, by rfl⟩ : syracuseStep 2066705 = 1550029) B1550029
theorem B723219 : Blo 722323 723219 := bstep (se 1 (by rfl) ⟨542414, by rfl⟩ : syracuseStep 723219 = 1084829) B1084829
theorem B1083683 : Blo 722323 1083683 := bstep (se 1 (by rfl) ⟨812762, by rfl⟩ : syracuseStep 1083683 = 1625525) B1625525
theorem B723235 : Blo 722323 723235 := bstep (se 1 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 723235 = 1084853) B1084853
theorem B4131107 : Blo 722323 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B723251 : Blo 722323 723251 := bstep (se 1 (by rfl) ⟨542438, by rfl⟩ : syracuseStep 723251 = 1084877) B1084877
theorem B1083713 : Blo 722323 1083713 := bstep (se 2 (by rfl) ⟨406392, by rfl⟩ : syracuseStep 1083713 = 812785) B812785
theorem B723267 : Blo 722323 723267 := bstep (se 1 (by rfl) ⟨542450, by rfl⟩ : syracuseStep 723267 = 1084901) B1084901
theorem B1083731 : Blo 722323 1083731 := bstep (se 1 (by rfl) ⟨812798, by rfl⟩ : syracuseStep 1083731 = 1625597) B1625597
theorem B723283 : Blo 722323 723283 := bstep (se 1 (by rfl) ⟨542462, by rfl⟩ : syracuseStep 723283 = 1084925) B1084925
theorem B723299 : Blo 722323 723299 := bstep (se 1 (by rfl) ⟨542474, by rfl⟩ : syracuseStep 723299 = 1084949) B1084949
theorem B1083761 : Blo 722323 1083761 := bstep (se 2 (by rfl) ⟨406410, by rfl⟩ : syracuseStep 1083761 = 812821) B812821
theorem B723315 : Blo 722323 723315 := bstep (se 1 (by rfl) ⟨542486, by rfl⟩ : syracuseStep 723315 = 1084973) B1084973
theorem B1083779 : Blo 722323 1083779 := bstep (se 1 (by rfl) ⟨812834, by rfl⟩ : syracuseStep 1083779 = 1625669) B1625669
theorem B723331 : Blo 722323 723331 := bstep (se 1 (by rfl) ⟨542498, by rfl⟩ : syracuseStep 723331 = 1084997) B1084997
theorem B1378691 : Blo 722323 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B723347 : Blo 722323 723347 := bstep (se 1 (by rfl) ⟨542510, by rfl⟩ : syracuseStep 723347 = 1085021) B1085021
theorem B1083809 : Blo 722323 1083809 := bstep (se 2 (by rfl) ⟨406428, by rfl⟩ : syracuseStep 1083809 = 812857) B812857
theorem B723363 : Blo 722323 723363 := bstep (se 1 (by rfl) ⟨542522, by rfl⟩ : syracuseStep 723363 = 1085045) B1085045
theorem B1837475 : Blo 722323 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B1083827 : Blo 722323 1083827 := bstep (se 1 (by rfl) ⟨812870, by rfl⟩ : syracuseStep 1083827 = 1625741) B1625741
theorem B723379 : Blo 722323 723379 := bstep (se 1 (by rfl) ⟨542534, by rfl⟩ : syracuseStep 723379 = 1085069) B1085069
theorem B723395 : Blo 722323 723395 := bstep (se 1 (by rfl) ⟨542546, by rfl⟩ : syracuseStep 723395 = 1085093) B1085093
theorem B1083857 : Blo 722323 1083857 := bstep (se 2 (by rfl) ⟨406446, by rfl⟩ : syracuseStep 1083857 = 812893) B812893
theorem B2066897 : Blo 722323 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B723411 : Blo 722323 723411 := bstep (se 1 (by rfl) ⟨542558, by rfl⟩ : syracuseStep 723411 = 1085117) B1085117
theorem B1083875 : Blo 722323 1083875 := bstep (se 1 (by rfl) ⟨812906, by rfl⟩ : syracuseStep 1083875 = 1625813) B1625813
theorem B723427 : Blo 722323 723427 := bstep (se 1 (by rfl) ⟨542570, by rfl⟩ : syracuseStep 723427 = 1085141) B1085141
theorem B2755043 : Blo 722323 2755043 := bstep (se 1 (by rfl) ⟨2066282, by rfl⟩ : syracuseStep 2755043 = 4132565) B4132565
theorem B723443 : Blo 722323 723443 := bstep (se 1 (by rfl) ⟨542582, by rfl⟩ : syracuseStep 723443 = 1085165) B1085165
theorem B1083905 : Blo 722323 1083905 := bstep (se 2 (by rfl) ⟨406464, by rfl⟩ : syracuseStep 1083905 = 812929) B812929
theorem B723459 : Blo 722323 723459 := bstep (se 1 (by rfl) ⟨542594, by rfl⟩ : syracuseStep 723459 = 1085189) B1085189
theorem B1083923 : Blo 722323 1083923 := bstep (se 1 (by rfl) ⟨812942, by rfl⟩ : syracuseStep 1083923 = 1625885) B1625885
theorem B723475 : Blo 722323 723475 := bstep (se 1 (by rfl) ⟨542606, by rfl⟩ : syracuseStep 723475 = 1085213) B1085213
theorem B723491 : Blo 722323 723491 := bstep (se 1 (by rfl) ⟨542618, by rfl⟩ : syracuseStep 723491 = 1085237) B1085237
theorem B1083953 : Blo 722323 1083953 := bstep (se 2 (by rfl) ⟨406482, by rfl⟩ : syracuseStep 1083953 = 812965) B812965
theorem B723507 : Blo 722323 723507 := bstep (se 1 (by rfl) ⟨542630, by rfl⟩ : syracuseStep 723507 = 1085261) B1085261
theorem B1083971 : Blo 722323 1083971 := bstep (se 1 (by rfl) ⟨812978, by rfl⟩ : syracuseStep 1083971 = 1625957) B1625957
theorem B723523 : Blo 722323 723523 := bstep (se 1 (by rfl) ⟨542642, by rfl⟩ : syracuseStep 723523 = 1085285) B1085285
theorem B723539 : Blo 722323 723539 := bstep (se 1 (by rfl) ⟨542654, by rfl⟩ : syracuseStep 723539 = 1085309) B1085309
theorem B1084001 : Blo 722323 1084001 := bstep (se 2 (by rfl) ⟨406500, by rfl⟩ : syracuseStep 1084001 = 813001) B813001
theorem B723555 : Blo 722323 723555 := bstep (se 1 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 723555 = 1085333) B1085333
theorem B1837667 : Blo 722323 1837667 := bstep (se 1 (by rfl) ⟨1378250, by rfl⟩ : syracuseStep 1837667 = 2756501) B2756501
theorem B1084019 : Blo 722323 1084019 := bstep (se 1 (by rfl) ⟨813014, by rfl⟩ : syracuseStep 1084019 = 1626029) B1626029
theorem B723571 : Blo 722323 723571 := bstep (se 1 (by rfl) ⟨542678, by rfl⟩ : syracuseStep 723571 = 1085357) B1085357
theorem B723587 : Blo 722323 723587 := bstep (se 1 (by rfl) ⟨542690, by rfl⟩ : syracuseStep 723587 = 1085381) B1085381
theorem B1084049 : Blo 722323 1084049 := bstep (se 2 (by rfl) ⟨406518, by rfl⟩ : syracuseStep 1084049 = 813037) B813037
theorem B723603 : Blo 722323 723603 := bstep (se 1 (by rfl) ⟨542702, by rfl⟩ : syracuseStep 723603 = 1085405) B1085405
theorem B1084067 : Blo 722323 1084067 := bstep (se 1 (by rfl) ⟨813050, by rfl⟩ : syracuseStep 1084067 = 1626101) B1626101
theorem B723619 : Blo 722323 723619 := bstep (se 1 (by rfl) ⟨542714, by rfl⟩ : syracuseStep 723619 = 1085429) B1085429
theorem B723635 : Blo 722323 723635 := bstep (se 1 (by rfl) ⟨542726, by rfl⟩ : syracuseStep 723635 = 1085453) B1085453
theorem B1084097 : Blo 722323 1084097 := bstep (se 2 (by rfl) ⟨406536, by rfl⟩ : syracuseStep 1084097 = 813073) B813073
theorem B723651 : Blo 722323 723651 := bstep (se 1 (by rfl) ⟨542738, by rfl⟩ : syracuseStep 723651 = 1085477) B1085477
theorem B1084115 : Blo 722323 1084115 := bstep (se 1 (by rfl) ⟨813086, by rfl⟩ : syracuseStep 1084115 = 1626173) B1626173
theorem B723667 : Blo 722323 723667 := bstep (se 1 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 723667 = 1085501) B1085501
theorem B723683 : Blo 722323 723683 := bstep (se 1 (by rfl) ⟨542762, by rfl⟩ : syracuseStep 723683 = 1085525) B1085525
theorem B1084145 : Blo 722323 1084145 := bstep (se 2 (by rfl) ⟨406554, by rfl⟩ : syracuseStep 1084145 = 813109) B813109
theorem B723699 : Blo 722323 723699 := bstep (se 1 (by rfl) ⟨542774, by rfl⟩ : syracuseStep 723699 = 1085549) B1085549
theorem B1084163 : Blo 722323 1084163 := bstep (se 1 (by rfl) ⟨813122, by rfl⟩ : syracuseStep 1084163 = 1626245) B1626245
theorem B723715 : Blo 722323 723715 := bstep (se 1 (by rfl) ⟨542786, by rfl⟩ : syracuseStep 723715 = 1085573) B1085573
theorem B723731 : Blo 722323 723731 := bstep (se 1 (by rfl) ⟨542798, by rfl⟩ : syracuseStep 723731 = 1085597) B1085597
theorem B1084193 : Blo 722323 1084193 := bstep (se 2 (by rfl) ⟨406572, by rfl⟩ : syracuseStep 1084193 = 813145) B813145
theorem B723747 : Blo 722323 723747 := bstep (se 1 (by rfl) ⟨542810, by rfl⟩ : syracuseStep 723747 = 1085621) B1085621
theorem B1084211 : Blo 722323 1084211 := bstep (se 1 (by rfl) ⟨813158, by rfl⟩ : syracuseStep 1084211 = 1626317) B1626317
theorem B723763 : Blo 722323 723763 := bstep (se 1 (by rfl) ⟨542822, by rfl⟩ : syracuseStep 723763 = 1085645) B1085645
theorem B723779 : Blo 722323 723779 := bstep (se 1 (by rfl) ⟨542834, by rfl⟩ : syracuseStep 723779 = 1085669) B1085669
theorem B1084241 : Blo 722323 1084241 := bstep (se 2 (by rfl) ⟨406590, by rfl⟩ : syracuseStep 1084241 = 813181) B813181
theorem B723795 : Blo 722323 723795 := bstep (se 1 (by rfl) ⟨542846, by rfl⟩ : syracuseStep 723795 = 1085693) B1085693
theorem B1084259 : Blo 722323 1084259 := bstep (se 1 (by rfl) ⟨813194, by rfl⟩ : syracuseStep 1084259 = 1626389) B1626389
theorem B723811 : Blo 722323 723811 := bstep (se 1 (by rfl) ⟨542858, by rfl⟩ : syracuseStep 723811 = 1085717) B1085717
theorem B723827 : Blo 722323 723827 := bstep (se 1 (by rfl) ⟨542870, by rfl⟩ : syracuseStep 723827 = 1085741) B1085741
theorem B1084289 : Blo 722323 1084289 := bstep (se 2 (by rfl) ⟨406608, by rfl⟩ : syracuseStep 1084289 = 813217) B813217
theorem B723843 : Blo 722323 723843 := bstep (se 1 (by rfl) ⟨542882, by rfl⟩ : syracuseStep 723843 = 1085765) B1085765
theorem B1084307 : Blo 722323 1084307 := bstep (se 1 (by rfl) ⟨813230, by rfl⟩ : syracuseStep 1084307 = 1626461) B1626461
theorem B723859 : Blo 722323 723859 := bstep (se 1 (by rfl) ⟨542894, by rfl⟩ : syracuseStep 723859 = 1085789) B1085789
theorem B723875 : Blo 722323 723875 := bstep (se 1 (by rfl) ⟨542906, by rfl⟩ : syracuseStep 723875 = 1085813) B1085813
theorem B1084337 : Blo 722323 1084337 := bstep (se 2 (by rfl) ⟨406626, by rfl⟩ : syracuseStep 1084337 = 813253) B813253
theorem B723891 : Blo 722323 723891 := bstep (se 1 (by rfl) ⟨542918, by rfl⟩ : syracuseStep 723891 = 1085837) B1085837
theorem B1084355 : Blo 722323 1084355 := bstep (se 1 (by rfl) ⟨813266, by rfl⟩ : syracuseStep 1084355 = 1626533) B1626533
theorem B723907 : Blo 722323 723907 := bstep (se 1 (by rfl) ⟨542930, by rfl⟩ : syracuseStep 723907 = 1085861) B1085861
theorem B12356549 : Blo 722323 12356549 := bstep (se 4 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 12356549 = 2316853) B2316853
theorem B723923 : Blo 722323 723923 := bstep (se 1 (by rfl) ⟨542942, by rfl⟩ : syracuseStep 723923 = 1085885) B1085885
theorem B1084385 : Blo 722323 1084385 := bstep (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) B813289
theorem B723939 : Blo 722323 723939 := bstep (se 1 (by rfl) ⟨542954, by rfl⟩ : syracuseStep 723939 = 1085909) B1085909
theorem B1084403 : Blo 722323 1084403 := bstep (se 1 (by rfl) ⟨813302, by rfl⟩ : syracuseStep 1084403 = 1626605) B1626605
theorem B723955 : Blo 722323 723955 := bstep (se 1 (by rfl) ⟨542966, by rfl⟩ : syracuseStep 723955 = 1085933) B1085933
theorem B723971 : Blo 722323 723971 := bstep (se 1 (by rfl) ⟨542978, by rfl⟩ : syracuseStep 723971 = 1085957) B1085957
theorem B1084433 : Blo 722323 1084433 := bstep (se 2 (by rfl) ⟨406662, by rfl⟩ : syracuseStep 1084433 = 813325) B813325
theorem B723987 : Blo 722323 723987 := bstep (se 1 (by rfl) ⟨542990, by rfl⟩ : syracuseStep 723987 = 1085981) B1085981
theorem B1084451 : Blo 722323 1084451 := bstep (se 1 (by rfl) ⟨813338, by rfl⟩ : syracuseStep 1084451 = 1626677) B1626677
theorem B724003 : Blo 722323 724003 := bstep (se 1 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 724003 = 1086005) B1086005
theorem B724019 : Blo 722323 724019 := bstep (se 1 (by rfl) ⟨543014, by rfl⟩ : syracuseStep 724019 = 1086029) B1086029
theorem B1084481 : Blo 722323 1084481 := bstep (se 2 (by rfl) ⟨406680, by rfl⟩ : syracuseStep 1084481 = 813361) B813361
theorem B724035 : Blo 722323 724035 := bstep (se 1 (by rfl) ⟨543026, by rfl⟩ : syracuseStep 724035 = 1086053) B1086053
theorem B1084499 : Blo 722323 1084499 := bstep (se 1 (by rfl) ⟨813374, by rfl⟩ : syracuseStep 1084499 = 1626749) B1626749
theorem B724051 : Blo 722323 724051 := bstep (se 1 (by rfl) ⟨543038, by rfl⟩ : syracuseStep 724051 = 1086077) B1086077
theorem B724067 : Blo 722323 724067 := bstep (se 1 (by rfl) ⟨543050, by rfl⟩ : syracuseStep 724067 = 1086101) B1086101
theorem B3673187 : Blo 722323 3673187 := bstep (se 1 (by rfl) ⟨2754890, by rfl⟩ : syracuseStep 3673187 = 5509781) B5509781
theorem B1084529 : Blo 722323 1084529 := bstep (se 2 (by rfl) ⟨406698, by rfl⟩ : syracuseStep 1084529 = 813397) B813397
theorem B724083 : Blo 722323 724083 := bstep (se 1 (by rfl) ⟨543062, by rfl⟩ : syracuseStep 724083 = 1086125) B1086125
theorem B1084547 : Blo 722323 1084547 := bstep (se 1 (by rfl) ⟨813410, by rfl⟩ : syracuseStep 1084547 = 1626821) B1626821
theorem B724099 : Blo 722323 724099 := bstep (se 1 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 724099 = 1086149) B1086149
theorem B724115 : Blo 722323 724115 := bstep (se 1 (by rfl) ⟨543086, by rfl⟩ : syracuseStep 724115 = 1086173) B1086173
theorem B1084577 : Blo 722323 1084577 := bstep (se 2 (by rfl) ⟨406716, by rfl⟩ : syracuseStep 1084577 = 813433) B813433
theorem B724131 : Blo 722323 724131 := bstep (se 1 (by rfl) ⟨543098, by rfl⟩ : syracuseStep 724131 = 1086197) B1086197
theorem B1084595 : Blo 722323 1084595 := bstep (se 1 (by rfl) ⟨813446, by rfl⟩ : syracuseStep 1084595 = 1626893) B1626893
theorem B724147 : Blo 722323 724147 := bstep (se 1 (by rfl) ⟨543110, by rfl⟩ : syracuseStep 724147 = 1086221) B1086221
theorem B724163 : Blo 722323 724163 := bstep (se 1 (by rfl) ⟨543122, by rfl⟩ : syracuseStep 724163 = 1086245) B1086245
theorem B1084625 : Blo 722323 1084625 := bstep (se 2 (by rfl) ⟨406734, by rfl⟩ : syracuseStep 1084625 = 813469) B813469
theorem B724179 : Blo 722323 724179 := bstep (se 1 (by rfl) ⟨543134, by rfl⟩ : syracuseStep 724179 = 1086269) B1086269
theorem B5508323 : Blo 722323 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B1084643 : Blo 722323 1084643 := bstep (se 1 (by rfl) ⟨813482, by rfl⟩ : syracuseStep 1084643 = 1626965) B1626965
theorem B724195 : Blo 722323 724195 := bstep (se 1 (by rfl) ⟨543146, by rfl⟩ : syracuseStep 724195 = 1086293) B1086293
theorem B2198765 : Blo 722323 2198765 := bstep (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) B824537
theorem B5573873 : Blo 722323 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B724211 : Blo 722323 724211 := bstep (se 1 (by rfl) ⟨543158, by rfl⟩ : syracuseStep 724211 = 1086317) B1086317
theorem B1084673 : Blo 722323 1084673 := bstep (se 2 (by rfl) ⟨406752, by rfl⟩ : syracuseStep 1084673 = 813505) B813505
theorem B724227 : Blo 722323 724227 := bstep (se 1 (by rfl) ⟨543170, by rfl⟩ : syracuseStep 724227 = 1086341) B1086341
theorem B1084691 : Blo 722323 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B724243 : Blo 722323 724243 := bstep (se 1 (by rfl) ⟨543182, by rfl⟩ : syracuseStep 724243 = 1086365) B1086365
theorem B724259 : Blo 722323 724259 := bstep (se 1 (by rfl) ⟨543194, by rfl⟩ : syracuseStep 724259 = 1086389) B1086389
theorem B1084721 : Blo 722323 1084721 := bstep (se 2 (by rfl) ⟨406770, by rfl⟩ : syracuseStep 1084721 = 813541) B813541
theorem B724275 : Blo 722323 724275 := bstep (se 1 (by rfl) ⟨543206, by rfl⟩ : syracuseStep 724275 = 1086413) B1086413
theorem B1084739 : Blo 722323 1084739 := bstep (se 1 (by rfl) ⟨813554, by rfl⟩ : syracuseStep 1084739 = 1627109) B1627109
theorem B724291 : Blo 722323 724291 := bstep (se 1 (by rfl) ⟨543218, by rfl⟩ : syracuseStep 724291 = 1086437) B1086437
theorem B724307 : Blo 722323 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B1084769 : Blo 722323 1084769 := bstep (se 2 (by rfl) ⟨406788, by rfl⟩ : syracuseStep 1084769 = 813577) B813577
theorem B724323 : Blo 722323 724323 := bstep (se 1 (by rfl) ⟨543242, by rfl⟩ : syracuseStep 724323 = 1086485) B1086485
theorem B1084787 : Blo 722323 1084787 := bstep (se 1 (by rfl) ⟨813590, by rfl⟩ : syracuseStep 1084787 = 1627181) B1627181
theorem B724339 : Blo 722323 724339 := bstep (se 1 (by rfl) ⟨543254, by rfl⟩ : syracuseStep 724339 = 1086509) B1086509
theorem B724355 : Blo 722323 724355 := bstep (se 1 (by rfl) ⟨543266, by rfl⟩ : syracuseStep 724355 = 1086533) B1086533
theorem B1084817 : Blo 722323 1084817 := bstep (se 2 (by rfl) ⟨406806, by rfl⟩ : syracuseStep 1084817 = 813613) B813613
theorem B724371 : Blo 722323 724371 := bstep (se 1 (by rfl) ⟨543278, by rfl⟩ : syracuseStep 724371 = 1086557) B1086557
theorem B1084835 : Blo 722323 1084835 := bstep (se 1 (by rfl) ⟨813626, by rfl⟩ : syracuseStep 1084835 = 1627253) B1627253
theorem B724387 : Blo 722323 724387 := bstep (se 1 (by rfl) ⟨543290, by rfl⟩ : syracuseStep 724387 = 1086581) B1086581
theorem B2067889 : Blo 722323 2067889 := bstep (se 2 (by rfl) ⟨775458, by rfl⟩ : syracuseStep 2067889 = 1550917) B1550917
theorem B724403 : Blo 722323 724403 := bstep (se 1 (by rfl) ⟨543302, by rfl⟩ : syracuseStep 724403 = 1086605) B1086605
theorem B1084865 : Blo 722323 1084865 := bstep (se 2 (by rfl) ⟨406824, by rfl⟩ : syracuseStep 1084865 = 813649) B813649
theorem B724419 : Blo 722323 724419 := bstep (se 1 (by rfl) ⟨543314, by rfl⟩ : syracuseStep 724419 = 1086629) B1086629
theorem B2756045 : Blo 722323 2756045 := bstep (se 3 (by rfl) ⟨516758, by rfl⟩ : syracuseStep 2756045 = 1033517) B1033517
theorem B1084883 : Blo 722323 1084883 := bstep (se 1 (by rfl) ⟨813662, by rfl⟩ : syracuseStep 1084883 = 1627325) B1627325
theorem B724435 : Blo 722323 724435 := bstep (se 1 (by rfl) ⟨543326, by rfl⟩ : syracuseStep 724435 = 1086653) B1086653
theorem B724451 : Blo 722323 724451 := bstep (se 1 (by rfl) ⟨543338, by rfl⟩ : syracuseStep 724451 = 1086677) B1086677
theorem B1084913 : Blo 722323 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B724467 : Blo 722323 724467 := bstep (se 1 (by rfl) ⟨543350, by rfl⟩ : syracuseStep 724467 = 1086701) B1086701
theorem B1084931 : Blo 722323 1084931 := bstep (se 1 (by rfl) ⟨813698, by rfl⟩ : syracuseStep 1084931 = 1627397) B1627397
theorem B724483 : Blo 722323 724483 := bstep (se 1 (by rfl) ⟨543362, by rfl⟩ : syracuseStep 724483 = 1086725) B1086725
theorem B724499 : Blo 722323 724499 := bstep (se 1 (by rfl) ⟨543374, by rfl⟩ : syracuseStep 724499 = 1086749) B1086749
theorem B1084961 : Blo 722323 1084961 := bstep (se 2 (by rfl) ⟨406860, by rfl⟩ : syracuseStep 1084961 = 813721) B813721
theorem B1543715 : Blo 722323 1543715 := bstep (se 1 (by rfl) ⟨1157786, by rfl⟩ : syracuseStep 1543715 = 2315573) B2315573
theorem B724515 : Blo 722323 724515 := bstep (se 1 (by rfl) ⟨543386, by rfl⟩ : syracuseStep 724515 = 1086773) B1086773
theorem B1084979 : Blo 722323 1084979 := bstep (se 1 (by rfl) ⟨813734, by rfl⟩ : syracuseStep 1084979 = 1627469) B1627469
theorem B724531 : Blo 722323 724531 := bstep (se 1 (by rfl) ⟨543398, by rfl⟩ : syracuseStep 724531 = 1086797) B1086797
theorem B724547 : Blo 722323 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B1085009 : Blo 722323 1085009 := bstep (se 2 (by rfl) ⟨406878, by rfl⟩ : syracuseStep 1085009 = 813757) B813757
theorem B724563 : Blo 722323 724563 := bstep (se 1 (by rfl) ⟨543422, by rfl⟩ : syracuseStep 724563 = 1086845) B1086845
theorem B1085027 : Blo 722323 1085027 := bstep (se 1 (by rfl) ⟨813770, by rfl⟩ : syracuseStep 1085027 = 1627541) B1627541
theorem B724579 : Blo 722323 724579 := bstep (se 1 (by rfl) ⟨543434, by rfl⟩ : syracuseStep 724579 = 1086869) B1086869
theorem B724595 : Blo 722323 724595 := bstep (se 1 (by rfl) ⟨543446, by rfl⟩ : syracuseStep 724595 = 1086893) B1086893
theorem B1085057 : Blo 722323 1085057 := bstep (se 2 (by rfl) ⟨406896, by rfl⟩ : syracuseStep 1085057 = 813793) B813793
theorem B724611 : Blo 722323 724611 := bstep (se 1 (by rfl) ⟨543458, by rfl⟩ : syracuseStep 724611 = 1086917) B1086917
theorem B1085075 : Blo 722323 1085075 := bstep (se 1 (by rfl) ⟨813806, by rfl⟩ : syracuseStep 1085075 = 1627613) B1627613
theorem B724627 : Blo 722323 724627 := bstep (se 1 (by rfl) ⟨543470, by rfl⟩ : syracuseStep 724627 = 1086941) B1086941
theorem B724643 : Blo 722323 724643 := bstep (se 1 (by rfl) ⟨543482, by rfl⟩ : syracuseStep 724643 = 1086965) B1086965
theorem B1085105 : Blo 722323 1085105 := bstep (se 2 (by rfl) ⟨406914, by rfl⟩ : syracuseStep 1085105 = 813829) B813829
theorem B724659 : Blo 722323 724659 := bstep (se 1 (by rfl) ⟨543494, by rfl⟩ : syracuseStep 724659 = 1086989) B1086989
theorem B1085123 : Blo 722323 1085123 := bstep (se 1 (by rfl) ⟨813842, by rfl⟩ : syracuseStep 1085123 = 1627685) B1627685
theorem B724675 : Blo 722323 724675 := bstep (se 1 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 724675 = 1087013) B1087013
theorem B15699653 : Blo 722323 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B2068163 : Blo 722323 2068163 := bstep (se 1 (by rfl) ⟨1551122, by rfl⟩ : syracuseStep 2068163 = 3102245) B3102245
theorem B724691 : Blo 722323 724691 := bstep (se 1 (by rfl) ⟨543518, by rfl⟩ : syracuseStep 724691 = 1087037) B1087037
theorem B1085153 : Blo 722323 1085153 := bstep (se 2 (by rfl) ⟨406932, by rfl⟩ : syracuseStep 1085153 = 813865) B813865
theorem B724707 : Blo 722323 724707 := bstep (se 1 (by rfl) ⟨543530, by rfl⟩ : syracuseStep 724707 = 1087061) B1087061
theorem B1085171 : Blo 722323 1085171 := bstep (se 1 (by rfl) ⟨813878, by rfl⟩ : syracuseStep 1085171 = 1627757) B1627757
theorem B724723 : Blo 722323 724723 := bstep (se 1 (by rfl) ⟨543542, by rfl⟩ : syracuseStep 724723 = 1087085) B1087085
theorem B724739 : Blo 722323 724739 := bstep (se 1 (by rfl) ⟨543554, by rfl⟩ : syracuseStep 724739 = 1087109) B1087109
theorem B1085201 : Blo 722323 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B724755 : Blo 722323 724755 := bstep (se 1 (by rfl) ⟨543566, by rfl⟩ : syracuseStep 724755 = 1087133) B1087133
theorem B1085219 : Blo 722323 1085219 := bstep (se 1 (by rfl) ⟨813914, by rfl⟩ : syracuseStep 1085219 = 1627829) B1627829
theorem B724771 : Blo 722323 724771 := bstep (se 1 (by rfl) ⟨543578, by rfl⟩ : syracuseStep 724771 = 1087157) B1087157
theorem B724787 : Blo 722323 724787 := bstep (se 1 (by rfl) ⟨543590, by rfl⟩ : syracuseStep 724787 = 1087181) B1087181
theorem B1085249 : Blo 722323 1085249 := bstep (se 2 (by rfl) ⟨406968, by rfl⟩ : syracuseStep 1085249 = 813937) B813937
theorem B724803 : Blo 722323 724803 := bstep (se 1 (by rfl) ⟨543602, by rfl⟩ : syracuseStep 724803 = 1087205) B1087205
theorem B1085267 : Blo 722323 1085267 := bstep (se 1 (by rfl) ⟨813950, by rfl⟩ : syracuseStep 1085267 = 1627901) B1627901
theorem B724819 : Blo 722323 724819 := bstep (se 1 (by rfl) ⟨543614, by rfl⟩ : syracuseStep 724819 = 1087229) B1087229
theorem B724835 : Blo 722323 724835 := bstep (se 1 (by rfl) ⟨543626, by rfl⟩ : syracuseStep 724835 = 1087253) B1087253
theorem B1085297 : Blo 722323 1085297 := bstep (se 2 (by rfl) ⟨406986, by rfl⟩ : syracuseStep 1085297 = 813973) B813973
theorem B724851 : Blo 722323 724851 := bstep (se 1 (by rfl) ⟨543638, by rfl⟩ : syracuseStep 724851 = 1087277) B1087277
theorem B1085315 : Blo 722323 1085315 := bstep (se 1 (by rfl) ⟨813986, by rfl⟩ : syracuseStep 1085315 = 1627973) B1627973
theorem B724867 : Blo 722323 724867 := bstep (se 1 (by rfl) ⟨543650, by rfl⟩ : syracuseStep 724867 = 1087301) B1087301
theorem B3673997 : Blo 722323 3673997 := bstep (se 3 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 3673997 = 1377749) B1377749
theorem B724883 : Blo 722323 724883 := bstep (se 1 (by rfl) ⟨543662, by rfl⟩ : syracuseStep 724883 = 1087325) B1087325
theorem B1085345 : Blo 722323 1085345 := bstep (se 2 (by rfl) ⟨407004, by rfl⟩ : syracuseStep 1085345 = 814009) B814009
theorem B724899 : Blo 722323 724899 := bstep (se 1 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 724899 = 1087349) B1087349
theorem B1085363 : Blo 722323 1085363 := bstep (se 1 (by rfl) ⟨814022, by rfl⟩ : syracuseStep 1085363 = 1628045) B1628045
theorem B724915 : Blo 722323 724915 := bstep (se 1 (by rfl) ⟨543686, by rfl⟩ : syracuseStep 724915 = 1087373) B1087373
theorem B724931 : Blo 722323 724931 := bstep (se 1 (by rfl) ⟨543698, by rfl⟩ : syracuseStep 724931 = 1087397) B1087397
theorem B1085393 : Blo 722323 1085393 := bstep (se 2 (by rfl) ⟨407022, by rfl⟩ : syracuseStep 1085393 = 814045) B814045
theorem B724947 : Blo 722323 724947 := bstep (se 1 (by rfl) ⟨543710, by rfl⟩ : syracuseStep 724947 = 1087421) B1087421
theorem B1085411 : Blo 722323 1085411 := bstep (se 1 (by rfl) ⟨814058, by rfl⟩ : syracuseStep 1085411 = 1628117) B1628117
theorem B6033379 : Blo 722323 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B724963 : Blo 722323 724963 := bstep (se 1 (by rfl) ⟨543722, by rfl⟩ : syracuseStep 724963 = 1087445) B1087445
theorem B1544177 : Blo 722323 1544177 := bstep (se 2 (by rfl) ⟨579066, by rfl⟩ : syracuseStep 1544177 = 1158133) B1158133
theorem B724979 : Blo 722323 724979 := bstep (se 1 (by rfl) ⟨543734, by rfl⟩ : syracuseStep 724979 = 1087469) B1087469
theorem B1085441 : Blo 722323 1085441 := bstep (se 2 (by rfl) ⟨407040, by rfl⟩ : syracuseStep 1085441 = 814081) B814081
theorem B724995 : Blo 722323 724995 := bstep (se 1 (by rfl) ⟨543746, by rfl⟩ : syracuseStep 724995 = 1087493) B1087493
theorem B1085459 : Blo 722323 1085459 := bstep (se 1 (by rfl) ⟨814094, by rfl⟩ : syracuseStep 1085459 = 1628189) B1628189
theorem B725011 : Blo 722323 725011 := bstep (se 1 (by rfl) ⟨543758, by rfl⟩ : syracuseStep 725011 = 1087517) B1087517
theorem B725027 : Blo 722323 725027 := bstep (se 1 (by rfl) ⟨543770, by rfl⟩ : syracuseStep 725027 = 1087541) B1087541
theorem B1085489 : Blo 722323 1085489 := bstep (se 2 (by rfl) ⟨407058, by rfl⟩ : syracuseStep 1085489 = 814117) B814117
theorem B725043 : Blo 722323 725043 := bstep (se 1 (by rfl) ⟨543782, by rfl⟩ : syracuseStep 725043 = 1087565) B1087565
theorem B1085507 : Blo 722323 1085507 := bstep (se 1 (by rfl) ⟨814130, by rfl⟩ : syracuseStep 1085507 = 1628261) B1628261
theorem B725059 : Blo 722323 725059 := bstep (se 1 (by rfl) ⟨543794, by rfl⟩ : syracuseStep 725059 = 1087589) B1087589
theorem B725075 : Blo 722323 725075 := bstep (se 1 (by rfl) ⟨543806, by rfl⟩ : syracuseStep 725075 = 1087613) B1087613
theorem B1085537 : Blo 722323 1085537 := bstep (se 2 (by rfl) ⟨407076, by rfl⟩ : syracuseStep 1085537 = 814153) B814153
theorem B725091 : Blo 722323 725091 := bstep (se 1 (by rfl) ⟨543818, by rfl⟩ : syracuseStep 725091 = 1087637) B1087637
theorem B1085555 : Blo 722323 1085555 := bstep (se 1 (by rfl) ⟨814166, by rfl⟩ : syracuseStep 1085555 = 1628333) B1628333
theorem B725107 : Blo 722323 725107 := bstep (se 1 (by rfl) ⟨543830, by rfl⟩ : syracuseStep 725107 = 1087661) B1087661
theorem B725123 : Blo 722323 725123 := bstep (se 1 (by rfl) ⟨543842, by rfl⟩ : syracuseStep 725123 = 1087685) B1087685
theorem B1085585 : Blo 722323 1085585 := bstep (se 2 (by rfl) ⟨407094, by rfl⟩ : syracuseStep 1085585 = 814189) B814189
theorem B725139 : Blo 722323 725139 := bstep (se 1 (by rfl) ⟨543854, by rfl⟩ : syracuseStep 725139 = 1087709) B1087709
theorem B1085603 : Blo 722323 1085603 := bstep (se 1 (by rfl) ⟨814202, by rfl⟩ : syracuseStep 1085603 = 1628405) B1628405
theorem B725155 : Blo 722323 725155 := bstep (se 1 (by rfl) ⟨543866, by rfl⟩ : syracuseStep 725155 = 1087733) B1087733
theorem B725171 : Blo 722323 725171 := bstep (se 1 (by rfl) ⟨543878, by rfl⟩ : syracuseStep 725171 = 1087757) B1087757
theorem B1085633 : Blo 722323 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B725187 : Blo 722323 725187 := bstep (se 1 (by rfl) ⟨543890, by rfl⟩ : syracuseStep 725187 = 1087781) B1087781
theorem B1085651 : Blo 722323 1085651 := bstep (se 1 (by rfl) ⟨814238, by rfl⟩ : syracuseStep 1085651 = 1628477) B1628477
theorem B725203 : Blo 722323 725203 := bstep (se 1 (by rfl) ⟨543902, by rfl⟩ : syracuseStep 725203 = 1087805) B1087805
theorem B725219 : Blo 722323 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B1085681 : Blo 722323 1085681 := bstep (se 2 (by rfl) ⟨407130, by rfl⟩ : syracuseStep 1085681 = 814261) B814261
theorem B725235 : Blo 722323 725235 := bstep (se 1 (by rfl) ⟨543926, by rfl⟩ : syracuseStep 725235 = 1087853) B1087853
theorem B1085699 : Blo 722323 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B725251 : Blo 722323 725251 := bstep (se 1 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 725251 = 1087877) B1087877
theorem B725267 : Blo 722323 725267 := bstep (se 1 (by rfl) ⟨543950, by rfl⟩ : syracuseStep 725267 = 1087901) B1087901
theorem B1085729 : Blo 722323 1085729 := bstep (se 2 (by rfl) ⟨407148, by rfl⟩ : syracuseStep 1085729 = 814297) B814297
theorem B725283 : Blo 722323 725283 := bstep (se 1 (by rfl) ⟨543962, by rfl⟩ : syracuseStep 725283 = 1087925) B1087925
theorem B1085747 : Blo 722323 1085747 := bstep (se 1 (by rfl) ⟨814310, by rfl⟩ : syracuseStep 1085747 = 1628621) B1628621
theorem B725299 : Blo 722323 725299 := bstep (se 1 (by rfl) ⟨543974, by rfl⟩ : syracuseStep 725299 = 1087949) B1087949
theorem B725315 : Blo 722323 725315 := bstep (se 1 (by rfl) ⟨543986, by rfl⟩ : syracuseStep 725315 = 1087973) B1087973
theorem B1085777 : Blo 722323 1085777 := bstep (se 2 (by rfl) ⟨407166, by rfl⟩ : syracuseStep 1085777 = 814333) B814333
theorem B725331 : Blo 722323 725331 := bstep (se 1 (by rfl) ⟨543998, by rfl⟩ : syracuseStep 725331 = 1087997) B1087997
theorem B1085795 : Blo 722323 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B725347 : Blo 722323 725347 := bstep (se 1 (by rfl) ⟨544010, by rfl⟩ : syracuseStep 725347 = 1088021) B1088021
theorem B725363 : Blo 722323 725363 := bstep (se 1 (by rfl) ⟨544022, by rfl⟩ : syracuseStep 725363 = 1088045) B1088045
theorem B1085825 : Blo 722323 1085825 := bstep (se 2 (by rfl) ⟨407184, by rfl⟩ : syracuseStep 1085825 = 814369) B814369
theorem B725379 : Blo 722323 725379 := bstep (se 1 (by rfl) ⟨544034, by rfl⟩ : syracuseStep 725379 = 1088069) B1088069
theorem B1085843 : Blo 722323 1085843 := bstep (se 1 (by rfl) ⟨814382, by rfl⟩ : syracuseStep 1085843 = 1628765) B1628765
theorem B725395 : Blo 722323 725395 := bstep (se 1 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 725395 = 1088093) B1088093
theorem B725411 : Blo 722323 725411 := bstep (se 1 (by rfl) ⟨544058, by rfl⟩ : syracuseStep 725411 = 1088117) B1088117
theorem B1085873 : Blo 722323 1085873 := bstep (se 2 (by rfl) ⟨407202, by rfl⟩ : syracuseStep 1085873 = 814405) B814405
theorem B725427 : Blo 722323 725427 := bstep (se 1 (by rfl) ⟨544070, by rfl⟩ : syracuseStep 725427 = 1088141) B1088141
theorem B1085891 : Blo 722323 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B725443 : Blo 722323 725443 := bstep (se 1 (by rfl) ⟨544082, by rfl⟩ : syracuseStep 725443 = 1088165) B1088165
theorem B725459 : Blo 722323 725459 := bstep (se 1 (by rfl) ⟨544094, by rfl⟩ : syracuseStep 725459 = 1088189) B1088189
theorem B1085921 : Blo 722323 1085921 := bstep (se 2 (by rfl) ⟨407220, by rfl⟩ : syracuseStep 1085921 = 814441) B814441
theorem B725475 : Blo 722323 725475 := bstep (se 1 (by rfl) ⟨544106, by rfl⟩ : syracuseStep 725475 = 1088213) B1088213
theorem B1085939 : Blo 722323 1085939 := bstep (se 1 (by rfl) ⟨814454, by rfl⟩ : syracuseStep 1085939 = 1628909) B1628909
theorem B725491 : Blo 722323 725491 := bstep (se 1 (by rfl) ⟨544118, by rfl⟩ : syracuseStep 725491 = 1088237) B1088237
theorem B725507 : Blo 722323 725507 := bstep (se 1 (by rfl) ⟨544130, by rfl⟩ : syracuseStep 725507 = 1088261) B1088261
theorem B1085969 : Blo 722323 1085969 := bstep (se 2 (by rfl) ⟨407238, by rfl⟩ : syracuseStep 1085969 = 814477) B814477
theorem B725523 : Blo 722323 725523 := bstep (se 1 (by rfl) ⟨544142, by rfl⟩ : syracuseStep 725523 = 1088285) B1088285
theorem B1085987 : Blo 722323 1085987 := bstep (se 1 (by rfl) ⟨814490, by rfl⟩ : syracuseStep 1085987 = 1628981) B1628981
theorem B725539 : Blo 722323 725539 := bstep (se 1 (by rfl) ⟨544154, by rfl⟩ : syracuseStep 725539 = 1088309) B1088309
theorem B725555 : Blo 722323 725555 := bstep (se 1 (by rfl) ⟨544166, by rfl⟩ : syracuseStep 725555 = 1088333) B1088333
theorem B30511669 : Blo 722323 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B1086017 : Blo 722323 1086017 := bstep (se 2 (by rfl) ⟨407256, by rfl⟩ : syracuseStep 1086017 = 814513) B814513
theorem B725571 : Blo 722323 725571 := bstep (se 1 (by rfl) ⟨544178, by rfl⟩ : syracuseStep 725571 = 1088357) B1088357
theorem B1086035 : Blo 722323 1086035 := bstep (se 1 (by rfl) ⟨814526, by rfl⟩ : syracuseStep 1086035 = 1629053) B1629053
theorem B725587 : Blo 722323 725587 := bstep (se 1 (by rfl) ⟨544190, by rfl⟩ : syracuseStep 725587 = 1088381) B1088381
theorem B725603 : Blo 722323 725603 := bstep (se 1 (by rfl) ⟨544202, by rfl⟩ : syracuseStep 725603 = 1088405) B1088405
theorem B1086065 : Blo 722323 1086065 := bstep (se 2 (by rfl) ⟨407274, by rfl⟩ : syracuseStep 1086065 = 814549) B814549
theorem B725619 : Blo 722323 725619 := bstep (se 1 (by rfl) ⟨544214, by rfl⟩ : syracuseStep 725619 = 1088429) B1088429
theorem B1086083 : Blo 722323 1086083 := bstep (se 1 (by rfl) ⟨814562, by rfl⟩ : syracuseStep 1086083 = 1629125) B1629125
theorem B725635 : Blo 722323 725635 := bstep (se 1 (by rfl) ⟨544226, by rfl⟩ : syracuseStep 725635 = 1088453) B1088453
theorem B725651 : Blo 722323 725651 := bstep (se 1 (by rfl) ⟨544238, by rfl⟩ : syracuseStep 725651 = 1088477) B1088477
theorem B1086113 : Blo 722323 1086113 := bstep (se 2 (by rfl) ⟨407292, by rfl⟩ : syracuseStep 1086113 = 814585) B814585
theorem B725667 : Blo 722323 725667 := bstep (se 1 (by rfl) ⟨544250, by rfl⟩ : syracuseStep 725667 = 1088501) B1088501
theorem B1086131 : Blo 722323 1086131 := bstep (se 1 (by rfl) ⟨814598, by rfl⟩ : syracuseStep 1086131 = 1629197) B1629197
theorem B725683 : Blo 722323 725683 := bstep (se 1 (by rfl) ⟨544262, by rfl⟩ : syracuseStep 725683 = 1088525) B1088525
theorem B725699 : Blo 722323 725699 := bstep (se 1 (by rfl) ⟨544274, by rfl⟩ : syracuseStep 725699 = 1088549) B1088549
theorem B1086161 : Blo 722323 1086161 := bstep (se 2 (by rfl) ⟨407310, by rfl⟩ : syracuseStep 1086161 = 814621) B814621
theorem B725715 : Blo 722323 725715 := bstep (se 1 (by rfl) ⟨544286, by rfl⟩ : syracuseStep 725715 = 1088573) B1088573
theorem B1086179 : Blo 722323 1086179 := bstep (se 1 (by rfl) ⟨814634, by rfl⟩ : syracuseStep 1086179 = 1629269) B1629269
theorem B725731 : Blo 722323 725731 := bstep (se 1 (by rfl) ⟨544298, by rfl⟩ : syracuseStep 725731 = 1088597) B1088597
theorem B725747 : Blo 722323 725747 := bstep (se 1 (by rfl) ⟨544310, by rfl⟩ : syracuseStep 725747 = 1088621) B1088621
theorem B1086209 : Blo 722323 1086209 := bstep (se 2 (by rfl) ⟨407328, by rfl⟩ : syracuseStep 1086209 = 814657) B814657
theorem B725763 : Blo 722323 725763 := bstep (se 1 (by rfl) ⟨544322, by rfl⟩ : syracuseStep 725763 = 1088645) B1088645
theorem B1086227 : Blo 722323 1086227 := bstep (se 1 (by rfl) ⟨814670, by rfl⟩ : syracuseStep 1086227 = 1629341) B1629341
theorem B725779 : Blo 722323 725779 := bstep (se 1 (by rfl) ⟨544334, by rfl⟩ : syracuseStep 725779 = 1088669) B1088669
theorem B725795 : Blo 722323 725795 := bstep (se 1 (by rfl) ⟨544346, by rfl⟩ : syracuseStep 725795 = 1088693) B1088693
theorem B1086257 : Blo 722323 1086257 := bstep (se 2 (by rfl) ⟨407346, by rfl⟩ : syracuseStep 1086257 = 814693) B814693
theorem B725811 : Blo 722323 725811 := bstep (se 1 (by rfl) ⟨544358, by rfl⟩ : syracuseStep 725811 = 1088717) B1088717
theorem B1086275 : Blo 722323 1086275 := bstep (se 1 (by rfl) ⟨814706, by rfl⟩ : syracuseStep 1086275 = 1629413) B1629413
theorem B725827 : Blo 722323 725827 := bstep (se 1 (by rfl) ⟨544370, by rfl⟩ : syracuseStep 725827 = 1088741) B1088741
theorem B725843 : Blo 722323 725843 := bstep (se 1 (by rfl) ⟨544382, by rfl⟩ : syracuseStep 725843 = 1088765) B1088765
theorem B1086305 : Blo 722323 1086305 := bstep (se 2 (by rfl) ⟨407364, by rfl⟩ : syracuseStep 1086305 = 814729) B814729
theorem B725859 : Blo 722323 725859 := bstep (se 1 (by rfl) ⟨544394, by rfl⟩ : syracuseStep 725859 = 1088789) B1088789
theorem B1086323 : Blo 722323 1086323 := bstep (se 1 (by rfl) ⟨814742, by rfl⟩ : syracuseStep 1086323 = 1629485) B1629485
theorem B725875 : Blo 722323 725875 := bstep (se 1 (by rfl) ⟨544406, by rfl⟩ : syracuseStep 725875 = 1088813) B1088813
theorem B725891 : Blo 722323 725891 := bstep (se 1 (by rfl) ⟨544418, by rfl⟩ : syracuseStep 725891 = 1088837) B1088837
theorem B1086353 : Blo 722323 1086353 := bstep (se 2 (by rfl) ⟨407382, by rfl⟩ : syracuseStep 1086353 = 814765) B814765
theorem B725907 : Blo 722323 725907 := bstep (se 1 (by rfl) ⟨544430, by rfl⟩ : syracuseStep 725907 = 1088861) B1088861
theorem B1086371 : Blo 722323 1086371 := bstep (se 1 (by rfl) ⟨814778, by rfl⟩ : syracuseStep 1086371 = 1629557) B1629557
theorem B725923 : Blo 722323 725923 := bstep (se 1 (by rfl) ⟨544442, by rfl⟩ : syracuseStep 725923 = 1088885) B1088885
theorem B725939 : Blo 722323 725939 := bstep (se 1 (by rfl) ⟨544454, by rfl⟩ : syracuseStep 725939 = 1088909) B1088909
theorem B1086401 : Blo 722323 1086401 := bstep (se 2 (by rfl) ⟨407400, by rfl⟩ : syracuseStep 1086401 = 814801) B814801
theorem B725955 : Blo 722323 725955 := bstep (se 1 (by rfl) ⟨544466, by rfl⟩ : syracuseStep 725955 = 1088933) B1088933
theorem B1086419 : Blo 722323 1086419 := bstep (se 1 (by rfl) ⟨814814, by rfl⟩ : syracuseStep 1086419 = 1629629) B1629629
theorem B725971 : Blo 722323 725971 := bstep (se 1 (by rfl) ⟨544478, by rfl⟩ : syracuseStep 725971 = 1088957) B1088957
theorem B725987 : Blo 722323 725987 := bstep (se 1 (by rfl) ⟨544490, by rfl⟩ : syracuseStep 725987 = 1088981) B1088981
theorem B1086449 : Blo 722323 1086449 := bstep (se 2 (by rfl) ⟨407418, by rfl⟩ : syracuseStep 1086449 = 814837) B814837
theorem B726003 : Blo 722323 726003 := bstep (se 1 (by rfl) ⟨544502, by rfl⟩ : syracuseStep 726003 = 1089005) B1089005
theorem B1086467 : Blo 722323 1086467 := bstep (se 1 (by rfl) ⟨814850, by rfl⟩ : syracuseStep 1086467 = 1629701) B1629701
theorem B726019 : Blo 722323 726019 := bstep (se 1 (by rfl) ⟨544514, by rfl⟩ : syracuseStep 726019 = 1089029) B1089029
theorem B726035 : Blo 722323 726035 := bstep (se 1 (by rfl) ⟨544526, by rfl⟩ : syracuseStep 726035 = 1089053) B1089053
theorem B1086497 : Blo 722323 1086497 := bstep (se 2 (by rfl) ⟨407436, by rfl⟩ : syracuseStep 1086497 = 814873) B814873
theorem B726051 : Blo 722323 726051 := bstep (se 1 (by rfl) ⟨544538, by rfl⟩ : syracuseStep 726051 = 1089077) B1089077
theorem B1086515 : Blo 722323 1086515 := bstep (se 1 (by rfl) ⟨814886, by rfl⟩ : syracuseStep 1086515 = 1629773) B1629773
theorem B726067 : Blo 722323 726067 := bstep (se 1 (by rfl) ⟨544550, by rfl⟩ : syracuseStep 726067 = 1089101) B1089101
theorem B726083 : Blo 722323 726083 := bstep (se 1 (by rfl) ⟨544562, by rfl⟩ : syracuseStep 726083 = 1089125) B1089125
theorem B1086545 : Blo 722323 1086545 := bstep (se 2 (by rfl) ⟨407454, by rfl⟩ : syracuseStep 1086545 = 814909) B814909
theorem B726099 : Blo 722323 726099 := bstep (se 1 (by rfl) ⟨544574, by rfl⟩ : syracuseStep 726099 = 1089149) B1089149
theorem B1086563 : Blo 722323 1086563 := bstep (se 1 (by rfl) ⟨814922, by rfl⟩ : syracuseStep 1086563 = 1629845) B1629845
theorem B726115 : Blo 722323 726115 := bstep (se 1 (by rfl) ⟨544586, by rfl⟩ : syracuseStep 726115 = 1089173) B1089173
theorem B726131 : Blo 722323 726131 := bstep (se 1 (by rfl) ⟨544598, by rfl⟩ : syracuseStep 726131 = 1089197) B1089197
theorem B1086593 : Blo 722323 1086593 := bstep (se 2 (by rfl) ⟨407472, by rfl⟩ : syracuseStep 1086593 = 814945) B814945
theorem B726147 : Blo 722323 726147 := bstep (se 1 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 726147 = 1089221) B1089221
theorem B1086611 : Blo 722323 1086611 := bstep (se 1 (by rfl) ⟨814958, by rfl⟩ : syracuseStep 1086611 = 1629917) B1629917
theorem B726163 : Blo 722323 726163 := bstep (se 1 (by rfl) ⟨544622, by rfl⟩ : syracuseStep 726163 = 1089245) B1089245
theorem B726179 : Blo 722323 726179 := bstep (se 1 (by rfl) ⟨544634, by rfl⟩ : syracuseStep 726179 = 1089269) B1089269
theorem B1086641 : Blo 722323 1086641 := bstep (se 2 (by rfl) ⟨407490, by rfl⟩ : syracuseStep 1086641 = 814981) B814981
theorem B726195 : Blo 722323 726195 := bstep (se 1 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 726195 = 1089293) B1089293
theorem B1086659 : Blo 722323 1086659 := bstep (se 1 (by rfl) ⟨814994, by rfl⟩ : syracuseStep 1086659 = 1629989) B1629989
theorem B726211 : Blo 722323 726211 := bstep (se 1 (by rfl) ⟨544658, by rfl⟩ : syracuseStep 726211 = 1089317) B1089317
theorem B726227 : Blo 722323 726227 := bstep (se 1 (by rfl) ⟨544670, by rfl⟩ : syracuseStep 726227 = 1089341) B1089341
theorem B1086689 : Blo 722323 1086689 := bstep (se 2 (by rfl) ⟨407508, by rfl⟩ : syracuseStep 1086689 = 815017) B815017
theorem B726243 : Blo 722323 726243 := bstep (se 1 (by rfl) ⟨544682, by rfl⟩ : syracuseStep 726243 = 1089365) B1089365
theorem B1086707 : Blo 722323 1086707 := bstep (se 1 (by rfl) ⟨815030, by rfl⟩ : syracuseStep 1086707 = 1630061) B1630061
theorem B726259 : Blo 722323 726259 := bstep (se 1 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 726259 = 1089389) B1089389
theorem B1545475 : Blo 722323 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B726275 : Blo 722323 726275 := bstep (se 1 (by rfl) ⟨544706, by rfl⟩ : syracuseStep 726275 = 1089413) B1089413
theorem B1086737 : Blo 722323 1086737 := bstep (se 2 (by rfl) ⟨407526, by rfl⟩ : syracuseStep 1086737 = 815053) B815053
theorem B726291 : Blo 722323 726291 := bstep (se 1 (by rfl) ⟨544718, by rfl⟩ : syracuseStep 726291 = 1089437) B1089437
theorem B1086755 : Blo 722323 1086755 := bstep (se 1 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 1086755 = 1630133) B1630133
theorem B726307 : Blo 722323 726307 := bstep (se 1 (by rfl) ⟨544730, by rfl⟩ : syracuseStep 726307 = 1089461) B1089461
theorem B726323 : Blo 722323 726323 := bstep (se 1 (by rfl) ⟨544742, by rfl⟩ : syracuseStep 726323 = 1089485) B1089485
theorem B1086785 : Blo 722323 1086785 := bstep (se 2 (by rfl) ⟨407544, by rfl⟩ : syracuseStep 1086785 = 815089) B815089
theorem B1086803 : Blo 722323 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B1086833 : Blo 722323 1086833 := bstep (se 2 (by rfl) ⟨407562, by rfl⟩ : syracuseStep 1086833 = 815125) B815125
theorem B1086851 : Blo 722323 1086851 := bstep (se 1 (by rfl) ⟨815138, by rfl⟩ : syracuseStep 1086851 = 1630277) B1630277
theorem B1086881 : Blo 722323 1086881 := bstep (se 2 (by rfl) ⟨407580, by rfl⟩ : syracuseStep 1086881 = 815161) B815161
theorem B1086899 : Blo 722323 1086899 := bstep (se 1 (by rfl) ⟨815174, by rfl⟩ : syracuseStep 1086899 = 1630349) B1630349
theorem B4134341 : Blo 722323 4134341 := bstep (se 4 (by rfl) ⟨387594, by rfl⟩ : syracuseStep 4134341 = 775189) B775189
theorem B1086929 : Blo 722323 1086929 := bstep (se 2 (by rfl) ⟨407598, by rfl⟩ : syracuseStep 1086929 = 815197) B815197
theorem B1086947 : Blo 722323 1086947 := bstep (se 1 (by rfl) ⟨815210, by rfl⟩ : syracuseStep 1086947 = 1630421) B1630421
theorem B1086977 : Blo 722323 1086977 := bstep (se 2 (by rfl) ⟨407616, by rfl⟩ : syracuseStep 1086977 = 815233) B815233
theorem B1545731 : Blo 722323 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B1086995 : Blo 722323 1086995 := bstep (se 1 (by rfl) ⟨815246, by rfl⟩ : syracuseStep 1086995 = 1630493) B1630493
theorem B1087025 : Blo 722323 1087025 := bstep (se 2 (by rfl) ⟨407634, by rfl⟩ : syracuseStep 1087025 = 815269) B815269
theorem B1087043 : Blo 722323 1087043 := bstep (se 1 (by rfl) ⟨815282, by rfl⟩ : syracuseStep 1087043 = 1630565) B1630565
theorem B1087073 : Blo 722323 1087073 := bstep (se 2 (by rfl) ⟨407652, by rfl⟩ : syracuseStep 1087073 = 815305) B815305
theorem B6035057 : Blo 722323 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B1087091 : Blo 722323 1087091 := bstep (se 1 (by rfl) ⟨815318, by rfl⟩ : syracuseStep 1087091 = 1630637) B1630637
theorem B1087121 : Blo 722323 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B1087139 : Blo 722323 1087139 := bstep (se 1 (by rfl) ⟨815354, by rfl⟩ : syracuseStep 1087139 = 1630709) B1630709
theorem B1087169 : Blo 722323 1087169 := bstep (se 2 (by rfl) ⟨407688, by rfl⟩ : syracuseStep 1087169 = 815377) B815377
theorem B1087187 : Blo 722323 1087187 := bstep (se 1 (by rfl) ⟨815390, by rfl⟩ : syracuseStep 1087187 = 1630781) B1630781
theorem B1087217 : Blo 722323 1087217 := bstep (se 2 (by rfl) ⟨407706, by rfl⟩ : syracuseStep 1087217 = 815413) B815413
theorem B1087235 : Blo 722323 1087235 := bstep (se 1 (by rfl) ⟨815426, by rfl⟩ : syracuseStep 1087235 = 1630853) B1630853
theorem B8492813 : Blo 722323 8492813 := bstep (se 3 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 8492813 = 3184805) B3184805
theorem B1087265 : Blo 722323 1087265 := bstep (se 2 (by rfl) ⟨407724, by rfl⟩ : syracuseStep 1087265 = 815449) B815449
theorem B1087283 : Blo 722323 1087283 := bstep (se 1 (by rfl) ⟨815462, by rfl⟩ : syracuseStep 1087283 = 1630925) B1630925
theorem B1087313 : Blo 722323 1087313 := bstep (se 2 (by rfl) ⟨407742, by rfl⟩ : syracuseStep 1087313 = 815485) B815485
theorem B1087331 : Blo 722323 1087331 := bstep (se 1 (by rfl) ⟨815498, by rfl⟩ : syracuseStep 1087331 = 1630997) B1630997
theorem B17667953 : Blo 722323 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B1087361 : Blo 722323 1087361 := bstep (se 2 (by rfl) ⟨407760, by rfl⟩ : syracuseStep 1087361 = 815521) B815521
theorem B4134797 : Blo 722323 4134797 := bstep (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) B1550549
theorem B1087379 : Blo 722323 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B1087409 : Blo 722323 1087409 := bstep (se 2 (by rfl) ⟨407778, by rfl⟩ : syracuseStep 1087409 = 815557) B815557
theorem B1087427 : Blo 722323 1087427 := bstep (se 1 (by rfl) ⟨815570, by rfl⟩ : syracuseStep 1087427 = 1631141) B1631141
theorem B1087457 : Blo 722323 1087457 := bstep (se 2 (by rfl) ⟨407796, by rfl⟩ : syracuseStep 1087457 = 815593) B815593
theorem B1087475 : Blo 722323 1087475 := bstep (se 1 (by rfl) ⟨815606, by rfl⟩ : syracuseStep 1087475 = 1631213) B1631213
theorem B1087505 : Blo 722323 1087505 := bstep (se 2 (by rfl) ⟨407814, by rfl⟩ : syracuseStep 1087505 = 815629) B815629
theorem B1087523 : Blo 722323 1087523 := bstep (se 1 (by rfl) ⟨815642, by rfl⟩ : syracuseStep 1087523 = 1631285) B1631285
theorem B1087553 : Blo 722323 1087553 := bstep (se 2 (by rfl) ⟨407832, by rfl⟩ : syracuseStep 1087553 = 815665) B815665
theorem B1087571 : Blo 722323 1087571 := bstep (se 1 (by rfl) ⟨815678, by rfl⟩ : syracuseStep 1087571 = 1631357) B1631357
theorem B1087601 : Blo 722323 1087601 := bstep (se 2 (by rfl) ⟨407850, by rfl⟩ : syracuseStep 1087601 = 815701) B815701
theorem B1087619 : Blo 722323 1087619 := bstep (se 1 (by rfl) ⟨815714, by rfl⟩ : syracuseStep 1087619 = 1631429) B1631429
theorem B1087649 : Blo 722323 1087649 := bstep (se 2 (by rfl) ⟨407868, by rfl⟩ : syracuseStep 1087649 = 815737) B815737
theorem B1087667 : Blo 722323 1087667 := bstep (se 1 (by rfl) ⟨815750, by rfl⟩ : syracuseStep 1087667 = 1631501) B1631501
theorem B1087697 : Blo 722323 1087697 := bstep (se 2 (by rfl) ⟨407886, by rfl⟩ : syracuseStep 1087697 = 815773) B815773
theorem B1087715 : Blo 722323 1087715 := bstep (se 1 (by rfl) ⟨815786, by rfl⟩ : syracuseStep 1087715 = 1631573) B1631573
theorem B1022209 : Blo 722323 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B1087745 : Blo 722323 1087745 := bstep (se 2 (by rfl) ⟨407904, by rfl⟩ : syracuseStep 1087745 = 815809) B815809
theorem B1087763 : Blo 722323 1087763 := bstep (se 1 (by rfl) ⟨815822, by rfl⟩ : syracuseStep 1087763 = 1631645) B1631645
theorem B1087793 : Blo 722323 1087793 := bstep (se 2 (by rfl) ⟨407922, by rfl⟩ : syracuseStep 1087793 = 815845) B815845
theorem B1087811 : Blo 722323 1087811 := bstep (se 1 (by rfl) ⟨815858, by rfl⟩ : syracuseStep 1087811 = 1631717) B1631717
theorem B1087841 : Blo 722323 1087841 := bstep (se 2 (by rfl) ⟨407940, by rfl⟩ : syracuseStep 1087841 = 815881) B815881
theorem B1087859 : Blo 722323 1087859 := bstep (se 1 (by rfl) ⟨815894, by rfl⟩ : syracuseStep 1087859 = 1631789) B1631789
theorem B1087889 : Blo 722323 1087889 := bstep (se 2 (by rfl) ⟨407958, by rfl⟩ : syracuseStep 1087889 = 815917) B815917
theorem B1087907 : Blo 722323 1087907 := bstep (se 1 (by rfl) ⟨815930, by rfl⟩ : syracuseStep 1087907 = 1631861) B1631861
theorem B1219009 : Blo 722323 1219009 := bstep (se 2 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 1219009 = 914257) B914257
theorem B1087937 : Blo 722323 1087937 := bstep (se 2 (by rfl) ⟨407976, by rfl⟩ : syracuseStep 1087937 = 815953) B815953
theorem B1546705 : Blo 722323 1546705 := bstep (se 2 (by rfl) ⟨580014, by rfl⟩ : syracuseStep 1546705 = 1160029) B1160029
theorem B1087955 : Blo 722323 1087955 := bstep (se 1 (by rfl) ⟨815966, by rfl⟩ : syracuseStep 1087955 = 1631933) B1631933
theorem B1219043 : Blo 722323 1219043 := bstep (se 1 (by rfl) ⟨914282, by rfl⟩ : syracuseStep 1219043 = 1828565) B1828565
theorem B1087985 : Blo 722323 1087985 := bstep (se 2 (by rfl) ⟨407994, by rfl⟩ : syracuseStep 1087985 = 815989) B815989
theorem B1088003 : Blo 722323 1088003 := bstep (se 1 (by rfl) ⟨816002, by rfl⟩ : syracuseStep 1088003 = 1632005) B1632005
theorem B1088033 : Blo 722323 1088033 := bstep (se 2 (by rfl) ⟨408012, by rfl⟩ : syracuseStep 1088033 = 816025) B816025
theorem B1088051 : Blo 722323 1088051 := bstep (se 1 (by rfl) ⟨816038, by rfl⟩ : syracuseStep 1088051 = 1632077) B1632077
theorem B1088081 : Blo 722323 1088081 := bstep (se 2 (by rfl) ⟨408030, by rfl⟩ : syracuseStep 1088081 = 816061) B816061
theorem B1219171 : Blo 722323 1219171 := bstep (se 1 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 1219171 = 1828757) B1828757
theorem B1088099 : Blo 722323 1088099 := bstep (se 1 (by rfl) ⟨816074, by rfl⟩ : syracuseStep 1088099 = 1632149) B1632149
theorem B1088129 : Blo 722323 1088129 := bstep (se 2 (by rfl) ⟨408048, by rfl⟩ : syracuseStep 1088129 = 816097) B816097
theorem B1088147 : Blo 722323 1088147 := bstep (se 1 (by rfl) ⟨816110, by rfl⟩ : syracuseStep 1088147 = 1632221) B1632221
theorem B1088177 : Blo 722323 1088177 := bstep (se 2 (by rfl) ⟨408066, by rfl⟩ : syracuseStep 1088177 = 816133) B816133
theorem B1088195 : Blo 722323 1088195 := bstep (se 1 (by rfl) ⟨816146, by rfl⟩ : syracuseStep 1088195 = 1632293) B1632293
theorem B1088225 : Blo 722323 1088225 := bstep (se 2 (by rfl) ⟨408084, by rfl⟩ : syracuseStep 1088225 = 816169) B816169
theorem B1219313 : Blo 722323 1219313 := bstep (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) B914485
theorem B3676913 : Blo 722323 3676913 := bstep (se 2 (by rfl) ⟨1378842, by rfl⟩ : syracuseStep 3676913 = 2757685) B2757685
theorem B1088243 : Blo 722323 1088243 := bstep (se 1 (by rfl) ⟨816182, by rfl⟩ : syracuseStep 1088243 = 1632365) B1632365
theorem B1088273 : Blo 722323 1088273 := bstep (se 2 (by rfl) ⟨408102, by rfl⟩ : syracuseStep 1088273 = 816205) B816205
theorem B1088291 : Blo 722323 1088291 := bstep (se 1 (by rfl) ⟨816218, by rfl⟩ : syracuseStep 1088291 = 1632437) B1632437
theorem B1088321 : Blo 722323 1088321 := bstep (se 2 (by rfl) ⟨408120, by rfl⟩ : syracuseStep 1088321 = 816241) B816241
theorem B1088339 : Blo 722323 1088339 := bstep (se 1 (by rfl) ⟨816254, by rfl⟩ : syracuseStep 1088339 = 1632509) B1632509
theorem B1219441 : Blo 722323 1219441 := bstep (se 2 (by rfl) ⟨457290, by rfl⟩ : syracuseStep 1219441 = 914581) B914581
theorem B1088369 : Blo 722323 1088369 := bstep (se 2 (by rfl) ⟨408138, by rfl⟩ : syracuseStep 1088369 = 816277) B816277
theorem B1088387 : Blo 722323 1088387 := bstep (se 1 (by rfl) ⟨816290, by rfl⟩ : syracuseStep 1088387 = 1632581) B1632581
theorem B1219475 : Blo 722323 1219475 := bstep (se 1 (by rfl) ⟨914606, by rfl⟩ : syracuseStep 1219475 = 1829213) B1829213
theorem B1088417 : Blo 722323 1088417 := bstep (se 2 (by rfl) ⟨408156, by rfl⟩ : syracuseStep 1088417 = 816313) B816313
theorem B1088435 : Blo 722323 1088435 := bstep (se 1 (by rfl) ⟨816326, by rfl⟩ : syracuseStep 1088435 = 1632653) B1632653
theorem B8919989 : Blo 722323 8919989 := bstep (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) B836249
theorem B1088465 : Blo 722323 1088465 := bstep (se 2 (by rfl) ⟨408174, by rfl⟩ : syracuseStep 1088465 = 816349) B816349
theorem B1088483 : Blo 722323 1088483 := bstep (se 1 (by rfl) ⟨816362, by rfl⟩ : syracuseStep 1088483 = 1632725) B1632725
theorem B1088513 : Blo 722323 1088513 := bstep (se 2 (by rfl) ⟨408192, by rfl⟩ : syracuseStep 1088513 = 816385) B816385
theorem B1219603 : Blo 722323 1219603 := bstep (se 1 (by rfl) ⟨914702, by rfl⟩ : syracuseStep 1219603 = 1829405) B1829405
theorem B1088531 : Blo 722323 1088531 := bstep (se 1 (by rfl) ⟨816398, by rfl⟩ : syracuseStep 1088531 = 1632797) B1632797
theorem B1088561 : Blo 722323 1088561 := bstep (se 2 (by rfl) ⟨408210, by rfl⟩ : syracuseStep 1088561 = 816421) B816421
theorem B1088579 : Blo 722323 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B1088609 : Blo 722323 1088609 := bstep (se 2 (by rfl) ⟨408228, by rfl⟩ : syracuseStep 1088609 = 816457) B816457
theorem B1547363 : Blo 722323 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B1088627 : Blo 722323 1088627 := bstep (se 1 (by rfl) ⟨816470, by rfl⟩ : syracuseStep 1088627 = 1632941) B1632941
theorem B1088657 : Blo 722323 1088657 := bstep (se 2 (by rfl) ⟨408246, by rfl⟩ : syracuseStep 1088657 = 816493) B816493
theorem B1219745 : Blo 722323 1219745 := bstep (se 2 (by rfl) ⟨457404, by rfl⟩ : syracuseStep 1219745 = 914809) B914809
theorem B1088675 : Blo 722323 1088675 := bstep (se 1 (by rfl) ⟨816506, by rfl⟩ : syracuseStep 1088675 = 1633013) B1633013
theorem B1088705 : Blo 722323 1088705 := bstep (se 2 (by rfl) ⟨408264, by rfl⟩ : syracuseStep 1088705 = 816529) B816529
theorem B1088723 : Blo 722323 1088723 := bstep (se 1 (by rfl) ⟨816542, by rfl⟩ : syracuseStep 1088723 = 1633085) B1633085
theorem B1088753 : Blo 722323 1088753 := bstep (se 2 (by rfl) ⟨408282, by rfl⟩ : syracuseStep 1088753 = 816565) B816565
theorem B1088771 : Blo 722323 1088771 := bstep (se 1 (by rfl) ⟨816578, by rfl⟩ : syracuseStep 1088771 = 1633157) B1633157
theorem B1219873 : Blo 722323 1219873 := bstep (se 2 (by rfl) ⟨457452, by rfl⟩ : syracuseStep 1219873 = 914905) B914905
theorem B1088801 : Blo 722323 1088801 := bstep (se 2 (by rfl) ⟨408300, by rfl⟩ : syracuseStep 1088801 = 816601) B816601
theorem B1088819 : Blo 722323 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B1219907 : Blo 722323 1219907 := bstep (se 1 (by rfl) ⟨914930, by rfl⟩ : syracuseStep 1219907 = 1829861) B1829861
theorem B1088849 : Blo 722323 1088849 := bstep (se 2 (by rfl) ⟨408318, by rfl⟩ : syracuseStep 1088849 = 816637) B816637
theorem B1088867 : Blo 722323 1088867 := bstep (se 1 (by rfl) ⟨816650, by rfl⟩ : syracuseStep 1088867 = 1633301) B1633301
theorem B1088897 : Blo 722323 1088897 := bstep (se 2 (by rfl) ⟨408336, by rfl⟩ : syracuseStep 1088897 = 816673) B816673
theorem B1088915 : Blo 722323 1088915 := bstep (se 1 (by rfl) ⟨816686, by rfl⟩ : syracuseStep 1088915 = 1633373) B1633373
theorem B1088945 : Blo 722323 1088945 := bstep (se 2 (by rfl) ⟨408354, by rfl⟩ : syracuseStep 1088945 = 816709) B816709
theorem B1220035 : Blo 722323 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B1088963 : Blo 722323 1088963 := bstep (se 1 (by rfl) ⟨816722, by rfl⟩ : syracuseStep 1088963 = 1633445) B1633445
theorem B57187781 : Blo 722323 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B1088993 : Blo 722323 1088993 := bstep (se 2 (by rfl) ⟨408372, by rfl⟩ : syracuseStep 1088993 = 816745) B816745
theorem B1089011 : Blo 722323 1089011 := bstep (se 1 (by rfl) ⟨816758, by rfl⟩ : syracuseStep 1089011 = 1633517) B1633517
theorem B1089041 : Blo 722323 1089041 := bstep (se 2 (by rfl) ⟨408390, by rfl⟩ : syracuseStep 1089041 = 816781) B816781
theorem B1089059 : Blo 722323 1089059 := bstep (se 1 (by rfl) ⟨816794, by rfl⟩ : syracuseStep 1089059 = 1633589) B1633589
theorem B1089089 : Blo 722323 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B1220177 : Blo 722323 1220177 := bstep (se 2 (by rfl) ⟨457566, by rfl⟩ : syracuseStep 1220177 = 915133) B915133
theorem B1089107 : Blo 722323 1089107 := bstep (se 1 (by rfl) ⟨816830, by rfl⟩ : syracuseStep 1089107 = 1633661) B1633661
theorem B1089137 : Blo 722323 1089137 := bstep (se 2 (by rfl) ⟨408426, by rfl⟩ : syracuseStep 1089137 = 816853) B816853
theorem B1089155 : Blo 722323 1089155 := bstep (se 1 (by rfl) ⟨816866, by rfl⟩ : syracuseStep 1089155 = 1633733) B1633733
theorem B1089185 : Blo 722323 1089185 := bstep (se 2 (by rfl) ⟨408444, by rfl⟩ : syracuseStep 1089185 = 816889) B816889
theorem B1089203 : Blo 722323 1089203 := bstep (se 1 (by rfl) ⟨816902, by rfl⟩ : syracuseStep 1089203 = 1633805) B1633805
theorem B1220305 : Blo 722323 1220305 := bstep (se 2 (by rfl) ⟨457614, by rfl⟩ : syracuseStep 1220305 = 915229) B915229
theorem B1089233 : Blo 722323 1089233 := bstep (se 2 (by rfl) ⟨408462, by rfl⟩ : syracuseStep 1089233 = 816925) B816925
theorem B1089251 : Blo 722323 1089251 := bstep (se 1 (by rfl) ⟨816938, by rfl⟩ : syracuseStep 1089251 = 1633877) B1633877
theorem B1220339 : Blo 722323 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B1089281 : Blo 722323 1089281 := bstep (se 2 (by rfl) ⟨408480, by rfl⟩ : syracuseStep 1089281 = 816961) B816961
theorem B1089299 : Blo 722323 1089299 := bstep (se 1 (by rfl) ⟨816974, by rfl⟩ : syracuseStep 1089299 = 1633949) B1633949
theorem B1089329 : Blo 722323 1089329 := bstep (se 2 (by rfl) ⟨408498, by rfl⟩ : syracuseStep 1089329 = 816997) B816997
theorem B1089347 : Blo 722323 1089347 := bstep (se 1 (by rfl) ⟨817010, by rfl⟩ : syracuseStep 1089347 = 1634021) B1634021
theorem B827219 : Blo 722323 827219 := bstep (se 1 (by rfl) ⟨620414, by rfl⟩ : syracuseStep 827219 = 1240829) B1240829
theorem B1089377 : Blo 722323 1089377 := bstep (se 2 (by rfl) ⟨408516, by rfl⟩ : syracuseStep 1089377 = 817033) B817033
theorem B1220467 : Blo 722323 1220467 := bstep (se 1 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 1220467 = 1830701) B1830701
theorem B1089395 : Blo 722323 1089395 := bstep (se 1 (by rfl) ⟨817046, by rfl⟩ : syracuseStep 1089395 = 1634093) B1634093
theorem B1089425 : Blo 722323 1089425 := bstep (se 2 (by rfl) ⟨408534, by rfl⟩ : syracuseStep 1089425 = 817069) B817069
theorem B1089443 : Blo 722323 1089443 := bstep (se 1 (by rfl) ⟨817082, by rfl⟩ : syracuseStep 1089443 = 1634165) B1634165
theorem B1548209 : Blo 722323 1548209 := bstep (se 2 (by rfl) ⟨580578, by rfl⟩ : syracuseStep 1548209 = 1161157) B1161157
theorem B1089473 : Blo 722323 1089473 := bstep (se 2 (by rfl) ⟨408552, by rfl⟩ : syracuseStep 1089473 = 817105) B817105
theorem B1220609 : Blo 722323 1220609 := bstep (se 2 (by rfl) ⟨457728, by rfl⟩ : syracuseStep 1220609 = 915457) B915457
theorem B1220737 : Blo 722323 1220737 := bstep (se 2 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 1220737 = 915553) B915553
theorem B1220771 : Blo 722323 1220771 := bstep (se 1 (by rfl) ⟨915578, by rfl⟩ : syracuseStep 1220771 = 1831157) B1831157
theorem B1220899 : Blo 722323 1220899 := bstep (se 1 (by rfl) ⟨915674, by rfl⟩ : syracuseStep 1220899 = 1831349) B1831349
theorem B1221041 : Blo 722323 1221041 := bstep (se 2 (by rfl) ⟨457890, by rfl⟩ : syracuseStep 1221041 = 915781) B915781
theorem B5513669 : Blo 722323 5513669 := bstep (se 4 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 5513669 = 1033813) B1033813
theorem B1221169 : Blo 722323 1221169 := bstep (se 2 (by rfl) ⟨457938, by rfl⟩ : syracuseStep 1221169 = 915877) B915877
theorem B1221203 : Blo 722323 1221203 := bstep (se 1 (by rfl) ⟨915902, by rfl⟩ : syracuseStep 1221203 = 1831805) B1831805
theorem B1221331 : Blo 722323 1221331 := bstep (se 1 (by rfl) ⟨915998, by rfl⟩ : syracuseStep 1221331 = 1831997) B1831997
theorem B3089123 : Blo 722323 3089123 := bstep (se 1 (by rfl) ⟨2316842, by rfl⟩ : syracuseStep 3089123 = 4633685) B4633685
theorem B1221473 : Blo 722323 1221473 := bstep (se 2 (by rfl) ⟨458052, by rfl⟩ : syracuseStep 1221473 = 916105) B916105
theorem B3351395 : Blo 722323 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B1221601 : Blo 722323 1221601 := bstep (se 2 (by rfl) ⟨458100, by rfl⟩ : syracuseStep 1221601 = 916201) B916201
theorem B1221635 : Blo 722323 1221635 := bstep (se 1 (by rfl) ⟨916226, by rfl⟩ : syracuseStep 1221635 = 1832453) B1832453
theorem B2204749 : Blo 722323 2204749 := bstep (se 3 (by rfl) ⟨413390, by rfl⟩ : syracuseStep 2204749 = 826781) B826781
theorem B1221763 : Blo 722323 1221763 := bstep (se 1 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 1221763 = 1832645) B1832645
theorem B1221905 : Blo 722323 1221905 := bstep (se 2 (by rfl) ⟨458214, by rfl⟩ : syracuseStep 1221905 = 916429) B916429
theorem B10462517 : Blo 722323 10462517 := bstep (se 5 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 10462517 = 980861) B980861
theorem B1222033 : Blo 722323 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B1222067 : Blo 722323 1222067 := bstep (se 1 (by rfl) ⟨916550, by rfl⟩ : syracuseStep 1222067 = 1833101) B1833101
theorem B2205137 : Blo 722323 2205137 := bstep (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) B1653853
theorem B3483107 : Blo 722323 3483107 := bstep (se 1 (by rfl) ⟨2612330, by rfl⟩ : syracuseStep 3483107 = 5224661) B5224661
theorem B1222195 : Blo 722323 1222195 := bstep (se 1 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 1222195 = 1833293) B1833293
theorem B1222337 : Blo 722323 1222337 := bstep (se 2 (by rfl) ⟨458376, by rfl⟩ : syracuseStep 1222337 = 916753) B916753
theorem B2238211 : Blo 722323 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B1222465 : Blo 722323 1222465 := bstep (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) B916849
theorem B1222499 : Blo 722323 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B1222627 : Blo 722323 1222627 := bstep (se 1 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 1222627 = 1833941) B1833941
theorem B1157171 : Blo 722323 1157171 := bstep (se 1 (by rfl) ⟨867878, by rfl⟩ : syracuseStep 1157171 = 1735757) B1735757
theorem B1222769 : Blo 722323 1222769 := bstep (se 2 (by rfl) ⟨458538, by rfl⟩ : syracuseStep 1222769 = 917077) B917077
theorem B1648817 : Blo 722323 1648817 := bstep (se 2 (by rfl) ⟨618306, by rfl⟩ : syracuseStep 1648817 = 1236613) B1236613
theorem B1157345 : Blo 722323 1157345 := bstep (se 2 (by rfl) ⟨434004, by rfl⟩ : syracuseStep 1157345 = 868009) B868009
theorem B7416035 : Blo 722323 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B1222897 : Blo 722323 1222897 := bstep (se 2 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 1222897 = 917173) B917173
theorem B1222931 : Blo 722323 1222931 := bstep (se 1 (by rfl) ⟨917198, by rfl⟩ : syracuseStep 1222931 = 1834397) B1834397
theorem B993665 : Blo 722323 993665 := bstep (se 2 (by rfl) ⟨372624, by rfl⟩ : syracuseStep 993665 = 745249) B745249
theorem B1223059 : Blo 722323 1223059 := bstep (se 1 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 1223059 = 1834589) B1834589
theorem B1223201 : Blo 722323 1223201 := bstep (se 2 (by rfl) ⟨458700, by rfl⟩ : syracuseStep 1223201 = 917401) B917401
theorem B1550993 : Blo 722323 1550993 := bstep (se 2 (by rfl) ⟨581622, by rfl⟩ : syracuseStep 1550993 = 1163245) B1163245
theorem B1223329 : Blo 722323 1223329 := bstep (se 2 (by rfl) ⟨458748, by rfl⟩ : syracuseStep 1223329 = 917497) B917497
theorem B3091121 : Blo 722323 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B1223363 : Blo 722323 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B4238021 : Blo 722323 4238021 := bstep (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) B794629
theorem B1223491 : Blo 722323 1223491 := bstep (se 1 (by rfl) ⟨917618, by rfl⟩ : syracuseStep 1223491 = 1835237) B1835237
theorem B1223633 : Blo 722323 1223633 := bstep (se 2 (by rfl) ⟨458862, by rfl⟩ : syracuseStep 1223633 = 917725) B917725
theorem B1223761 : Blo 722323 1223761 := bstep (se 2 (by rfl) ⟨458910, by rfl⟩ : syracuseStep 1223761 = 917821) B917821
theorem B1223795 : Blo 722323 1223795 := bstep (se 1 (by rfl) ⟨917846, by rfl⟩ : syracuseStep 1223795 = 1835693) B1835693
theorem B11775203 : Blo 722323 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B1223923 : Blo 722323 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B732451 : Blo 722323 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B1224065 : Blo 722323 1224065 := bstep (se 2 (by rfl) ⟨459024, by rfl⟩ : syracuseStep 1224065 = 918049) B918049
theorem B1486289 : Blo 722323 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B1224193 : Blo 722323 1224193 := bstep (se 2 (by rfl) ⟨459072, by rfl⟩ : syracuseStep 1224193 = 918145) B918145
theorem B1224227 : Blo 722323 1224227 := bstep (se 1 (by rfl) ⟨918170, by rfl⟩ : syracuseStep 1224227 = 1836341) B1836341
theorem B1224355 : Blo 722323 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B1224497 : Blo 722323 1224497 := bstep (se 2 (by rfl) ⟨459186, by rfl⟩ : syracuseStep 1224497 = 918373) B918373
theorem B1650563 : Blo 722323 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B1224625 : Blo 722323 1224625 := bstep (se 2 (by rfl) ⟨459234, by rfl⟩ : syracuseStep 1224625 = 918469) B918469
theorem B1224659 : Blo 722323 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B1224787 : Blo 722323 1224787 := bstep (se 1 (by rfl) ⟨918590, by rfl⟩ : syracuseStep 1224787 = 1837181) B1837181
theorem B1159363 : Blo 722323 1159363 := bstep (se 1 (by rfl) ⟨869522, by rfl⟩ : syracuseStep 1159363 = 1739045) B1739045
theorem B1224929 : Blo 722323 1224929 := bstep (se 2 (by rfl) ⟨459348, by rfl⟩ : syracuseStep 1224929 = 918697) B918697
theorem B3911921 : Blo 722323 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B1159427 : Blo 722323 1159427 := bstep (se 1 (by rfl) ⟨869570, by rfl⟩ : syracuseStep 1159427 = 1739141) B1739141
theorem B1716515 : Blo 722323 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B3092813 : Blo 722323 3092813 := bstep (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) B1159805
theorem B1225057 : Blo 722323 1225057 := bstep (se 2 (by rfl) ⟨459396, by rfl⟩ : syracuseStep 1225057 = 918793) B918793
theorem B1225091 : Blo 722323 1225091 := bstep (se 1 (by rfl) ⟨918818, by rfl⟩ : syracuseStep 1225091 = 1837637) B1837637
theorem B3912113 : Blo 722323 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B1225219 : Blo 722323 1225219 := bstep (se 1 (by rfl) ⟨918914, by rfl⟩ : syracuseStep 1225219 = 1837829) B1837829
theorem B930355 : Blo 722323 930355 := bstep (se 1 (by rfl) ⟨697766, by rfl⟩ : syracuseStep 930355 = 1395533) B1395533
theorem B1225361 : Blo 722323 1225361 := bstep (se 2 (by rfl) ⟨459510, by rfl⟩ : syracuseStep 1225361 = 919021) B919021
theorem B1225489 : Blo 722323 1225489 := bstep (se 2 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 1225489 = 919117) B919117
theorem B2437937 : Blo 722323 2437937 := bstep (se 2 (by rfl) ⟨914226, by rfl⟩ : syracuseStep 2437937 = 1828453) B1828453
theorem B1225523 : Blo 722323 1225523 := bstep (se 1 (by rfl) ⟨919142, by rfl⟩ : syracuseStep 1225523 = 1838285) B1838285
theorem B1225651 : Blo 722323 1225651 := bstep (se 1 (by rfl) ⟨919238, by rfl⟩ : syracuseStep 1225651 = 1838477) B1838477
theorem B734179 : Blo 722323 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B1586161 : Blo 722323 1586161 := bstep (se 2 (by rfl) ⟨594810, by rfl⟩ : syracuseStep 1586161 = 1189621) B1189621
theorem B6173765 : Blo 722323 6173765 := bstep (se 4 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 6173765 = 1157581) B1157581
theorem B3486797 : Blo 722323 3486797 := bstep (se 3 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 3486797 = 1307549) B1307549
theorem B8795249 : Blo 722323 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B1160401 : Blo 722323 1160401 := bstep (se 2 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 1160401 = 870301) B870301
theorem B2438477 : Blo 722323 2438477 := bstep (se 3 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 2438477 = 914429) B914429
theorem B2438531 : Blo 722323 2438531 := bstep (se 1 (by rfl) ⟨1828898, by rfl⟩ : syracuseStep 2438531 = 3657797) B3657797
theorem B1160657 : Blo 722323 1160657 := bstep (se 2 (by rfl) ⟨435246, by rfl⟩ : syracuseStep 1160657 = 870493) B870493
theorem B4634117 : Blo 722323 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B1029667 : Blo 722323 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B2438801 : Blo 722323 2438801 := bstep (se 2 (by rfl) ⟨914550, by rfl⟩ : syracuseStep 2438801 = 1829101) B1829101
theorem B1160849 : Blo 722323 1160849 := bstep (se 2 (by rfl) ⟨435318, by rfl⟩ : syracuseStep 1160849 = 870637) B870637
theorem B3389219 : Blo 722323 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B8239157 : Blo 722323 8239157 := bstep (se 5 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 8239157 = 772421) B772421
theorem B5093489 : Blo 722323 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B2439341 : Blo 722323 2439341 := bstep (se 3 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 2439341 = 914753) B914753
theorem B2439395 : Blo 722323 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B2439665 : Blo 722323 2439665 := bstep (se 2 (by rfl) ⟨914874, by rfl⟩ : syracuseStep 2439665 = 1829749) B1829749
theorem B1391185 : Blo 722323 1391185 := bstep (se 2 (by rfl) ⟨521694, by rfl⟩ : syracuseStep 1391185 = 1043389) B1043389
theorem B5880433 : Blo 722323 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B1030801 : Blo 722323 1030801 := bstep (se 2 (by rfl) ⟨386550, by rfl⟩ : syracuseStep 1030801 = 773101) B773101
theorem B735971 : Blo 722323 735971 := bstep (se 1 (by rfl) ⟨551978, by rfl⟩ : syracuseStep 735971 = 1103957) B1103957
theorem B1030897 : Blo 722323 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B2931491 : Blo 722323 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B1162163 : Blo 722323 1162163 := bstep (se 1 (by rfl) ⟨871622, by rfl⟩ : syracuseStep 1162163 = 1743245) B1743245
theorem B2440205 : Blo 722323 2440205 := bstep (se 3 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 2440205 = 915077) B915077
theorem B2440259 : Blo 722323 2440259 := bstep (se 1 (by rfl) ⟨1830194, by rfl⟩ : syracuseStep 2440259 = 3660389) B3660389
theorem B1162387 : Blo 722323 1162387 := bstep (se 1 (by rfl) ⟨871790, by rfl⟩ : syracuseStep 1162387 = 1743581) B1743581
theorem B1162451 : Blo 722323 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B1031393 : Blo 722323 1031393 := bstep (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) B773545
theorem B2440529 : Blo 722323 2440529 := bstep (se 2 (by rfl) ⟨915198, by rfl⟩ : syracuseStep 2440529 = 1830397) B1830397
theorem B1162579 : Blo 722323 1162579 := bstep (se 1 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 1162579 = 1743869) B1743869
theorem B5488397 : Blo 722323 5488397 := bstep (se 3 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 5488397 = 2058149) B2058149
theorem B4407139 : Blo 722323 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B2441069 : Blo 722323 2441069 := bstep (se 3 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 2441069 = 915401) B915401
theorem B2441123 : Blo 722323 2441123 := bstep (se 1 (by rfl) ⟨1830842, by rfl⟩ : syracuseStep 2441123 = 3661685) B3661685
theorem B1163297 : Blo 722323 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B1032259 : Blo 722323 1032259 := bstep (se 1 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 1032259 = 1548389) B1548389
theorem B1163425 : Blo 722323 1163425 := bstep (se 2 (by rfl) ⟨436284, by rfl⟩ : syracuseStep 1163425 = 872569) B872569
theorem B4636835 : Blo 722323 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B1032355 : Blo 722323 1032355 := bstep (se 1 (by rfl) ⟨774266, by rfl⟩ : syracuseStep 1032355 = 1548533) B1548533
theorem B2441393 : Blo 722323 2441393 := bstep (se 2 (by rfl) ⟨915522, by rfl⟩ : syracuseStep 2441393 = 1831045) B1831045
theorem B3097187 : Blo 722323 3097187 := bstep (se 1 (by rfl) ⟨2322890, by rfl⟩ : syracuseStep 3097187 = 4645781) B4645781
theorem B1032851 : Blo 722323 1032851 := bstep (se 1 (by rfl) ⟨774638, by rfl⟩ : syracuseStep 1032851 = 1549277) B1549277
theorem B3719857 : Blo 722323 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B2441933 : Blo 722323 2441933 := bstep (se 3 (by rfl) ⟨457862, by rfl⟩ : syracuseStep 2441933 = 915725) B915725
theorem B2441987 : Blo 722323 2441987 := bstep (se 1 (by rfl) ⟨1831490, by rfl⟩ : syracuseStep 2441987 = 3662981) B3662981
theorem B2474819 : Blo 722323 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B2442257 : Blo 722323 2442257 := bstep (se 2 (by rfl) ⟨915846, by rfl⟩ : syracuseStep 2442257 = 1831693) B1831693
theorem B1098787 : Blo 722323 1098787 := bstep (se 1 (by rfl) ⟨824090, by rfl⟩ : syracuseStep 1098787 = 1648181) B1648181
theorem B1393777 : Blo 722323 1393777 := bstep (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) B1045333
theorem B1033489 : Blo 722323 1033489 := bstep (se 2 (by rfl) ⟨387558, by rfl⟩ : syracuseStep 1033489 = 775117) B775117
theorem B1656209 : Blo 722323 1656209 := bstep (se 2 (by rfl) ⟨621078, by rfl⟩ : syracuseStep 1656209 = 1242157) B1242157
theorem B1394147 : Blo 722323 1394147 := bstep (se 1 (by rfl) ⟨1045610, by rfl⟩ : syracuseStep 1394147 = 2091221) B2091221
theorem B2442797 : Blo 722323 2442797 := bstep (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) B916049
theorem B1033825 : Blo 722323 1033825 := bstep (se 2 (by rfl) ⟨387684, by rfl⟩ : syracuseStep 1033825 = 775369) B775369
theorem B2442851 : Blo 722323 2442851 := bstep (se 1 (by rfl) ⟨1832138, by rfl⟩ : syracuseStep 2442851 = 3664277) B3664277
theorem B1132211 : Blo 722323 1132211 := bstep (se 1 (by rfl) ⟨849158, by rfl⟩ : syracuseStep 1132211 = 1698317) B1698317
theorem B2934605 : Blo 722323 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B2443121 : Blo 722323 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B2607025 : Blo 722323 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B19810325 : Blo 722323 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B4638833 : Blo 722323 4638833 := bstep (se 2 (by rfl) ⟨1739562, by rfl⟩ : syracuseStep 4638833 = 3479125) B3479125
theorem B4409477 : Blo 722323 4409477 := bstep (se 4 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 4409477 = 826777) B826777
theorem B772259 : Blo 722323 772259 := bstep (se 1 (by rfl) ⟨579194, by rfl⟩ : syracuseStep 772259 = 1158389) B1158389
theorem B1099955 : Blo 722323 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B4114637 : Blo 722323 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B7948529 : Blo 722323 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B2443661 : Blo 722323 2443661 := bstep (se 3 (by rfl) ⟨458186, by rfl⟩ : syracuseStep 2443661 = 916373) B916373
theorem B2443715 : Blo 722323 2443715 := bstep (se 1 (by rfl) ⟨1832786, by rfl⟩ : syracuseStep 2443715 = 3665573) B3665573
theorem B7817741 : Blo 722323 7817741 := bstep (se 3 (by rfl) ⟨1465826, by rfl⟩ : syracuseStep 7817741 = 2931653) B2931653
theorem B9423373 : Blo 722323 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B3099185 : Blo 722323 3099185 := bstep (se 2 (by rfl) ⟨1162194, by rfl⟩ : syracuseStep 3099185 = 2324389) B2324389
theorem B5491313 : Blo 722323 5491313 := bstep (se 2 (by rfl) ⟨2059242, by rfl⟩ : syracuseStep 5491313 = 4118485) B4118485
theorem B2476675 : Blo 722323 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B2443985 : Blo 722323 2443985 := bstep (se 2 (by rfl) ⟨916494, by rfl⟩ : syracuseStep 2443985 = 1832989) B1832989
theorem B773011 : Blo 722323 773011 := bstep (se 1 (by rfl) ⟨579758, by rfl⟩ : syracuseStep 773011 = 1159517) B1159517
theorem B1952707 : Blo 722323 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B4115569 : Blo 722323 4115569 := bstep (se 2 (by rfl) ⟨1543338, by rfl⟩ : syracuseStep 4115569 = 3086677) B3086677
theorem B1100963 : Blo 722323 1100963 := bstep (se 1 (by rfl) ⟨825722, by rfl⟩ : syracuseStep 1100963 = 1651445) B1651445
theorem B2444525 : Blo 722323 2444525 := bstep (se 3 (by rfl) ⟨458348, by rfl⟩ : syracuseStep 2444525 = 916697) B916697
theorem B2444579 : Blo 722323 2444579 := bstep (se 1 (by rfl) ⟨1833434, by rfl⟩ : syracuseStep 2444579 = 3666869) B3666869
theorem B1625489 : Blo 722323 1625489 := bstep (se 2 (by rfl) ⟨609558, by rfl⟩ : syracuseStep 1625489 = 1219117) B1219117
theorem B1625507 : Blo 722323 1625507 := bstep (se 1 (by rfl) ⟨1219130, by rfl⟩ : syracuseStep 1625507 = 2438261) B2438261
theorem B2444849 : Blo 722323 2444849 := bstep (se 2 (by rfl) ⟨916818, by rfl⟩ : syracuseStep 2444849 = 1833637) B1833637
theorem B2379377 : Blo 722323 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B9293453 : Blo 722323 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B839315 : Blo 722323 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B1625777 : Blo 722323 1625777 := bstep (se 2 (by rfl) ⟨609666, by rfl⟩ : syracuseStep 1625777 = 1219333) B1219333
theorem B1625795 : Blo 722323 1625795 := bstep (se 1 (by rfl) ⟨1219346, by rfl⟩ : syracuseStep 1625795 = 2438693) B2438693
theorem B1101523 : Blo 722323 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B1855331 : Blo 722323 1855331 := bstep (se 1 (by rfl) ⟨1391498, by rfl⟩ : syracuseStep 1855331 = 2782997) B2782997
theorem B3657635 : Blo 722323 3657635 := bstep (se 1 (by rfl) ⟨2743226, by rfl⟩ : syracuseStep 3657635 = 5486453) B5486453
theorem B1953713 : Blo 722323 1953713 := bstep (se 2 (by rfl) ⟨732642, by rfl⟩ : syracuseStep 1953713 = 1465285) B1465285
theorem B1626065 : Blo 722323 1626065 := bstep (se 2 (by rfl) ⟨609774, by rfl⟩ : syracuseStep 1626065 = 1219549) B1219549
theorem B1626083 : Blo 722323 1626083 := bstep (se 1 (by rfl) ⟨1219562, by rfl⟩ : syracuseStep 1626083 = 2439125) B2439125
theorem B6606917 : Blo 722323 6606917 := bstep (se 4 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 6606917 = 1238797) B1238797
theorem B2445389 : Blo 722323 2445389 := bstep (se 3 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 2445389 = 917021) B917021
theorem B3919985 : Blo 722323 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B2445443 : Blo 722323 2445443 := bstep (se 1 (by rfl) ⟨1834082, by rfl⟩ : syracuseStep 2445443 = 3668165) B3668165
theorem B1626353 : Blo 722323 1626353 := bstep (se 2 (by rfl) ⟨609882, by rfl⟩ : syracuseStep 1626353 = 1219765) B1219765
theorem B1626371 : Blo 722323 1626371 := bstep (se 1 (by rfl) ⟨1219778, by rfl⟩ : syracuseStep 1626371 = 2439557) B2439557
theorem B774403 : Blo 722323 774403 := bstep (se 1 (by rfl) ⟨580802, by rfl⟩ : syracuseStep 774403 = 1161605) B1161605
theorem B2445713 : Blo 722323 2445713 := bstep (se 2 (by rfl) ⟨917142, by rfl⟩ : syracuseStep 2445713 = 1834285) B1834285
theorem B4641293 : Blo 722323 4641293 := bstep (se 3 (by rfl) ⟨870242, by rfl⟩ : syracuseStep 4641293 = 1740485) B1740485
theorem B1626641 : Blo 722323 1626641 := bstep (se 2 (by rfl) ⟨609990, by rfl⟩ : syracuseStep 1626641 = 1219981) B1219981
theorem B4117027 : Blo 722323 4117027 := bstep (se 1 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 4117027 = 6175541) B6175541
theorem B1626659 : Blo 722323 1626659 := bstep (se 1 (by rfl) ⟨1219994, by rfl⟩ : syracuseStep 1626659 = 2439989) B2439989
theorem B3658445 : Blo 722323 3658445 := bstep (se 3 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 3658445 = 1371917) B1371917
theorem B2085677 : Blo 722323 2085677 := bstep (se 3 (by rfl) ⟨391064, by rfl⟩ : syracuseStep 2085677 = 782129) B782129
theorem B1626929 : Blo 722323 1626929 := bstep (se 2 (by rfl) ⟨610098, by rfl⟩ : syracuseStep 1626929 = 1220197) B1220197
theorem B1626947 : Blo 722323 1626947 := bstep (se 1 (by rfl) ⟨1220210, by rfl⟩ : syracuseStep 1626947 = 2440421) B2440421
theorem B2446253 : Blo 722323 2446253 := bstep (se 3 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 2446253 = 917345) B917345
theorem B6181829 : Blo 722323 6181829 := bstep (se 4 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 6181829 = 1159093) B1159093
theorem B3101645 : Blo 722323 3101645 := bstep (se 3 (by rfl) ⟨581558, by rfl⟩ : syracuseStep 3101645 = 1163117) B1163117
theorem B2446307 : Blo 722323 2446307 := bstep (se 1 (by rfl) ⟨1834730, by rfl⟩ : syracuseStep 2446307 = 3669461) B3669461
theorem B4117553 : Blo 722323 4117553 := bstep (se 2 (by rfl) ⟨1544082, by rfl⟩ : syracuseStep 4117553 = 3088165) B3088165
theorem B2610253 : Blo 722323 2610253 := bstep (se 3 (by rfl) ⟨489422, by rfl⟩ : syracuseStep 2610253 = 978845) B978845
theorem B1627217 : Blo 722323 1627217 := bstep (se 2 (by rfl) ⟨610206, by rfl⟩ : syracuseStep 1627217 = 1220413) B1220413
theorem B3298403 : Blo 722323 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B1627235 : Blo 722323 1627235 := bstep (se 1 (by rfl) ⟨1220426, by rfl⟩ : syracuseStep 1627235 = 2440853) B2440853
theorem B2446577 : Blo 722323 2446577 := bstep (se 2 (by rfl) ⟨917466, by rfl⟩ : syracuseStep 2446577 = 1834933) B1834933
theorem B1627505 : Blo 722323 1627505 := bstep (se 2 (by rfl) ⟨610314, by rfl⟩ : syracuseStep 1627505 = 1220629) B1220629
theorem B1627523 : Blo 722323 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B6182513 : Blo 722323 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B1627793 : Blo 722323 1627793 := bstep (se 2 (by rfl) ⟨610422, by rfl⟩ : syracuseStep 1627793 = 1220845) B1220845
theorem B1627811 : Blo 722323 1627811 := bstep (se 1 (by rfl) ⟨1220858, by rfl⟩ : syracuseStep 1627811 = 2441717) B2441717
theorem B1103537 : Blo 722323 1103537 := bstep (se 2 (by rfl) ⟨413826, by rfl⟩ : syracuseStep 1103537 = 827653) B827653
theorem B2447117 : Blo 722323 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B2447171 : Blo 722323 2447171 := bstep (se 1 (by rfl) ⟨1835378, by rfl⟩ : syracuseStep 2447171 = 3670757) B3670757
theorem B1628081 : Blo 722323 1628081 := bstep (se 2 (by rfl) ⟨610530, by rfl⟩ : syracuseStep 1628081 = 1221061) B1221061
theorem B1628099 : Blo 722323 1628099 := bstep (se 1 (by rfl) ⟨1221074, by rfl⟩ : syracuseStep 1628099 = 2442149) B2442149
theorem B1955789 : Blo 722323 1955789 := bstep (se 3 (by rfl) ⟨366710, by rfl⟩ : syracuseStep 1955789 = 733421) B733421
theorem B2447441 : Blo 722323 2447441 := bstep (se 2 (by rfl) ⟨917790, by rfl⟩ : syracuseStep 2447441 = 1835581) B1835581
theorem B1628369 : Blo 722323 1628369 := bstep (se 2 (by rfl) ⟨610638, by rfl⟩ : syracuseStep 1628369 = 1221277) B1221277
theorem B1628387 : Blo 722323 1628387 := bstep (se 1 (by rfl) ⟨1221290, by rfl⟩ : syracuseStep 1628387 = 2442581) B2442581
theorem B2742605 : Blo 722323 2742605 := bstep (se 3 (by rfl) ⟨514238, by rfl⟩ : syracuseStep 2742605 = 1028477) B1028477
theorem B2480483 : Blo 722323 2480483 := bstep (se 1 (by rfl) ⟨1860362, by rfl⟩ : syracuseStep 2480483 = 3720725) B3720725
theorem B8346037 : Blo 722323 8346037 := bstep (se 5 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 8346037 = 782441) B782441
theorem B4119011 : Blo 722323 4119011 := bstep (se 1 (by rfl) ⟨3089258, by rfl⟩ : syracuseStep 4119011 = 6178517) B6178517
theorem B3299825 : Blo 722323 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B1628657 : Blo 722323 1628657 := bstep (se 2 (by rfl) ⟨610746, by rfl⟩ : syracuseStep 1628657 = 1221493) B1221493
theorem B1628675 : Blo 722323 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B2447981 : Blo 722323 2447981 := bstep (se 3 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 2447981 = 917993) B917993
theorem B2939533 : Blo 722323 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B2448035 : Blo 722323 2448035 := bstep (se 1 (by rfl) ⟨1836026, by rfl⟩ : syracuseStep 2448035 = 3672053) B3672053
theorem B2611939 : Blo 722323 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B1628945 : Blo 722323 1628945 := bstep (se 2 (by rfl) ⟨610854, by rfl⟩ : syracuseStep 1628945 = 1221709) B1221709
theorem B1628963 : Blo 722323 1628963 := bstep (se 1 (by rfl) ⟨1221722, by rfl⟩ : syracuseStep 1628963 = 2443445) B2443445
theorem B6970211 : Blo 722323 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B2317187 : Blo 722323 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B2448305 : Blo 722323 2448305 := bstep (se 2 (by rfl) ⟨918114, by rfl⟩ : syracuseStep 2448305 = 1836229) B1836229
theorem B1629233 : Blo 722323 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B1629251 : Blo 722323 1629251 := bstep (se 1 (by rfl) ⟨1221938, by rfl⟩ : syracuseStep 1629251 = 2443877) B2443877
theorem B2743409 : Blo 722323 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B1629521 : Blo 722323 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B1629539 : Blo 722323 1629539 := bstep (se 1 (by rfl) ⟨1222154, by rfl⟩ : syracuseStep 1629539 = 2444309) B2444309
theorem B1236353 : Blo 722323 1236353 := bstep (se 2 (by rfl) ⟨463632, by rfl⟩ : syracuseStep 1236353 = 927265) B927265
theorem B2448845 : Blo 722323 2448845 := bstep (se 3 (by rfl) ⟨459158, by rfl⟩ : syracuseStep 2448845 = 918317) B918317
theorem B2448899 : Blo 722323 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B3661361 : Blo 722323 3661361 := bstep (se 2 (by rfl) ⟨1373010, by rfl⟩ : syracuseStep 3661361 = 2746021) B2746021
theorem B1629809 : Blo 722323 1629809 := bstep (se 2 (by rfl) ⟨611178, by rfl⟩ : syracuseStep 1629809 = 1222357) B1222357
theorem B1629827 : Blo 722323 1629827 := bstep (se 1 (by rfl) ⟨1222370, by rfl⟩ : syracuseStep 1629827 = 2444741) B2444741
theorem B2318033 : Blo 722323 2318033 := bstep (se 2 (by rfl) ⟨869262, by rfl⟩ : syracuseStep 2318033 = 1738525) B1738525
theorem B1957613 : Blo 722323 1957613 := bstep (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) B734105
theorem B2744077 : Blo 722323 2744077 := bstep (se 3 (by rfl) ⟨514514, by rfl⟩ : syracuseStep 2744077 = 1029029) B1029029
theorem B1269521 : Blo 722323 1269521 := bstep (se 2 (by rfl) ⟨476070, by rfl⟩ : syracuseStep 1269521 = 952141) B952141
theorem B2449169 : Blo 722323 2449169 := bstep (se 2 (by rfl) ⟨918438, by rfl⟩ : syracuseStep 2449169 = 1836877) B1836877
theorem B1957745 : Blo 722323 1957745 := bstep (se 2 (by rfl) ⟨734154, by rfl⟩ : syracuseStep 1957745 = 1468309) B1468309
theorem B1630097 : Blo 722323 1630097 := bstep (se 2 (by rfl) ⟨611286, by rfl⟩ : syracuseStep 1630097 = 1222573) B1222573
theorem B1630115 : Blo 722323 1630115 := bstep (se 1 (by rfl) ⟨1222586, by rfl⟩ : syracuseStep 1630115 = 2445173) B2445173
theorem B1630385 : Blo 722323 1630385 := bstep (se 2 (by rfl) ⟨611394, by rfl⟩ : syracuseStep 1630385 = 1222789) B1222789
theorem B1630403 : Blo 722323 1630403 := bstep (se 1 (by rfl) ⟨1222802, by rfl⟩ : syracuseStep 1630403 = 2445605) B2445605
theorem B2515181 : Blo 722323 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B2449709 : Blo 722323 2449709 := bstep (se 3 (by rfl) ⟨459320, by rfl⟩ : syracuseStep 2449709 = 918641) B918641
theorem B4120901 : Blo 722323 4120901 := bstep (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) B772669
theorem B2449763 : Blo 722323 2449763 := bstep (se 1 (by rfl) ⟨1837322, by rfl⟩ : syracuseStep 2449763 = 3674645) B3674645
theorem B1630673 : Blo 722323 1630673 := bstep (se 2 (by rfl) ⟨611502, by rfl⟩ : syracuseStep 1630673 = 1223005) B1223005
theorem B1630691 : Blo 722323 1630691 := bstep (se 1 (by rfl) ⟨1223018, by rfl⟩ : syracuseStep 1630691 = 2446037) B2446037
theorem B2744867 : Blo 722323 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B2450033 : Blo 722323 2450033 := bstep (se 2 (by rfl) ⟨918762, by rfl⟩ : syracuseStep 2450033 = 1837525) B1837525
theorem B1630961 : Blo 722323 1630961 := bstep (se 2 (by rfl) ⟨611610, by rfl⟩ : syracuseStep 1630961 = 1223221) B1223221
theorem B1630979 : Blo 722323 1630979 := bstep (se 1 (by rfl) ⟨1223234, by rfl⟩ : syracuseStep 1630979 = 2446469) B2446469
theorem B3662819 : Blo 722323 3662819 := bstep (se 1 (by rfl) ⟨2747114, by rfl⟩ : syracuseStep 3662819 = 5494229) B5494229
theorem B1631249 : Blo 722323 1631249 := bstep (se 2 (by rfl) ⟨611718, by rfl⟩ : syracuseStep 1631249 = 1223437) B1223437
theorem B1631267 : Blo 722323 1631267 := bstep (se 1 (by rfl) ⟨1223450, by rfl⟩ : syracuseStep 1631267 = 2446901) B2446901
theorem B2057329 : Blo 722323 2057329 := bstep (se 2 (by rfl) ⟨771498, by rfl⟩ : syracuseStep 2057329 = 1542997) B1542997
theorem B2450573 : Blo 722323 2450573 := bstep (se 3 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 2450573 = 918965) B918965
theorem B2745521 : Blo 722323 2745521 := bstep (se 2 (by rfl) ⟨1029570, by rfl⟩ : syracuseStep 2745521 = 2059141) B2059141
theorem B2942129 : Blo 722323 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B2450627 : Blo 722323 2450627 := bstep (se 1 (by rfl) ⟨1837970, by rfl⟩ : syracuseStep 2450627 = 3675941) B3675941
theorem B1631537 : Blo 722323 1631537 := bstep (se 2 (by rfl) ⟨611826, by rfl⟩ : syracuseStep 1631537 = 1223653) B1223653
theorem B1631555 : Blo 722323 1631555 := bstep (se 1 (by rfl) ⟨1223666, by rfl⟩ : syracuseStep 1631555 = 2447333) B2447333
theorem B3302819 : Blo 722323 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B976321 : Blo 722323 976321 := bstep (se 2 (by rfl) ⟨366120, by rfl⟩ : syracuseStep 976321 = 732241) B732241
theorem B8250821 : Blo 722323 8250821 := bstep (se 4 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 8250821 = 1547029) B1547029
theorem B2450897 : Blo 722323 2450897 := bstep (se 2 (by rfl) ⟨919086, by rfl⟩ : syracuseStep 2450897 = 1838173) B1838173
theorem B2319853 : Blo 722323 2319853 := bstep (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) B869945
theorem B1828433 : Blo 722323 1828433 := bstep (se 2 (by rfl) ⟨685662, by rfl⟩ : syracuseStep 1828433 = 1371325) B1371325
theorem B1631825 : Blo 722323 1631825 := bstep (se 2 (by rfl) ⟨611934, by rfl⟩ : syracuseStep 1631825 = 1223869) B1223869
theorem B1631843 : Blo 722323 1631843 := bstep (se 1 (by rfl) ⟨1223882, by rfl⟩ : syracuseStep 1631843 = 2447765) B2447765
theorem B812659 : Blo 722323 812659 := bstep (se 1 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 812659 = 1218989) B1218989
theorem B1468081 : Blo 722323 1468081 := bstep (se 2 (by rfl) ⟨550530, by rfl⟩ : syracuseStep 1468081 = 1101061) B1101061
theorem B1238723 : Blo 722323 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B812803 : Blo 722323 812803 := bstep (se 1 (by rfl) ⟨609602, by rfl⟩ : syracuseStep 812803 = 1219205) B1219205
theorem B3663629 : Blo 722323 3663629 := bstep (se 3 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 3663629 = 1373861) B1373861
theorem B1632113 : Blo 722323 1632113 := bstep (se 2 (by rfl) ⟨612042, by rfl⟩ : syracuseStep 1632113 = 1224085) B1224085
theorem B1632131 : Blo 722323 1632131 := bstep (se 1 (by rfl) ⟨1224098, by rfl⟩ : syracuseStep 1632131 = 2448197) B2448197
theorem B1959821 : Blo 722323 1959821 := bstep (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) B734933
theorem B812947 : Blo 722323 812947 := bstep (se 1 (by rfl) ⟨609710, by rfl⟩ : syracuseStep 812947 = 1219421) B1219421
theorem B1173521 : Blo 722323 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B813091 : Blo 722323 813091 := bstep (se 1 (by rfl) ⟨609818, by rfl⟩ : syracuseStep 813091 = 1219637) B1219637
theorem B2517101 : Blo 722323 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B1042561 : Blo 722323 1042561 := bstep (se 2 (by rfl) ⟨390960, by rfl⟩ : syracuseStep 1042561 = 781921) B781921
theorem B1632401 : Blo 722323 1632401 := bstep (se 2 (by rfl) ⟨612150, by rfl⟩ : syracuseStep 1632401 = 1224301) B1224301
theorem B1632419 : Blo 722323 1632419 := bstep (se 1 (by rfl) ⟨1224314, by rfl⟩ : syracuseStep 1632419 = 2448629) B2448629
theorem B813235 : Blo 722323 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B1042723 : Blo 722323 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B813379 : Blo 722323 813379 := bstep (se 1 (by rfl) ⟨610034, by rfl⟩ : syracuseStep 813379 = 1220069) B1220069
theorem B2058605 : Blo 722323 2058605 := bstep (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) B771977
theorem B1632689 : Blo 722323 1632689 := bstep (se 2 (by rfl) ⟨612258, by rfl⟩ : syracuseStep 1632689 = 1224517) B1224517
theorem B1632707 : Blo 722323 1632707 := bstep (se 1 (by rfl) ⟨1224530, by rfl⟩ : syracuseStep 1632707 = 2449061) B2449061
theorem B813523 : Blo 722323 813523 := bstep (se 1 (by rfl) ⟨610142, by rfl⟩ : syracuseStep 813523 = 1220285) B1220285
theorem B2058787 : Blo 722323 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B1829425 : Blo 722323 1829425 := bstep (se 2 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 1829425 = 1372069) B1372069
theorem B2091587 : Blo 722323 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B2058833 : Blo 722323 2058833 := bstep (se 2 (by rfl) ⟨772062, by rfl⟩ : syracuseStep 2058833 = 1544125) B1544125
theorem B813667 : Blo 722323 813667 := bstep (se 1 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 813667 = 1220501) B1220501
theorem B2746979 : Blo 722323 2746979 := bstep (se 1 (by rfl) ⟨2060234, by rfl⟩ : syracuseStep 2746979 = 4120469) B4120469
theorem B2746993 : Blo 722323 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B1632977 : Blo 722323 1632977 := bstep (se 2 (by rfl) ⟨612366, by rfl⟩ : syracuseStep 1632977 = 1224733) B1224733
theorem B1632995 : Blo 722323 1632995 := bstep (se 1 (by rfl) ⟨1224746, by rfl⟩ : syracuseStep 1632995 = 2449493) B2449493
theorem B813811 : Blo 722323 813811 := bstep (se 1 (by rfl) ⟨610358, by rfl⟩ : syracuseStep 813811 = 1220717) B1220717
theorem B1829699 : Blo 722323 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B813955 : Blo 722323 813955 := bstep (se 1 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 813955 = 1220933) B1220933
theorem B1469315 : Blo 722323 1469315 := bstep (se 1 (by rfl) ⟨1101986, by rfl⟩ : syracuseStep 1469315 = 2203973) B2203973
theorem B4025285 : Blo 722323 4025285 := bstep (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) B754741
theorem B1633265 : Blo 722323 1633265 := bstep (se 2 (by rfl) ⟨612474, by rfl⟩ : syracuseStep 1633265 = 1224949) B1224949
theorem B1829891 : Blo 722323 1829891 := bstep (se 1 (by rfl) ⟨1372418, by rfl⟩ : syracuseStep 1829891 = 2744837) B2744837
theorem B1633283 : Blo 722323 1633283 := bstep (se 1 (by rfl) ⟨1224962, by rfl⟩ : syracuseStep 1633283 = 2449925) B2449925
theorem B814099 : Blo 722323 814099 := bstep (se 1 (by rfl) ⟨610574, by rfl⟩ : syracuseStep 814099 = 1221149) B1221149
theorem B814243 : Blo 722323 814243 := bstep (se 1 (by rfl) ⟨610682, by rfl⟩ : syracuseStep 814243 = 1221365) B1221365
theorem B978115 : Blo 722323 978115 := bstep (se 1 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 978115 = 1467173) B1467173
theorem B2944205 : Blo 722323 2944205 := bstep (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) B1104077
theorem B1305841 : Blo 722323 1305841 := bstep (se 2 (by rfl) ⟨489690, by rfl⟩ : syracuseStep 1305841 = 979381) B979381
theorem B1633553 : Blo 722323 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B1633571 : Blo 722323 1633571 := bstep (se 1 (by rfl) ⟨1225178, by rfl⟩ : syracuseStep 1633571 = 2450357) B2450357
theorem B814387 : Blo 722323 814387 := bstep (se 1 (by rfl) ⟨610790, by rfl⟩ : syracuseStep 814387 = 1221581) B1221581
theorem B814531 : Blo 722323 814531 := bstep (se 1 (by rfl) ⟨610898, by rfl⟩ : syracuseStep 814531 = 1221797) B1221797
theorem B1633841 : Blo 722323 1633841 := bstep (se 2 (by rfl) ⟨612690, by rfl⟩ : syracuseStep 1633841 = 1225381) B1225381
theorem B978499 : Blo 722323 978499 := bstep (se 1 (by rfl) ⟨733874, by rfl⟩ : syracuseStep 978499 = 1467749) B1467749
theorem B1633859 : Blo 722323 1633859 := bstep (se 1 (by rfl) ⟨1225394, by rfl⟩ : syracuseStep 1633859 = 2450789) B2450789
theorem B814675 : Blo 722323 814675 := bstep (se 1 (by rfl) ⟨611006, by rfl⟩ : syracuseStep 814675 = 1222013) B1222013
theorem B1371811 : Blo 722323 1371811 := bstep (se 1 (by rfl) ⟨1028858, by rfl⟩ : syracuseStep 1371811 = 2057717) B2057717
theorem B1175233 : Blo 722323 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B814819 : Blo 722323 814819 := bstep (se 1 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 814819 = 1222229) B1222229
theorem B1371971 : Blo 722323 1371971 := bstep (se 1 (by rfl) ⟨1028978, by rfl⟩ : syracuseStep 1371971 = 2057957) B2057957
theorem B1634129 : Blo 722323 1634129 := bstep (se 2 (by rfl) ⟨612798, by rfl⟩ : syracuseStep 1634129 = 1225597) B1225597
theorem B978785 : Blo 722323 978785 := bstep (se 2 (by rfl) ⟨367044, by rfl⟩ : syracuseStep 978785 = 734089) B734089
theorem B1634147 : Blo 722323 1634147 := bstep (se 1 (by rfl) ⟨1225610, by rfl⟩ : syracuseStep 1634147 = 2451221) B2451221
theorem B814963 : Blo 722323 814963 := bstep (se 1 (by rfl) ⟨611222, by rfl⟩ : syracuseStep 814963 = 1222445) B1222445
theorem B1830833 : Blo 722323 1830833 := bstep (se 2 (by rfl) ⟨686562, by rfl⟩ : syracuseStep 1830833 = 1373125) B1373125
theorem B1830883 : Blo 722323 1830883 := bstep (se 1 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 1830883 = 2746325) B2746325
theorem B2060291 : Blo 722323 2060291 := bstep (se 1 (by rfl) ⟨1545218, by rfl⟩ : syracuseStep 2060291 = 3090437) B3090437
theorem B815107 : Blo 722323 815107 := bstep (se 1 (by rfl) ⟨611330, by rfl⟩ : syracuseStep 815107 = 1222661) B1222661
theorem B2748451 : Blo 722323 2748451 := bstep (se 1 (by rfl) ⟨2061338, by rfl⟩ : syracuseStep 2748451 = 4122677) B4122677
theorem B1831025 : Blo 722323 1831025 := bstep (se 2 (by rfl) ⟨686634, by rfl⟩ : syracuseStep 1831025 = 1373269) B1373269
theorem B815251 : Blo 722323 815251 := bstep (se 1 (by rfl) ⟨611438, by rfl⟩ : syracuseStep 815251 = 1222877) B1222877
theorem B7827683 : Blo 722323 7827683 := bstep (se 1 (by rfl) ⟨5870762, by rfl⟩ : syracuseStep 7827683 = 11741525) B11741525
theorem B815395 : Blo 722323 815395 := bstep (se 1 (by rfl) ⟨611546, by rfl⟩ : syracuseStep 815395 = 1223093) B1223093
theorem B12513649 : Blo 722323 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B815539 : Blo 722323 815539 := bstep (se 1 (by rfl) ⟨611654, by rfl⟩ : syracuseStep 815539 = 1223309) B1223309
theorem B815683 : Blo 722323 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B979537 : Blo 722323 979537 := bstep (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) B734653
theorem B9269873 : Blo 722323 9269873 := bstep (se 2 (by rfl) ⟨3476202, by rfl⟩ : syracuseStep 9269873 = 6952405) B6952405
theorem B3666545 : Blo 722323 3666545 := bstep (se 2 (by rfl) ⟨1374954, by rfl⟩ : syracuseStep 3666545 = 2749909) B2749909
theorem B1307267 : Blo 722323 1307267 := bstep (se 1 (by rfl) ⟨980450, by rfl⟩ : syracuseStep 1307267 = 1960901) B1960901
theorem B979651 : Blo 722323 979651 := bstep (se 1 (by rfl) ⟨734738, by rfl⟩ : syracuseStep 979651 = 1469477) B1469477
theorem B815827 : Blo 722323 815827 := bstep (se 1 (by rfl) ⟨611870, by rfl⟩ : syracuseStep 815827 = 1223741) B1223741
theorem B4649699 : Blo 722323 4649699 := bstep (se 1 (by rfl) ⟨3487274, by rfl⟩ : syracuseStep 4649699 = 6974549) B6974549
theorem B1307441 : Blo 722323 1307441 := bstep (se 2 (by rfl) ⟨490290, by rfl⟩ : syracuseStep 1307441 = 980581) B980581
theorem B815971 : Blo 722323 815971 := bstep (se 1 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 815971 = 1223957) B1223957
theorem B1373041 : Blo 722323 1373041 := bstep (se 2 (by rfl) ⟨514890, by rfl⟩ : syracuseStep 1373041 = 1029781) B1029781
theorem B2323313 : Blo 722323 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B914323 : Blo 722323 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B914419 : Blo 722323 914419 := bstep (se 1 (by rfl) ⟨685814, by rfl⟩ : syracuseStep 914419 = 1371629) B1371629
theorem B816115 : Blo 722323 816115 := bstep (se 1 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 816115 = 1224173) B1224173
theorem B2323505 : Blo 722323 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B1832017 : Blo 722323 1832017 := bstep (se 2 (by rfl) ⟨687006, by rfl⟩ : syracuseStep 1832017 = 1374013) B1374013
theorem B816259 : Blo 722323 816259 := bstep (se 1 (by rfl) ⟨612194, by rfl⟩ : syracuseStep 816259 = 1224389) B1224389
theorem B2061521 : Blo 722323 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B816403 : Blo 722323 816403 := bstep (se 1 (by rfl) ⟨612302, by rfl⟩ : syracuseStep 816403 = 1224605) B1224605
theorem B980257 : Blo 722323 980257 := bstep (se 2 (by rfl) ⟨367596, by rfl⟩ : syracuseStep 980257 = 735193) B735193
theorem B1832291 : Blo 722323 1832291 := bstep (se 1 (by rfl) ⟨1374218, by rfl⟩ : syracuseStep 1832291 = 2748437) B2748437
theorem B816547 : Blo 722323 816547 := bstep (se 1 (by rfl) ⟨612410, by rfl⟩ : syracuseStep 816547 = 1224821) B1224821
theorem B914915 : Blo 722323 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B6190577 : Blo 722323 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B6977009 : Blo 722323 6977009 := bstep (se 2 (by rfl) ⟨2616378, by rfl⟩ : syracuseStep 6977009 = 5232757) B5232757
theorem B1832483 : Blo 722323 1832483 := bstep (se 1 (by rfl) ⟨1374362, by rfl⟩ : syracuseStep 1832483 = 2748725) B2748725
theorem B816691 : Blo 722323 816691 := bstep (se 1 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 816691 = 1225037) B1225037
theorem B816835 : Blo 722323 816835 := bstep (se 1 (by rfl) ⟨612626, by rfl⟩ : syracuseStep 816835 = 1225253) B1225253
theorem B980689 : Blo 722323 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B980753 : Blo 722323 980753 := bstep (se 2 (by rfl) ⟨367782, by rfl⟩ : syracuseStep 980753 = 735565) B735565
theorem B816979 : Blo 722323 816979 := bstep (se 1 (by rfl) ⟨612734, by rfl⟩ : syracuseStep 816979 = 1225469) B1225469
theorem B784243 : Blo 722323 784243 := bstep (se 1 (by rfl) ⟨588182, by rfl⟩ : syracuseStep 784243 = 1176365) B1176365
theorem B980851 : Blo 722323 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B1374097 : Blo 722323 1374097 := bstep (se 2 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 1374097 = 1030573) B1030573
theorem B4650929 : Blo 722323 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B1308593 : Blo 722323 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B4126733 : Blo 722323 4126733 := bstep (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) B1547525
theorem B3668003 : Blo 722323 3668003 := bstep (se 1 (by rfl) ⟨2751002, by rfl⟩ : syracuseStep 3668003 = 5502005) B5502005
theorem B5568581 : Blo 722323 5568581 := bstep (se 4 (by rfl) ⟨522054, by rfl⟩ : syracuseStep 5568581 = 1044109) B1044109
theorem B3471437 : Blo 722323 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B13924493 : Blo 722323 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B1308817 : Blo 722323 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B915619 : Blo 722323 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B2750669 : Blo 722323 2750669 := bstep (se 3 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 2750669 = 1031501) B1031501
theorem B915715 : Blo 722323 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B1374499 : Blo 722323 1374499 := bstep (se 1 (by rfl) ⟨1030874, by rfl⟩ : syracuseStep 1374499 = 2061749) B2061749
theorem B1374545 : Blo 722323 1374545 := bstep (se 2 (by rfl) ⟨515454, by rfl⟩ : syracuseStep 1374545 = 1030909) B1030909
theorem B1767761 : Blo 722323 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B1571185 : Blo 722323 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B6977933 : Blo 722323 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B1833425 : Blo 722323 1833425 := bstep (se 2 (by rfl) ⟨687534, by rfl⟩ : syracuseStep 1833425 = 1375069) B1375069
theorem B1833475 : Blo 722323 1833475 := bstep (se 1 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 1833475 = 2750213) B2750213
theorem B1374833 : Blo 722323 1374833 := bstep (se 2 (by rfl) ⟨515562, by rfl⟩ : syracuseStep 1374833 = 1031125) B1031125
theorem B2062979 : Blo 722323 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B1833617 : Blo 722323 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B916211 : Blo 722323 916211 := bstep (se 1 (by rfl) ⟨687158, by rfl⟩ : syracuseStep 916211 = 1374317) B1374317
theorem B3668813 : Blo 722323 3668813 := bstep (se 3 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 3668813 = 1375805) B1375805
theorem B9272333 : Blo 722323 9272333 := bstep (se 3 (by rfl) ⟨1738562, by rfl⟩ : syracuseStep 9272333 = 3477125) B3477125
theorem B5209229 : Blo 722323 5209229 := bstep (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) B1953461
theorem B4947085 : Blo 722323 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B8256653 : Blo 722323 8256653 := bstep (se 3 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 8256653 = 3096245) B3096245
theorem B2096323 : Blo 722323 2096323 := bstep (se 1 (by rfl) ⟨1572242, by rfl⟩ : syracuseStep 2096323 = 3144485) B3144485
theorem B2325773 : Blo 722323 2325773 := bstep (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) B872165
theorem B1375555 : Blo 722323 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B2063789 : Blo 722323 2063789 := bstep (se 3 (by rfl) ⟨386960, by rfl⟩ : syracuseStep 2063789 = 773921) B773921
theorem B916915 : Blo 722323 916915 := bstep (se 1 (by rfl) ⟨687686, by rfl⟩ : syracuseStep 916915 = 1375373) B1375373
theorem B917011 : Blo 722323 917011 := bstep (se 1 (by rfl) ⟨687758, by rfl⟩ : syracuseStep 917011 = 1375517) B1375517
theorem B2063981 : Blo 722323 2063981 := bstep (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) B773993
theorem B1834609 : Blo 722323 1834609 := bstep (se 2 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 1834609 = 1375957) B1375957
theorem B1376003 : Blo 722323 1376003 := bstep (se 1 (by rfl) ⟨1032002, by rfl⟩ : syracuseStep 1376003 = 2064005) B2064005
theorem B2981681 : Blo 722323 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B1834883 : Blo 722323 1834883 := bstep (se 1 (by rfl) ⟨1376162, by rfl⟩ : syracuseStep 1834883 = 2752325) B2752325
theorem B6193037 : Blo 722323 6193037 := bstep (se 3 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 6193037 = 2322389) B2322389
theorem B1376345 : Blo 722323 1376345 := bstep (se 2 (by rfl) ⟨516129, by rfl⟩ : syracuseStep 1376345 = 1032259) B1032259
theorem B3670109 : Blo 722323 3670109 := bstep (se 3 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 3670109 = 1376291) B1376291
theorem B2752643 : Blo 722323 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B2064791 : Blo 722323 2064791 := bstep (se 1 (by rfl) ⟨1548593, by rfl⟩ : syracuseStep 2064791 = 3097187) B3097187
theorem B2753099 : Blo 722323 2753099 := bstep (se 1 (by rfl) ⟨2064824, by rfl⟩ : syracuseStep 2753099 = 4129649) B4129649
theorem B20873821 : Blo 722323 20873821 := bstep (se 3 (by rfl) ⟨3913841, by rfl⟩ : syracuseStep 20873821 = 7827683) B7827683
theorem B918155 : Blo 722323 918155 := bstep (se 1 (by rfl) ⟨688616, by rfl⟩ : syracuseStep 918155 = 1377233) B1377233
theorem B1835723 : Blo 722323 1835723 := bstep (se 1 (by rfl) ⟨1376792, by rfl⟩ : syracuseStep 1835723 = 2753585) B2753585
theorem B6980357 : Blo 722323 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B2753297 : Blo 722323 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B6030155 : Blo 722323 6030155 := bstep (se 1 (by rfl) ⟨4522616, by rfl⟩ : syracuseStep 6030155 = 9045233) B9045233
theorem B5505893 : Blo 722323 5505893 := bstep (se 4 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 5505893 = 1032355) B1032355
theorem B754807 : Blo 722323 754807 := bstep (se 1 (by rfl) ⟨566105, by rfl⟩ : syracuseStep 754807 = 1132211) B1132211
theorem B5506379 : Blo 722323 5506379 := bstep (se 1 (by rfl) ⟨4129784, by rfl⟩ : syracuseStep 5506379 = 8259569) B8259569
theorem B918859 : Blo 722323 918859 := bstep (se 1 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 918859 = 1378289) B1378289
theorem B13206883 : Blo 722323 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B4130149 : Blo 722323 4130149 := bstep (se 4 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 4130149 = 774403) B774403
theorem B722327 : Blo 722323 722327 := bstep (se 1 (by rfl) ⟨541745, by rfl⟩ : syracuseStep 722327 = 1083491) B1083491
theorem B722347 : Blo 722323 722347 := bstep (se 1 (by rfl) ⟨541760, by rfl⟩ : syracuseStep 722347 = 1083521) B1083521
theorem B722359 : Blo 722323 722359 := bstep (se 1 (by rfl) ⟨541769, by rfl⟩ : syracuseStep 722359 = 1083539) B1083539
theorem B722379 : Blo 722323 722379 := bstep (se 1 (by rfl) ⟨541784, by rfl⟩ : syracuseStep 722379 = 1083569) B1083569
theorem B722391 : Blo 722323 722391 := bstep (se 1 (by rfl) ⟨541793, by rfl⟩ : syracuseStep 722391 = 1083587) B1083587
theorem B722411 : Blo 722323 722411 := bstep (se 1 (by rfl) ⟨541808, by rfl⟩ : syracuseStep 722411 = 1083617) B1083617
theorem B722423 : Blo 722323 722423 := bstep (se 1 (by rfl) ⟨541817, by rfl⟩ : syracuseStep 722423 = 1083635) B1083635
theorem B722443 : Blo 722323 722443 := bstep (se 1 (by rfl) ⟨541832, by rfl⟩ : syracuseStep 722443 = 1083665) B1083665
theorem B1377803 : Blo 722323 1377803 := bstep (se 1 (by rfl) ⟨1033352, by rfl⟩ : syracuseStep 1377803 = 2066705) B2066705
theorem B722455 : Blo 722323 722455 := bstep (se 1 (by rfl) ⟨541841, by rfl⟩ : syracuseStep 722455 = 1083683) B1083683
theorem B2754071 : Blo 722323 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B722475 : Blo 722323 722475 := bstep (se 1 (by rfl) ⟨541856, by rfl⟩ : syracuseStep 722475 = 1083713) B1083713
theorem B722487 : Blo 722323 722487 := bstep (se 1 (by rfl) ⟨541865, by rfl⟩ : syracuseStep 722487 = 1083731) B1083731
theorem B722507 : Blo 722323 722507 := bstep (se 1 (by rfl) ⟨541880, by rfl⟩ : syracuseStep 722507 = 1083761) B1083761
theorem B722519 : Blo 722323 722519 := bstep (se 1 (by rfl) ⟨541889, by rfl⟩ : syracuseStep 722519 = 1083779) B1083779
theorem B919127 : Blo 722323 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B722539 : Blo 722323 722539 := bstep (se 1 (by rfl) ⟨541904, by rfl⟩ : syracuseStep 722539 = 1083809) B1083809
theorem B722551 : Blo 722323 722551 := bstep (se 1 (by rfl) ⟨541913, by rfl⟩ : syracuseStep 722551 = 1083827) B1083827
theorem B722571 : Blo 722323 722571 := bstep (se 1 (by rfl) ⟨541928, by rfl⟩ : syracuseStep 722571 = 1083857) B1083857
theorem B722583 : Blo 722323 722583 := bstep (se 1 (by rfl) ⟨541937, by rfl⟩ : syracuseStep 722583 = 1083875) B1083875
theorem B1836695 : Blo 722323 1836695 := bstep (se 1 (by rfl) ⟨1377521, by rfl⟩ : syracuseStep 1836695 = 2755043) B2755043
theorem B722603 : Blo 722323 722603 := bstep (se 1 (by rfl) ⟨541952, by rfl⟩ : syracuseStep 722603 = 1083905) B1083905
theorem B5211827 : Blo 722323 5211827 := bstep (se 1 (by rfl) ⟨3908870, by rfl⟩ : syracuseStep 5211827 = 7817741) B7817741
theorem B722615 : Blo 722323 722615 := bstep (se 1 (by rfl) ⟨541961, by rfl⟩ : syracuseStep 722615 = 1083923) B1083923
theorem B1377985 : Blo 722323 1377985 := bstep (se 2 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 1377985 = 1033489) B1033489
theorem B722635 : Blo 722323 722635 := bstep (se 1 (by rfl) ⟨541976, by rfl⟩ : syracuseStep 722635 = 1083953) B1083953
theorem B2066123 : Blo 722323 2066123 := bstep (se 1 (by rfl) ⟨1549592, by rfl⟩ : syracuseStep 2066123 = 3099185) B3099185
theorem B722647 : Blo 722323 722647 := bstep (se 1 (by rfl) ⟨541985, by rfl⟩ : syracuseStep 722647 = 1083971) B1083971
theorem B2754269 : Blo 722323 2754269 := bstep (se 3 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 2754269 = 1032851) B1032851
theorem B722667 : Blo 722323 722667 := bstep (se 1 (by rfl) ⟨542000, by rfl⟩ : syracuseStep 722667 = 1084001) B1084001
theorem B722679 : Blo 722323 722679 := bstep (se 1 (by rfl) ⟨542009, by rfl⟩ : syracuseStep 722679 = 1084019) B1084019
theorem B722699 : Blo 722323 722699 := bstep (se 1 (by rfl) ⟨542024, by rfl⟩ : syracuseStep 722699 = 1084049) B1084049
theorem B722711 : Blo 722323 722711 := bstep (se 1 (by rfl) ⟨542033, by rfl⟩ : syracuseStep 722711 = 1084067) B1084067
theorem B722731 : Blo 722323 722731 := bstep (se 1 (by rfl) ⟨542048, by rfl⟩ : syracuseStep 722731 = 1084097) B1084097
theorem B722743 : Blo 722323 722743 := bstep (se 1 (by rfl) ⟨542057, by rfl⟩ : syracuseStep 722743 = 1084115) B1084115
theorem B722763 : Blo 722323 722763 := bstep (se 1 (by rfl) ⟨542072, by rfl⟩ : syracuseStep 722763 = 1084145) B1084145
theorem B722775 : Blo 722323 722775 := bstep (se 1 (by rfl) ⟨542081, by rfl⟩ : syracuseStep 722775 = 1084163) B1084163
theorem B722795 : Blo 722323 722795 := bstep (se 1 (by rfl) ⟨542096, by rfl⟩ : syracuseStep 722795 = 1084193) B1084193
theorem B722807 : Blo 722323 722807 := bstep (se 1 (by rfl) ⟨542105, by rfl⟩ : syracuseStep 722807 = 1084211) B1084211
theorem B722827 : Blo 722323 722827 := bstep (se 1 (by rfl) ⟨542120, by rfl⟩ : syracuseStep 722827 = 1084241) B1084241
theorem B722839 : Blo 722323 722839 := bstep (se 1 (by rfl) ⟨542129, by rfl⟩ : syracuseStep 722839 = 1084259) B1084259
theorem B722859 : Blo 722323 722859 := bstep (se 1 (by rfl) ⟨542144, by rfl⟩ : syracuseStep 722859 = 1084289) B1084289
theorem B722871 : Blo 722323 722871 := bstep (se 1 (by rfl) ⟨542153, by rfl⟩ : syracuseStep 722871 = 1084307) B1084307
theorem B722891 : Blo 722323 722891 := bstep (se 1 (by rfl) ⟨542168, by rfl⟩ : syracuseStep 722891 = 1084337) B1084337
theorem B722903 : Blo 722323 722903 := bstep (se 1 (by rfl) ⟨542177, by rfl⟩ : syracuseStep 722903 = 1084355) B1084355
theorem B722923 : Blo 722323 722923 := bstep (se 1 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 722923 = 1084385) B1084385
theorem B722935 : Blo 722323 722935 := bstep (se 1 (by rfl) ⟨542201, by rfl⟩ : syracuseStep 722935 = 1084403) B1084403
theorem B722955 : Blo 722323 722955 := bstep (se 1 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 722955 = 1084433) B1084433
theorem B722967 : Blo 722323 722967 := bstep (se 1 (by rfl) ⟨542225, by rfl⟩ : syracuseStep 722967 = 1084451) B1084451
theorem B722987 : Blo 722323 722987 := bstep (se 1 (by rfl) ⟨542240, by rfl⟩ : syracuseStep 722987 = 1084481) B1084481
theorem B722999 : Blo 722323 722999 := bstep (se 1 (by rfl) ⟨542249, by rfl⟩ : syracuseStep 722999 = 1084499) B1084499
theorem B723019 : Blo 722323 723019 := bstep (se 1 (by rfl) ⟨542264, by rfl⟩ : syracuseStep 723019 = 1084529) B1084529
theorem B723031 : Blo 722323 723031 := bstep (se 1 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 723031 = 1084547) B1084547
theorem B723051 : Blo 722323 723051 := bstep (se 1 (by rfl) ⟨542288, by rfl⟩ : syracuseStep 723051 = 1084577) B1084577
theorem B723063 : Blo 722323 723063 := bstep (se 1 (by rfl) ⟨542297, by rfl⟩ : syracuseStep 723063 = 1084595) B1084595
theorem B1378433 : Blo 722323 1378433 := bstep (se 2 (by rfl) ⟨516912, by rfl⟩ : syracuseStep 1378433 = 1033825) B1033825
theorem B723083 : Blo 722323 723083 := bstep (se 1 (by rfl) ⟨542312, by rfl⟩ : syracuseStep 723083 = 1084625) B1084625
theorem B723095 : Blo 722323 723095 := bstep (se 1 (by rfl) ⟨542321, by rfl⟩ : syracuseStep 723095 = 1084643) B1084643
theorem B3672215 : Blo 722323 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B1083545 : Blo 722323 1083545 := bstep (se 2 (by rfl) ⟨406329, by rfl⟩ : syracuseStep 1083545 = 812659) B812659
theorem B723115 : Blo 722323 723115 := bstep (se 1 (by rfl) ⟨542336, by rfl⟩ : syracuseStep 723115 = 1084673) B1084673
theorem B723127 : Blo 722323 723127 := bstep (se 1 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 723127 = 1084691) B1084691
theorem B723147 : Blo 722323 723147 := bstep (se 1 (by rfl) ⟨542360, by rfl⟩ : syracuseStep 723147 = 1084721) B1084721
theorem B723159 : Blo 722323 723159 := bstep (se 1 (by rfl) ⟨542369, by rfl⟩ : syracuseStep 723159 = 1084739) B1084739
theorem B723179 : Blo 722323 723179 := bstep (se 1 (by rfl) ⟨542384, by rfl⟩ : syracuseStep 723179 = 1084769) B1084769
theorem B723191 : Blo 722323 723191 := bstep (se 1 (by rfl) ⟨542393, by rfl⟩ : syracuseStep 723191 = 1084787) B1084787
theorem B1083659 : Blo 722323 1083659 := bstep (se 1 (by rfl) ⟨812744, by rfl⟩ : syracuseStep 1083659 = 1625489) B1625489
theorem B723211 : Blo 722323 723211 := bstep (se 1 (by rfl) ⟨542408, by rfl⟩ : syracuseStep 723211 = 1084817) B1084817
theorem B1083671 : Blo 722323 1083671 := bstep (se 1 (by rfl) ⟨812753, by rfl⟩ : syracuseStep 1083671 = 1625507) B1625507
theorem B723223 : Blo 722323 723223 := bstep (se 1 (by rfl) ⟨542417, by rfl⟩ : syracuseStep 723223 = 1084835) B1084835
theorem B723243 : Blo 722323 723243 := bstep (se 1 (by rfl) ⟨542432, by rfl⟩ : syracuseStep 723243 = 1084865) B1084865
theorem B1837363 : Blo 722323 1837363 := bstep (se 1 (by rfl) ⟨1378022, by rfl⟩ : syracuseStep 1837363 = 2756045) B2756045
theorem B723255 : Blo 722323 723255 := bstep (se 1 (by rfl) ⟨542441, by rfl⟩ : syracuseStep 723255 = 1084883) B1084883
theorem B723275 : Blo 722323 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B723287 : Blo 722323 723287 := bstep (se 1 (by rfl) ⟨542465, by rfl⟩ : syracuseStep 723287 = 1084931) B1084931
theorem B1083737 : Blo 722323 1083737 := bstep (se 2 (by rfl) ⟨406401, by rfl⟩ : syracuseStep 1083737 = 812803) B812803
theorem B723307 : Blo 722323 723307 := bstep (se 1 (by rfl) ⟨542480, by rfl⟩ : syracuseStep 723307 = 1084961) B1084961
theorem B723319 : Blo 722323 723319 := bstep (se 1 (by rfl) ⟨542489, by rfl⟩ : syracuseStep 723319 = 1084979) B1084979
theorem B723339 : Blo 722323 723339 := bstep (se 1 (by rfl) ⟨542504, by rfl⟩ : syracuseStep 723339 = 1085009) B1085009
theorem B723351 : Blo 722323 723351 := bstep (se 1 (by rfl) ⟨542513, by rfl⟩ : syracuseStep 723351 = 1085027) B1085027
theorem B723371 : Blo 722323 723371 := bstep (se 1 (by rfl) ⟨542528, by rfl⟩ : syracuseStep 723371 = 1085057) B1085057
theorem B6195635 : Blo 722323 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B723383 : Blo 722323 723383 := bstep (se 1 (by rfl) ⟨542537, by rfl⟩ : syracuseStep 723383 = 1085075) B1085075
theorem B1837505 : Blo 722323 1837505 := bstep (se 2 (by rfl) ⟨689064, by rfl⟩ : syracuseStep 1837505 = 1378129) B1378129
theorem B1083851 : Blo 722323 1083851 := bstep (se 1 (by rfl) ⟨812888, by rfl⟩ : syracuseStep 1083851 = 1625777) B1625777
theorem B723403 : Blo 722323 723403 := bstep (se 1 (by rfl) ⟨542552, by rfl⟩ : syracuseStep 723403 = 1085105) B1085105
theorem B1083863 : Blo 722323 1083863 := bstep (se 1 (by rfl) ⟨812897, by rfl⟩ : syracuseStep 1083863 = 1625795) B1625795
theorem B723415 : Blo 722323 723415 := bstep (se 1 (by rfl) ⟨542561, by rfl⟩ : syracuseStep 723415 = 1085123) B1085123
theorem B1378775 : Blo 722323 1378775 := bstep (se 1 (by rfl) ⟨1034081, by rfl⟩ : syracuseStep 1378775 = 2068163) B2068163
theorem B723435 : Blo 722323 723435 := bstep (se 1 (by rfl) ⟨542576, by rfl⟩ : syracuseStep 723435 = 1085153) B1085153
theorem B723447 : Blo 722323 723447 := bstep (se 1 (by rfl) ⟨542585, by rfl⟩ : syracuseStep 723447 = 1085171) B1085171
theorem B723467 : Blo 722323 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B723479 : Blo 722323 723479 := bstep (se 1 (by rfl) ⟨542609, by rfl⟩ : syracuseStep 723479 = 1085219) B1085219
theorem B1083929 : Blo 722323 1083929 := bstep (se 2 (by rfl) ⟨406473, by rfl⟩ : syracuseStep 1083929 = 812947) B812947
theorem B723499 : Blo 722323 723499 := bstep (se 1 (by rfl) ⟨542624, by rfl⟩ : syracuseStep 723499 = 1085249) B1085249
theorem B723511 : Blo 722323 723511 := bstep (se 1 (by rfl) ⟨542633, by rfl⟩ : syracuseStep 723511 = 1085267) B1085267
theorem B3476033 : Blo 722323 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B723531 : Blo 722323 723531 := bstep (se 1 (by rfl) ⟨542648, by rfl⟩ : syracuseStep 723531 = 1085297) B1085297
theorem B723543 : Blo 722323 723543 := bstep (se 1 (by rfl) ⟨542657, by rfl⟩ : syracuseStep 723543 = 1085315) B1085315
theorem B723563 : Blo 722323 723563 := bstep (se 1 (by rfl) ⟨542672, by rfl⟩ : syracuseStep 723563 = 1085345) B1085345
theorem B723575 : Blo 722323 723575 := bstep (se 1 (by rfl) ⟨542681, by rfl⟩ : syracuseStep 723575 = 1085363) B1085363
theorem B1084043 : Blo 722323 1084043 := bstep (se 1 (by rfl) ⟨813032, by rfl⟩ : syracuseStep 1084043 = 1626065) B1626065
theorem B723595 : Blo 722323 723595 := bstep (se 1 (by rfl) ⟨542696, by rfl⟩ : syracuseStep 723595 = 1085393) B1085393
theorem B1084055 : Blo 722323 1084055 := bstep (se 1 (by rfl) ⟨813041, by rfl⟩ : syracuseStep 1084055 = 1626083) B1626083
theorem B723607 : Blo 722323 723607 := bstep (se 1 (by rfl) ⟨542705, by rfl⟩ : syracuseStep 723607 = 1085411) B1085411
theorem B723627 : Blo 722323 723627 := bstep (se 1 (by rfl) ⟨542720, by rfl⟩ : syracuseStep 723627 = 1085441) B1085441
theorem B723639 : Blo 722323 723639 := bstep (se 1 (by rfl) ⟨542729, by rfl⟩ : syracuseStep 723639 = 1085459) B1085459
theorem B723659 : Blo 722323 723659 := bstep (se 1 (by rfl) ⟨542744, by rfl⟩ : syracuseStep 723659 = 1085489) B1085489
theorem B723671 : Blo 722323 723671 := bstep (se 1 (by rfl) ⟨542753, by rfl⟩ : syracuseStep 723671 = 1085507) B1085507
theorem B1084121 : Blo 722323 1084121 := bstep (se 2 (by rfl) ⟨406545, by rfl⟩ : syracuseStep 1084121 = 813091) B813091
theorem B723691 : Blo 722323 723691 := bstep (se 1 (by rfl) ⟨542768, by rfl⟩ : syracuseStep 723691 = 1085537) B1085537
theorem B723703 : Blo 722323 723703 := bstep (se 1 (by rfl) ⟨542777, by rfl⟩ : syracuseStep 723703 = 1085555) B1085555
theorem B723723 : Blo 722323 723723 := bstep (se 1 (by rfl) ⟨542792, by rfl⟩ : syracuseStep 723723 = 1085585) B1085585
theorem B723735 : Blo 722323 723735 := bstep (se 1 (by rfl) ⟨542801, by rfl⟩ : syracuseStep 723735 = 1085603) B1085603
theorem B723755 : Blo 722323 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B6196013 : Blo 722323 6196013 := bstep (se 3 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 6196013 = 2323505) B2323505
theorem B723767 : Blo 722323 723767 := bstep (se 1 (by rfl) ⟨542825, by rfl⟩ : syracuseStep 723767 = 1085651) B1085651
theorem B1084235 : Blo 722323 1084235 := bstep (se 1 (by rfl) ⟨813176, by rfl⟩ : syracuseStep 1084235 = 1626353) B1626353
theorem B723787 : Blo 722323 723787 := bstep (se 1 (by rfl) ⟨542840, by rfl⟩ : syracuseStep 723787 = 1085681) B1085681
theorem B1084247 : Blo 722323 1084247 := bstep (se 1 (by rfl) ⟨813185, by rfl⟩ : syracuseStep 1084247 = 1626371) B1626371
theorem B723799 : Blo 722323 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B723819 : Blo 722323 723819 := bstep (se 1 (by rfl) ⟨542864, by rfl⟩ : syracuseStep 723819 = 1085729) B1085729
theorem B723831 : Blo 722323 723831 := bstep (se 1 (by rfl) ⟨542873, by rfl⟩ : syracuseStep 723831 = 1085747) B1085747
theorem B723851 : Blo 722323 723851 := bstep (se 1 (by rfl) ⟨542888, by rfl⟩ : syracuseStep 723851 = 1085777) B1085777
theorem B723863 : Blo 722323 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1084313 : Blo 722323 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B723883 : Blo 722323 723883 := bstep (se 1 (by rfl) ⟨542912, by rfl⟩ : syracuseStep 723883 = 1085825) B1085825
theorem B723895 : Blo 722323 723895 := bstep (se 1 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 723895 = 1085843) B1085843
theorem B723915 : Blo 722323 723915 := bstep (se 1 (by rfl) ⟨542936, by rfl⟩ : syracuseStep 723915 = 1085873) B1085873
theorem B723927 : Blo 722323 723927 := bstep (se 1 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 723927 = 1085891) B1085891
theorem B723947 : Blo 722323 723947 := bstep (se 1 (by rfl) ⟨542960, by rfl⟩ : syracuseStep 723947 = 1085921) B1085921
theorem B723959 : Blo 722323 723959 := bstep (se 1 (by rfl) ⟨542969, by rfl⟩ : syracuseStep 723959 = 1085939) B1085939
theorem B1084427 : Blo 722323 1084427 := bstep (se 1 (by rfl) ⟨813320, by rfl⟩ : syracuseStep 1084427 = 1626641) B1626641
theorem B723979 : Blo 722323 723979 := bstep (se 1 (by rfl) ⟨542984, by rfl⟩ : syracuseStep 723979 = 1085969) B1085969
theorem B1084439 : Blo 722323 1084439 := bstep (se 1 (by rfl) ⟨813329, by rfl⟩ : syracuseStep 1084439 = 1626659) B1626659
theorem B723991 : Blo 722323 723991 := bstep (se 1 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 723991 = 1085987) B1085987
theorem B724011 : Blo 722323 724011 := bstep (se 1 (by rfl) ⟨543008, by rfl⟩ : syracuseStep 724011 = 1086017) B1086017
theorem B724023 : Blo 722323 724023 := bstep (se 1 (by rfl) ⟨543017, by rfl⟩ : syracuseStep 724023 = 1086035) B1086035
theorem B724043 : Blo 722323 724043 := bstep (se 1 (by rfl) ⟨543032, by rfl⟩ : syracuseStep 724043 = 1086065) B1086065
theorem B724055 : Blo 722323 724055 := bstep (se 1 (by rfl) ⟨543041, by rfl⟩ : syracuseStep 724055 = 1086083) B1086083
theorem B1084505 : Blo 722323 1084505 := bstep (se 2 (by rfl) ⟨406689, by rfl⟩ : syracuseStep 1084505 = 813379) B813379
theorem B724075 : Blo 722323 724075 := bstep (se 1 (by rfl) ⟨543056, by rfl⟩ : syracuseStep 724075 = 1086113) B1086113
theorem B724087 : Blo 722323 724087 := bstep (se 1 (by rfl) ⟨543065, by rfl⟩ : syracuseStep 724087 = 1086131) B1086131
theorem B724107 : Blo 722323 724107 := bstep (se 1 (by rfl) ⟨543080, by rfl⟩ : syracuseStep 724107 = 1086161) B1086161
theorem B724119 : Blo 722323 724119 := bstep (se 1 (by rfl) ⟨543089, by rfl⟩ : syracuseStep 724119 = 1086179) B1086179
theorem B724139 : Blo 722323 724139 := bstep (se 1 (by rfl) ⟨543104, by rfl⟩ : syracuseStep 724139 = 1086209) B1086209
theorem B724151 : Blo 722323 724151 := bstep (se 1 (by rfl) ⟨543113, by rfl⟩ : syracuseStep 724151 = 1086227) B1086227
theorem B1084619 : Blo 722323 1084619 := bstep (se 1 (by rfl) ⟨813464, by rfl⟩ : syracuseStep 1084619 = 1626929) B1626929
theorem B724171 : Blo 722323 724171 := bstep (se 1 (by rfl) ⟨543128, by rfl⟩ : syracuseStep 724171 = 1086257) B1086257
theorem B1084631 : Blo 722323 1084631 := bstep (se 1 (by rfl) ⟨813473, by rfl⟩ : syracuseStep 1084631 = 1626947) B1626947
theorem B724183 : Blo 722323 724183 := bstep (se 1 (by rfl) ⟨543137, by rfl⟩ : syracuseStep 724183 = 1086275) B1086275
theorem B724203 : Blo 722323 724203 := bstep (se 1 (by rfl) ⟨543152, by rfl⟩ : syracuseStep 724203 = 1086305) B1086305
theorem B724215 : Blo 722323 724215 := bstep (se 1 (by rfl) ⟨543161, by rfl⟩ : syracuseStep 724215 = 1086323) B1086323
theorem B724235 : Blo 722323 724235 := bstep (se 1 (by rfl) ⟨543176, by rfl⟩ : syracuseStep 724235 = 1086353) B1086353
theorem B724247 : Blo 722323 724247 := bstep (se 1 (by rfl) ⟨543185, by rfl⟩ : syracuseStep 724247 = 1086371) B1086371
theorem B1084697 : Blo 722323 1084697 := bstep (se 2 (by rfl) ⟨406761, by rfl⟩ : syracuseStep 1084697 = 813523) B813523
theorem B724267 : Blo 722323 724267 := bstep (se 1 (by rfl) ⟨543200, by rfl⟩ : syracuseStep 724267 = 1086401) B1086401
theorem B2067763 : Blo 722323 2067763 := bstep (se 1 (by rfl) ⟨1550822, by rfl⟩ : syracuseStep 2067763 = 3101645) B3101645
theorem B724279 : Blo 722323 724279 := bstep (se 1 (by rfl) ⟨543209, by rfl⟩ : syracuseStep 724279 = 1086419) B1086419
theorem B724299 : Blo 722323 724299 := bstep (se 1 (by rfl) ⟨543224, by rfl⟩ : syracuseStep 724299 = 1086449) B1086449
theorem B724311 : Blo 722323 724311 := bstep (se 1 (by rfl) ⟨543233, by rfl⟩ : syracuseStep 724311 = 1086467) B1086467
theorem B13208933 : Blo 722323 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B724331 : Blo 722323 724331 := bstep (se 1 (by rfl) ⟨543248, by rfl⟩ : syracuseStep 724331 = 1086497) B1086497
theorem B724343 : Blo 722323 724343 := bstep (se 1 (by rfl) ⟨543257, by rfl⟩ : syracuseStep 724343 = 1086515) B1086515
theorem B1084811 : Blo 722323 1084811 := bstep (se 1 (by rfl) ⟨813608, by rfl⟩ : syracuseStep 1084811 = 1627217) B1627217
theorem B724363 : Blo 722323 724363 := bstep (se 1 (by rfl) ⟨543272, by rfl⟩ : syracuseStep 724363 = 1086545) B1086545
theorem B2198935 : Blo 722323 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B1084823 : Blo 722323 1084823 := bstep (se 1 (by rfl) ⟨813617, by rfl⟩ : syracuseStep 1084823 = 1627235) B1627235
theorem B724375 : Blo 722323 724375 := bstep (se 1 (by rfl) ⟨543281, by rfl⟩ : syracuseStep 724375 = 1086563) B1086563
theorem B724395 : Blo 722323 724395 := bstep (se 1 (by rfl) ⟨543296, by rfl⟩ : syracuseStep 724395 = 1086593) B1086593
theorem B724407 : Blo 722323 724407 := bstep (se 1 (by rfl) ⟨543305, by rfl⟩ : syracuseStep 724407 = 1086611) B1086611
theorem B724427 : Blo 722323 724427 := bstep (se 1 (by rfl) ⟨543320, by rfl⟩ : syracuseStep 724427 = 1086641) B1086641
theorem B724439 : Blo 722323 724439 := bstep (se 1 (by rfl) ⟨543329, by rfl⟩ : syracuseStep 724439 = 1086659) B1086659
theorem B1084889 : Blo 722323 1084889 := bstep (se 2 (by rfl) ⟨406833, by rfl⟩ : syracuseStep 1084889 = 813667) B813667
theorem B724459 : Blo 722323 724459 := bstep (se 1 (by rfl) ⟨543344, by rfl⟩ : syracuseStep 724459 = 1086689) B1086689
theorem B724471 : Blo 722323 724471 := bstep (se 1 (by rfl) ⟨543353, by rfl⟩ : syracuseStep 724471 = 1086707) B1086707
theorem B724491 : Blo 722323 724491 := bstep (se 1 (by rfl) ⟨543368, by rfl⟩ : syracuseStep 724491 = 1086737) B1086737
theorem B724503 : Blo 722323 724503 := bstep (se 1 (by rfl) ⟨543377, by rfl⟩ : syracuseStep 724503 = 1086755) B1086755
theorem B724523 : Blo 722323 724523 := bstep (se 1 (by rfl) ⟨543392, by rfl⟩ : syracuseStep 724523 = 1086785) B1086785
theorem B724535 : Blo 722323 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B1085003 : Blo 722323 1085003 := bstep (se 1 (by rfl) ⟨813752, by rfl⟩ : syracuseStep 1085003 = 1627505) B1627505
theorem B724555 : Blo 722323 724555 := bstep (se 1 (by rfl) ⟨543416, by rfl⟩ : syracuseStep 724555 = 1086833) B1086833
theorem B1085015 : Blo 722323 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B724567 : Blo 722323 724567 := bstep (se 1 (by rfl) ⟨543425, by rfl⟩ : syracuseStep 724567 = 1086851) B1086851
theorem B724587 : Blo 722323 724587 := bstep (se 1 (by rfl) ⟨543440, by rfl⟩ : syracuseStep 724587 = 1086881) B1086881
theorem B724599 : Blo 722323 724599 := bstep (se 1 (by rfl) ⟨543449, by rfl⟩ : syracuseStep 724599 = 1086899) B1086899
theorem B2756227 : Blo 722323 2756227 := bstep (se 1 (by rfl) ⟨2067170, by rfl⟩ : syracuseStep 2756227 = 4134341) B4134341
theorem B724619 : Blo 722323 724619 := bstep (se 1 (by rfl) ⟨543464, by rfl⟩ : syracuseStep 724619 = 1086929) B1086929
theorem B724631 : Blo 722323 724631 := bstep (se 1 (by rfl) ⟨543473, by rfl⟩ : syracuseStep 724631 = 1086947) B1086947
theorem B1085081 : Blo 722323 1085081 := bstep (se 2 (by rfl) ⟨406905, by rfl⟩ : syracuseStep 1085081 = 813811) B813811
theorem B724651 : Blo 722323 724651 := bstep (se 1 (by rfl) ⟨543488, by rfl⟩ : syracuseStep 724651 = 1086977) B1086977
theorem B724663 : Blo 722323 724663 := bstep (se 1 (by rfl) ⟨543497, by rfl⟩ : syracuseStep 724663 = 1086995) B1086995
theorem B724683 : Blo 722323 724683 := bstep (se 1 (by rfl) ⟨543512, by rfl⟩ : syracuseStep 724683 = 1087025) B1087025
theorem B724695 : Blo 722323 724695 := bstep (se 1 (by rfl) ⟨543521, by rfl⟩ : syracuseStep 724695 = 1087043) B1087043
theorem B724715 : Blo 722323 724715 := bstep (se 1 (by rfl) ⟨543536, by rfl⟩ : syracuseStep 724715 = 1087073) B1087073
theorem B724727 : Blo 722323 724727 := bstep (se 1 (by rfl) ⟨543545, by rfl⟩ : syracuseStep 724727 = 1087091) B1087091
theorem B1085195 : Blo 722323 1085195 := bstep (se 1 (by rfl) ⟨813896, by rfl⟩ : syracuseStep 1085195 = 1627793) B1627793
theorem B724747 : Blo 722323 724747 := bstep (se 1 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 724747 = 1087121) B1087121
theorem B1085207 : Blo 722323 1085207 := bstep (se 1 (by rfl) ⟨813905, by rfl⟩ : syracuseStep 1085207 = 1627811) B1627811
theorem B724759 : Blo 722323 724759 := bstep (se 1 (by rfl) ⟨543569, by rfl⟩ : syracuseStep 724759 = 1087139) B1087139
theorem B724779 : Blo 722323 724779 := bstep (se 1 (by rfl) ⟨543584, by rfl⟩ : syracuseStep 724779 = 1087169) B1087169
theorem B724791 : Blo 722323 724791 := bstep (se 1 (by rfl) ⟨543593, by rfl⟩ : syracuseStep 724791 = 1087187) B1087187
theorem B724811 : Blo 722323 724811 := bstep (se 1 (by rfl) ⟨543608, by rfl⟩ : syracuseStep 724811 = 1087217) B1087217
theorem B724823 : Blo 722323 724823 := bstep (se 1 (by rfl) ⟨543617, by rfl⟩ : syracuseStep 724823 = 1087235) B1087235
theorem B1085273 : Blo 722323 1085273 := bstep (se 2 (by rfl) ⟨406977, by rfl⟩ : syracuseStep 1085273 = 813955) B813955
theorem B724843 : Blo 722323 724843 := bstep (se 1 (by rfl) ⟨543632, by rfl⟩ : syracuseStep 724843 = 1087265) B1087265
theorem B724855 : Blo 722323 724855 := bstep (se 1 (by rfl) ⟨543641, by rfl⟩ : syracuseStep 724855 = 1087283) B1087283
theorem B724875 : Blo 722323 724875 := bstep (se 1 (by rfl) ⟨543656, by rfl⟩ : syracuseStep 724875 = 1087313) B1087313
theorem B724887 : Blo 722323 724887 := bstep (se 1 (by rfl) ⟨543665, by rfl⟩ : syracuseStep 724887 = 1087331) B1087331
theorem B724907 : Blo 722323 724907 := bstep (se 1 (by rfl) ⟨543680, by rfl⟩ : syracuseStep 724907 = 1087361) B1087361
theorem B2756531 : Blo 722323 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B724919 : Blo 722323 724919 := bstep (se 1 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 724919 = 1087379) B1087379
theorem B1085387 : Blo 722323 1085387 := bstep (se 1 (by rfl) ⟨814040, by rfl⟩ : syracuseStep 1085387 = 1628081) B1628081
theorem B724939 : Blo 722323 724939 := bstep (se 1 (by rfl) ⟨543704, by rfl⟩ : syracuseStep 724939 = 1087409) B1087409
theorem B1085399 : Blo 722323 1085399 := bstep (se 1 (by rfl) ⟨814049, by rfl⟩ : syracuseStep 1085399 = 1628099) B1628099
theorem B724951 : Blo 722323 724951 := bstep (se 1 (by rfl) ⟨543713, by rfl⟩ : syracuseStep 724951 = 1087427) B1087427
theorem B724971 : Blo 722323 724971 := bstep (se 1 (by rfl) ⟨543728, by rfl⟩ : syracuseStep 724971 = 1087457) B1087457
theorem B724983 : Blo 722323 724983 := bstep (se 1 (by rfl) ⟨543737, by rfl⟩ : syracuseStep 724983 = 1087475) B1087475
theorem B725003 : Blo 722323 725003 := bstep (se 1 (by rfl) ⟨543752, by rfl⟩ : syracuseStep 725003 = 1087505) B1087505
theorem B725015 : Blo 722323 725015 := bstep (se 1 (by rfl) ⟨543761, by rfl⟩ : syracuseStep 725015 = 1087523) B1087523
theorem B1085465 : Blo 722323 1085465 := bstep (se 2 (by rfl) ⟨407049, by rfl⟩ : syracuseStep 1085465 = 814099) B814099
theorem B725035 : Blo 722323 725035 := bstep (se 1 (by rfl) ⟨543776, by rfl⟩ : syracuseStep 725035 = 1087553) B1087553
theorem B725047 : Blo 722323 725047 := bstep (se 1 (by rfl) ⟨543785, by rfl⟩ : syracuseStep 725047 = 1087571) B1087571
theorem B725067 : Blo 722323 725067 := bstep (se 1 (by rfl) ⟨543800, by rfl⟩ : syracuseStep 725067 = 1087601) B1087601
theorem B725079 : Blo 722323 725079 := bstep (se 1 (by rfl) ⟨543809, by rfl⟩ : syracuseStep 725079 = 1087619) B1087619
theorem B725099 : Blo 722323 725099 := bstep (se 1 (by rfl) ⟨543824, by rfl⟩ : syracuseStep 725099 = 1087649) B1087649
theorem B725111 : Blo 722323 725111 := bstep (se 1 (by rfl) ⟨543833, by rfl⟩ : syracuseStep 725111 = 1087667) B1087667
theorem B1085579 : Blo 722323 1085579 := bstep (se 1 (by rfl) ⟨814184, by rfl⟩ : syracuseStep 1085579 = 1628369) B1628369
theorem B725131 : Blo 722323 725131 := bstep (se 1 (by rfl) ⟨543848, by rfl⟩ : syracuseStep 725131 = 1087697) B1087697
theorem B1085591 : Blo 722323 1085591 := bstep (se 1 (by rfl) ⟨814193, by rfl⟩ : syracuseStep 1085591 = 1628387) B1628387
theorem B725143 : Blo 722323 725143 := bstep (se 1 (by rfl) ⟨543857, by rfl⟩ : syracuseStep 725143 = 1087715) B1087715
theorem B725163 : Blo 722323 725163 := bstep (se 1 (by rfl) ⟨543872, by rfl⟩ : syracuseStep 725163 = 1087745) B1087745
theorem B725175 : Blo 722323 725175 := bstep (se 1 (by rfl) ⟨543881, by rfl⟩ : syracuseStep 725175 = 1087763) B1087763
theorem B725195 : Blo 722323 725195 := bstep (se 1 (by rfl) ⟨543896, by rfl⟩ : syracuseStep 725195 = 1087793) B1087793
theorem B725207 : Blo 722323 725207 := bstep (se 1 (by rfl) ⟨543905, by rfl⟩ : syracuseStep 725207 = 1087811) B1087811
theorem B1085657 : Blo 722323 1085657 := bstep (se 2 (by rfl) ⟨407121, by rfl⟩ : syracuseStep 1085657 = 814243) B814243
theorem B725227 : Blo 722323 725227 := bstep (se 1 (by rfl) ⟨543920, by rfl⟩ : syracuseStep 725227 = 1087841) B1087841
theorem B725239 : Blo 722323 725239 := bstep (se 1 (by rfl) ⟨543929, by rfl⟩ : syracuseStep 725239 = 1087859) B1087859
theorem B725259 : Blo 722323 725259 := bstep (se 1 (by rfl) ⟨543944, by rfl⟩ : syracuseStep 725259 = 1087889) B1087889
theorem B725271 : Blo 722323 725271 := bstep (se 1 (by rfl) ⟨543953, by rfl⟩ : syracuseStep 725271 = 1087907) B1087907
theorem B725291 : Blo 722323 725291 := bstep (se 1 (by rfl) ⟨543968, by rfl⟩ : syracuseStep 725291 = 1087937) B1087937
theorem B725303 : Blo 722323 725303 := bstep (se 1 (by rfl) ⟨543977, by rfl⟩ : syracuseStep 725303 = 1087955) B1087955
theorem B1741121 : Blo 722323 1741121 := bstep (se 2 (by rfl) ⟨652920, by rfl⟩ : syracuseStep 1741121 = 1305841) B1305841
theorem B2199883 : Blo 722323 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B1085771 : Blo 722323 1085771 := bstep (se 1 (by rfl) ⟨814328, by rfl⟩ : syracuseStep 1085771 = 1628657) B1628657
theorem B725323 : Blo 722323 725323 := bstep (se 1 (by rfl) ⟨543992, by rfl⟩ : syracuseStep 725323 = 1087985) B1087985
theorem B1085783 : Blo 722323 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B725335 : Blo 722323 725335 := bstep (se 1 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 725335 = 1088003) B1088003
theorem B725355 : Blo 722323 725355 := bstep (se 1 (by rfl) ⟨544016, by rfl⟩ : syracuseStep 725355 = 1088033) B1088033
theorem B725367 : Blo 722323 725367 := bstep (se 1 (by rfl) ⟨544025, by rfl⟩ : syracuseStep 725367 = 1088051) B1088051
theorem B725387 : Blo 722323 725387 := bstep (se 1 (by rfl) ⟨544040, by rfl⟩ : syracuseStep 725387 = 1088081) B1088081
theorem B725399 : Blo 722323 725399 := bstep (se 1 (by rfl) ⟨544049, by rfl⟩ : syracuseStep 725399 = 1088099) B1088099
theorem B1085849 : Blo 722323 1085849 := bstep (se 2 (by rfl) ⟨407193, by rfl⟩ : syracuseStep 1085849 = 814387) B814387
theorem B725419 : Blo 722323 725419 := bstep (se 1 (by rfl) ⟨544064, by rfl⟩ : syracuseStep 725419 = 1088129) B1088129
theorem B725431 : Blo 722323 725431 := bstep (se 1 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 725431 = 1088147) B1088147
theorem B725451 : Blo 722323 725451 := bstep (se 1 (by rfl) ⟨544088, by rfl⟩ : syracuseStep 725451 = 1088177) B1088177
theorem B725463 : Blo 722323 725463 := bstep (se 1 (by rfl) ⟨544097, by rfl⟩ : syracuseStep 725463 = 1088195) B1088195
theorem B725483 : Blo 722323 725483 := bstep (se 1 (by rfl) ⟨544112, by rfl⟩ : syracuseStep 725483 = 1088225) B1088225
theorem B725495 : Blo 722323 725495 := bstep (se 1 (by rfl) ⟨544121, by rfl⟩ : syracuseStep 725495 = 1088243) B1088243
theorem B1085963 : Blo 722323 1085963 := bstep (se 1 (by rfl) ⟨814472, by rfl⟩ : syracuseStep 1085963 = 1628945) B1628945
theorem B725515 : Blo 722323 725515 := bstep (se 1 (by rfl) ⟨544136, by rfl⟩ : syracuseStep 725515 = 1088273) B1088273
theorem B1085975 : Blo 722323 1085975 := bstep (se 1 (by rfl) ⟨814481, by rfl⟩ : syracuseStep 1085975 = 1628963) B1628963
theorem B725527 : Blo 722323 725527 := bstep (se 1 (by rfl) ⟨544145, by rfl⟩ : syracuseStep 725527 = 1088291) B1088291
theorem B725547 : Blo 722323 725547 := bstep (se 1 (by rfl) ⟨544160, by rfl⟩ : syracuseStep 725547 = 1088321) B1088321
theorem B725559 : Blo 722323 725559 := bstep (se 1 (by rfl) ⟨544169, by rfl⟩ : syracuseStep 725559 = 1088339) B1088339
theorem B2757185 : Blo 722323 2757185 := bstep (se 2 (by rfl) ⟨1033944, by rfl⟩ : syracuseStep 2757185 = 2067889) B2067889
theorem B725579 : Blo 722323 725579 := bstep (se 1 (by rfl) ⟨544184, by rfl⟩ : syracuseStep 725579 = 1088369) B1088369
theorem B725591 : Blo 722323 725591 := bstep (se 1 (by rfl) ⟨544193, by rfl⟩ : syracuseStep 725591 = 1088387) B1088387
theorem B1086041 : Blo 722323 1086041 := bstep (se 2 (by rfl) ⟨407265, by rfl⟩ : syracuseStep 1086041 = 814531) B814531
theorem B725611 : Blo 722323 725611 := bstep (se 1 (by rfl) ⟨544208, by rfl⟩ : syracuseStep 725611 = 1088417) B1088417
theorem B725623 : Blo 722323 725623 := bstep (se 1 (by rfl) ⟨544217, by rfl⟩ : syracuseStep 725623 = 1088435) B1088435
theorem B725643 : Blo 722323 725643 := bstep (se 1 (by rfl) ⟨544232, by rfl⟩ : syracuseStep 725643 = 1088465) B1088465
theorem B725655 : Blo 722323 725655 := bstep (se 1 (by rfl) ⟨544241, by rfl⟩ : syracuseStep 725655 = 1088483) B1088483
theorem B725675 : Blo 722323 725675 := bstep (se 1 (by rfl) ⟨544256, by rfl⟩ : syracuseStep 725675 = 1088513) B1088513
theorem B725687 : Blo 722323 725687 := bstep (se 1 (by rfl) ⟨544265, by rfl⟩ : syracuseStep 725687 = 1088531) B1088531
theorem B1086155 : Blo 722323 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B725707 : Blo 722323 725707 := bstep (se 1 (by rfl) ⟨544280, by rfl⟩ : syracuseStep 725707 = 1088561) B1088561
theorem B1086167 : Blo 722323 1086167 := bstep (se 1 (by rfl) ⟨814625, by rfl⟩ : syracuseStep 1086167 = 1629251) B1629251
theorem B725719 : Blo 722323 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B725739 : Blo 722323 725739 := bstep (se 1 (by rfl) ⟨544304, by rfl⟩ : syracuseStep 725739 = 1088609) B1088609
theorem B725751 : Blo 722323 725751 := bstep (se 1 (by rfl) ⟨544313, by rfl⟩ : syracuseStep 725751 = 1088627) B1088627
theorem B725771 : Blo 722323 725771 := bstep (se 1 (by rfl) ⟨544328, by rfl⟩ : syracuseStep 725771 = 1088657) B1088657
theorem B725783 : Blo 722323 725783 := bstep (se 1 (by rfl) ⟨544337, by rfl⟩ : syracuseStep 725783 = 1088675) B1088675
theorem B1086233 : Blo 722323 1086233 := bstep (se 2 (by rfl) ⟨407337, by rfl⟩ : syracuseStep 1086233 = 814675) B814675
theorem B725803 : Blo 722323 725803 := bstep (se 1 (by rfl) ⟨544352, by rfl⟩ : syracuseStep 725803 = 1088705) B1088705
theorem B725815 : Blo 722323 725815 := bstep (se 1 (by rfl) ⟨544361, by rfl⟩ : syracuseStep 725815 = 1088723) B1088723
theorem B725835 : Blo 722323 725835 := bstep (se 1 (by rfl) ⟨544376, by rfl⟩ : syracuseStep 725835 = 1088753) B1088753
theorem B725847 : Blo 722323 725847 := bstep (se 1 (by rfl) ⟨544385, by rfl⟩ : syracuseStep 725847 = 1088771) B1088771
theorem B725867 : Blo 722323 725867 := bstep (se 1 (by rfl) ⟨544400, by rfl⟩ : syracuseStep 725867 = 1088801) B1088801
theorem B725879 : Blo 722323 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B1086347 : Blo 722323 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B725899 : Blo 722323 725899 := bstep (se 1 (by rfl) ⟨544424, by rfl⟩ : syracuseStep 725899 = 1088849) B1088849
theorem B1086359 : Blo 722323 1086359 := bstep (se 1 (by rfl) ⟨814769, by rfl⟩ : syracuseStep 1086359 = 1629539) B1629539
theorem B725911 : Blo 722323 725911 := bstep (se 1 (by rfl) ⟨544433, by rfl⟩ : syracuseStep 725911 = 1088867) B1088867
theorem B725931 : Blo 722323 725931 := bstep (se 1 (by rfl) ⟨544448, by rfl⟩ : syracuseStep 725931 = 1088897) B1088897
theorem B725943 : Blo 722323 725943 := bstep (se 1 (by rfl) ⟨544457, by rfl⟩ : syracuseStep 725943 = 1088915) B1088915
theorem B725963 : Blo 722323 725963 := bstep (se 1 (by rfl) ⟨544472, by rfl⟩ : syracuseStep 725963 = 1088945) B1088945
theorem B725975 : Blo 722323 725975 := bstep (se 1 (by rfl) ⟨544481, by rfl⟩ : syracuseStep 725975 = 1088963) B1088963
theorem B1086425 : Blo 722323 1086425 := bstep (se 2 (by rfl) ⟨407409, by rfl⟩ : syracuseStep 1086425 = 814819) B814819
theorem B725995 : Blo 722323 725995 := bstep (se 1 (by rfl) ⟨544496, by rfl⟩ : syracuseStep 725995 = 1088993) B1088993
theorem B726007 : Blo 722323 726007 := bstep (se 1 (by rfl) ⟨544505, by rfl⟩ : syracuseStep 726007 = 1089011) B1089011
theorem B726027 : Blo 722323 726027 := bstep (se 1 (by rfl) ⟨544520, by rfl⟩ : syracuseStep 726027 = 1089041) B1089041
theorem B726039 : Blo 722323 726039 := bstep (se 1 (by rfl) ⟨544529, by rfl⟩ : syracuseStep 726039 = 1089059) B1089059
theorem B726059 : Blo 722323 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B726071 : Blo 722323 726071 := bstep (se 1 (by rfl) ⟨544553, by rfl⟩ : syracuseStep 726071 = 1089107) B1089107
theorem B1086539 : Blo 722323 1086539 := bstep (se 1 (by rfl) ⟨814904, by rfl⟩ : syracuseStep 1086539 = 1629809) B1629809
theorem B726091 : Blo 722323 726091 := bstep (se 1 (by rfl) ⟨544568, by rfl⟩ : syracuseStep 726091 = 1089137) B1089137
theorem B1086551 : Blo 722323 1086551 := bstep (se 1 (by rfl) ⟨814913, by rfl⟩ : syracuseStep 1086551 = 1629827) B1629827
theorem B726103 : Blo 722323 726103 := bstep (se 1 (by rfl) ⟨544577, by rfl⟩ : syracuseStep 726103 = 1089155) B1089155
theorem B726123 : Blo 722323 726123 := bstep (se 1 (by rfl) ⟨544592, by rfl⟩ : syracuseStep 726123 = 1089185) B1089185
theorem B726135 : Blo 722323 726135 := bstep (se 1 (by rfl) ⟨544601, by rfl⟩ : syracuseStep 726135 = 1089203) B1089203
theorem B1545355 : Blo 722323 1545355 := bstep (se 1 (by rfl) ⟨1159016, by rfl⟩ : syracuseStep 1545355 = 2318033) B2318033
theorem B726155 : Blo 722323 726155 := bstep (se 1 (by rfl) ⟨544616, by rfl⟩ : syracuseStep 726155 = 1089233) B1089233
theorem B726167 : Blo 722323 726167 := bstep (se 1 (by rfl) ⟨544625, by rfl⟩ : syracuseStep 726167 = 1089251) B1089251
theorem B1086617 : Blo 722323 1086617 := bstep (se 2 (by rfl) ⟨407481, by rfl⟩ : syracuseStep 1086617 = 814963) B814963
theorem B726187 : Blo 722323 726187 := bstep (se 1 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 726187 = 1089281) B1089281
theorem B726199 : Blo 722323 726199 := bstep (se 1 (by rfl) ⟨544649, by rfl⟩ : syracuseStep 726199 = 1089299) B1089299
theorem B726219 : Blo 722323 726219 := bstep (se 1 (by rfl) ⟨544664, by rfl⟩ : syracuseStep 726219 = 1089329) B1089329
theorem B726231 : Blo 722323 726231 := bstep (se 1 (by rfl) ⟨544673, by rfl⟩ : syracuseStep 726231 = 1089347) B1089347
theorem B726251 : Blo 722323 726251 := bstep (se 1 (by rfl) ⟨544688, by rfl⟩ : syracuseStep 726251 = 1089377) B1089377
theorem B726263 : Blo 722323 726263 := bstep (se 1 (by rfl) ⟨544697, by rfl⟩ : syracuseStep 726263 = 1089395) B1089395
theorem B1086731 : Blo 722323 1086731 := bstep (se 1 (by rfl) ⟨815048, by rfl⟩ : syracuseStep 1086731 = 1630097) B1630097
theorem B726283 : Blo 722323 726283 := bstep (se 1 (by rfl) ⟨544712, by rfl⟩ : syracuseStep 726283 = 1089425) B1089425
theorem B1086743 : Blo 722323 1086743 := bstep (se 1 (by rfl) ⟨815057, by rfl⟩ : syracuseStep 1086743 = 1630115) B1630115
theorem B726295 : Blo 722323 726295 := bstep (se 1 (by rfl) ⟨544721, by rfl⟩ : syracuseStep 726295 = 1089443) B1089443
theorem B726315 : Blo 722323 726315 := bstep (se 1 (by rfl) ⟨544736, by rfl⟩ : syracuseStep 726315 = 1089473) B1089473
theorem B1086809 : Blo 722323 1086809 := bstep (se 2 (by rfl) ⟨407553, by rfl⟩ : syracuseStep 1086809 = 815107) B815107
theorem B1086923 : Blo 722323 1086923 := bstep (se 1 (by rfl) ⟨815192, by rfl⟩ : syracuseStep 1086923 = 1630385) B1630385
theorem B1086935 : Blo 722323 1086935 := bstep (se 1 (by rfl) ⟨815201, by rfl⟩ : syracuseStep 1086935 = 1630403) B1630403
theorem B3085789 : Blo 722323 3085789 := bstep (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) B1157171
theorem B1087001 : Blo 722323 1087001 := bstep (se 2 (by rfl) ⟨407625, by rfl⟩ : syracuseStep 1087001 = 815251) B815251
theorem B1545817 : Blo 722323 1545817 := bstep (se 2 (by rfl) ⟨579681, by rfl⟩ : syracuseStep 1545817 = 1159363) B1159363
theorem B3675779 : Blo 722323 3675779 := bstep (se 1 (by rfl) ⟨2756834, by rfl⟩ : syracuseStep 3675779 = 5513669) B5513669
theorem B1087115 : Blo 722323 1087115 := bstep (se 1 (by rfl) ⟨815336, by rfl⟩ : syracuseStep 1087115 = 1630673) B1630673
theorem B1087127 : Blo 722323 1087127 := bstep (se 1 (by rfl) ⟨815345, by rfl⟩ : syracuseStep 1087127 = 1630691) B1630691
theorem B1087193 : Blo 722323 1087193 := bstep (se 2 (by rfl) ⟨407697, by rfl⟩ : syracuseStep 1087193 = 815395) B815395
theorem B16684865 : Blo 722323 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B1087307 : Blo 722323 1087307 := bstep (se 1 (by rfl) ⟨815480, by rfl⟩ : syracuseStep 1087307 = 1630961) B1630961
theorem B1087319 : Blo 722323 1087319 := bstep (se 1 (by rfl) ⟨815489, by rfl⟩ : syracuseStep 1087319 = 1630979) B1630979
theorem B2234263 : Blo 722323 2234263 := bstep (se 1 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 2234263 = 3351395) B3351395
theorem B1087385 : Blo 722323 1087385 := bstep (se 2 (by rfl) ⟨407769, by rfl⟩ : syracuseStep 1087385 = 815539) B815539
theorem B1087499 : Blo 722323 1087499 := bstep (se 1 (by rfl) ⟨815624, by rfl⟩ : syracuseStep 1087499 = 1631249) B1631249
theorem B1087511 : Blo 722323 1087511 := bstep (se 1 (by rfl) ⟨815633, by rfl⟩ : syracuseStep 1087511 = 1631267) B1631267
theorem B1087577 : Blo 722323 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B1087691 : Blo 722323 1087691 := bstep (se 1 (by rfl) ⟨815768, by rfl⟩ : syracuseStep 1087691 = 1631537) B1631537
theorem B1087703 : Blo 722323 1087703 := bstep (se 1 (by rfl) ⟨815777, by rfl⟩ : syracuseStep 1087703 = 1631555) B1631555
theorem B2201879 : Blo 722323 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1087769 : Blo 722323 1087769 := bstep (se 2 (by rfl) ⟨407913, by rfl⟩ : syracuseStep 1087769 = 815827) B815827
theorem B11180389 : Blo 722323 11180389 := bstep (se 4 (by rfl) ⟨1048161, by rfl⟩ : syracuseStep 11180389 = 2096323) B2096323
theorem B1218955 : Blo 722323 1218955 := bstep (se 1 (by rfl) ⟨914216, by rfl⟩ : syracuseStep 1218955 = 1828433) B1828433
theorem B1087883 : Blo 722323 1087883 := bstep (se 1 (by rfl) ⟨815912, by rfl⟩ : syracuseStep 1087883 = 1631825) B1631825
theorem B1087895 : Blo 722323 1087895 := bstep (se 1 (by rfl) ⟨815921, by rfl⟩ : syracuseStep 1087895 = 1631843) B1631843
theorem B825815 : Blo 722323 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B1087961 : Blo 722323 1087961 := bstep (se 2 (by rfl) ⟨407985, by rfl⟩ : syracuseStep 1087961 = 815971) B815971
theorem B1219097 : Blo 722323 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B5511725 : Blo 722323 5511725 := bstep (se 3 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 5511725 = 2066897) B2066897
theorem B1088075 : Blo 722323 1088075 := bstep (se 1 (by rfl) ⟨816056, by rfl⟩ : syracuseStep 1088075 = 1632113) B1632113
theorem B1088087 : Blo 722323 1088087 := bstep (se 1 (by rfl) ⟨816065, by rfl⟩ : syracuseStep 1088087 = 1632131) B1632131
theorem B1219225 : Blo 722323 1219225 := bstep (se 2 (by rfl) ⟨457209, by rfl⟩ : syracuseStep 1219225 = 914419) B914419
theorem B1088153 : Blo 722323 1088153 := bstep (se 2 (by rfl) ⟨408057, by rfl⟩ : syracuseStep 1088153 = 816115) B816115
theorem B1678067 : Blo 722323 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B1088267 : Blo 722323 1088267 := bstep (se 1 (by rfl) ⟨816200, by rfl⟩ : syracuseStep 1088267 = 1632401) B1632401
theorem B3480337 : Blo 722323 3480337 := bstep (se 2 (by rfl) ⟨1305126, by rfl⟩ : syracuseStep 3480337 = 2610253) B2610253
theorem B1088279 : Blo 722323 1088279 := bstep (se 1 (by rfl) ⟨816209, by rfl⟩ : syracuseStep 1088279 = 1632419) B1632419
theorem B1088345 : Blo 722323 1088345 := bstep (se 2 (by rfl) ⟨408129, by rfl⟩ : syracuseStep 1088345 = 816259) B816259
theorem B1547201 : Blo 722323 1547201 := bstep (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) B1160401
theorem B1088459 : Blo 722323 1088459 := bstep (se 1 (by rfl) ⟨816344, by rfl⟩ : syracuseStep 1088459 = 1632689) B1632689
theorem B1088471 : Blo 722323 1088471 := bstep (se 1 (by rfl) ⟨816353, by rfl⟩ : syracuseStep 1088471 = 1632707) B1632707
theorem B1088537 : Blo 722323 1088537 := bstep (se 2 (by rfl) ⟨408201, by rfl⟩ : syracuseStep 1088537 = 816403) B816403
theorem B4135981 : Blo 722323 4135981 := bstep (se 3 (by rfl) ⟨775496, by rfl⟩ : syracuseStep 4135981 = 1550993) B1550993
theorem B1088651 : Blo 722323 1088651 := bstep (se 1 (by rfl) ⟨816488, by rfl⟩ : syracuseStep 1088651 = 1632977) B1632977
theorem B1088663 : Blo 722323 1088663 := bstep (se 1 (by rfl) ⟨816497, by rfl⟩ : syracuseStep 1088663 = 1632995) B1632995
theorem B1219799 : Blo 722323 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B1088729 : Blo 722323 1088729 := bstep (se 2 (by rfl) ⟨408273, by rfl⟩ : syracuseStep 1088729 = 816547) B816547
theorem B1088843 : Blo 722323 1088843 := bstep (se 1 (by rfl) ⟨816632, by rfl⟩ : syracuseStep 1088843 = 1633265) B1633265
theorem B1219927 : Blo 722323 1219927 := bstep (se 1 (by rfl) ⟨914945, by rfl⟩ : syracuseStep 1219927 = 1829891) B1829891
theorem B1088855 : Blo 722323 1088855 := bstep (se 1 (by rfl) ⟨816641, by rfl⟩ : syracuseStep 1088855 = 1633283) B1633283
theorem B1088921 : Blo 722323 1088921 := bstep (se 2 (by rfl) ⟨408345, by rfl⟩ : syracuseStep 1088921 = 816691) B816691
theorem B1089035 : Blo 722323 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B1089047 : Blo 722323 1089047 := bstep (se 1 (by rfl) ⟨816785, by rfl⟩ : syracuseStep 1089047 = 1633571) B1633571
theorem B1089113 : Blo 722323 1089113 := bstep (se 2 (by rfl) ⟨408417, by rfl⟩ : syracuseStep 1089113 = 816835) B816835
theorem B990859 : Blo 722323 990859 := bstep (se 1 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 990859 = 1486289) B1486289
theorem B1089227 : Blo 722323 1089227 := bstep (se 1 (by rfl) ⟨816920, by rfl⟩ : syracuseStep 1089227 = 1633841) B1633841
theorem B1089239 : Blo 722323 1089239 := bstep (se 1 (by rfl) ⟨816929, by rfl⟩ : syracuseStep 1089239 = 1633859) B1633859
theorem B1089305 : Blo 722323 1089305 := bstep (se 2 (by rfl) ⟨408489, by rfl⟩ : syracuseStep 1089305 = 816979) B816979
theorem B1089419 : Blo 722323 1089419 := bstep (se 1 (by rfl) ⟨817064, by rfl⟩ : syracuseStep 1089419 = 1634129) B1634129
theorem B1089431 : Blo 722323 1089431 := bstep (se 1 (by rfl) ⟨817073, by rfl⟩ : syracuseStep 1089431 = 1634147) B1634147
theorem B1220555 : Blo 722323 1220555 := bstep (se 1 (by rfl) ⟨915416, by rfl⟩ : syracuseStep 1220555 = 1830833) B1830833
theorem B1220683 : Blo 722323 1220683 := bstep (se 1 (by rfl) ⟨915512, by rfl⟩ : syracuseStep 1220683 = 1831025) B1831025
theorem B1220825 : Blo 722323 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B1220953 : Blo 722323 1220953 := bstep (se 2 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 1220953 = 915715) B915715
theorem B5218661 : Blo 722323 5218661 := bstep (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) B978499
theorem B1548875 : Blo 722323 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B7840577 : Blo 722323 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B1221527 : Blo 722323 1221527 := bstep (se 1 (by rfl) ⟨916145, by rfl⟩ : syracuseStep 1221527 = 1832291) B1832291
theorem B3482585 : Blo 722323 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B3089411 : Blo 722323 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B1221655 : Blo 722323 1221655 := bstep (se 1 (by rfl) ⟨916241, by rfl⟩ : syracuseStep 1221655 = 1832483) B1832483
theorem B11937125 : Blo 722323 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B3712387 : Blo 722323 3712387 := bstep (se 1 (by rfl) ⟨2784290, by rfl⟩ : syracuseStep 3712387 = 5568581) B5568581
theorem B9282995 : Blo 722323 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B6596113 : Blo 722323 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B1549849 : Blo 722323 1549849 := bstep (se 2 (by rfl) ⟨581193, by rfl⟩ : syracuseStep 1549849 = 1162387) B1162387
theorem B1222283 : Blo 722323 1222283 := bstep (se 1 (by rfl) ⟨916712, by rfl⟩ : syracuseStep 1222283 = 1833425) B1833425
theorem B2238173 : Blo 722323 2238173 := bstep (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) B839315
theorem B1222411 : Blo 722323 1222411 := bstep (se 1 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 1222411 = 1833617) B1833617
theorem B1550105 : Blo 722323 1550105 := bstep (se 2 (by rfl) ⟨581289, by rfl⟩ : syracuseStep 1550105 = 1162579) B1162579
theorem B1222553 : Blo 722323 1222553 := bstep (se 2 (by rfl) ⟨458457, by rfl⟩ : syracuseStep 1222553 = 916915) B916915
theorem B5220301 : Blo 722323 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B1222681 : Blo 722323 1222681 := bstep (se 2 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 1222681 = 917011) B917011
theorem B1550515 : Blo 722323 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B2205917 : Blo 722323 2205917 := bstep (se 3 (by rfl) ⟨413609, by rfl⟩ : syracuseStep 2205917 = 827219) B827219
theorem B5876185 : Blo 722323 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B1223255 : Blo 722323 1223255 := bstep (se 1 (by rfl) ⟨917441, by rfl⟩ : syracuseStep 1223255 = 1834883) B1834883
theorem B1223383 : Blo 722323 1223383 := bstep (se 1 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 1223383 = 1835075) B1835075
theorem B3091223 : Blo 722323 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B1551233 : Blo 722323 1551233 := bstep (se 2 (by rfl) ⟨581712, by rfl⟩ : syracuseStep 1551233 = 1163425) B1163425
theorem B1649879 : Blo 722323 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B1224011 : Blo 722323 1224011 := bstep (se 1 (by rfl) ⟨918008, by rfl⟩ : syracuseStep 1224011 = 1836017) B1836017
theorem B1224139 : Blo 722323 1224139 := bstep (se 1 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 1224139 = 1836209) B1836209
theorem B4959809 : Blo 722323 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1224281 : Blo 722323 1224281 := bstep (se 2 (by rfl) ⟨459105, by rfl⟩ : syracuseStep 1224281 = 918211) B918211
theorem B929431 : Blo 722323 929431 := bstep (se 1 (by rfl) ⟨697073, by rfl⟩ : syracuseStep 929431 = 1394147) B1394147
theorem B1224409 : Blo 722323 1224409 := bstep (se 2 (by rfl) ⟨459153, by rfl⟩ : syracuseStep 1224409 = 918307) B918307
theorem B25472945 : Blo 722323 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B14135219 : Blo 722323 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B5451781 : Blo 722323 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B3092555 : Blo 722323 3092555 := bstep (se 1 (by rfl) ⟨2319416, by rfl⟩ : syracuseStep 3092555 = 4638833) B4638833
theorem B733303 : Blo 722323 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B1224983 : Blo 722323 1224983 := bstep (se 1 (by rfl) ⟨918737, by rfl⟩ : syracuseStep 1224983 = 1837475) B1837475
theorem B1225111 : Blo 722323 1225111 := bstep (se 1 (by rfl) ⟨918833, by rfl⟩ : syracuseStep 1225111 = 1837667) B1837667
theorem B8237699 : Blo 722323 8237699 := bstep (se 1 (by rfl) ⟨6178274, by rfl⟩ : syracuseStep 8237699 = 12356549) B12356549
theorem B3093137 : Blo 722323 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B3715915 : Blo 722323 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B1029143 : Blo 722323 1029143 := bstep (se 1 (by rfl) ⟨771857, by rfl⟩ : syracuseStep 1029143 = 1543715) B1543715
theorem B1586251 : Blo 722323 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B5944421 : Blo 722323 5944421 := bstep (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) B1114579
theorem B10466435 : Blo 722323 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B2438423 : Blo 722323 2438423 := bstep (se 1 (by rfl) ⟨1828817, by rfl⟩ : syracuseStep 2438423 = 3657635) B3657635
theorem B1029451 : Blo 722323 1029451 := bstep (se 1 (by rfl) ⟨772088, by rfl⟩ : syracuseStep 1029451 = 1544177) B1544177
theorem B4404611 : Blo 722323 4404611 := bstep (se 1 (by rfl) ⟨3303458, by rfl⟩ : syracuseStep 4404611 = 6606917) B6606917
theorem B4961893 : Blo 722323 4961893 := bstep (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) B930355
theorem B3094195 : Blo 722323 3094195 := bstep (se 1 (by rfl) ⟨2320646, by rfl⟩ : syracuseStep 3094195 = 4641293) B4641293
theorem B2438963 : Blo 722323 2438963 := bstep (se 1 (by rfl) ⟨1829222, by rfl⟩ : syracuseStep 2438963 = 3658445) B3658445
theorem B1390451 : Blo 722323 1390451 := bstep (se 1 (by rfl) ⟨1042838, by rfl⟩ : syracuseStep 1390451 = 2085677) B2085677
theorem B12564497 : Blo 722323 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B2439233 : Blo 722323 2439233 := bstep (se 2 (by rfl) ⟨914712, by rfl⟩ : syracuseStep 2439233 = 1829425) B1829425
theorem B1030487 : Blo 722323 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B735691 : Blo 722323 735691 := bstep (se 1 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 735691 = 1103537) B1103537
theorem B1030681 : Blo 722323 1030681 := bstep (se 2 (by rfl) ⟨386505, by rfl⟩ : syracuseStep 1030681 = 773011) B773011
theorem B5880365 : Blo 722323 5880365 := bstep (se 3 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 5880365 = 2205137) B2205137
theorem B11778635 : Blo 722323 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B2603609 : Blo 722323 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B2439773 : Blo 722323 2439773 := bstep (se 3 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 2439773 = 914915) B914915
theorem B13187765 : Blo 722323 13187765 := bstep (se 5 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 13187765 = 1236353) B1236353
theorem B5487425 : Blo 722323 5487425 := bstep (se 2 (by rfl) ⟨2057784, by rfl⟩ : syracuseStep 5487425 = 4115569) B4115569
theorem B1653655 : Blo 722323 1653655 := bstep (se 1 (by rfl) ⟨1240241, by rfl⟩ : syracuseStep 1653655 = 2480483) B2480483
theorem B3095597 : Blo 722323 3095597 := bstep (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) B1160849
theorem B5946659 : Blo 722323 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B38125187 : Blo 722323 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B2440907 : Blo 722323 2440907 := bstep (se 1 (by rfl) ⟨1830680, by rfl⟩ : syracuseStep 2440907 = 3661361) B3661361
theorem B3489581 : Blo 722323 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B1032139 : Blo 722323 1032139 := bstep (se 1 (by rfl) ⟨774104, by rfl⟩ : syracuseStep 1032139 = 1548209) B1548209
theorem B2441177 : Blo 722323 2441177 := bstep (se 2 (by rfl) ⟨915441, by rfl⟩ : syracuseStep 2441177 = 1830883) B1830883
theorem B8044505 : Blo 722323 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B13582637 : Blo 722323 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B2441879 : Blo 722323 2441879 := bstep (se 1 (by rfl) ⟨1831409, by rfl⟩ : syracuseStep 2441879 = 3662819) B3662819
theorem B5489369 : Blo 722323 5489369 := bstep (se 2 (by rfl) ⟨2058513, by rfl⟩ : syracuseStep 5489369 = 4117027) B4117027
theorem B40682225 : Blo 722323 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B2442419 : Blo 722323 2442419 := bstep (se 1 (by rfl) ⟨1831814, by rfl⟩ : syracuseStep 2442419 = 3663629) B3663629
theorem B2114881 : Blo 722323 2114881 := bstep (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) B1586161
theorem B2442689 : Blo 722323 2442689 := bstep (se 2 (by rfl) ⟨916008, by rfl⟩ : syracuseStep 2442689 = 1832017) B1832017
theorem B1099211 : Blo 722323 1099211 := bstep (se 1 (by rfl) ⟨824408, by rfl⟩ : syracuseStep 1099211 = 1648817) B1648817
theorem B771563 : Blo 722323 771563 := bstep (se 1 (by rfl) ⟨578672, by rfl⟩ : syracuseStep 771563 = 1157345) B1157345
theorem B2443229 : Blo 722323 2443229 := bstep (se 3 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 2443229 = 916211) B916211
theorem B7817309 : Blo 722323 7817309 := bstep (se 3 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 7817309 = 2931491) B2931491
theorem B7850135 : Blo 722323 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B6179165 : Blo 722323 6179165 := bstep (se 3 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 6179165 = 2317187) B2317187
theorem B1100375 : Blo 722323 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B2607947 : Blo 722323 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B772951 : Blo 722323 772951 := bstep (se 1 (by rfl) ⟨579713, by rfl⟩ : syracuseStep 772951 = 1159427) B1159427
theorem B2608075 : Blo 722323 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B6179915 : Blo 722323 6179915 := bstep (se 1 (by rfl) ⟨4634936, by rfl⟩ : syracuseStep 6179915 = 9269873) B9269873
theorem B2444363 : Blo 722323 2444363 := bstep (se 1 (by rfl) ⟨1833272, by rfl⟩ : syracuseStep 2444363 = 3666545) B3666545
theorem B871511 : Blo 722323 871511 := bstep (se 1 (by rfl) ⟨653633, by rfl⟩ : syracuseStep 871511 = 1307267) B1307267
theorem B2935901 : Blo 722323 2935901 := bstep (se 3 (by rfl) ⟨550481, by rfl⟩ : syracuseStep 2935901 = 1100963) B1100963
theorem B3099799 : Blo 722323 3099799 := bstep (se 1 (by rfl) ⟨2324849, by rfl⟩ : syracuseStep 3099799 = 4649699) B4649699
theorem B1625291 : Blo 722323 1625291 := bstep (se 1 (by rfl) ⟨1218968, by rfl⟩ : syracuseStep 1625291 = 2437937) B2437937
theorem B871627 : Blo 722323 871627 := bstep (se 1 (by rfl) ⟨653720, by rfl⟩ : syracuseStep 871627 = 1307441) B1307441
theorem B3099869 : Blo 722323 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B11128049 : Blo 722323 11128049 := bstep (se 2 (by rfl) ⟨4173018, by rfl⟩ : syracuseStep 11128049 = 8346037) B8346037
theorem B1625345 : Blo 722323 1625345 := bstep (se 2 (by rfl) ⟨609504, by rfl⟩ : syracuseStep 1625345 = 1219009) B1219009
theorem B2444633 : Blo 722323 2444633 := bstep (se 2 (by rfl) ⟨916737, by rfl⟩ : syracuseStep 2444633 = 1833475) B1833475
theorem B4115843 : Blo 722323 4115843 := bstep (se 1 (by rfl) ⟨3086882, by rfl⟩ : syracuseStep 4115843 = 6173765) B6173765
theorem B1854913 : Blo 722323 1854913 := bstep (se 2 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 1854913 = 1391185) B1391185
theorem B1625561 : Blo 722323 1625561 := bstep (se 2 (by rfl) ⟨609585, by rfl⟩ : syracuseStep 1625561 = 1219171) B1219171
theorem B1625651 : Blo 722323 1625651 := bstep (se 1 (by rfl) ⟨1219238, by rfl⟩ : syracuseStep 1625651 = 2438477) B2438477
theorem B1625687 : Blo 722323 1625687 := bstep (se 1 (by rfl) ⟨1219265, by rfl⟩ : syracuseStep 1625687 = 2438531) B2438531
theorem B773771 : Blo 722323 773771 := bstep (se 1 (by rfl) ⟨580328, by rfl⟩ : syracuseStep 773771 = 1160657) B1160657
theorem B10440373 : Blo 722323 10440373 := bstep (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) B978785
theorem B1625867 : Blo 722323 1625867 := bstep (se 1 (by rfl) ⟨1219400, by rfl⟩ : syracuseStep 1625867 = 2438801) B2438801
theorem B1625921 : Blo 722323 1625921 := bstep (se 2 (by rfl) ⟨609720, by rfl⟩ : syracuseStep 1625921 = 1219441) B1219441
theorem B3100619 : Blo 722323 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B2445335 : Blo 722323 2445335 := bstep (se 1 (by rfl) ⟨1834001, by rfl⟩ : syracuseStep 2445335 = 3668003) B3668003
theorem B1626137 : Blo 722323 1626137 := bstep (se 2 (by rfl) ⟨609801, by rfl⟩ : syracuseStep 1626137 = 1219603) B1219603
theorem B5492771 : Blo 722323 5492771 := bstep (se 1 (by rfl) ⟨4119578, by rfl⟩ : syracuseStep 5492771 = 8239157) B8239157
theorem B2314291 : Blo 722323 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B1626227 : Blo 722323 1626227 := bstep (se 1 (by rfl) ⟨1219670, by rfl⟩ : syracuseStep 1626227 = 2439341) B2439341
theorem B1626263 : Blo 722323 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B1626443 : Blo 722323 1626443 := bstep (se 1 (by rfl) ⟨1219832, by rfl⟩ : syracuseStep 1626443 = 2439665) B2439665
theorem B1626497 : Blo 722323 1626497 := bstep (se 2 (by rfl) ⟨609936, by rfl⟩ : syracuseStep 1626497 = 1219873) B1219873
theorem B2445875 : Blo 722323 2445875 := bstep (se 1 (by rfl) ⟨1834406, by rfl⟩ : syracuseStep 2445875 = 3668813) B3668813
theorem B1626713 : Blo 722323 1626713 := bstep (se 2 (by rfl) ⟨610017, by rfl⟩ : syracuseStep 1626713 = 1220035) B1220035
theorem B774775 : Blo 722323 774775 := bstep (se 1 (by rfl) ⟨581081, by rfl⟩ : syracuseStep 774775 = 1162163) B1162163
theorem B1626803 : Blo 722323 1626803 := bstep (se 1 (by rfl) ⟨1220102, by rfl⟩ : syracuseStep 1626803 = 2440205) B2440205
theorem B6181555 : Blo 722323 6181555 := bstep (se 1 (by rfl) ⟨4636166, by rfl⟩ : syracuseStep 6181555 = 9272333) B9272333
theorem B1626839 : Blo 722323 1626839 := bstep (se 1 (by rfl) ⟨1220129, by rfl⟩ : syracuseStep 1626839 = 2440259) B2440259
theorem B2446145 : Blo 722323 2446145 := bstep (se 2 (by rfl) ⟨917304, by rfl⟩ : syracuseStep 2446145 = 1834609) B1834609
theorem B1627019 : Blo 722323 1627019 := bstep (se 1 (by rfl) ⟨1220264, by rfl⟩ : syracuseStep 1627019 = 2440529) B2440529
theorem B1627073 : Blo 722323 1627073 := bstep (se 2 (by rfl) ⟨610152, by rfl⟩ : syracuseStep 1627073 = 1220305) B1220305
theorem B3658769 : Blo 722323 3658769 := bstep (se 2 (by rfl) ⟨1372038, by rfl⟩ : syracuseStep 3658769 = 2744077) B2744077
theorem B1627289 : Blo 722323 1627289 := bstep (se 2 (by rfl) ⟨610233, by rfl⟩ : syracuseStep 1627289 = 1220467) B1220467
theorem B3658931 : Blo 722323 3658931 := bstep (se 1 (by rfl) ⟨2744198, by rfl⟩ : syracuseStep 3658931 = 5488397) B5488397
theorem B1987787 : Blo 722323 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B1627379 : Blo 722323 1627379 := bstep (se 1 (by rfl) ⟨1220534, by rfl⟩ : syracuseStep 1627379 = 2441069) B2441069
theorem B1627415 : Blo 722323 1627415 := bstep (se 1 (by rfl) ⟨1220561, by rfl⟩ : syracuseStep 1627415 = 2441123) B2441123
theorem B2446685 : Blo 722323 2446685 := bstep (se 3 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 2446685 = 917507) B917507
theorem B775531 : Blo 722323 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B1627595 : Blo 722323 1627595 := bstep (se 1 (by rfl) ⟨1220696, by rfl⟩ : syracuseStep 1627595 = 2441393) B2441393
theorem B1627649 : Blo 722323 1627649 := bstep (se 2 (by rfl) ⟨610368, by rfl⟩ : syracuseStep 1627649 = 1220737) B1220737
theorem B1627865 : Blo 722323 1627865 := bstep (se 2 (by rfl) ⟨610449, by rfl⟩ : syracuseStep 1627865 = 1220899) B1220899
theorem B1627955 : Blo 722323 1627955 := bstep (se 1 (by rfl) ⟨1220966, by rfl⟩ : syracuseStep 1627955 = 2441933) B2441933
theorem B1627991 : Blo 722323 1627991 := bstep (se 1 (by rfl) ⟨1220993, by rfl⟩ : syracuseStep 1627991 = 2441987) B2441987
theorem B5560325 : Blo 722323 5560325 := bstep (se 4 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 5560325 = 1042561) B1042561
theorem B1628171 : Blo 722323 1628171 := bstep (se 1 (by rfl) ⟨1221128, by rfl⟩ : syracuseStep 1628171 = 2442257) B2442257
theorem B1628225 : Blo 722323 1628225 := bstep (se 2 (by rfl) ⟨610584, by rfl⟩ : syracuseStep 1628225 = 1221169) B1221169
theorem B12343427 : Blo 722323 12343427 := bstep (se 1 (by rfl) ⟨9257570, by rfl⟩ : syracuseStep 12343427 = 18515141) B18515141
theorem B12409037 : Blo 722323 12409037 := bstep (se 3 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 12409037 = 4653389) B4653389
theorem B1104139 : Blo 722323 1104139 := bstep (se 1 (by rfl) ⟨828104, by rfl⟩ : syracuseStep 1104139 = 1656209) B1656209
theorem B1857815 : Blo 722323 1857815 := bstep (se 1 (by rfl) ⟨1393361, by rfl⟩ : syracuseStep 1857815 = 2786723) B2786723
theorem B1628441 : Blo 722323 1628441 := bstep (se 2 (by rfl) ⟨610665, by rfl⟩ : syracuseStep 1628441 = 1221331) B1221331
theorem B1628531 : Blo 722323 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B1628567 : Blo 722323 1628567 := bstep (se 1 (by rfl) ⟨1221425, by rfl⟩ : syracuseStep 1628567 = 2442851) B2442851
theorem B2447819 : Blo 722323 2447819 := bstep (se 1 (by rfl) ⟨1835864, by rfl⟩ : syracuseStep 2447819 = 3671729) B3671729
theorem B1956403 : Blo 722323 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1628747 : Blo 722323 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B1628801 : Blo 722323 1628801 := bstep (se 2 (by rfl) ⟨610800, by rfl⟩ : syracuseStep 1628801 = 1221601) B1221601
theorem B1465049 : Blo 722323 1465049 := bstep (se 2 (by rfl) ⟨549393, by rfl⟩ : syracuseStep 1465049 = 1098787) B1098787
theorem B2448089 : Blo 722323 2448089 := bstep (se 2 (by rfl) ⟨918033, by rfl⟩ : syracuseStep 2448089 = 1836067) B1836067
theorem B2939651 : Blo 722323 2939651 := bstep (se 1 (by rfl) ⟨2204738, by rfl⟩ : syracuseStep 2939651 = 4409477) B4409477
theorem B2939665 : Blo 722323 2939665 := bstep (se 2 (by rfl) ⟨1102374, by rfl⟩ : syracuseStep 2939665 = 2204749) B2204749
theorem B2743091 : Blo 722323 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B2743105 : Blo 722323 2743105 := bstep (se 2 (by rfl) ⟨1028664, by rfl⟩ : syracuseStep 2743105 = 2057329) B2057329
theorem B5299019 : Blo 722323 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B1629017 : Blo 722323 1629017 := bstep (se 2 (by rfl) ⟨610881, by rfl⟩ : syracuseStep 1629017 = 1221763) B1221763
theorem B5561189 : Blo 722323 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B1629107 : Blo 722323 1629107 := bstep (se 1 (by rfl) ⟨1221830, by rfl⟩ : syracuseStep 1629107 = 2443661) B2443661
theorem B1629143 : Blo 722323 1629143 := bstep (se 1 (by rfl) ⟨1221857, by rfl⟩ : syracuseStep 1629143 = 2443715) B2443715
theorem B3660875 : Blo 722323 3660875 := bstep (se 1 (by rfl) ⟨2745656, by rfl⟩ : syracuseStep 3660875 = 5491313) B5491313
theorem B1629323 : Blo 722323 1629323 := bstep (se 1 (by rfl) ⟨1221992, by rfl⟩ : syracuseStep 1629323 = 2443985) B2443985
theorem B1629377 : Blo 722323 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B1301761 : Blo 722323 1301761 := bstep (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) B976321
theorem B2448791 : Blo 722323 2448791 := bstep (se 1 (by rfl) ⟨1836593, by rfl⟩ : syracuseStep 2448791 = 3673187) B3673187
theorem B1629593 : Blo 722323 1629593 := bstep (se 2 (by rfl) ⟨611097, by rfl⟩ : syracuseStep 1629593 = 1222195) B1222195
theorem B1465843 : Blo 722323 1465843 := bstep (se 1 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 1465843 = 2198765) B2198765
theorem B1629683 : Blo 722323 1629683 := bstep (se 1 (by rfl) ⟨1222262, by rfl⟩ : syracuseStep 1629683 = 2444525) B2444525
theorem B1629719 : Blo 722323 1629719 := bstep (se 1 (by rfl) ⟨1222289, by rfl⟩ : syracuseStep 1629719 = 2444579) B2444579
theorem B1957441 : Blo 722323 1957441 := bstep (se 2 (by rfl) ⟨734040, by rfl⟩ : syracuseStep 1957441 = 1468081) B1468081
theorem B1629899 : Blo 722323 1629899 := bstep (se 1 (by rfl) ⟨1222424, by rfl⟩ : syracuseStep 1629899 = 2444849) B2444849
theorem B1629953 : Blo 722323 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B26828597 : Blo 722323 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B1236887 : Blo 722323 1236887 := bstep (se 1 (by rfl) ⟨927665, by rfl⟩ : syracuseStep 1236887 = 1855331) B1855331
theorem B2449331 : Blo 722323 2449331 := bstep (se 1 (by rfl) ⟨1836998, by rfl⟩ : syracuseStep 2449331 = 3673997) B3673997
theorem B1302475 : Blo 722323 1302475 := bstep (se 1 (by rfl) ⟨976856, by rfl⟩ : syracuseStep 1302475 = 1953713) B1953713
theorem B1630169 : Blo 722323 1630169 := bstep (se 2 (by rfl) ⟨611313, by rfl⟩ : syracuseStep 1630169 = 1222627) B1222627
theorem B1630259 : Blo 722323 1630259 := bstep (se 1 (by rfl) ⟨1222694, by rfl⟩ : syracuseStep 1630259 = 2445389) B2445389
theorem B2613323 : Blo 722323 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1630295 : Blo 722323 1630295 := bstep (se 1 (by rfl) ⟨1222721, by rfl⟩ : syracuseStep 1630295 = 2445443) B2445443
theorem B2449601 : Blo 722323 2449601 := bstep (se 2 (by rfl) ⟨918600, by rfl⟩ : syracuseStep 2449601 = 1837201) B1837201
theorem B1630475 : Blo 722323 1630475 := bstep (se 1 (by rfl) ⟨1222856, by rfl⟩ : syracuseStep 1630475 = 2445713) B2445713
theorem B62710037 : Blo 722323 62710037 := bstep (se 6 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 62710037 = 2939533) B2939533
theorem B1630529 : Blo 722323 1630529 := bstep (se 2 (by rfl) ⟨611448, by rfl⟩ : syracuseStep 1630529 = 1222897) B1222897
theorem B1630745 : Blo 722323 1630745 := bstep (se 2 (by rfl) ⟨611529, by rfl⟩ : syracuseStep 1630745 = 1223059) B1223059
theorem B1630835 : Blo 722323 1630835 := bstep (se 1 (by rfl) ⟨1223126, by rfl⟩ : syracuseStep 1630835 = 2446253) B2446253
theorem B4121219 : Blo 722323 4121219 := bstep (se 1 (by rfl) ⟨3090914, by rfl⟩ : syracuseStep 4121219 = 6181829) B6181829
theorem B1630871 : Blo 722323 1630871 := bstep (se 1 (by rfl) ⟨1223153, by rfl⟩ : syracuseStep 1630871 = 2446307) B2446307
theorem B2745035 : Blo 722323 2745035 := bstep (se 1 (by rfl) ⟨2058776, by rfl⟩ : syracuseStep 2745035 = 4117553) B4117553
theorem B2745049 : Blo 722323 2745049 := bstep (se 2 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 2745049 = 2058787) B2058787
theorem B2450141 : Blo 722323 2450141 := bstep (se 3 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 2450141 = 918803) B918803
theorem B3662657 : Blo 722323 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B1631051 : Blo 722323 1631051 := bstep (se 1 (by rfl) ⟨1223288, by rfl⟩ : syracuseStep 1631051 = 2446577) B2446577
theorem B1631105 : Blo 722323 1631105 := bstep (se 2 (by rfl) ⟨611664, by rfl⟩ : syracuseStep 1631105 = 1223329) B1223329
theorem B4121675 : Blo 722323 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B4023371 : Blo 722323 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B1631321 : Blo 722323 1631321 := bstep (se 2 (by rfl) ⟨611745, by rfl⟩ : syracuseStep 1631321 = 1223491) B1223491
theorem B1631411 : Blo 722323 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B5661875 : Blo 722323 5661875 := bstep (se 1 (by rfl) ⟨4246406, by rfl⟩ : syracuseStep 5661875 = 8492813) B8492813
theorem B1631447 : Blo 722323 1631447 := bstep (se 1 (by rfl) ⟨1223585, by rfl⟩ : syracuseStep 1631447 = 2447171) B2447171
theorem B5498117 : Blo 722323 5498117 := bstep (se 4 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 5498117 = 1030897) B1030897
theorem B1303859 : Blo 722323 1303859 := bstep (se 1 (by rfl) ⟨977894, by rfl⟩ : syracuseStep 1303859 = 1955789) B1955789
theorem B1631627 : Blo 722323 1631627 := bstep (se 1 (by rfl) ⟨1223720, by rfl⟩ : syracuseStep 1631627 = 2447441) B2447441
theorem B1631681 : Blo 722323 1631681 := bstep (se 2 (by rfl) ⟨611880, by rfl⟩ : syracuseStep 1631681 = 1223761) B1223761
theorem B1828403 : Blo 722323 1828403 := bstep (se 1 (by rfl) ⟨1371302, by rfl⟩ : syracuseStep 1828403 = 2742605) B2742605
theorem B1304153 : Blo 722323 1304153 := bstep (se 2 (by rfl) ⟨489057, by rfl⟩ : syracuseStep 1304153 = 978115) B978115
theorem B812695 : Blo 722323 812695 := bstep (se 1 (by rfl) ⟨609521, by rfl⟩ : syracuseStep 812695 = 1219043) B1219043
theorem B2746007 : Blo 722323 2746007 := bstep (se 1 (by rfl) ⟨2059505, by rfl⟩ : syracuseStep 2746007 = 4119011) B4119011
theorem B1631897 : Blo 722323 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B976601 : Blo 722323 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B1631987 : Blo 722323 1631987 := bstep (se 1 (by rfl) ⟨1223990, by rfl⟩ : syracuseStep 1631987 = 2447981) B2447981
theorem B1632023 : Blo 722323 1632023 := bstep (se 1 (by rfl) ⟨1224017, by rfl⟩ : syracuseStep 1632023 = 2448035) B2448035
theorem B812875 : Blo 722323 812875 := bstep (se 1 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 812875 = 1219313) B1219313
theorem B2451275 : Blo 722323 2451275 := bstep (se 1 (by rfl) ⟨1838456, by rfl⟩ : syracuseStep 2451275 = 3676913) B3676913
theorem B4646807 : Blo 722323 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B812983 : Blo 722323 812983 := bstep (se 1 (by rfl) ⟨609737, by rfl⟩ : syracuseStep 812983 = 1219475) B1219475
theorem B1632203 : Blo 722323 1632203 := bstep (se 1 (by rfl) ⟨1224152, by rfl⟩ : syracuseStep 1632203 = 2448305) B2448305
theorem B1632257 : Blo 722323 1632257 := bstep (se 2 (by rfl) ⟨612096, by rfl⟩ : syracuseStep 1632257 = 1224193) B1224193
theorem B2615341 : Blo 722323 2615341 := bstep (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) B980753
theorem B1828939 : Blo 722323 1828939 := bstep (se 1 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 1828939 = 2743409) B2743409
theorem B813163 : Blo 722323 813163 := bstep (se 1 (by rfl) ⟨609872, by rfl⟩ : syracuseStep 813163 = 1219745) B1219745
theorem B813271 : Blo 722323 813271 := bstep (se 1 (by rfl) ⟨609953, by rfl⟩ : syracuseStep 813271 = 1219907) B1219907
theorem B1829081 : Blo 722323 1829081 := bstep (se 2 (by rfl) ⟨685905, by rfl⟩ : syracuseStep 1829081 = 1371811) B1371811
theorem B1632473 : Blo 722323 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B1566977 : Blo 722323 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1468697 : Blo 722323 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B1632563 : Blo 722323 1632563 := bstep (se 1 (by rfl) ⟨1224422, by rfl⟩ : syracuseStep 1632563 = 2448845) B2448845
theorem B1632599 : Blo 722323 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B813451 : Blo 722323 813451 := bstep (se 1 (by rfl) ⟨610088, by rfl⟩ : syracuseStep 813451 = 1220177) B1220177
theorem B813559 : Blo 722323 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B846347 : Blo 722323 846347 := bstep (se 1 (by rfl) ⟨634760, by rfl⟩ : syracuseStep 846347 = 1269521) B1269521
theorem B1632779 : Blo 722323 1632779 := bstep (se 1 (by rfl) ⟨1224584, by rfl⟩ : syracuseStep 1632779 = 2449169) B2449169
theorem B1632833 : Blo 722323 1632833 := bstep (se 2 (by rfl) ⟨612312, by rfl⟩ : syracuseStep 1632833 = 1224625) B1224625
theorem B1305163 : Blo 722323 1305163 := bstep (se 1 (by rfl) ⟨978872, by rfl⟩ : syracuseStep 1305163 = 1957745) B1957745
theorem B813739 : Blo 722323 813739 := bstep (se 1 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 813739 = 1220609) B1220609
theorem B3664601 : Blo 722323 3664601 := bstep (se 2 (by rfl) ⟨1374225, by rfl⟩ : syracuseStep 3664601 = 2748451) B2748451
theorem B813847 : Blo 722323 813847 := bstep (se 1 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 813847 = 1220771) B1220771
theorem B1633049 : Blo 722323 1633049 := bstep (se 2 (by rfl) ⟨612393, by rfl⟩ : syracuseStep 1633049 = 1224787) B1224787
theorem B1633139 : Blo 722323 1633139 := bstep (se 1 (by rfl) ⟨1224854, by rfl⟩ : syracuseStep 1633139 = 2449709) B2449709
theorem B2747267 : Blo 722323 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B1633175 : Blo 722323 1633175 := bstep (se 1 (by rfl) ⟨1224881, by rfl⟩ : syracuseStep 1633175 = 2449763) B2449763
theorem B814027 : Blo 722323 814027 := bstep (se 1 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 814027 = 1221041) B1221041
theorem B1829911 : Blo 722323 1829911 := bstep (se 1 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 1829911 = 2744867) B2744867
theorem B814135 : Blo 722323 814135 := bstep (se 1 (by rfl) ⟨610601, by rfl⟩ : syracuseStep 814135 = 1221203) B1221203
theorem B1633355 : Blo 722323 1633355 := bstep (se 1 (by rfl) ⟨1225016, by rfl⟩ : syracuseStep 1633355 = 2450033) B2450033
theorem B2059357 : Blo 722323 2059357 := bstep (se 3 (by rfl) ⟨386129, by rfl⟩ : syracuseStep 2059357 = 772259) B772259
theorem B1633409 : Blo 722323 1633409 := bstep (se 2 (by rfl) ⟨612528, by rfl⟩ : syracuseStep 1633409 = 1225057) B1225057
theorem B2059415 : Blo 722323 2059415 := bstep (se 1 (by rfl) ⟨1544561, by rfl⟩ : syracuseStep 2059415 = 3089123) B3089123
theorem B814315 : Blo 722323 814315 := bstep (se 1 (by rfl) ⟨610736, by rfl⟩ : syracuseStep 814315 = 1221473) B1221473
theorem B7433477 : Blo 722323 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B814423 : Blo 722323 814423 := bstep (se 1 (by rfl) ⟨610817, by rfl⟩ : syracuseStep 814423 = 1221635) B1221635
theorem B1633625 : Blo 722323 1633625 := bstep (se 2 (by rfl) ⟨612609, by rfl⟩ : syracuseStep 1633625 = 1225219) B1225219
theorem B22310261 : Blo 722323 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B1633715 : Blo 722323 1633715 := bstep (se 1 (by rfl) ⟨1225286, by rfl⟩ : syracuseStep 1633715 = 2450573) B2450573
theorem B1306049 : Blo 722323 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B1830347 : Blo 722323 1830347 := bstep (se 1 (by rfl) ⟨1372760, by rfl⟩ : syracuseStep 1830347 = 2745521) B2745521
theorem B1961419 : Blo 722323 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B1633751 : Blo 722323 1633751 := bstep (se 1 (by rfl) ⟨1225313, by rfl⟩ : syracuseStep 1633751 = 2450627) B2450627
theorem B814603 : Blo 722323 814603 := bstep (se 1 (by rfl) ⟨610952, by rfl⟩ : syracuseStep 814603 = 1221905) B1221905
theorem B6975011 : Blo 722323 6975011 := bstep (se 1 (by rfl) ⟨5231258, by rfl⟩ : syracuseStep 6975011 = 10462517) B10462517
theorem B1306201 : Blo 722323 1306201 := bstep (se 2 (by rfl) ⟨489825, by rfl⟩ : syracuseStep 1306201 = 979651) B979651
theorem B814711 : Blo 722323 814711 := bstep (se 1 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 814711 = 1222067) B1222067
theorem B5500547 : Blo 722323 5500547 := bstep (se 1 (by rfl) ⟨4125410, by rfl⟩ : syracuseStep 5500547 = 8250821) B8250821
theorem B1633931 : Blo 722323 1633931 := bstep (se 1 (by rfl) ⟨1225448, by rfl⟩ : syracuseStep 1633931 = 2450897) B2450897
theorem B2322071 : Blo 722323 2322071 := bstep (se 1 (by rfl) ⟨1741553, by rfl⟩ : syracuseStep 2322071 = 3483107) B3483107
theorem B2649773 : Blo 722323 2649773 := bstep (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) B993665
theorem B1633985 : Blo 722323 1633985 := bstep (se 2 (by rfl) ⟨612744, by rfl⟩ : syracuseStep 1633985 = 1225489) B1225489
theorem B814891 : Blo 722323 814891 := bstep (se 1 (by rfl) ⟨611168, by rfl⟩ : syracuseStep 814891 = 1222337) B1222337
theorem B1830721 : Blo 722323 1830721 := bstep (se 2 (by rfl) ⟨686520, by rfl⟩ : syracuseStep 1830721 = 1373041) B1373041
theorem B814999 : Blo 722323 814999 := bstep (se 1 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 814999 = 1222499) B1222499
theorem B1634201 : Blo 722323 1634201 := bstep (se 2 (by rfl) ⟨612825, by rfl⟩ : syracuseStep 1634201 = 1225651) B1225651
theorem B1306547 : Blo 722323 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B978905 : Blo 722323 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B782347 : Blo 722323 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B815179 : Blo 722323 815179 := bstep (se 1 (by rfl) ⟨611384, by rfl⟩ : syracuseStep 815179 = 1222769) B1222769
theorem B4944023 : Blo 722323 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B815287 : Blo 722323 815287 := bstep (se 1 (by rfl) ⟨611465, by rfl⟩ : syracuseStep 815287 = 1222931) B1222931
theorem B1372403 : Blo 722323 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B3666221 : Blo 722323 3666221 := bstep (se 3 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 3666221 = 1374833) B1374833
theorem B2060633 : Blo 722323 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B815467 : Blo 722323 815467 := bstep (se 1 (by rfl) ⟨611600, by rfl⟩ : syracuseStep 815467 = 1223201) B1223201
theorem B1307009 : Blo 722323 1307009 := bstep (se 2 (by rfl) ⟨490128, by rfl⟩ : syracuseStep 1307009 = 980257) B980257
theorem B1372555 : Blo 722323 1372555 := bstep (se 1 (by rfl) ⟨1029416, by rfl⟩ : syracuseStep 1372555 = 2058833) B2058833
theorem B1831319 : Blo 722323 1831319 := bstep (se 1 (by rfl) ⟨1373489, by rfl⟩ : syracuseStep 1831319 = 2746979) B2746979
theorem B2060747 : Blo 722323 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B815575 : Blo 722323 815575 := bstep (se 1 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 815575 = 1223363) B1223363
theorem B11301389 : Blo 722323 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B979543 : Blo 722323 979543 := bstep (se 1 (by rfl) ⟨734657, by rfl⟩ : syracuseStep 979543 = 1469315) B1469315
theorem B1962589 : Blo 722323 1962589 := bstep (se 3 (by rfl) ⟨367985, by rfl⟩ : syracuseStep 1962589 = 735971) B735971
theorem B2683523 : Blo 722323 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B815755 : Blo 722323 815755 := bstep (se 1 (by rfl) ⟨611816, by rfl⟩ : syracuseStep 815755 = 1223633) B1223633
theorem B1372889 : Blo 722323 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B815863 : Blo 722323 815863 := bstep (se 1 (by rfl) ⟨611897, by rfl⟩ : syracuseStep 815863 = 1223795) B1223795
theorem B1962803 : Blo 722323 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B816043 : Blo 722323 816043 := bstep (se 1 (by rfl) ⟨612032, by rfl⟩ : syracuseStep 816043 = 1224065) B1224065
theorem B1307585 : Blo 722323 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B816151 : Blo 722323 816151 := bstep (se 1 (by rfl) ⟨612113, by rfl⟩ : syracuseStep 816151 = 1224227) B1224227
theorem B1045657 : Blo 722323 1045657 := bstep (se 2 (by rfl) ⟨392121, by rfl⟩ : syracuseStep 1045657 = 784243) B784243
theorem B1307801 : Blo 722323 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B1832129 : Blo 722323 1832129 := bstep (se 2 (by rfl) ⟨687048, by rfl⟩ : syracuseStep 1832129 = 1374097) B1374097
theorem B816331 : Blo 722323 816331 := bstep (se 1 (by rfl) ⟨612248, by rfl⟩ : syracuseStep 816331 = 1224497) B1224497
theorem B914647 : Blo 722323 914647 := bstep (se 1 (by rfl) ⟨685985, by rfl⟩ : syracuseStep 914647 = 1371971) B1371971
theorem B816439 : Blo 722323 816439 := bstep (se 1 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 816439 = 1224659) B1224659
theorem B1373527 : Blo 722323 1373527 := bstep (se 1 (by rfl) ⟨1030145, by rfl⟩ : syracuseStep 1373527 = 2060291) B2060291
theorem B816619 : Blo 722323 816619 := bstep (se 1 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 816619 = 1224929) B1224929
theorem B1144343 : Blo 722323 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B2061875 : Blo 722323 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B816727 : Blo 722323 816727 := bstep (se 1 (by rfl) ⟨612545, by rfl⟩ : syracuseStep 816727 = 1225091) B1225091
theorem B4126301 : Blo 722323 4126301 := bstep (se 3 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 4126301 = 1547363) B1547363
theorem B13891277 : Blo 722323 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B1832665 : Blo 722323 1832665 := bstep (se 2 (by rfl) ⟨687249, by rfl⟩ : syracuseStep 1832665 = 1374499) B1374499
theorem B816907 : Blo 722323 816907 := bstep (se 1 (by rfl) ⟨612680, by rfl⟩ : syracuseStep 816907 = 1225361) B1225361
theorem B2094913 : Blo 722323 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B817015 : Blo 722323 817015 := bstep (se 1 (by rfl) ⟨612761, by rfl⟩ : syracuseStep 817015 = 1225523) B1225523
theorem B2750381 : Blo 722323 2750381 := bstep (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) B1031393
theorem B2062273 : Blo 722323 2062273 := bstep (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) B1546705
theorem B2324531 : Blo 722323 2324531 := bstep (se 1 (by rfl) ⟨1743398, by rfl⟩ : syracuseStep 2324531 = 3486797) B3486797
theorem B5863499 : Blo 722323 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B1374347 : Blo 722323 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B1374401 : Blo 722323 1374401 := bstep (se 2 (by rfl) ⟨515400, by rfl⟩ : syracuseStep 1374401 = 1030801) B1030801
theorem B4127051 : Blo 722323 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B4651339 : Blo 722323 4651339 := bstep (se 1 (by rfl) ⟨3488504, by rfl⟩ : syracuseStep 4651339 = 6977009) B6977009
theorem B2259479 : Blo 722323 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B2751155 : Blo 722323 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B1833779 : Blo 722323 1833779 := bstep (se 1 (by rfl) ⟨1375334, by rfl⟩ : syracuseStep 1833779 = 2750669) B2750669
theorem B916363 : Blo 722323 916363 := bstep (se 1 (by rfl) ⟨687272, by rfl⟩ : syracuseStep 916363 = 1374545) B1374545
theorem B1178507 : Blo 722323 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B4651955 : Blo 722323 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B5503949 : Blo 722323 5503949 := bstep (se 3 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 5503949 = 2063981) B2063981
theorem B1375319 : Blo 722323 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B1834073 : Blo 722323 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B5504435 : Blo 722323 5504435 := bstep (se 1 (by rfl) ⟨4128326, by rfl⟩ : syracuseStep 5504435 = 8256653) B8256653
theorem B1375859 : Blo 722323 1375859 := bstep (se 1 (by rfl) ⟨1031894, by rfl⟩ : syracuseStep 1375859 = 2063789) B2063789
theorem B917335 : Blo 722323 917335 := bstep (se 1 (by rfl) ⟨688001, by rfl⟩ : syracuseStep 917335 = 1376003) B1376003
theorem B4128691 : Blo 722323 4128691 := bstep (se 1 (by rfl) ⟨3096518, by rfl⟩ : syracuseStep 4128691 = 6193037) B6193037
theorem B917563 : Blo 722323 917563 := bstep (se 1 (by rfl) ⟨688172, by rfl⟩ : syracuseStep 917563 = 1376345) B1376345
theorem B1835095 : Blo 722323 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B1376527 : Blo 722323 1376527 := bstep (se 1 (by rfl) ⟨1032395, by rfl⟩ : syracuseStep 1376527 = 2064791) B2064791
theorem B1835399 : Blo 722323 1835399 := bstep (se 1 (by rfl) ⟨1376549, by rfl⟩ : syracuseStep 1835399 = 2753099) B2753099
theorem B4653571 : Blo 722323 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B1835531 : Blo 722323 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B3670595 : Blo 722323 3670595 := bstep (se 1 (by rfl) ⟨2752946, by rfl⟩ : syracuseStep 3670595 = 5505893) B5505893
theorem B3670919 : Blo 722323 3670919 := bstep (se 1 (by rfl) ⟨2753189, by rfl⟩ : syracuseStep 3670919 = 5506379) B5506379
theorem B918535 : Blo 722323 918535 := bstep (se 1 (by rfl) ⟨688901, by rfl⟩ : syracuseStep 918535 = 1377803) B1377803
theorem B1836047 : Blo 722323 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B3474551 : Blo 722323 3474551 := bstep (se 1 (by rfl) ⟨2605913, by rfl⟩ : syracuseStep 3474551 = 5211827) B5211827
theorem B1377415 : Blo 722323 1377415 := bstep (se 1 (by rfl) ⟨1033061, by rfl⟩ : syracuseStep 1377415 = 2066123) B2066123
theorem B1836179 : Blo 722323 1836179 := bstep (se 1 (by rfl) ⟨1377134, by rfl⟩ : syracuseStep 1836179 = 2754269) B2754269
theorem B5211539 : Blo 722323 5211539 := bstep (se 1 (by rfl) ⟨3908654, by rfl⟩ : syracuseStep 5211539 = 7817309) B7817309
theorem B918955 : Blo 722323 918955 := bstep (se 1 (by rfl) ⟨689216, by rfl⟩ : syracuseStep 918955 = 1378433) B1378433
theorem B722363 : Blo 722323 722363 := bstep (se 1 (by rfl) ⟨541772, by rfl⟩ : syracuseStep 722363 = 1083545) B1083545
theorem B722439 : Blo 722323 722439 := bstep (se 1 (by rfl) ⟨541829, by rfl⟩ : syracuseStep 722439 = 1083659) B1083659
theorem B722447 : Blo 722323 722447 := bstep (se 1 (by rfl) ⟨541835, by rfl⟩ : syracuseStep 722447 = 1083671) B1083671
theorem B722491 : Blo 722323 722491 := bstep (se 1 (by rfl) ⟨541868, by rfl⟩ : syracuseStep 722491 = 1083737) B1083737
theorem B4130423 : Blo 722323 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B722567 : Blo 722323 722567 := bstep (se 1 (by rfl) ⟨541925, by rfl⟩ : syracuseStep 722567 = 1083851) B1083851
theorem B722575 : Blo 722323 722575 := bstep (se 1 (by rfl) ⟨541931, by rfl⟩ : syracuseStep 722575 = 1083863) B1083863
theorem B919183 : Blo 722323 919183 := bstep (se 1 (by rfl) ⟨689387, by rfl⟩ : syracuseStep 919183 = 1378775) B1378775
theorem B722619 : Blo 722323 722619 := bstep (se 1 (by rfl) ⟨541964, by rfl⟩ : syracuseStep 722619 = 1083929) B1083929
theorem B722695 : Blo 722323 722695 := bstep (se 1 (by rfl) ⟨542021, by rfl⟩ : syracuseStep 722695 = 1084043) B1084043
theorem B722703 : Blo 722323 722703 := bstep (se 1 (by rfl) ⟨542027, by rfl⟩ : syracuseStep 722703 = 1084055) B1084055
theorem B5506865 : Blo 722323 5506865 := bstep (se 2 (by rfl) ⟨2065074, by rfl⟩ : syracuseStep 5506865 = 4130149) B4130149
theorem B722747 : Blo 722323 722747 := bstep (se 1 (by rfl) ⟨542060, by rfl⟩ : syracuseStep 722747 = 1084121) B1084121
theorem B4949849 : Blo 722323 4949849 := bstep (se 2 (by rfl) ⟨1856193, by rfl⟩ : syracuseStep 4949849 = 3712387) B3712387
theorem B4130675 : Blo 722323 4130675 := bstep (se 1 (by rfl) ⟨3098006, by rfl⟩ : syracuseStep 4130675 = 6196013) B6196013
theorem B722823 : Blo 722323 722823 := bstep (se 1 (by rfl) ⟨542117, by rfl⟩ : syracuseStep 722823 = 1084235) B1084235
theorem B1738631 : Blo 722323 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B722831 : Blo 722323 722831 := bstep (se 1 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 722831 = 1084247) B1084247
theorem B722875 : Blo 722323 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B722951 : Blo 722323 722951 := bstep (se 1 (by rfl) ⟨542213, by rfl⟩ : syracuseStep 722951 = 1084427) B1084427
theorem B722959 : Blo 722323 722959 := bstep (se 1 (by rfl) ⟨542219, by rfl⟩ : syracuseStep 722959 = 1084439) B1084439
theorem B2066465 : Blo 722323 2066465 := bstep (se 2 (by rfl) ⟨774924, by rfl⟩ : syracuseStep 2066465 = 1549849) B1549849
theorem B723003 : Blo 722323 723003 := bstep (se 1 (by rfl) ⟨542252, by rfl⟩ : syracuseStep 723003 = 1084505) B1084505
theorem B1083527 : Blo 722323 1083527 := bstep (se 1 (by rfl) ⟨812645, by rfl⟩ : syracuseStep 1083527 = 1625291) B1625291
theorem B723079 : Blo 722323 723079 := bstep (se 1 (by rfl) ⟨542309, by rfl⟩ : syracuseStep 723079 = 1084619) B1084619
theorem B723087 : Blo 722323 723087 := bstep (se 1 (by rfl) ⟨542315, by rfl⟩ : syracuseStep 723087 = 1084631) B1084631
theorem B2066579 : Blo 722323 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B1083563 : Blo 722323 1083563 := bstep (se 1 (by rfl) ⟨812672, by rfl⟩ : syracuseStep 1083563 = 1625345) B1625345
theorem B723131 : Blo 722323 723131 := bstep (se 1 (by rfl) ⟨542348, by rfl⟩ : syracuseStep 723131 = 1084697) B1084697
theorem B1083593 : Blo 722323 1083593 := bstep (se 2 (by rfl) ⟨406347, by rfl⟩ : syracuseStep 1083593 = 812695) B812695
theorem B1837313 : Blo 722323 1837313 := bstep (se 2 (by rfl) ⟨688992, by rfl⟩ : syracuseStep 1837313 = 1377985) B1377985
theorem B723207 : Blo 722323 723207 := bstep (se 1 (by rfl) ⟨542405, by rfl⟩ : syracuseStep 723207 = 1084811) B1084811
theorem B723215 : Blo 722323 723215 := bstep (se 1 (by rfl) ⟨542411, by rfl⟩ : syracuseStep 723215 = 1084823) B1084823
theorem B1083707 : Blo 722323 1083707 := bstep (se 1 (by rfl) ⟨812780, by rfl⟩ : syracuseStep 1083707 = 1625561) B1625561
theorem B723259 : Blo 722323 723259 := bstep (se 1 (by rfl) ⟨542444, by rfl⟩ : syracuseStep 723259 = 1084889) B1084889
theorem B1083767 : Blo 722323 1083767 := bstep (se 1 (by rfl) ⟨812825, by rfl⟩ : syracuseStep 1083767 = 1625651) B1625651
theorem B723335 : Blo 722323 723335 := bstep (se 1 (by rfl) ⟨542501, by rfl⟩ : syracuseStep 723335 = 1085003) B1085003
theorem B1083791 : Blo 722323 1083791 := bstep (se 1 (by rfl) ⟨812843, by rfl⟩ : syracuseStep 1083791 = 1625687) B1625687
theorem B723343 : Blo 722323 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B1083833 : Blo 722323 1083833 := bstep (se 2 (by rfl) ⟨406437, by rfl⟩ : syracuseStep 1083833 = 812875) B812875
theorem B723387 : Blo 722323 723387 := bstep (se 1 (by rfl) ⟨542540, by rfl⟩ : syracuseStep 723387 = 1085081) B1085081
theorem B1083911 : Blo 722323 1083911 := bstep (se 1 (by rfl) ⟨812933, by rfl⟩ : syracuseStep 1083911 = 1625867) B1625867
theorem B723463 : Blo 722323 723463 := bstep (se 1 (by rfl) ⟨542597, by rfl⟩ : syracuseStep 723463 = 1085195) B1085195
theorem B723471 : Blo 722323 723471 := bstep (se 1 (by rfl) ⟨542603, by rfl⟩ : syracuseStep 723471 = 1085207) B1085207
theorem B1083947 : Blo 722323 1083947 := bstep (se 1 (by rfl) ⟨812960, by rfl⟩ : syracuseStep 1083947 = 1625921) B1625921
theorem B723515 : Blo 722323 723515 := bstep (se 1 (by rfl) ⟨542636, by rfl⟩ : syracuseStep 723515 = 1085273) B1085273
theorem B1083977 : Blo 722323 1083977 := bstep (se 2 (by rfl) ⟨406491, by rfl⟩ : syracuseStep 1083977 = 812983) B812983
theorem B1837687 : Blo 722323 1837687 := bstep (se 1 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 1837687 = 2756531) B2756531
theorem B723591 : Blo 722323 723591 := bstep (se 1 (by rfl) ⟨542693, by rfl⟩ : syracuseStep 723591 = 1085387) B1085387
theorem B723599 : Blo 722323 723599 := bstep (se 1 (by rfl) ⟨542699, by rfl⟩ : syracuseStep 723599 = 1085399) B1085399
theorem B16714421 : Blo 722323 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1084091 : Blo 722323 1084091 := bstep (se 1 (by rfl) ⟨813068, by rfl⟩ : syracuseStep 1084091 = 1626137) B1626137
theorem B723643 : Blo 722323 723643 := bstep (se 1 (by rfl) ⟨542732, by rfl⟩ : syracuseStep 723643 = 1085465) B1085465
theorem B1084151 : Blo 722323 1084151 := bstep (se 1 (by rfl) ⟨813113, by rfl⟩ : syracuseStep 1084151 = 1626227) B1626227
theorem B723719 : Blo 722323 723719 := bstep (se 1 (by rfl) ⟨542789, by rfl⟩ : syracuseStep 723719 = 1085579) B1085579
theorem B1084175 : Blo 722323 1084175 := bstep (se 1 (by rfl) ⟨813131, by rfl⟩ : syracuseStep 1084175 = 1626263) B1626263
theorem B723727 : Blo 722323 723727 := bstep (se 1 (by rfl) ⟨542795, by rfl⟩ : syracuseStep 723727 = 1085591) B1085591
theorem B1084217 : Blo 722323 1084217 := bstep (se 2 (by rfl) ⟨406581, by rfl⟩ : syracuseStep 1084217 = 813163) B813163
theorem B723771 : Blo 722323 723771 := bstep (se 1 (by rfl) ⟨542828, by rfl⟩ : syracuseStep 723771 = 1085657) B1085657
theorem B1084295 : Blo 722323 1084295 := bstep (se 1 (by rfl) ⟨813221, by rfl⟩ : syracuseStep 1084295 = 1626443) B1626443
theorem B723847 : Blo 722323 723847 := bstep (se 1 (by rfl) ⟨542885, by rfl⟩ : syracuseStep 723847 = 1085771) B1085771
theorem B723855 : Blo 722323 723855 := bstep (se 1 (by rfl) ⟨542891, by rfl⟩ : syracuseStep 723855 = 1085783) B1085783
theorem B2067353 : Blo 722323 2067353 := bstep (se 2 (by rfl) ⟨775257, by rfl⟩ : syracuseStep 2067353 = 1550515) B1550515
theorem B1084331 : Blo 722323 1084331 := bstep (se 1 (by rfl) ⟨813248, by rfl⟩ : syracuseStep 1084331 = 1626497) B1626497
theorem B723899 : Blo 722323 723899 := bstep (se 1 (by rfl) ⟨542924, by rfl⟩ : syracuseStep 723899 = 1085849) B1085849
theorem B1084361 : Blo 722323 1084361 := bstep (se 2 (by rfl) ⟨406635, by rfl⟩ : syracuseStep 1084361 = 813271) B813271
theorem B723975 : Blo 722323 723975 := bstep (se 1 (by rfl) ⟨542981, by rfl⟩ : syracuseStep 723975 = 1085963) B1085963
theorem B723983 : Blo 722323 723983 := bstep (se 1 (by rfl) ⟨542987, by rfl⟩ : syracuseStep 723983 = 1085975) B1085975
theorem B1838123 : Blo 722323 1838123 := bstep (se 1 (by rfl) ⟨1378592, by rfl⟩ : syracuseStep 1838123 = 2757185) B2757185
theorem B1084475 : Blo 722323 1084475 := bstep (se 1 (by rfl) ⟨813356, by rfl⟩ : syracuseStep 1084475 = 1626713) B1626713
theorem B724027 : Blo 722323 724027 := bstep (se 1 (by rfl) ⟨543020, by rfl⟩ : syracuseStep 724027 = 1086041) B1086041
theorem B1084535 : Blo 722323 1084535 := bstep (se 1 (by rfl) ⟨813401, by rfl⟩ : syracuseStep 1084535 = 1626803) B1626803
theorem B724103 : Blo 722323 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B1084559 : Blo 722323 1084559 := bstep (se 1 (by rfl) ⟨813419, by rfl⟩ : syracuseStep 1084559 = 1626839) B1626839
theorem B724111 : Blo 722323 724111 := bstep (se 1 (by rfl) ⟨543083, by rfl⟩ : syracuseStep 724111 = 1086167) B1086167
theorem B1084601 : Blo 722323 1084601 := bstep (se 2 (by rfl) ⟨406725, by rfl⟩ : syracuseStep 1084601 = 813451) B813451
theorem B724155 : Blo 722323 724155 := bstep (se 1 (by rfl) ⟨543116, by rfl⟩ : syracuseStep 724155 = 1086233) B1086233
theorem B1084679 : Blo 722323 1084679 := bstep (se 1 (by rfl) ⟨813509, by rfl⟩ : syracuseStep 1084679 = 1627019) B1627019
theorem B724231 : Blo 722323 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B724239 : Blo 722323 724239 := bstep (se 1 (by rfl) ⟨543179, by rfl⟩ : syracuseStep 724239 = 1086359) B1086359
theorem B7834913 : Blo 722323 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B4132133 : Blo 722323 4132133 := bstep (se 4 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 4132133 = 774775) B774775
theorem B1084715 : Blo 722323 1084715 := bstep (se 1 (by rfl) ⟨813536, by rfl⟩ : syracuseStep 1084715 = 1627073) B1627073
theorem B724283 : Blo 722323 724283 := bstep (se 1 (by rfl) ⟨543212, by rfl⟩ : syracuseStep 724283 = 1086425) B1086425
theorem B1084745 : Blo 722323 1084745 := bstep (se 2 (by rfl) ⟨406779, by rfl⟩ : syracuseStep 1084745 = 813559) B813559
theorem B724359 : Blo 722323 724359 := bstep (se 1 (by rfl) ⟨543269, by rfl⟩ : syracuseStep 724359 = 1086539) B1086539
theorem B724367 : Blo 722323 724367 := bstep (se 1 (by rfl) ⟨543275, by rfl⟩ : syracuseStep 724367 = 1086551) B1086551
theorem B1740217 : Blo 722323 1740217 := bstep (se 2 (by rfl) ⟨652581, by rfl⟩ : syracuseStep 1740217 = 1305163) B1305163
theorem B1084859 : Blo 722323 1084859 := bstep (se 1 (by rfl) ⟨813644, by rfl⟩ : syracuseStep 1084859 = 1627289) B1627289
theorem B724411 : Blo 722323 724411 := bstep (se 1 (by rfl) ⟨543308, by rfl⟩ : syracuseStep 724411 = 1086617) B1086617
theorem B1084919 : Blo 722323 1084919 := bstep (se 1 (by rfl) ⟨813689, by rfl⟩ : syracuseStep 1084919 = 1627379) B1627379
theorem B724487 : Blo 722323 724487 := bstep (se 1 (by rfl) ⟨543365, by rfl⟩ : syracuseStep 724487 = 1086731) B1086731
theorem B1084943 : Blo 722323 1084943 := bstep (se 1 (by rfl) ⟨813707, by rfl⟩ : syracuseStep 1084943 = 1627415) B1627415
theorem B724495 : Blo 722323 724495 := bstep (se 1 (by rfl) ⟨543371, by rfl⟩ : syracuseStep 724495 = 1086743) B1086743
theorem B1084985 : Blo 722323 1084985 := bstep (se 2 (by rfl) ⟨406869, by rfl⟩ : syracuseStep 1084985 = 813739) B813739
theorem B724539 : Blo 722323 724539 := bstep (se 1 (by rfl) ⟨543404, by rfl⟩ : syracuseStep 724539 = 1086809) B1086809
theorem B1085063 : Blo 722323 1085063 := bstep (se 1 (by rfl) ⟨813797, by rfl⟩ : syracuseStep 1085063 = 1627595) B1627595
theorem B724615 : Blo 722323 724615 := bstep (se 1 (by rfl) ⟨543461, by rfl⟩ : syracuseStep 724615 = 1086923) B1086923
theorem B724623 : Blo 722323 724623 := bstep (se 1 (by rfl) ⟨543467, by rfl⟩ : syracuseStep 724623 = 1086935) B1086935
theorem B1085099 : Blo 722323 1085099 := bstep (se 1 (by rfl) ⟨813824, by rfl⟩ : syracuseStep 1085099 = 1627649) B1627649
theorem B724667 : Blo 722323 724667 := bstep (se 1 (by rfl) ⟨543500, by rfl⟩ : syracuseStep 724667 = 1087001) B1087001
theorem B1085129 : Blo 722323 1085129 := bstep (se 2 (by rfl) ⟨406923, by rfl⟩ : syracuseStep 1085129 = 813847) B813847
theorem B724743 : Blo 722323 724743 := bstep (se 1 (by rfl) ⟨543557, by rfl⟩ : syracuseStep 724743 = 1087115) B1087115
theorem B724751 : Blo 722323 724751 := bstep (se 1 (by rfl) ⟨543563, by rfl⟩ : syracuseStep 724751 = 1087127) B1087127
theorem B1085243 : Blo 722323 1085243 := bstep (se 1 (by rfl) ⟨813932, by rfl⟩ : syracuseStep 1085243 = 1627865) B1627865
theorem B724795 : Blo 722323 724795 := bstep (se 1 (by rfl) ⟨543596, by rfl⟩ : syracuseStep 724795 = 1087193) B1087193
theorem B1085303 : Blo 722323 1085303 := bstep (se 1 (by rfl) ⟨813977, by rfl⟩ : syracuseStep 1085303 = 1627955) B1627955
theorem B724871 : Blo 722323 724871 := bstep (se 1 (by rfl) ⟨543653, by rfl⟩ : syracuseStep 724871 = 1087307) B1087307
theorem B1085327 : Blo 722323 1085327 := bstep (se 1 (by rfl) ⟨813995, by rfl⟩ : syracuseStep 1085327 = 1627991) B1627991
theorem B724879 : Blo 722323 724879 := bstep (se 1 (by rfl) ⟨543659, by rfl⟩ : syracuseStep 724879 = 1087319) B1087319
theorem B1085369 : Blo 722323 1085369 := bstep (se 2 (by rfl) ⟨407013, by rfl⟩ : syracuseStep 1085369 = 814027) B814027
theorem B3477433 : Blo 722323 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B724923 : Blo 722323 724923 := bstep (se 1 (by rfl) ⟨543692, by rfl⟩ : syracuseStep 724923 = 1087385) B1087385
theorem B3706883 : Blo 722323 3706883 := bstep (se 1 (by rfl) ⟨2780162, by rfl⟩ : syracuseStep 3706883 = 5560325) B5560325
theorem B1085447 : Blo 722323 1085447 := bstep (se 1 (by rfl) ⟨814085, by rfl⟩ : syracuseStep 1085447 = 1628171) B1628171
theorem B724999 : Blo 722323 724999 := bstep (se 1 (by rfl) ⟨543749, by rfl⟩ : syracuseStep 724999 = 1087499) B1087499
theorem B725007 : Blo 722323 725007 := bstep (se 1 (by rfl) ⟨543755, by rfl⟩ : syracuseStep 725007 = 1087511) B1087511
theorem B1085483 : Blo 722323 1085483 := bstep (se 1 (by rfl) ⟨814112, by rfl⟩ : syracuseStep 1085483 = 1628225) B1628225
theorem B725051 : Blo 722323 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B1085513 : Blo 722323 1085513 := bstep (se 2 (by rfl) ⟨407067, by rfl⟩ : syracuseStep 1085513 = 814135) B814135
theorem B8228951 : Blo 722323 8228951 := bstep (se 1 (by rfl) ⟨6171713, by rfl⟩ : syracuseStep 8228951 = 12343427) B12343427
theorem B725127 : Blo 722323 725127 := bstep (se 1 (by rfl) ⟨543845, by rfl⟩ : syracuseStep 725127 = 1087691) B1087691
theorem B725135 : Blo 722323 725135 := bstep (se 1 (by rfl) ⟨543851, by rfl⟩ : syracuseStep 725135 = 1087703) B1087703
theorem B1085627 : Blo 722323 1085627 := bstep (se 1 (by rfl) ⟨814220, by rfl⟩ : syracuseStep 1085627 = 1628441) B1628441
theorem B725179 : Blo 722323 725179 := bstep (se 1 (by rfl) ⟨543884, by rfl⟩ : syracuseStep 725179 = 1087769) B1087769
theorem B4133065 : Blo 722323 4133065 := bstep (se 2 (by rfl) ⟨1549899, by rfl⟩ : syracuseStep 4133065 = 3099799) B3099799
theorem B1085687 : Blo 722323 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B725255 : Blo 722323 725255 := bstep (se 1 (by rfl) ⟨543941, by rfl⟩ : syracuseStep 725255 = 1087883) B1087883
theorem B1085711 : Blo 722323 1085711 := bstep (se 1 (by rfl) ⟨814283, by rfl⟩ : syracuseStep 1085711 = 1628567) B1628567
theorem B725263 : Blo 722323 725263 := bstep (se 1 (by rfl) ⟨543947, by rfl⟩ : syracuseStep 725263 = 1087895) B1087895
theorem B1085753 : Blo 722323 1085753 := bstep (se 2 (by rfl) ⟨407157, by rfl⟩ : syracuseStep 1085753 = 814315) B814315
theorem B725307 : Blo 722323 725307 := bstep (se 1 (by rfl) ⟨543980, by rfl⟩ : syracuseStep 725307 = 1087961) B1087961
theorem B3674483 : Blo 722323 3674483 := bstep (se 1 (by rfl) ⟨2755862, by rfl⟩ : syracuseStep 3674483 = 5511725) B5511725
theorem B1085831 : Blo 722323 1085831 := bstep (se 1 (by rfl) ⟨814373, by rfl⟩ : syracuseStep 1085831 = 1628747) B1628747
theorem B725383 : Blo 722323 725383 := bstep (se 1 (by rfl) ⟨544037, by rfl⟩ : syracuseStep 725383 = 1088075) B1088075
theorem B725391 : Blo 722323 725391 := bstep (se 1 (by rfl) ⟨544043, by rfl⟩ : syracuseStep 725391 = 1088087) B1088087
theorem B2757017 : Blo 722323 2757017 := bstep (se 2 (by rfl) ⟨1033881, by rfl⟩ : syracuseStep 2757017 = 2067763) B2067763
theorem B1085867 : Blo 722323 1085867 := bstep (se 1 (by rfl) ⟨814400, by rfl⟩ : syracuseStep 1085867 = 1628801) B1628801
theorem B725435 : Blo 722323 725435 := bstep (se 1 (by rfl) ⟨544076, by rfl⟩ : syracuseStep 725435 = 1088153) B1088153
theorem B1085897 : Blo 722323 1085897 := bstep (se 2 (by rfl) ⟨407211, by rfl⟩ : syracuseStep 1085897 = 814423) B814423
theorem B1118711 : Blo 722323 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B725511 : Blo 722323 725511 := bstep (se 1 (by rfl) ⟨544133, by rfl⟩ : syracuseStep 725511 = 1088267) B1088267
theorem B725519 : Blo 722323 725519 := bstep (se 1 (by rfl) ⟨544139, by rfl⟩ : syracuseStep 725519 = 1088279) B1088279
theorem B1086011 : Blo 722323 1086011 := bstep (se 1 (by rfl) ⟨814508, by rfl⟩ : syracuseStep 1086011 = 1629017) B1629017
theorem B725563 : Blo 722323 725563 := bstep (se 1 (by rfl) ⟨544172, by rfl⟩ : syracuseStep 725563 = 1088345) B1088345
theorem B3707459 : Blo 722323 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B1086071 : Blo 722323 1086071 := bstep (se 1 (by rfl) ⟨814553, by rfl⟩ : syracuseStep 1086071 = 1629107) B1629107
theorem B725639 : Blo 722323 725639 := bstep (se 1 (by rfl) ⟨544229, by rfl⟩ : syracuseStep 725639 = 1088459) B1088459
theorem B1086095 : Blo 722323 1086095 := bstep (se 1 (by rfl) ⟨814571, by rfl⟩ : syracuseStep 1086095 = 1629143) B1629143
theorem B725647 : Blo 722323 725647 := bstep (se 1 (by rfl) ⟨544235, by rfl⟩ : syracuseStep 725647 = 1088471) B1088471
theorem B13931189 : Blo 722323 13931189 := bstep (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) B1306049
theorem B1086137 : Blo 722323 1086137 := bstep (se 2 (by rfl) ⟨407301, by rfl⟩ : syracuseStep 1086137 = 814603) B814603
theorem B725691 : Blo 722323 725691 := bstep (se 1 (by rfl) ⟨544268, by rfl⟩ : syracuseStep 725691 = 1088537) B1088537
theorem B1086215 : Blo 722323 1086215 := bstep (se 1 (by rfl) ⟨814661, by rfl⟩ : syracuseStep 1086215 = 1629323) B1629323
theorem B725767 : Blo 722323 725767 := bstep (se 1 (by rfl) ⟨544325, by rfl⟩ : syracuseStep 725767 = 1088651) B1088651
theorem B725775 : Blo 722323 725775 := bstep (se 1 (by rfl) ⟨544331, by rfl⟩ : syracuseStep 725775 = 1088663) B1088663
theorem B1741601 : Blo 722323 1741601 := bstep (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) B1306201
theorem B1086251 : Blo 722323 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B725819 : Blo 722323 725819 := bstep (se 1 (by rfl) ⟨544364, by rfl⟩ : syracuseStep 725819 = 1088729) B1088729
theorem B1086281 : Blo 722323 1086281 := bstep (se 2 (by rfl) ⟨407355, by rfl⟩ : syracuseStep 1086281 = 814711) B814711
theorem B3674969 : Blo 722323 3674969 := bstep (se 2 (by rfl) ⟨1378113, by rfl⟩ : syracuseStep 3674969 = 2756227) B2756227
theorem B725895 : Blo 722323 725895 := bstep (se 1 (by rfl) ⟨544421, by rfl⟩ : syracuseStep 725895 = 1088843) B1088843
theorem B725903 : Blo 722323 725903 := bstep (se 1 (by rfl) ⟨544427, by rfl⟩ : syracuseStep 725903 = 1088855) B1088855
theorem B1086395 : Blo 722323 1086395 := bstep (se 1 (by rfl) ⟨814796, by rfl⟩ : syracuseStep 1086395 = 1629593) B1629593
theorem B725947 : Blo 722323 725947 := bstep (se 1 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 725947 = 1088921) B1088921
theorem B3707869 : Blo 722323 3707869 := bstep (se 3 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 3707869 = 1390451) B1390451
theorem B1086455 : Blo 722323 1086455 := bstep (se 1 (by rfl) ⟨814841, by rfl⟩ : syracuseStep 1086455 = 1629683) B1629683
theorem B726023 : Blo 722323 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B1086479 : Blo 722323 1086479 := bstep (se 1 (by rfl) ⟨814859, by rfl⟩ : syracuseStep 1086479 = 1629719) B1629719
theorem B726031 : Blo 722323 726031 := bstep (se 1 (by rfl) ⟨544523, by rfl⟩ : syracuseStep 726031 = 1089047) B1089047
theorem B1086521 : Blo 722323 1086521 := bstep (se 2 (by rfl) ⟨407445, by rfl⟩ : syracuseStep 1086521 = 814891) B814891
theorem B726075 : Blo 722323 726075 := bstep (se 1 (by rfl) ⟨544556, by rfl⟩ : syracuseStep 726075 = 1089113) B1089113
theorem B1086599 : Blo 722323 1086599 := bstep (se 1 (by rfl) ⟨814949, by rfl⟩ : syracuseStep 1086599 = 1629899) B1629899
theorem B726151 : Blo 722323 726151 := bstep (se 1 (by rfl) ⟨544613, by rfl⟩ : syracuseStep 726151 = 1089227) B1089227
theorem B726159 : Blo 722323 726159 := bstep (se 1 (by rfl) ⟨544619, by rfl⟩ : syracuseStep 726159 = 1089239) B1089239
theorem B1086635 : Blo 722323 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B726203 : Blo 722323 726203 := bstep (se 1 (by rfl) ⟨544652, by rfl⟩ : syracuseStep 726203 = 1089305) B1089305
theorem B1086665 : Blo 722323 1086665 := bstep (se 2 (by rfl) ⟨407499, by rfl⟩ : syracuseStep 1086665 = 814999) B814999
theorem B726279 : Blo 722323 726279 := bstep (se 1 (by rfl) ⟨544709, by rfl⟩ : syracuseStep 726279 = 1089419) B1089419
theorem B824591 : Blo 722323 824591 := bstep (se 1 (by rfl) ⟨618443, by rfl⟩ : syracuseStep 824591 = 1236887) B1236887
theorem B726287 : Blo 722323 726287 := bstep (se 1 (by rfl) ⟨544715, by rfl⟩ : syracuseStep 726287 = 1089431) B1089431
theorem B1086779 : Blo 722323 1086779 := bstep (se 1 (by rfl) ⟨815084, by rfl⟩ : syracuseStep 1086779 = 1630169) B1630169
theorem B1086839 : Blo 722323 1086839 := bstep (se 1 (by rfl) ⟨815129, by rfl⟩ : syracuseStep 1086839 = 1630259) B1630259
theorem B1086863 : Blo 722323 1086863 := bstep (se 1 (by rfl) ⟨815147, by rfl⟩ : syracuseStep 1086863 = 1630295) B1630295
theorem B3085721 : Blo 722323 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B1086905 : Blo 722323 1086905 := bstep (se 2 (by rfl) ⟨407589, by rfl⟩ : syracuseStep 1086905 = 815179) B815179
theorem B1086983 : Blo 722323 1086983 := bstep (se 1 (by rfl) ⟨815237, by rfl⟩ : syracuseStep 1086983 = 1630475) B1630475
theorem B1087019 : Blo 722323 1087019 := bstep (se 1 (by rfl) ⟨815264, by rfl⟩ : syracuseStep 1087019 = 1630529) B1630529
theorem B3479107 : Blo 722323 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B1087049 : Blo 722323 1087049 := bstep (se 2 (by rfl) ⟨407643, by rfl⟩ : syracuseStep 1087049 = 815287) B815287
theorem B1087163 : Blo 722323 1087163 := bstep (se 1 (by rfl) ⟨815372, by rfl⟩ : syracuseStep 1087163 = 1630745) B1630745
theorem B1087223 : Blo 722323 1087223 := bstep (se 1 (by rfl) ⟨815417, by rfl⟩ : syracuseStep 1087223 = 1630835) B1630835
theorem B1087247 : Blo 722323 1087247 := bstep (se 1 (by rfl) ⟨815435, by rfl⟩ : syracuseStep 1087247 = 1630871) B1630871
theorem B1087289 : Blo 722323 1087289 := bstep (se 2 (by rfl) ⟨407733, by rfl⟩ : syracuseStep 1087289 = 815467) B815467
theorem B1087367 : Blo 722323 1087367 := bstep (se 1 (by rfl) ⟨815525, by rfl⟩ : syracuseStep 1087367 = 1631051) B1631051
theorem B1087403 : Blo 722323 1087403 := bstep (se 1 (by rfl) ⟨815552, by rfl⟩ : syracuseStep 1087403 = 1631105) B1631105
theorem B1087433 : Blo 722323 1087433 := bstep (se 2 (by rfl) ⟨407787, by rfl⟩ : syracuseStep 1087433 = 815575) B815575
theorem B1087547 : Blo 722323 1087547 := bstep (se 1 (by rfl) ⟨815660, by rfl⟩ : syracuseStep 1087547 = 1631321) B1631321
theorem B1087607 : Blo 722323 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B3774583 : Blo 722323 3774583 := bstep (se 1 (by rfl) ⟨2830937, by rfl⟩ : syracuseStep 3774583 = 5661875) B5661875
theorem B1087631 : Blo 722323 1087631 := bstep (se 1 (by rfl) ⟨815723, by rfl⟩ : syracuseStep 1087631 = 1631447) B1631447
theorem B1087673 : Blo 722323 1087673 := bstep (se 2 (by rfl) ⟨407877, by rfl⟩ : syracuseStep 1087673 = 815755) B815755
theorem B1087751 : Blo 722323 1087751 := bstep (se 1 (by rfl) ⟨815813, by rfl⟩ : syracuseStep 1087751 = 1631627) B1631627
theorem B1087787 : Blo 722323 1087787 := bstep (se 1 (by rfl) ⟨815840, by rfl⟩ : syracuseStep 1087787 = 1631681) B1631681
theorem B1087817 : Blo 722323 1087817 := bstep (se 2 (by rfl) ⟨407931, by rfl⟩ : syracuseStep 1087817 = 815863) B815863
theorem B1218935 : Blo 722323 1218935 := bstep (se 1 (by rfl) ⟨914201, by rfl⟩ : syracuseStep 1218935 = 1828403) B1828403
theorem B4954553 : Blo 722323 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B1087931 : Blo 722323 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B1087991 : Blo 722323 1087991 := bstep (se 1 (by rfl) ⟨815993, by rfl⟩ : syracuseStep 1087991 = 1631987) B1631987
theorem B1088015 : Blo 722323 1088015 := bstep (se 1 (by rfl) ⟨816011, by rfl⟩ : syracuseStep 1088015 = 1632023) B1632023
theorem B1088057 : Blo 722323 1088057 := bstep (se 2 (by rfl) ⟨408021, by rfl⟩ : syracuseStep 1088057 = 816043) B816043
theorem B2202173 : Blo 722323 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1088135 : Blo 722323 1088135 := bstep (se 1 (by rfl) ⟨816101, by rfl⟩ : syracuseStep 1088135 = 1632203) B1632203
theorem B1088171 : Blo 722323 1088171 := bstep (se 1 (by rfl) ⟨816128, by rfl⟩ : syracuseStep 1088171 = 1632257) B1632257
theorem B1088201 : Blo 722323 1088201 := bstep (se 2 (by rfl) ⟨408075, by rfl⟩ : syracuseStep 1088201 = 816151) B816151
theorem B1219387 : Blo 722323 1219387 := bstep (se 1 (by rfl) ⟨914540, by rfl⟩ : syracuseStep 1219387 = 1829081) B1829081
theorem B1088315 : Blo 722323 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B1088375 : Blo 722323 1088375 := bstep (se 1 (by rfl) ⟨816281, by rfl⟩ : syracuseStep 1088375 = 1632563) B1632563
theorem B1088399 : Blo 722323 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B1088441 : Blo 722323 1088441 := bstep (se 2 (by rfl) ⟨408165, by rfl⟩ : syracuseStep 1088441 = 816331) B816331
theorem B1219529 : Blo 722323 1219529 := bstep (se 2 (by rfl) ⟨457323, by rfl⟩ : syracuseStep 1219529 = 914647) B914647
theorem B1088519 : Blo 722323 1088519 := bstep (se 1 (by rfl) ⟨816389, by rfl⟩ : syracuseStep 1088519 = 1632779) B1632779
theorem B1088555 : Blo 722323 1088555 := bstep (se 1 (by rfl) ⟨816416, by rfl⟩ : syracuseStep 1088555 = 1632833) B1632833
theorem B1088585 : Blo 722323 1088585 := bstep (se 2 (by rfl) ⟨408219, by rfl⟩ : syracuseStep 1088585 = 816439) B816439
theorem B1088699 : Blo 722323 1088699 := bstep (se 1 (by rfl) ⟨816524, by rfl⟩ : syracuseStep 1088699 = 1633049) B1633049
theorem B1088759 : Blo 722323 1088759 := bstep (se 1 (by rfl) ⟨816569, by rfl⟩ : syracuseStep 1088759 = 1633139) B1633139
theorem B1088783 : Blo 722323 1088783 := bstep (se 1 (by rfl) ⟨816587, by rfl⟩ : syracuseStep 1088783 = 1633175) B1633175
theorem B1088825 : Blo 722323 1088825 := bstep (se 2 (by rfl) ⟨408309, by rfl⟩ : syracuseStep 1088825 = 816619) B816619
theorem B1088903 : Blo 722323 1088903 := bstep (se 1 (by rfl) ⟨816677, by rfl⟩ : syracuseStep 1088903 = 1633355) B1633355
theorem B1088939 : Blo 722323 1088939 := bstep (se 1 (by rfl) ⟨816704, by rfl⟩ : syracuseStep 1088939 = 1633409) B1633409
theorem B1088969 : Blo 722323 1088969 := bstep (se 2 (by rfl) ⟨408363, by rfl⟩ : syracuseStep 1088969 = 816727) B816727
theorem B4955651 : Blo 722323 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B1089083 : Blo 722323 1089083 := bstep (se 1 (by rfl) ⟨816812, by rfl⟩ : syracuseStep 1089083 = 1633625) B1633625
theorem B1089143 : Blo 722323 1089143 := bstep (se 1 (by rfl) ⟨816857, by rfl⟩ : syracuseStep 1089143 = 1633715) B1633715
theorem B1220231 : Blo 722323 1220231 := bstep (se 1 (by rfl) ⟨915173, by rfl⟩ : syracuseStep 1220231 = 1830347) B1830347
theorem B1089167 : Blo 722323 1089167 := bstep (se 1 (by rfl) ⟨816875, by rfl⟩ : syracuseStep 1089167 = 1633751) B1633751
theorem B1089209 : Blo 722323 1089209 := bstep (se 2 (by rfl) ⟨408453, by rfl⟩ : syracuseStep 1089209 = 816907) B816907
theorem B2793217 : Blo 722323 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1089287 : Blo 722323 1089287 := bstep (se 1 (by rfl) ⟨816965, by rfl⟩ : syracuseStep 1089287 = 1633931) B1633931
theorem B1548047 : Blo 722323 1548047 := bstep (se 1 (by rfl) ⟨1161035, by rfl⟩ : syracuseStep 1548047 = 2322071) B2322071
theorem B1089323 : Blo 722323 1089323 := bstep (se 1 (by rfl) ⟨816992, by rfl⟩ : syracuseStep 1089323 = 1633985) B1633985
theorem B1089353 : Blo 722323 1089353 := bstep (se 2 (by rfl) ⟨408507, by rfl⟩ : syracuseStep 1089353 = 817015) B817015
theorem B1089467 : Blo 722323 1089467 := bstep (se 1 (by rfl) ⟨817100, by rfl⟩ : syracuseStep 1089467 = 1634201) B1634201
theorem B1220879 : Blo 722323 1220879 := bstep (se 1 (by rfl) ⟨915659, by rfl⟩ : syracuseStep 1220879 = 1831319) B1831319
theorem B6201785 : Blo 722323 6201785 := bstep (se 2 (by rfl) ⟨2325669, by rfl⟩ : syracuseStep 6201785 = 4651339) B4651339
theorem B1221419 : Blo 722323 1221419 := bstep (se 1 (by rfl) ⟨916064, by rfl⟩ : syracuseStep 1221419 = 1832129) B1832129
theorem B762895 : Blo 722323 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B1221817 : Blo 722323 1221817 := bstep (se 2 (by rfl) ⟨458181, by rfl⟩ : syracuseStep 1221817 = 916363) B916363
theorem B2204873 : Blo 722323 2204873 := bstep (se 2 (by rfl) ⟨826827, by rfl⟩ : syracuseStep 2204873 = 1653655) B1653655
theorem B1549687 : Blo 722323 1549687 := bstep (se 1 (by rfl) ⟨1162265, by rfl⟩ : syracuseStep 1549687 = 2324531) B2324531
theorem B3908999 : Blo 722323 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B5514641 : Blo 722323 5514641 := bstep (se 2 (by rfl) ⟨2067990, by rfl⟩ : syracuseStep 5514641 = 4135981) B4135981
theorem B8791843 : Blo 722323 8791843 := bstep (se 1 (by rfl) ⟨6593882, by rfl⟩ : syracuseStep 8791843 = 13187765) B13187765
theorem B1222519 : Blo 722323 1222519 := bstep (se 1 (by rfl) ⟨916889, by rfl⟩ : syracuseStep 1222519 = 1833779) B1833779
theorem B1222715 : Blo 722323 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1321145 : Blo 722323 1321145 := bstep (se 2 (by rfl) ⟨495429, by rfl⟩ : syracuseStep 1321145 = 990859) B990859
theorem B1223113 : Blo 722323 1223113 := bstep (se 2 (by rfl) ⟨458667, by rfl⟩ : syracuseStep 1223113 = 917335) B917335
theorem B8268317 : Blo 722323 8268317 := bstep (se 3 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 8268317 = 3100619) B3100619
theorem B9055091 : Blo 722323 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B1223815 : Blo 722323 1223815 := bstep (se 1 (by rfl) ⟨917861, by rfl⟩ : syracuseStep 1223815 = 1835723) B1835723
theorem B3910949 : Blo 722323 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B27831761 : Blo 722323 27831761 := bstep (se 2 (by rfl) ⟨10436910, by rfl⟩ : syracuseStep 27831761 = 20873821) B20873821
theorem B1224463 : Blo 722323 1224463 := bstep (se 1 (by rfl) ⟨918347, by rfl⟩ : syracuseStep 1224463 = 1836695) B1836695
theorem B1225003 : Blo 722323 1225003 := bstep (se 1 (by rfl) ⟨918752, by rfl⟩ : syracuseStep 1225003 = 1837505) B1837505
theorem B733583 : Blo 722323 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B1225145 : Blo 722323 1225145 := bstep (se 2 (by rfl) ⟨459429, by rfl⟩ : syracuseStep 1225145 = 918859) B918859
theorem B17609177 : Blo 722323 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B8794817 : Blo 722323 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B7418699 : Blo 722323 7418699 := bstep (se 1 (by rfl) ⟨5564024, by rfl⟩ : syracuseStep 7418699 = 11128049) B11128049
theorem B6960401 : Blo 722323 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B3487121 : Blo 722323 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B2438585 : Blo 722323 2438585 := bstep (se 2 (by rfl) ⟨914469, by rfl⟩ : syracuseStep 2438585 = 1828939) B1828939
theorem B1160747 : Blo 722323 1160747 := bstep (se 1 (by rfl) ⟨870560, by rfl⟩ : syracuseStep 1160747 = 1741121) B1741121
theorem B2439179 : Blo 722323 2439179 := bstep (se 1 (by rfl) ⟨1829384, by rfl⟩ : syracuseStep 2439179 = 3658769) B3658769
theorem B2439287 : Blo 722323 2439287 := bstep (se 1 (by rfl) ⟨1829465, by rfl⟩ : syracuseStep 2439287 = 3658931) B3658931
theorem B1030601 : Blo 722323 1030601 := bstep (se 2 (by rfl) ⟨386475, by rfl⟩ : syracuseStep 1030601 = 772951) B772951
theorem B11123243 : Blo 722323 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B2439881 : Blo 722323 2439881 := bstep (se 2 (by rfl) ⟨914955, by rfl⟩ : syracuseStep 2439881 = 1829911) B1829911
theorem B8272691 : Blo 722323 8272691 := bstep (se 1 (by rfl) ⟨6204518, by rfl⟩ : syracuseStep 8272691 = 12409037) B12409037
theorem B1162169 : Blo 722323 1162169 := bstep (se 2 (by rfl) ⟨435813, by rfl⟩ : syracuseStep 1162169 = 871627) B871627
theorem B2931913 : Blo 722323 2931913 := bstep (se 2 (by rfl) ⟨1099467, by rfl⟩ : syracuseStep 2931913 = 2198935) B2198935
theorem B2604269 : Blo 722323 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B2473217 : Blo 722323 2473217 := bstep (se 2 (by rfl) ⟨927456, by rfl⟩ : syracuseStep 2473217 = 1854913) B1854913
theorem B1031467 : Blo 722323 1031467 := bstep (se 1 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 1031467 = 1547201) B1547201
theorem B2440583 : Blo 722323 2440583 := bstep (se 1 (by rfl) ⟨1830437, by rfl⟩ : syracuseStep 2440583 = 3660875) B3660875
theorem B2440961 : Blo 722323 2440961 := bstep (se 2 (by rfl) ⟨915360, by rfl⟩ : syracuseStep 2440961 = 1830721) B1830721
theorem B1032583 : Blo 722323 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B2933177 : Blo 722323 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B2441771 : Blo 722323 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B5227051 : Blo 722323 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B3916525 : Blo 722323 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B869239 : Blo 722323 869239 := bstep (se 1 (by rfl) ⟨651929, by rfl⟩ : syracuseStep 869239 = 1303859) B1303859
theorem B8242073 : Blo 722323 8242073 := bstep (se 2 (by rfl) ⟨3090777, by rfl⟩ : syracuseStep 8242073 = 6181555) B6181555
theorem B869435 : Blo 722323 869435 := bstep (se 1 (by rfl) ⟨652076, by rfl⟩ : syracuseStep 869435 = 1304153) B1304153
theorem B1492115 : Blo 722323 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B1033403 : Blo 722323 1033403 := bstep (se 1 (by rfl) ⟨775052, by rfl⟩ : syracuseStep 1033403 = 1550105) B1550105
theorem B3097871 : Blo 722323 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B2115001 : Blo 722323 2115001 := bstep (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) B1586251
theorem B31409693 : Blo 722323 31409693 := bstep (se 3 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 31409693 = 11778635) B11778635
theorem B1394209 : Blo 722323 1394209 := bstep (se 2 (by rfl) ⟨522828, by rfl⟩ : syracuseStep 1394209 = 1045657) B1045657
theorem B1034041 : Blo 722323 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B2443067 : Blo 722323 2443067 := bstep (se 1 (by rfl) ⟨1832300, by rfl⟩ : syracuseStep 2443067 = 3664601) B3664601
theorem B1034155 : Blo 722323 1034155 := bstep (se 1 (by rfl) ⟨775616, by rfl⟩ : syracuseStep 1034155 = 1551233) B1551233
theorem B4114385 : Blo 722323 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B1099919 : Blo 722323 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B2443553 : Blo 722323 2443553 := bstep (se 2 (by rfl) ⟨916332, by rfl⟩ : syracuseStep 2443553 = 1832665) B1832665
theorem B871031 : Blo 722323 871031 := bstep (se 1 (by rfl) ⟨653273, by rfl⟩ : syracuseStep 871031 = 1306547) B1306547
theorem B9423479 : Blo 722323 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B3296015 : Blo 722323 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B2444147 : Blo 722323 2444147 := bstep (se 1 (by rfl) ⟨1833110, by rfl⟩ : syracuseStep 2444147 = 3666221) B3666221
theorem B871339 : Blo 722323 871339 := bstep (se 1 (by rfl) ⟨653504, by rfl⟩ : syracuseStep 871339 = 1307009) B1307009
theorem B5491799 : Blo 722323 5491799 := bstep (se 1 (by rfl) ⟨4118849, by rfl⟩ : syracuseStep 5491799 = 8237699) B8237699
theorem B1789015 : Blo 722323 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B1625273 : Blo 722323 1625273 := bstep (se 2 (by rfl) ⟨609477, by rfl⟩ : syracuseStep 1625273 = 1218955) B1218955
theorem B871723 : Blo 722323 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B2608537 : Blo 722323 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B871867 : Blo 722323 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B1625615 : Blo 722323 1625615 := bstep (se 1 (by rfl) ⟨1219211, by rfl⟩ : syracuseStep 1625615 = 2438423) B2438423
theorem B1625633 : Blo 722323 1625633 := bstep (se 2 (by rfl) ⟨609612, by rfl⟩ : syracuseStep 1625633 = 1219225) B1219225
theorem B2936407 : Blo 722323 2936407 := bstep (se 1 (by rfl) ⟨2202305, by rfl⟩ : syracuseStep 2936407 = 4404611) B4404611
theorem B4640449 : Blo 722323 4640449 := bstep (se 2 (by rfl) ⟨1740168, by rfl⟩ : syracuseStep 4640449 = 3480337) B3480337
theorem B3919553 : Blo 722323 3919553 := bstep (se 2 (by rfl) ⟨1469832, by rfl⟩ : syracuseStep 3919553 = 2939665) B2939665
theorem B3657473 : Blo 722323 3657473 := bstep (se 2 (by rfl) ⟨1371552, by rfl⟩ : syracuseStep 3657473 = 2743105) B2743105
theorem B9260851 : Blo 722323 9260851 := bstep (se 1 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 9260851 = 13891277) B13891277
theorem B1625975 : Blo 722323 1625975 := bstep (se 1 (by rfl) ⟨1219481, by rfl⟩ : syracuseStep 1625975 = 2438963) B2438963
theorem B8376331 : Blo 722323 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B1626155 : Blo 722323 1626155 := bstep (se 1 (by rfl) ⟨1219616, by rfl⟩ : syracuseStep 1626155 = 2439233) B2439233
theorem B3920243 : Blo 722323 3920243 := bstep (se 1 (by rfl) ⟨2940182, by rfl⟩ : syracuseStep 3920243 = 5880365) B5880365
theorem B1626515 : Blo 722323 1626515 := bstep (se 1 (by rfl) ⟨1219886, by rfl⟩ : syracuseStep 1626515 = 2439773) B2439773
theorem B1626569 : Blo 722323 1626569 := bstep (se 2 (by rfl) ⟨609963, by rfl⟩ : syracuseStep 1626569 = 1219927) B1219927
theorem B7066061 : Blo 722323 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B3658283 : Blo 722323 3658283 := bstep (se 1 (by rfl) ⟨2743712, by rfl⟩ : syracuseStep 3658283 = 5487425) B5487425
theorem B3101303 : Blo 722323 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B1954457 : Blo 722323 1954457 := bstep (se 2 (by rfl) ⟨732921, by rfl⟩ : syracuseStep 1954457 = 1465843) B1465843
theorem B2609921 : Blo 722323 2609921 := bstep (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) B1957441
theorem B25416791 : Blo 722323 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B1627271 : Blo 722323 1627271 := bstep (se 1 (by rfl) ⟨1220453, by rfl⟩ : syracuseStep 1627271 = 2440907) B2440907
theorem B2610413 : Blo 722323 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B1627451 : Blo 722323 1627451 := bstep (se 1 (by rfl) ⟨1220588, by rfl⟩ : syracuseStep 1627451 = 2441177) B2441177
theorem B5363003 : Blo 722323 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B2446739 : Blo 722323 2446739 := bstep (se 1 (by rfl) ⟨1835054, by rfl⟩ : syracuseStep 2446739 = 3670109) B3670109
theorem B1627577 : Blo 722323 1627577 := bstep (se 2 (by rfl) ⟨610341, by rfl⟩ : syracuseStep 1627577 = 1220683) B1220683
theorem B6968861 : Blo 722323 6968861 := bstep (se 3 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 6968861 = 2613323) B2613323
theorem B1627919 : Blo 722323 1627919 := bstep (se 1 (by rfl) ⟨1220939, by rfl⟩ : syracuseStep 1627919 = 2441879) B2441879
theorem B1627937 : Blo 722323 1627937 := bstep (se 2 (by rfl) ⟨610476, by rfl⟩ : syracuseStep 1627937 = 1220953) B1220953
theorem B3659579 : Blo 722323 3659579 := bstep (se 1 (by rfl) ⟨2744684, by rfl⟩ : syracuseStep 3659579 = 5489369) B5489369
theorem B27121483 : Blo 722323 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B3659741 : Blo 722323 3659741 := bstep (se 3 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 3659741 = 1372403) B1372403
theorem B1628279 : Blo 722323 1628279 := bstep (se 1 (by rfl) ⟨1221209, by rfl⟩ : syracuseStep 1628279 = 2442419) B2442419
theorem B9296117 : Blo 722323 9296117 := bstep (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) B871511
theorem B3660065 : Blo 722323 3660065 := bstep (se 2 (by rfl) ⟨1372524, by rfl⟩ : syracuseStep 3660065 = 2745049) B2745049
theorem B1628459 : Blo 722323 1628459 := bstep (se 1 (by rfl) ⟨1221344, by rfl⟩ : syracuseStep 1628459 = 2442689) B2442689
theorem B1628819 : Blo 722323 1628819 := bstep (se 1 (by rfl) ⟨1221614, by rfl⟩ : syracuseStep 1628819 = 2443229) B2443229
theorem B1628873 : Blo 722323 1628873 := bstep (se 2 (by rfl) ⟨610827, by rfl⟩ : syracuseStep 1628873 = 1221655) B1221655
theorem B2448143 : Blo 722323 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B5233423 : Blo 722323 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B1006409 : Blo 722323 1006409 := bstep (se 2 (by rfl) ⟨377403, by rfl⟩ : syracuseStep 1006409 = 754807) B754807
theorem B4119443 : Blo 722323 4119443 := bstep (se 1 (by rfl) ⟨3089582, by rfl⟩ : syracuseStep 4119443 = 6179165) B6179165
theorem B2448413 : Blo 722323 2448413 := bstep (se 3 (by rfl) ⟨459077, by rfl⟩ : syracuseStep 2448413 = 918155) B918155
theorem B2317355 : Blo 722323 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B3661037 : Blo 722323 3661037 := bstep (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) B1372889
theorem B4119943 : Blo 722323 4119943 := bstep (se 1 (by rfl) ⟨3089957, by rfl⟩ : syracuseStep 4119943 = 6179915) B6179915
theorem B1629575 : Blo 722323 1629575 := bstep (se 1 (by rfl) ⟨1222181, by rfl⟩ : syracuseStep 1629575 = 2444363) B2444363
theorem B1957267 : Blo 722323 1957267 := bstep (se 1 (by rfl) ⟨1467950, by rfl⟩ : syracuseStep 1957267 = 2935901) B2935901
theorem B5234141 : Blo 722323 5234141 := bstep (se 3 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 5234141 = 1962803) B1962803
theorem B16080413 : Blo 722323 16080413 := bstep (se 3 (by rfl) ⟨3015077, by rfl⟩ : syracuseStep 16080413 = 6030155) B6030155
theorem B1629755 : Blo 722323 1629755 := bstep (se 1 (by rfl) ⟨1222316, by rfl⟩ : syracuseStep 1629755 = 2444633) B2444633
theorem B8805955 : Blo 722323 8805955 := bstep (se 1 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 8805955 = 13208933) B13208933
theorem B2743895 : Blo 722323 2743895 := bstep (se 1 (by rfl) ⟨2057921, by rfl⟩ : syracuseStep 2743895 = 4115843) B4115843
theorem B1629881 : Blo 722323 1629881 := bstep (se 2 (by rfl) ⟨611205, by rfl⟩ : syracuseStep 1629881 = 1222411) B1222411
theorem B1630223 : Blo 722323 1630223 := bstep (se 1 (by rfl) ⟨1222667, by rfl⟩ : syracuseStep 1630223 = 2445335) B2445335
theorem B3661847 : Blo 722323 3661847 := bstep (se 1 (by rfl) ⟨2746385, by rfl⟩ : syracuseStep 3661847 = 5492771) B5492771
theorem B1630241 : Blo 722323 1630241 := bstep (se 2 (by rfl) ⟨611340, by rfl⟩ : syracuseStep 1630241 = 1222681) B1222681
theorem B2744381 : Blo 722323 2744381 := bstep (se 3 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 2744381 = 1029143) B1029143
theorem B27910493 : Blo 722323 27910493 := bstep (se 3 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 27910493 = 10466435) B10466435
theorem B1630583 : Blo 722323 1630583 := bstep (se 1 (by rfl) ⟨1222937, by rfl⟩ : syracuseStep 1630583 = 2445875) B2445875
theorem B2449817 : Blo 722323 2449817 := bstep (se 2 (by rfl) ⟨918681, by rfl⟩ : syracuseStep 2449817 = 1837363) B1837363
theorem B5300765 : Blo 722323 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B1630763 : Blo 722323 1630763 := bstep (se 1 (by rfl) ⟨1223072, by rfl⟩ : syracuseStep 1630763 = 2446145) B2446145
theorem B1631123 : Blo 722323 1631123 := bstep (se 1 (by rfl) ⟨1223342, by rfl⟩ : syracuseStep 1631123 = 2446685) B2446685
theorem B1631177 : Blo 722323 1631177 := bstep (se 2 (by rfl) ⟨611691, by rfl⟩ : syracuseStep 1631177 = 1223383) B1223383
theorem B2450519 : Blo 722323 2450519 := bstep (se 1 (by rfl) ⟨1837889, by rfl⟩ : syracuseStep 2450519 = 3675779) B3675779
theorem B2057501 : Blo 722323 2057501 := bstep (se 3 (by rfl) ⟨385781, by rfl⟩ : syracuseStep 2057501 = 771563) B771563
theorem B2745809 : Blo 722323 2745809 := bstep (se 2 (by rfl) ⟨1029678, by rfl⟩ : syracuseStep 2745809 = 2059357) B2059357
theorem B1238543 : Blo 722323 1238543 := bstep (se 1 (by rfl) ⟨928907, by rfl⟩ : syracuseStep 1238543 = 1857815) B1857815
theorem B1467919 : Blo 722323 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B2451005 : Blo 722323 2451005 := bstep (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) B919127
theorem B1631879 : Blo 722323 1631879 := bstep (se 1 (by rfl) ⟨1223909, by rfl⟩ : syracuseStep 1631879 = 2447819) B2447819
theorem B812731 : Blo 722323 812731 := bstep (se 1 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 812731 = 1219097) B1219097
theorem B976699 : Blo 722323 976699 := bstep (se 1 (by rfl) ⟨732524, by rfl⟩ : syracuseStep 976699 = 1465049) B1465049
theorem B1632059 : Blo 722323 1632059 := bstep (se 1 (by rfl) ⟨1224044, by rfl⟩ : syracuseStep 1632059 = 2448089) B2448089
theorem B1959767 : Blo 722323 1959767 := bstep (se 1 (by rfl) ⟨1469825, by rfl⟩ : syracuseStep 1959767 = 2939651) B2939651
theorem B1828727 : Blo 722323 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B3532679 : Blo 722323 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B1632185 : Blo 722323 1632185 := bstep (se 2 (by rfl) ⟨612069, by rfl⟩ : syracuseStep 1632185 = 1224139) B1224139
theorem B2615225 : Blo 722323 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B11724917 : Blo 722323 11724917 := bstep (se 5 (by rfl) ⟨549605, by rfl⟩ : syracuseStep 11724917 = 1099211) B1099211
theorem B813199 : Blo 722323 813199 := bstep (se 1 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 813199 = 1219799) B1219799
theorem B1239241 : Blo 722323 1239241 := bstep (se 2 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 1239241 = 929431) B929431
theorem B13920497 : Blo 722323 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B1632527 : Blo 722323 1632527 := bstep (se 1 (by rfl) ⟨1224395, by rfl⟩ : syracuseStep 1632527 = 2448791) B2448791
theorem B1632545 : Blo 722323 1632545 := bstep (se 2 (by rfl) ⟨612204, by rfl⟩ : syracuseStep 1632545 = 1224409) B1224409
theorem B17885731 : Blo 722323 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B1632887 : Blo 722323 1632887 := bstep (se 1 (by rfl) ⟨1224665, by rfl⟩ : syracuseStep 1632887 = 2449331) B2449331
theorem B813703 : Blo 722323 813703 := bstep (se 1 (by rfl) ⟨610277, by rfl⟩ : syracuseStep 813703 = 1220555) B1220555
theorem B7269041 : Blo 722323 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B1043129 : Blo 722323 1043129 := bstep (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) B782347
theorem B1633067 : Blo 722323 1633067 := bstep (se 1 (by rfl) ⟨1224800, by rfl⟩ : syracuseStep 1633067 = 2449601) B2449601
theorem B813883 : Blo 722323 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B41806691 : Blo 722323 41806691 := bstep (se 1 (by rfl) ⟨31355018, by rfl⟩ : syracuseStep 41806691 = 62710037) B62710037
theorem B3664925 : Blo 722323 3664925 := bstep (se 3 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 3664925 = 1374347) B1374347
theorem B2747479 : Blo 722323 2747479 := bstep (se 1 (by rfl) ⟨2060609, by rfl⟩ : syracuseStep 2747479 = 4121219) B4121219
theorem B1830023 : Blo 722323 1830023 := bstep (se 1 (by rfl) ⟨1372517, by rfl⟩ : syracuseStep 1830023 = 2745035) B2745035
theorem B1633427 : Blo 722323 1633427 := bstep (se 1 (by rfl) ⟨1225070, by rfl⟩ : syracuseStep 1633427 = 2450141) B2450141
theorem B1830073 : Blo 722323 1830073 := bstep (se 2 (by rfl) ⟨686277, by rfl⟩ : syracuseStep 1830073 = 1372555) B1372555
theorem B1633481 : Blo 722323 1633481 := bstep (se 2 (by rfl) ⟨612555, by rfl⟩ : syracuseStep 1633481 = 1225111) B1225111
theorem B814351 : Blo 722323 814351 := bstep (se 1 (by rfl) ⟨610763, by rfl⟩ : syracuseStep 814351 = 1221527) B1221527
theorem B2321723 : Blo 722323 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B2059607 : Blo 722323 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B2747783 : Blo 722323 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B2682247 : Blo 722323 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B1306057 : Blo 722323 1306057 := bstep (se 2 (by rfl) ⟨489771, by rfl⟩ : syracuseStep 1306057 = 979543) B979543
theorem B2616785 : Blo 722323 2616785 := bstep (se 2 (by rfl) ⟨981294, by rfl⟩ : syracuseStep 2616785 = 1962589) B1962589
theorem B3665411 : Blo 722323 3665411 := bstep (se 1 (by rfl) ⟨2749058, by rfl⟩ : syracuseStep 3665411 = 5498117) B5498117
theorem B2747965 : Blo 722323 2747965 := bstep (se 3 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 2747965 = 1030487) B1030487
theorem B7958083 : Blo 722323 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B6188663 : Blo 722323 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B814855 : Blo 722323 814855 := bstep (se 1 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 814855 = 1222283) B1222283
theorem B1830671 : Blo 722323 1830671 := bstep (se 1 (by rfl) ⟨1373003, by rfl⟩ : syracuseStep 1830671 = 2746007) B2746007
theorem B1634183 : Blo 722323 1634183 := bstep (se 1 (by rfl) ⟨1225637, by rfl⟩ : syracuseStep 1634183 = 2451275) B2451275
theorem B815035 : Blo 722323 815035 := bstep (se 1 (by rfl) ⟨611276, by rfl⟩ : syracuseStep 815035 = 1222553) B1222553
theorem B45117461 : Blo 722323 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B2256925 : Blo 722323 2256925 := bstep (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) B846347
theorem B1470611 : Blo 722323 1470611 := bstep (se 1 (by rfl) ⟨1102958, by rfl⟩ : syracuseStep 1470611 = 2205917) B2205917
theorem B2060473 : Blo 722323 2060473 := bstep (se 2 (by rfl) ⟨772677, by rfl⟩ : syracuseStep 2060473 = 1545355) B1545355
theorem B815503 : Blo 722323 815503 := bstep (se 1 (by rfl) ⟨611627, by rfl⟩ : syracuseStep 815503 = 1223255) B1223255
theorem B1372601 : Blo 722323 1372601 := bstep (se 2 (by rfl) ⟨514725, by rfl⟩ : syracuseStep 1372601 = 1029451) B1029451
theorem B1831369 : Blo 722323 1831369 := bstep (se 2 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 1831369 = 1373527) B1373527
theorem B2060815 : Blo 722323 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B1831511 : Blo 722323 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B1372943 : Blo 722323 1372943 := bstep (se 1 (by rfl) ⟨1029707, by rfl⟩ : syracuseStep 1372943 = 2059415) B2059415
theorem B2061089 : Blo 722323 2061089 := bstep (se 2 (by rfl) ⟨772908, by rfl⟩ : syracuseStep 2061089 = 1545817) B1545817
theorem B6615857 : Blo 722323 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B816007 : Blo 722323 816007 := bstep (se 1 (by rfl) ⟨612005, by rfl⟩ : syracuseStep 816007 = 1224011) B1224011
theorem B4125593 : Blo 722323 4125593 := bstep (se 2 (by rfl) ⟨1547097, by rfl⟩ : syracuseStep 4125593 = 3094195) B3094195
theorem B14873507 : Blo 722323 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B4650007 : Blo 722323 4650007 := bstep (se 1 (by rfl) ⟨3487505, by rfl⟩ : syracuseStep 4650007 = 6975011) B6975011
theorem B3142685 : Blo 722323 3142685 := bstep (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) B1178507
theorem B3306539 : Blo 722323 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B816187 : Blo 722323 816187 := bstep (se 1 (by rfl) ⟨612140, by rfl⟩ : syracuseStep 816187 = 1224281) B1224281
theorem B3667031 : Blo 722323 3667031 := bstep (se 1 (by rfl) ⟨2750273, by rfl⟩ : syracuseStep 3667031 = 5500547) B5500547
theorem B2979017 : Blo 722323 2979017 := bstep (se 2 (by rfl) ⟨1117131, by rfl⟩ : syracuseStep 2979017 = 2234263) B2234263
theorem B2749697 : Blo 722323 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B2061703 : Blo 722323 2061703 := bstep (se 1 (by rfl) ⟨1546277, by rfl⟩ : syracuseStep 2061703 = 3092555) B3092555
theorem B816655 : Blo 722323 816655 := bstep (se 1 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 816655 = 1224983) B1224983
theorem B1373755 : Blo 722323 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B3667517 : Blo 722323 3667517 := bstep (se 3 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 3667517 = 1375319) B1375319
theorem B1373831 : Blo 722323 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B7534259 : Blo 722323 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B1472185 : Blo 722323 1472185 := bstep (se 2 (by rfl) ⟨552069, by rfl⟩ : syracuseStep 1472185 = 1104139) B1104139
theorem B2062091 : Blo 722323 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B14907185 : Blo 722323 14907185 := bstep (se 2 (by rfl) ⟨5590194, by rfl⟩ : syracuseStep 14907185 = 11180389) B11180389
theorem B980921 : Blo 722323 980921 := bstep (se 2 (by rfl) ⟨367845, by rfl⟩ : syracuseStep 980921 = 735691) B735691
theorem B1374241 : Blo 722323 1374241 := bstep (se 2 (by rfl) ⟨515340, by rfl⟩ : syracuseStep 1374241 = 1030681) B1030681
theorem B3962947 : Blo 722323 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B1374583 : Blo 722323 1374583 := bstep (se 1 (by rfl) ⟨1030937, by rfl⟩ : syracuseStep 1374583 = 2061875) B2061875
theorem B2750867 : Blo 722323 2750867 := bstep (se 1 (by rfl) ⟨2063150, by rfl⟩ : syracuseStep 2750867 = 4126301) B4126301
theorem B1833587 : Blo 722323 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B916267 : Blo 722323 916267 := bstep (se 1 (by rfl) ⟨687200, by rfl⟩ : syracuseStep 916267 = 1374401) B1374401
theorem B2751367 : Blo 722323 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B1735681 : Blo 722323 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B1506319 : Blo 722323 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B2063389 : Blo 722323 2063389 := bstep (se 3 (by rfl) ⟨386885, by rfl⟩ : syracuseStep 2063389 = 773771) B773771
theorem B1735739 : Blo 722323 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B1834103 : Blo 722323 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B3669299 : Blo 722323 3669299 := bstep (se 1 (by rfl) ⟨2751974, by rfl⟩ : syracuseStep 3669299 = 5503949) B5503949
theorem B2063731 : Blo 722323 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B9305549 : Blo 722323 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B3964439 : Blo 722323 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B3669623 : Blo 722323 3669623 := bstep (se 1 (by rfl) ⟨2752217, by rfl⟩ : syracuseStep 3669623 = 5504435) B5504435
theorem B917239 : Blo 722323 917239 := bstep (se 1 (by rfl) ⟨687929, by rfl⟩ : syracuseStep 917239 = 1375859) B1375859
theorem B67927853 : Blo 722323 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B5504921 : Blo 722323 5504921 := bstep (se 2 (by rfl) ⟨2064345, by rfl⟩ : syracuseStep 5504921 = 4128691) B4128691
theorem B1736633 : Blo 722323 1736633 := bstep (se 2 (by rfl) ⟨651237, by rfl⟩ : syracuseStep 1736633 = 1302475) B1302475
theorem B1376185 : Blo 722323 1376185 := bstep (se 2 (by rfl) ⟨516069, by rfl⟩ : syracuseStep 1376185 = 1032139) B1032139
theorem B1835369 : Blo 722323 1835369 := bstep (se 2 (by rfl) ⟨688263, by rfl⟩ : syracuseStep 1835369 = 1376527) B1376527
theorem B1376777 : Blo 722323 1376777 := bstep (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) B1032583
theorem B9273973 : Blo 722323 9273973 := bstep (se 5 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 9273973 = 869435) B869435
theorem B2065247 : Blo 722323 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B3474359 : Blo 722323 3474359 := bstep (se 1 (by rfl) ⟨2605769, by rfl⟩ : syracuseStep 3474359 = 5211539) B5211539
theorem B10453981 : Blo 722323 10453981 := bstep (se 3 (by rfl) ⟨1960121, by rfl⟩ : syracuseStep 10453981 = 3920243) B3920243
theorem B20939795 : Blo 722323 20939795 := bstep (se 1 (by rfl) ⟨15704846, by rfl⟩ : syracuseStep 20939795 = 31409693) B31409693
theorem B2753615 : Blo 722323 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B3671243 : Blo 722323 3671243 := bstep (se 1 (by rfl) ⟨2753432, by rfl⟩ : syracuseStep 3671243 = 5506865) B5506865
theorem B2753783 : Blo 722323 2753783 := bstep (se 1 (by rfl) ⟨2065337, by rfl⟩ : syracuseStep 2753783 = 4130675) B4130675
theorem B2983229 : Blo 722323 2983229 := bstep (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) B1118711
theorem B1017193 : Blo 722323 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B1377643 : Blo 722323 1377643 := bstep (se 1 (by rfl) ⟨1033232, by rfl⟩ : syracuseStep 1377643 = 2066465) B2066465
theorem B722351 : Blo 722323 722351 := bstep (se 1 (by rfl) ⟨541763, by rfl⟩ : syracuseStep 722351 = 1083527) B1083527
theorem B1377719 : Blo 722323 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B722375 : Blo 722323 722375 := bstep (se 1 (by rfl) ⟨541781, by rfl⟩ : syracuseStep 722375 = 1083563) B1083563
theorem B722395 : Blo 722323 722395 := bstep (se 1 (by rfl) ⟨541796, by rfl⟩ : syracuseStep 722395 = 1083593) B1083593
theorem B1836553 : Blo 722323 1836553 := bstep (se 2 (by rfl) ⟨688707, by rfl⟩ : syracuseStep 1836553 = 1377415) B1377415
theorem B722471 : Blo 722323 722471 := bstep (se 1 (by rfl) ⟨541853, by rfl⟩ : syracuseStep 722471 = 1083707) B1083707
theorem B722511 : Blo 722323 722511 := bstep (se 1 (by rfl) ⟨541883, by rfl⟩ : syracuseStep 722511 = 1083767) B1083767
theorem B722527 : Blo 722323 722527 := bstep (se 1 (by rfl) ⟨541895, by rfl⟩ : syracuseStep 722527 = 1083791) B1083791
theorem B722555 : Blo 722323 722555 := bstep (se 1 (by rfl) ⟨541916, by rfl⟩ : syracuseStep 722555 = 1083833) B1083833
theorem B722607 : Blo 722323 722607 := bstep (se 1 (by rfl) ⟨541955, by rfl⟩ : syracuseStep 722607 = 1083911) B1083911
theorem B722631 : Blo 722323 722631 := bstep (se 1 (by rfl) ⟨541973, by rfl⟩ : syracuseStep 722631 = 1083947) B1083947
theorem B722651 : Blo 722323 722651 := bstep (se 1 (by rfl) ⟨541988, by rfl⟩ : syracuseStep 722651 = 1083977) B1083977
theorem B11142947 : Blo 722323 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B722727 : Blo 722323 722727 := bstep (se 1 (by rfl) ⟨542045, by rfl⟩ : syracuseStep 722727 = 1084091) B1084091
theorem B2066249 : Blo 722323 2066249 := bstep (se 2 (by rfl) ⟨774843, by rfl⟩ : syracuseStep 2066249 = 1549687) B1549687
theorem B722767 : Blo 722323 722767 := bstep (se 1 (by rfl) ⟨542075, by rfl⟩ : syracuseStep 722767 = 1084151) B1084151
theorem B2197343 : Blo 722323 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B722783 : Blo 722323 722783 := bstep (se 1 (by rfl) ⟨542087, by rfl⟩ : syracuseStep 722783 = 1084175) B1084175
theorem B722811 : Blo 722323 722811 := bstep (se 1 (by rfl) ⟨542108, by rfl⟩ : syracuseStep 722811 = 1084217) B1084217
theorem B722863 : Blo 722323 722863 := bstep (se 1 (by rfl) ⟨542147, by rfl⟩ : syracuseStep 722863 = 1084295) B1084295
theorem B1378235 : Blo 722323 1378235 := bstep (se 1 (by rfl) ⟨1033676, by rfl⟩ : syracuseStep 1378235 = 2067353) B2067353
theorem B722887 : Blo 722323 722887 := bstep (se 1 (by rfl) ⟨542165, by rfl⟩ : syracuseStep 722887 = 1084331) B1084331
theorem B722907 : Blo 722323 722907 := bstep (se 1 (by rfl) ⟨542180, by rfl⟩ : syracuseStep 722907 = 1084361) B1084361
theorem B722983 : Blo 722323 722983 := bstep (se 1 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 722983 = 1084475) B1084475
theorem B723023 : Blo 722323 723023 := bstep (se 1 (by rfl) ⟨542267, by rfl⟩ : syracuseStep 723023 = 1084535) B1084535
theorem B723039 : Blo 722323 723039 := bstep (se 1 (by rfl) ⟨542279, by rfl⟩ : syracuseStep 723039 = 1084559) B1084559
theorem B1083515 : Blo 722323 1083515 := bstep (se 1 (by rfl) ⟨812636, by rfl⟩ : syracuseStep 1083515 = 1625273) B1625273
theorem B723067 : Blo 722323 723067 := bstep (se 1 (by rfl) ⟨542300, by rfl⟩ : syracuseStep 723067 = 1084601) B1084601
theorem B723119 : Blo 722323 723119 := bstep (se 1 (by rfl) ⟨542339, by rfl⟩ : syracuseStep 723119 = 1084679) B1084679
theorem B2754755 : Blo 722323 2754755 := bstep (se 1 (by rfl) ⟨2066066, by rfl⟩ : syracuseStep 2754755 = 4132133) B4132133
theorem B723143 : Blo 722323 723143 := bstep (se 1 (by rfl) ⟨542357, by rfl⟩ : syracuseStep 723143 = 1084715) B1084715
theorem B723163 : Blo 722323 723163 := bstep (se 1 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 723163 = 1084745) B1084745
theorem B1083641 : Blo 722323 1083641 := bstep (se 2 (by rfl) ⟨406365, by rfl⟩ : syracuseStep 1083641 = 812731) B812731
theorem B723239 : Blo 722323 723239 := bstep (se 1 (by rfl) ⟨542429, by rfl⟩ : syracuseStep 723239 = 1084859) B1084859
theorem B723279 : Blo 722323 723279 := bstep (se 1 (by rfl) ⟨542459, by rfl⟩ : syracuseStep 723279 = 1084919) B1084919
theorem B1083743 : Blo 722323 1083743 := bstep (se 1 (by rfl) ⟨812807, by rfl⟩ : syracuseStep 1083743 = 1625615) B1625615
theorem B723295 : Blo 722323 723295 := bstep (se 1 (by rfl) ⟨542471, by rfl⟩ : syracuseStep 723295 = 1084943) B1084943
theorem B1083755 : Blo 722323 1083755 := bstep (se 1 (by rfl) ⟨812816, by rfl⟩ : syracuseStep 1083755 = 1625633) B1625633
theorem B723323 : Blo 722323 723323 := bstep (se 1 (by rfl) ⟨542492, by rfl⟩ : syracuseStep 723323 = 1084985) B1084985
theorem B1378721 : Blo 722323 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B723375 : Blo 722323 723375 := bstep (se 1 (by rfl) ⟨542531, by rfl⟩ : syracuseStep 723375 = 1085063) B1085063
theorem B723399 : Blo 722323 723399 := bstep (se 1 (by rfl) ⟨542549, by rfl⟩ : syracuseStep 723399 = 1085099) B1085099
theorem B723419 : Blo 722323 723419 := bstep (se 1 (by rfl) ⟨542564, by rfl⟩ : syracuseStep 723419 = 1085129) B1085129
theorem B723495 : Blo 722323 723495 := bstep (se 1 (by rfl) ⟨542621, by rfl⟩ : syracuseStep 723495 = 1085243) B1085243
theorem B1378873 : Blo 722323 1378873 := bstep (se 2 (by rfl) ⟨517077, by rfl⟩ : syracuseStep 1378873 = 1034155) B1034155
theorem B1083983 : Blo 722323 1083983 := bstep (se 1 (by rfl) ⟨812987, by rfl⟩ : syracuseStep 1083983 = 1625975) B1625975
theorem B723535 : Blo 722323 723535 := bstep (se 1 (by rfl) ⟨542651, by rfl⟩ : syracuseStep 723535 = 1085303) B1085303
theorem B723551 : Blo 722323 723551 := bstep (se 1 (by rfl) ⟨542663, by rfl⟩ : syracuseStep 723551 = 1085327) B1085327
theorem B723579 : Blo 722323 723579 := bstep (se 1 (by rfl) ⟨542684, by rfl⟩ : syracuseStep 723579 = 1085369) B1085369
theorem B723631 : Blo 722323 723631 := bstep (se 1 (by rfl) ⟨542723, by rfl⟩ : syracuseStep 723631 = 1085447) B1085447
theorem B1084103 : Blo 722323 1084103 := bstep (se 1 (by rfl) ⟨813077, by rfl⟩ : syracuseStep 1084103 = 1626155) B1626155
theorem B723655 : Blo 722323 723655 := bstep (se 1 (by rfl) ⟨542741, by rfl⟩ : syracuseStep 723655 = 1085483) B1085483
theorem B723675 : Blo 722323 723675 := bstep (se 1 (by rfl) ⟨542756, by rfl⟩ : syracuseStep 723675 = 1085513) B1085513
theorem B8817437 : Blo 722323 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B723751 : Blo 722323 723751 := bstep (se 1 (by rfl) ⟨542813, by rfl⟩ : syracuseStep 723751 = 1085627) B1085627
theorem B723791 : Blo 722323 723791 := bstep (se 1 (by rfl) ⟨542843, by rfl⟩ : syracuseStep 723791 = 1085687) B1085687
theorem B723807 : Blo 722323 723807 := bstep (se 1 (by rfl) ⟨542855, by rfl⟩ : syracuseStep 723807 = 1085711) B1085711
theorem B1084265 : Blo 722323 1084265 := bstep (se 2 (by rfl) ⟨406599, by rfl⟩ : syracuseStep 1084265 = 813199) B813199
theorem B723835 : Blo 722323 723835 := bstep (se 1 (by rfl) ⟨542876, by rfl⟩ : syracuseStep 723835 = 1085753) B1085753
theorem B723887 : Blo 722323 723887 := bstep (se 1 (by rfl) ⟨542915, by rfl⟩ : syracuseStep 723887 = 1085831) B1085831
theorem B1084343 : Blo 722323 1084343 := bstep (se 1 (by rfl) ⟨813257, by rfl⟩ : syracuseStep 1084343 = 1626515) B1626515
theorem B1838011 : Blo 722323 1838011 := bstep (se 1 (by rfl) ⟨1378508, by rfl⟩ : syracuseStep 1838011 = 2757017) B2757017
theorem B723911 : Blo 722323 723911 := bstep (se 1 (by rfl) ⟨542933, by rfl⟩ : syracuseStep 723911 = 1085867) B1085867
theorem B1084379 : Blo 722323 1084379 := bstep (se 1 (by rfl) ⟨813284, by rfl⟩ : syracuseStep 1084379 = 1626569) B1626569
theorem B723931 : Blo 722323 723931 := bstep (se 1 (by rfl) ⟨542948, by rfl⟩ : syracuseStep 723931 = 1085897) B1085897
theorem B724007 : Blo 722323 724007 := bstep (se 1 (by rfl) ⟨543005, by rfl⟩ : syracuseStep 724007 = 1086011) B1086011
theorem B724047 : Blo 722323 724047 := bstep (se 1 (by rfl) ⟨543035, by rfl⟩ : syracuseStep 724047 = 1086071) B1086071
theorem B2067535 : Blo 722323 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B724063 : Blo 722323 724063 := bstep (se 1 (by rfl) ⟨543047, by rfl⟩ : syracuseStep 724063 = 1086095) B1086095
theorem B724091 : Blo 722323 724091 := bstep (se 1 (by rfl) ⟨543068, by rfl⟩ : syracuseStep 724091 = 1086137) B1086137
theorem B2755741 : Blo 722323 2755741 := bstep (se 3 (by rfl) ⟨516701, by rfl⟩ : syracuseStep 2755741 = 1033403) B1033403
theorem B1739947 : Blo 722323 1739947 := bstep (se 1 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 1739947 = 2609921) B2609921
theorem B724143 : Blo 722323 724143 := bstep (se 1 (by rfl) ⟨543107, by rfl⟩ : syracuseStep 724143 = 1086215) B1086215
theorem B724167 : Blo 722323 724167 := bstep (se 1 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 724167 = 1086251) B1086251
theorem B724187 : Blo 722323 724187 := bstep (se 1 (by rfl) ⟨543140, by rfl⟩ : syracuseStep 724187 = 1086281) B1086281
theorem B724263 : Blo 722323 724263 := bstep (se 1 (by rfl) ⟨543197, by rfl⟩ : syracuseStep 724263 = 1086395) B1086395
theorem B724303 : Blo 722323 724303 := bstep (se 1 (by rfl) ⟨543227, by rfl⟩ : syracuseStep 724303 = 1086455) B1086455
theorem B724319 : Blo 722323 724319 := bstep (se 1 (by rfl) ⟨543239, by rfl⟩ : syracuseStep 724319 = 1086479) B1086479
theorem B724347 : Blo 722323 724347 := bstep (se 1 (by rfl) ⟨543260, by rfl⟩ : syracuseStep 724347 = 1086521) B1086521
theorem B2198909 : Blo 722323 2198909 := bstep (se 3 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 2198909 = 824591) B824591
theorem B16944527 : Blo 722323 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B1084847 : Blo 722323 1084847 := bstep (se 1 (by rfl) ⟨813635, by rfl⟩ : syracuseStep 1084847 = 1627271) B1627271
theorem B724399 : Blo 722323 724399 := bstep (se 1 (by rfl) ⟨543299, by rfl⟩ : syracuseStep 724399 = 1086599) B1086599
theorem B724423 : Blo 722323 724423 := bstep (se 1 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 724423 = 1086635) B1086635
theorem B724443 : Blo 722323 724443 := bstep (se 1 (by rfl) ⟨543332, by rfl⟩ : syracuseStep 724443 = 1086665) B1086665
theorem B1740275 : Blo 722323 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B1084937 : Blo 722323 1084937 := bstep (se 2 (by rfl) ⟨406851, by rfl⟩ : syracuseStep 1084937 = 813703) B813703
theorem B1084967 : Blo 722323 1084967 := bstep (se 1 (by rfl) ⟨813725, by rfl⟩ : syracuseStep 1084967 = 1627451) B1627451
theorem B3575335 : Blo 722323 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B724519 : Blo 722323 724519 := bstep (se 1 (by rfl) ⟨543389, by rfl⟩ : syracuseStep 724519 = 1086779) B1086779
theorem B724559 : Blo 722323 724559 := bstep (se 1 (by rfl) ⟨543419, by rfl⟩ : syracuseStep 724559 = 1086839) B1086839
theorem B724575 : Blo 722323 724575 := bstep (se 1 (by rfl) ⟨543431, by rfl⟩ : syracuseStep 724575 = 1086863) B1086863
theorem B1085051 : Blo 722323 1085051 := bstep (se 1 (by rfl) ⟨813788, by rfl⟩ : syracuseStep 1085051 = 1627577) B1627577
theorem B724603 : Blo 722323 724603 := bstep (se 1 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 724603 = 1086905) B1086905
theorem B724655 : Blo 722323 724655 := bstep (se 1 (by rfl) ⟨543491, by rfl⟩ : syracuseStep 724655 = 1086983) B1086983
theorem B724679 : Blo 722323 724679 := bstep (se 1 (by rfl) ⟨543509, by rfl⟩ : syracuseStep 724679 = 1087019) B1087019
theorem B724699 : Blo 722323 724699 := bstep (se 1 (by rfl) ⟨543524, by rfl⟩ : syracuseStep 724699 = 1087049) B1087049
theorem B1085177 : Blo 722323 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B724775 : Blo 722323 724775 := bstep (se 1 (by rfl) ⟨543581, by rfl⟩ : syracuseStep 724775 = 1087163) B1087163
theorem B724815 : Blo 722323 724815 := bstep (se 1 (by rfl) ⟨543611, by rfl⟩ : syracuseStep 724815 = 1087223) B1087223
theorem B1085279 : Blo 722323 1085279 := bstep (se 1 (by rfl) ⟨813959, by rfl⟩ : syracuseStep 1085279 = 1627919) B1627919
theorem B724831 : Blo 722323 724831 := bstep (se 1 (by rfl) ⟨543623, by rfl⟩ : syracuseStep 724831 = 1087247) B1087247
theorem B1085291 : Blo 722323 1085291 := bstep (se 1 (by rfl) ⟨813968, by rfl⟩ : syracuseStep 1085291 = 1627937) B1627937
theorem B724859 : Blo 722323 724859 := bstep (se 1 (by rfl) ⟨543644, by rfl⟩ : syracuseStep 724859 = 1087289) B1087289
theorem B724911 : Blo 722323 724911 := bstep (se 1 (by rfl) ⟨543683, by rfl⟩ : syracuseStep 724911 = 1087367) B1087367
theorem B724935 : Blo 722323 724935 := bstep (se 1 (by rfl) ⟨543701, by rfl⟩ : syracuseStep 724935 = 1087403) B1087403
theorem B724955 : Blo 722323 724955 := bstep (se 1 (by rfl) ⟨543716, by rfl⟩ : syracuseStep 724955 = 1087433) B1087433
theorem B725031 : Blo 722323 725031 := bstep (se 1 (by rfl) ⟨543773, by rfl⟩ : syracuseStep 725031 = 1087547) B1087547
theorem B1085519 : Blo 722323 1085519 := bstep (se 1 (by rfl) ⟨814139, by rfl⟩ : syracuseStep 1085519 = 1628279) B1628279
theorem B725071 : Blo 722323 725071 := bstep (se 1 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 725071 = 1087607) B1087607
theorem B725087 : Blo 722323 725087 := bstep (se 1 (by rfl) ⟨543815, by rfl⟩ : syracuseStep 725087 = 1087631) B1087631
theorem B725115 : Blo 722323 725115 := bstep (se 1 (by rfl) ⟨543836, by rfl⟩ : syracuseStep 725115 = 1087673) B1087673
theorem B6197411 : Blo 722323 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B725167 : Blo 722323 725167 := bstep (se 1 (by rfl) ⟨543875, by rfl⟩ : syracuseStep 725167 = 1087751) B1087751
theorem B1085639 : Blo 722323 1085639 := bstep (se 1 (by rfl) ⟨814229, by rfl⟩ : syracuseStep 1085639 = 1628459) B1628459
theorem B725191 : Blo 722323 725191 := bstep (se 1 (by rfl) ⟨543893, by rfl⟩ : syracuseStep 725191 = 1087787) B1087787
theorem B725211 : Blo 722323 725211 := bstep (se 1 (by rfl) ⟨543908, by rfl⟩ : syracuseStep 725211 = 1087817) B1087817
theorem B725287 : Blo 722323 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B725327 : Blo 722323 725327 := bstep (se 1 (by rfl) ⟨543995, by rfl⟩ : syracuseStep 725327 = 1087991) B1087991
theorem B725343 : Blo 722323 725343 := bstep (se 1 (by rfl) ⟨544007, by rfl⟩ : syracuseStep 725343 = 1088015) B1088015
theorem B1085801 : Blo 722323 1085801 := bstep (se 2 (by rfl) ⟨407175, by rfl⟩ : syracuseStep 1085801 = 814351) B814351
theorem B725371 : Blo 722323 725371 := bstep (se 1 (by rfl) ⟨544028, by rfl⟩ : syracuseStep 725371 = 1088057) B1088057
theorem B725423 : Blo 722323 725423 := bstep (se 1 (by rfl) ⟨544067, by rfl⟩ : syracuseStep 725423 = 1088135) B1088135
theorem B1085879 : Blo 722323 1085879 := bstep (se 1 (by rfl) ⟨814409, by rfl⟩ : syracuseStep 1085879 = 1628819) B1628819
theorem B725447 : Blo 722323 725447 := bstep (se 1 (by rfl) ⟨544085, by rfl⟩ : syracuseStep 725447 = 1088171) B1088171
theorem B1085915 : Blo 722323 1085915 := bstep (se 1 (by rfl) ⟨814436, by rfl⟩ : syracuseStep 1085915 = 1628873) B1628873
theorem B725467 : Blo 722323 725467 := bstep (se 1 (by rfl) ⟨544100, by rfl⟩ : syracuseStep 725467 = 1088201) B1088201
theorem B3576329 : Blo 722323 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B3478049 : Blo 722323 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B725543 : Blo 722323 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B725583 : Blo 722323 725583 := bstep (se 1 (by rfl) ⟨544187, by rfl⟩ : syracuseStep 725583 = 1088375) B1088375
theorem B725599 : Blo 722323 725599 := bstep (se 1 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 725599 = 1088399) B1088399
theorem B1741409 : Blo 722323 1741409 := bstep (se 2 (by rfl) ⟨653028, by rfl⟩ : syracuseStep 1741409 = 1306057) B1306057
theorem B725627 : Blo 722323 725627 := bstep (se 1 (by rfl) ⟨544220, by rfl⟩ : syracuseStep 725627 = 1088441) B1088441
theorem B725679 : Blo 722323 725679 := bstep (se 1 (by rfl) ⟨544259, by rfl⟩ : syracuseStep 725679 = 1088519) B1088519
theorem B1544903 : Blo 722323 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B725703 : Blo 722323 725703 := bstep (se 1 (by rfl) ⟨544277, by rfl⟩ : syracuseStep 725703 = 1088555) B1088555
theorem B725723 : Blo 722323 725723 := bstep (se 1 (by rfl) ⟨544292, by rfl⟩ : syracuseStep 725723 = 1088585) B1088585
theorem B725799 : Blo 722323 725799 := bstep (se 1 (by rfl) ⟨544349, by rfl⟩ : syracuseStep 725799 = 1088699) B1088699
theorem B725839 : Blo 722323 725839 := bstep (se 1 (by rfl) ⟨544379, by rfl⟩ : syracuseStep 725839 = 1088759) B1088759
theorem B725855 : Blo 722323 725855 := bstep (se 1 (by rfl) ⟨544391, by rfl⟩ : syracuseStep 725855 = 1088783) B1088783
theorem B725883 : Blo 722323 725883 := bstep (se 1 (by rfl) ⟨544412, by rfl⟩ : syracuseStep 725883 = 1088825) B1088825
theorem B1086383 : Blo 722323 1086383 := bstep (se 1 (by rfl) ⟨814787, by rfl⟩ : syracuseStep 1086383 = 1629575) B1629575
theorem B725935 : Blo 722323 725935 := bstep (se 1 (by rfl) ⟨544451, by rfl⟩ : syracuseStep 725935 = 1088903) B1088903
theorem B725959 : Blo 722323 725959 := bstep (se 1 (by rfl) ⟨544469, by rfl⟩ : syracuseStep 725959 = 1088939) B1088939
theorem B725979 : Blo 722323 725979 := bstep (se 1 (by rfl) ⟨544484, by rfl⟩ : syracuseStep 725979 = 1088969) B1088969
theorem B1086473 : Blo 722323 1086473 := bstep (se 2 (by rfl) ⟨407427, by rfl⟩ : syracuseStep 1086473 = 814855) B814855
theorem B1086503 : Blo 722323 1086503 := bstep (se 1 (by rfl) ⟨814877, by rfl⟩ : syracuseStep 1086503 = 1629755) B1629755
theorem B726055 : Blo 722323 726055 := bstep (se 1 (by rfl) ⟨544541, by rfl⟩ : syracuseStep 726055 = 1089083) B1089083
theorem B726095 : Blo 722323 726095 := bstep (se 1 (by rfl) ⟨544571, by rfl⟩ : syracuseStep 726095 = 1089143) B1089143
theorem B726111 : Blo 722323 726111 := bstep (se 1 (by rfl) ⟨544583, by rfl⟩ : syracuseStep 726111 = 1089167) B1089167
theorem B1086587 : Blo 722323 1086587 := bstep (se 1 (by rfl) ⟨814940, by rfl⟩ : syracuseStep 1086587 = 1629881) B1629881
theorem B726139 : Blo 722323 726139 := bstep (se 1 (by rfl) ⟨544604, by rfl⟩ : syracuseStep 726139 = 1089209) B1089209
theorem B726191 : Blo 722323 726191 := bstep (se 1 (by rfl) ⟨544643, by rfl⟩ : syracuseStep 726191 = 1089287) B1089287
theorem B726215 : Blo 722323 726215 := bstep (se 1 (by rfl) ⟨544661, by rfl⟩ : syracuseStep 726215 = 1089323) B1089323
theorem B726235 : Blo 722323 726235 := bstep (se 1 (by rfl) ⟨544676, by rfl⟩ : syracuseStep 726235 = 1089353) B1089353
theorem B1086713 : Blo 722323 1086713 := bstep (se 2 (by rfl) ⟨407517, by rfl⟩ : syracuseStep 1086713 = 815035) B815035
theorem B726311 : Blo 722323 726311 := bstep (se 1 (by rfl) ⟨544733, by rfl⟩ : syracuseStep 726311 = 1089467) B1089467
theorem B1086815 : Blo 722323 1086815 := bstep (se 1 (by rfl) ⟨815111, by rfl⟩ : syracuseStep 1086815 = 1630223) B1630223
theorem B1086827 : Blo 722323 1086827 := bstep (se 1 (by rfl) ⟨815120, by rfl⟩ : syracuseStep 1086827 = 1630241) B1630241
theorem B8033701 : Blo 722323 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B1087055 : Blo 722323 1087055 := bstep (se 1 (by rfl) ⟨815291, by rfl⟩ : syracuseStep 1087055 = 1630583) B1630583
theorem B5510753 : Blo 722323 5510753 := bstep (se 2 (by rfl) ⟨2066532, by rfl⟩ : syracuseStep 5510753 = 4133065) B4133065
theorem B4134523 : Blo 722323 4134523 := bstep (se 1 (by rfl) ⟨3100892, by rfl⟩ : syracuseStep 4134523 = 6201785) B6201785
theorem B31266445 : Blo 722323 31266445 := bstep (se 3 (by rfl) ⟨5862458, by rfl⟩ : syracuseStep 31266445 = 11724917) B11724917
theorem B1087175 : Blo 722323 1087175 := bstep (se 1 (by rfl) ⟨815381, by rfl⟩ : syracuseStep 1087175 = 1630763) B1630763
theorem B1087337 : Blo 722323 1087337 := bstep (se 2 (by rfl) ⟨407751, by rfl⟩ : syracuseStep 1087337 = 815503) B815503
theorem B1087415 : Blo 722323 1087415 := bstep (se 1 (by rfl) ⟨815561, by rfl⟩ : syracuseStep 1087415 = 1631123) B1631123
theorem B1087451 : Blo 722323 1087451 := bstep (se 1 (by rfl) ⟨815588, by rfl⟩ : syracuseStep 1087451 = 1631177) B1631177
theorem B3676427 : Blo 722323 3676427 := bstep (se 1 (by rfl) ⟨2757320, by rfl⟩ : syracuseStep 3676427 = 5514641) B5514641
theorem B825695 : Blo 722323 825695 := bstep (se 1 (by rfl) ⟨619271, by rfl⟩ : syracuseStep 825695 = 1238543) B1238543
theorem B1087919 : Blo 722323 1087919 := bstep (se 1 (by rfl) ⟨815939, by rfl⟩ : syracuseStep 1087919 = 1631879) B1631879
theorem B1088009 : Blo 722323 1088009 := bstep (se 2 (by rfl) ⟨408003, by rfl⟩ : syracuseStep 1088009 = 816007) B816007
theorem B1088039 : Blo 722323 1088039 := bstep (se 1 (by rfl) ⟨816029, by rfl⟩ : syracuseStep 1088039 = 1632059) B1632059
theorem B1219151 : Blo 722323 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B1088123 : Blo 722323 1088123 := bstep (se 1 (by rfl) ⟨816092, by rfl⟩ : syracuseStep 1088123 = 1632185) B1632185
theorem B6200009 : Blo 722323 6200009 := bstep (se 2 (by rfl) ⟨2325003, by rfl⟩ : syracuseStep 6200009 = 4650007) B4650007
theorem B1088249 : Blo 722323 1088249 := bstep (se 2 (by rfl) ⟨408093, by rfl⟩ : syracuseStep 1088249 = 816187) B816187
theorem B9280331 : Blo 722323 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B1088351 : Blo 722323 1088351 := bstep (se 1 (by rfl) ⟨816263, by rfl⟩ : syracuseStep 1088351 = 1632527) B1632527
theorem B1088363 : Blo 722323 1088363 := bstep (se 1 (by rfl) ⟨816272, by rfl⟩ : syracuseStep 1088363 = 1632545) B1632545
theorem B5512211 : Blo 722323 5512211 := bstep (se 1 (by rfl) ⟨4134158, by rfl⟩ : syracuseStep 5512211 = 8268317) B8268317
theorem B1088591 : Blo 722323 1088591 := bstep (se 1 (by rfl) ⟨816443, by rfl⟩ : syracuseStep 1088591 = 1632887) B1632887
theorem B1088711 : Blo 722323 1088711 := bstep (se 1 (by rfl) ⟨816533, by rfl⟩ : syracuseStep 1088711 = 1633067) B1633067
theorem B1088873 : Blo 722323 1088873 := bstep (se 2 (by rfl) ⟨408327, by rfl⟩ : syracuseStep 1088873 = 816655) B816655
theorem B1220015 : Blo 722323 1220015 := bstep (se 1 (by rfl) ⟨915011, by rfl⟩ : syracuseStep 1220015 = 1830023) B1830023
theorem B1088951 : Blo 722323 1088951 := bstep (se 1 (by rfl) ⟨816713, by rfl⟩ : syracuseStep 1088951 = 1633427) B1633427
theorem B1088987 : Blo 722323 1088987 := bstep (se 1 (by rfl) ⟨816740, by rfl⟩ : syracuseStep 1088987 = 1633481) B1633481
theorem B11280005 : Blo 722323 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B18554507 : Blo 722323 18554507 := bstep (se 1 (by rfl) ⟨13915880, by rfl⟩ : syracuseStep 18554507 = 27831761) B27831761
theorem B1744523 : Blo 722323 1744523 := bstep (se 1 (by rfl) ⟨1308392, by rfl⟩ : syracuseStep 1744523 = 2616785) B2616785
theorem B1220447 : Blo 722323 1220447 := bstep (se 1 (by rfl) ⟨915335, by rfl⟩ : syracuseStep 1220447 = 1830671) B1830671
theorem B1089455 : Blo 722323 1089455 := bstep (se 1 (by rfl) ⟨817091, by rfl⟩ : syracuseStep 1089455 = 1634183) B1634183
theorem B5283929 : Blo 722323 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B11739451 : Blo 722323 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B1221007 : Blo 722323 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B1221689 : Blo 722323 1221689 := bstep (se 2 (by rfl) ⟨458133, by rfl⟩ : syracuseStep 1221689 = 916267) B916267
theorem B5022839 : Blo 722323 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B9938123 : Blo 722323 9938123 := bstep (se 1 (by rfl) ⟨7453592, by rfl⟩ : syracuseStep 9938123 = 14907185) B14907185
theorem B3909217 : Blo 722323 3909217 := bstep (se 2 (by rfl) ⟨1465956, by rfl⟩ : syracuseStep 3909217 = 2931913) B2931913
theorem B7415495 : Blo 722323 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B1222391 : Blo 722323 1222391 := bstep (se 1 (by rfl) ⟨916793, by rfl⟩ : syracuseStep 1222391 = 1833587) B1833587
theorem B5515127 : Blo 722323 5515127 := bstep (se 1 (by rfl) ⟨4136345, by rfl⟩ : syracuseStep 5515127 = 8272691) B8272691
theorem B1157159 : Blo 722323 1157159 := bstep (se 1 (by rfl) ⟨867869, by rfl⟩ : syracuseStep 1157159 = 1735739) B1735739
theorem B1222735 : Blo 722323 1222735 := bstep (se 1 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 1222735 = 1834103) B1834103
theorem B11741273 : Blo 722323 11741273 := bstep (se 2 (by rfl) ⟨4402977, by rfl⟩ : syracuseStep 11741273 = 8805955) B8805955
theorem B1648811 : Blo 722323 1648811 := bstep (se 1 (by rfl) ⟨1236608, by rfl⟩ : syracuseStep 1648811 = 2473217) B2473217
theorem B6203699 : Blo 722323 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B1222985 : Blo 722323 1222985 := bstep (se 2 (by rfl) ⟨458619, by rfl⟩ : syracuseStep 1222985 = 917239) B917239
theorem B1157755 : Blo 722323 1157755 := bstep (se 1 (by rfl) ⟨868316, by rfl⟩ : syracuseStep 1157755 = 1736633) B1736633
theorem B1223417 : Blo 722323 1223417 := bstep (se 2 (by rfl) ⟨458781, by rfl⟩ : syracuseStep 1223417 = 917563) B917563
theorem B1223599 : Blo 722323 1223599 := bstep (se 1 (by rfl) ⟨917699, by rfl⟩ : syracuseStep 1223599 = 1835399) B1835399
theorem B1223687 : Blo 722323 1223687 := bstep (se 1 (by rfl) ⟨917765, by rfl⟩ : syracuseStep 1223687 = 1835531) B1835531
theorem B6204761 : Blo 722323 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B1224031 : Blo 722323 1224031 := bstep (se 1 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 1224031 = 1836047) B1836047
theorem B1224119 : Blo 722323 1224119 := bstep (se 1 (by rfl) ⟨918089, by rfl⟩ : syracuseStep 1224119 = 1836179) B1836179
theorem B5222033 : Blo 722323 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B1158985 : Blo 722323 1158985 := bstep (se 2 (by rfl) ⟨434619, by rfl⟩ : syracuseStep 1158985 = 869239) B869239
theorem B1224713 : Blo 722323 1224713 := bstep (se 2 (by rfl) ⟨459267, by rfl⟩ : syracuseStep 1224713 = 918535) B918535
theorem B1224875 : Blo 722323 1224875 := bstep (se 1 (by rfl) ⟨918656, by rfl⟩ : syracuseStep 1224875 = 1837313) B1837313
theorem B1225273 : Blo 722323 1225273 := bstep (se 2 (by rfl) ⟨459477, by rfl⟩ : syracuseStep 1225273 = 918955) B918955
theorem B1225415 : Blo 722323 1225415 := bstep (se 1 (by rfl) ⟨919061, by rfl⟩ : syracuseStep 1225415 = 1838123) B1838123
theorem B1225577 : Blo 722323 1225577 := bstep (se 2 (by rfl) ⟨459591, by rfl⟩ : syracuseStep 1225577 = 919183) B919183
theorem B5223275 : Blo 722323 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B2438315 : Blo 722323 2438315 := bstep (se 1 (by rfl) ⟨1828736, by rfl⟩ : syracuseStep 2438315 = 3657473) B3657473
theorem B2471255 : Blo 722323 2471255 := bstep (se 1 (by rfl) ⟨1853441, by rfl⟩ : syracuseStep 2471255 = 3706883) B3706883
theorem B5485967 : Blo 722323 5485967 := bstep (se 1 (by rfl) ⟨4114475, by rfl⟩ : syracuseStep 5485967 = 8228951) B8228951
theorem B1652321 : Blo 722323 1652321 := bstep (se 2 (by rfl) ⟨619620, by rfl⟩ : syracuseStep 1652321 = 1239241) B1239241
theorem B2438855 : Blo 722323 2438855 := bstep (se 1 (by rfl) ⟨1829141, by rfl⟩ : syracuseStep 2438855 = 3658283) B3658283
theorem B2471639 : Blo 722323 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B3978973 : Blo 722323 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B9287459 : Blo 722323 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B1161067 : Blo 722323 1161067 := bstep (se 1 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 1161067 = 1741601) B1741601
theorem B2439719 : Blo 722323 2439719 := bstep (se 1 (by rfl) ⟨1829789, by rfl⟩ : syracuseStep 2439719 = 3659579) B3659579
theorem B1161785 : Blo 722323 1161785 := bstep (se 2 (by rfl) ⟨435669, by rfl⟩ : syracuseStep 1161785 = 871339) B871339
theorem B2439827 : Blo 722323 2439827 := bstep (se 1 (by rfl) ⟨1829870, by rfl⟩ : syracuseStep 2439827 = 3659741) B3659741
theorem B2440043 : Blo 722323 2440043 := bstep (se 1 (by rfl) ⟨1830032, by rfl⟩ : syracuseStep 2440043 = 3660065) B3660065
theorem B2440097 : Blo 722323 2440097 := bstep (se 2 (by rfl) ⟨915036, by rfl⟩ : syracuseStep 2440097 = 1830073) B1830073
theorem B1162297 : Blo 722323 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B3915209 : Blo 722323 3915209 := bstep (se 2 (by rfl) ⟨1468203, by rfl⟩ : syracuseStep 3915209 = 2936407) B2936407
theorem B2440691 : Blo 722323 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B3489427 : Blo 722323 3489427 := bstep (se 1 (by rfl) ⟨2617070, by rfl⟩ : syracuseStep 3489427 = 5234141) B5234141
theorem B4636349 : Blo 722323 4636349 := bstep (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) B1738631
theorem B1032031 : Blo 722323 1032031 := bstep (se 1 (by rfl) ⟨774023, by rfl⟩ : syracuseStep 1032031 = 1548047) B1548047
theorem B4636577 : Blo 722323 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B2441231 : Blo 722323 2441231 := bstep (se 1 (by rfl) ⟨1830923, by rfl⟩ : syracuseStep 2441231 = 3661847) B3661847
theorem B171524405 : Blo 722323 171524405 := bstep (se 5 (by rfl) ⟨8040206, by rfl⟩ : syracuseStep 171524405 = 16080413) B16080413
theorem B2933117 : Blo 722323 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B2441825 : Blo 722323 2441825 := bstep (se 2 (by rfl) ⟨915684, by rfl⟩ : syracuseStep 2441825 = 1831369) B1831369
theorem B2605999 : Blo 722323 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B19384109 : Blo 722323 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B27871127 : Blo 722323 27871127 := bstep (se 1 (by rfl) ⟨20903345, by rfl⟩ : syracuseStep 27871127 = 41806691) B41806691
theorem B2443283 : Blo 722323 2443283 := bstep (se 1 (by rfl) ⟨1832462, by rfl⟩ : syracuseStep 2443283 = 3664925) B3664925
theorem B4638809 : Blo 722323 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B10438757 : Blo 722323 10438757 := bstep (se 4 (by rfl) ⟨978633, by rfl⟩ : syracuseStep 10438757 = 1957267) B1957267
theorem B2607299 : Blo 722323 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B2443607 : Blo 722323 2443607 := bstep (se 1 (by rfl) ⟨1832705, by rfl⟩ : syracuseStep 2443607 = 3665411) B3665411
theorem B36161977 : Blo 722323 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B5032777 : Blo 722323 5032777 := bstep (se 2 (by rfl) ⟨1887291, by rfl⟩ : syracuseStep 5032777 = 3774583) B3774583
theorem B4410571 : Blo 722323 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B9915671 : Blo 722323 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B2444687 : Blo 722323 2444687 := bstep (se 1 (by rfl) ⟨1833515, by rfl⟩ : syracuseStep 2444687 = 3667031) B3667031
theorem B1986011 : Blo 722323 1986011 := bstep (se 1 (by rfl) ⟨1489508, by rfl⟩ : syracuseStep 1986011 = 2979017) B2979017
theorem B4640267 : Blo 722323 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B5492285 : Blo 722323 5492285 := bstep (se 3 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 5492285 = 2059607) B2059607
theorem B1625723 : Blo 722323 1625723 := bstep (se 1 (by rfl) ⟨1219292, by rfl⟩ : syracuseStep 1625723 = 2438585) B2438585
theorem B773831 : Blo 722323 773831 := bstep (se 1 (by rfl) ⟨580373, by rfl⟩ : syracuseStep 773831 = 1160747) B1160747
theorem B2445011 : Blo 722323 2445011 := bstep (se 1 (by rfl) ⟨1833758, by rfl⟩ : syracuseStep 2445011 = 3667517) B3667517
theorem B1625849 : Blo 722323 1625849 := bstep (se 2 (by rfl) ⟨609693, by rfl⟩ : syracuseStep 1625849 = 1219387) B1219387
theorem B2314241 : Blo 722323 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B1626119 : Blo 722323 1626119 := bstep (se 1 (by rfl) ⟨1219589, by rfl⟩ : syracuseStep 1626119 = 2439179) B2439179
theorem B1626191 : Blo 722323 1626191 := bstep (se 1 (by rfl) ⟨1219643, by rfl⟩ : syracuseStep 1626191 = 2439287) B2439287
theorem B1626587 : Blo 722323 1626587 := bstep (se 1 (by rfl) ⟨1219940, by rfl⟩ : syracuseStep 1626587 = 2439881) B2439881
theorem B5493257 : Blo 722323 5493257 := bstep (se 2 (by rfl) ⟨2059971, by rfl⟩ : syracuseStep 5493257 = 4119943) B4119943
theorem B774779 : Blo 722323 774779 := bstep (se 1 (by rfl) ⟨581084, by rfl⟩ : syracuseStep 774779 = 1162169) B1162169
theorem B2446199 : Blo 722323 2446199 := bstep (se 1 (by rfl) ⟨1834649, by rfl⟩ : syracuseStep 2446199 = 3669299) B3669299
theorem B1627055 : Blo 722323 1627055 := bstep (se 1 (by rfl) ⟨1220291, by rfl⟩ : syracuseStep 1627055 = 2440583) B2440583
theorem B3724289 : Blo 722323 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B2642959 : Blo 722323 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B2446415 : Blo 722323 2446415 := bstep (se 1 (by rfl) ⟨1834811, by rfl⟩ : syracuseStep 2446415 = 3669623) B3669623
theorem B1627307 : Blo 722323 1627307 := bstep (se 1 (by rfl) ⟨1220480, by rfl⟩ : syracuseStep 1627307 = 2440961) B2440961
theorem B2446793 : Blo 722323 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B1627847 : Blo 722323 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B2447063 : Blo 722323 2447063 := bstep (se 1 (by rfl) ⟨1835297, by rfl⟩ : syracuseStep 2447063 = 3670595) B3670595
theorem B2447279 : Blo 722323 2447279 := bstep (se 1 (by rfl) ⟨1835459, by rfl⟩ : syracuseStep 2447279 = 3670919) B3670919
theorem B5494715 : Blo 722323 5494715 := bstep (se 1 (by rfl) ⟨4121036, by rfl⟩ : syracuseStep 5494715 = 8242073) B8242073
theorem B6969401 : Blo 722323 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B2316367 : Blo 722323 2316367 := bstep (se 1 (by rfl) ⟨1737275, by rfl⟩ : syracuseStep 2316367 = 3474551) B3474551
theorem B1956221 : Blo 722323 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B7821805 : Blo 722323 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B1628711 : Blo 722323 1628711 := bstep (se 1 (by rfl) ⟨1221533, by rfl⟩ : syracuseStep 1628711 = 2443067) B2443067
theorem B3299899 : Blo 722323 3299899 := bstep (se 1 (by rfl) ⟨2474924, by rfl⟩ : syracuseStep 3299899 = 4949849) B4949849
theorem B2742923 : Blo 722323 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B1629035 : Blo 722323 1629035 := bstep (se 1 (by rfl) ⟨1221776, by rfl⟩ : syracuseStep 1629035 = 2443553) B2443553
theorem B1629089 : Blo 722323 1629089 := bstep (se 2 (by rfl) ⟨610908, by rfl⟩ : syracuseStep 1629089 = 1221817) B1221817
theorem B6282319 : Blo 722323 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B1629431 : Blo 722323 1629431 := bstep (se 1 (by rfl) ⟨1222073, by rfl⟩ : syracuseStep 1629431 = 2444147) B2444147
theorem B1957225 : Blo 722323 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B1858945 : Blo 722323 1858945 := bstep (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) B1394209
theorem B3661199 : Blo 722323 3661199 := bstep (se 1 (by rfl) ⟨2745899, by rfl⟩ : syracuseStep 3661199 = 5491799) B5491799
theorem B11722457 : Blo 722323 11722457 := bstep (se 2 (by rfl) ⟨4395921, by rfl⟩ : syracuseStep 11722457 = 8791843) B8791843
theorem B1302265 : Blo 722323 1302265 := bstep (se 2 (by rfl) ⟨488349, by rfl⟩ : syracuseStep 1302265 = 976699) B976699
theorem B2613035 : Blo 722323 2613035 := bstep (se 1 (by rfl) ⟨1959776, by rfl⟩ : syracuseStep 2613035 = 3919553) B3919553
theorem B1630025 : Blo 722323 1630025 := bstep (se 2 (by rfl) ⟨611259, by rfl⟩ : syracuseStep 1630025 = 1222519) B1222519
theorem B8380493 : Blo 722323 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B2449655 : Blo 722323 2449655 := bstep (se 1 (by rfl) ⟨1837241, by rfl⟩ : syracuseStep 2449655 = 3674483) B3674483
theorem B4710707 : Blo 722323 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B1302971 : Blo 722323 1302971 := bstep (se 1 (by rfl) ⟨977228, by rfl⟩ : syracuseStep 1302971 = 1954457) B1954457
theorem B2449979 : Blo 722323 2449979 := bstep (se 1 (by rfl) ⟨1837484, by rfl⟩ : syracuseStep 2449979 = 3674969) B3674969
theorem B1630817 : Blo 722323 1630817 := bstep (se 2 (by rfl) ⟨611556, by rfl⟩ : syracuseStep 1630817 = 1223113) B1223113
theorem B23847641 : Blo 722323 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B2450249 : Blo 722323 2450249 := bstep (se 2 (by rfl) ⟨918843, by rfl⟩ : syracuseStep 2450249 = 1837687) B1837687
theorem B1631159 : Blo 722323 1631159 := bstep (se 1 (by rfl) ⟨1223369, by rfl⟩ : syracuseStep 1631159 = 2446739) B2446739
theorem B2057147 : Blo 722323 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B4645907 : Blo 722323 4645907 := bstep (se 1 (by rfl) ⟨3484430, by rfl⟩ : syracuseStep 4645907 = 6968861) B6968861
theorem B3663305 : Blo 722323 3663305 := bstep (se 2 (by rfl) ⟨1373739, by rfl⟩ : syracuseStep 3663305 = 2747479) B2747479
theorem B2385353 : Blo 722323 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B1631753 : Blo 722323 1631753 := bstep (se 2 (by rfl) ⟨611907, by rfl⟩ : syracuseStep 1631753 = 1223815) B1223815
theorem B812623 : Blo 722323 812623 := bstep (se 1 (by rfl) ⟨609467, by rfl⟩ : syracuseStep 812623 = 1218935) B1218935
theorem B3303035 : Blo 722323 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B1468115 : Blo 722323 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B1632095 : Blo 722323 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B2320289 : Blo 722323 2320289 := bstep (se 2 (by rfl) ⟨870108, by rfl⟩ : syracuseStep 2320289 = 1740217) B1740217
theorem B2746295 : Blo 722323 2746295 := bstep (se 1 (by rfl) ⟨2059721, by rfl⟩ : syracuseStep 2746295 = 4119443) B4119443
theorem B813019 : Blo 722323 813019 := bstep (se 1 (by rfl) ⟨609764, by rfl⟩ : syracuseStep 813019 = 1219529) B1219529
theorem B1632275 : Blo 722323 1632275 := bstep (se 1 (by rfl) ⟨1224206, by rfl⟩ : syracuseStep 1632275 = 2448413) B2448413
theorem B3663953 : Blo 722323 3663953 := bstep (se 2 (by rfl) ⟨1373982, by rfl⟩ : syracuseStep 3663953 = 2747965) B2747965
theorem B10610777 : Blo 722323 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B6187265 : Blo 722323 6187265 := bstep (se 2 (by rfl) ⟨2320224, by rfl⟩ : syracuseStep 6187265 = 4640449) B4640449
theorem B3303767 : Blo 722323 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B1632617 : Blo 722323 1632617 := bstep (se 2 (by rfl) ⟨612231, by rfl⟩ : syracuseStep 1632617 = 1224463) B1224463
theorem B1829263 : Blo 722323 1829263 := bstep (se 1 (by rfl) ⟨1371947, by rfl⟩ : syracuseStep 1829263 = 2743895) B2743895
theorem B12347801 : Blo 722323 12347801 := bstep (se 2 (by rfl) ⟨4630425, by rfl⟩ : syracuseStep 12347801 = 9260851) B9260851
theorem B813487 : Blo 722323 813487 := bstep (se 1 (by rfl) ⟨610115, by rfl⟩ : syracuseStep 813487 = 1220231) B1220231
theorem B6973933 : Blo 722323 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B2615789 : Blo 722323 2615789 := bstep (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) B980921
theorem B11168441 : Blo 722323 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B3009233 : Blo 722323 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B1829587 : Blo 722323 1829587 := bstep (se 1 (by rfl) ⟨1372190, by rfl⟩ : syracuseStep 1829587 = 2744381) B2744381
theorem B813919 : Blo 722323 813919 := bstep (se 1 (by rfl) ⟨610439, by rfl⟩ : syracuseStep 813919 = 1220879) B1220879
theorem B18606995 : Blo 722323 18606995 := bstep (se 1 (by rfl) ⟨13955246, by rfl⟩ : syracuseStep 18606995 = 27910493) B27910493
theorem B2747297 : Blo 722323 2747297 := bstep (se 2 (by rfl) ⟨1030236, by rfl⟩ : syracuseStep 2747297 = 2060473) B2060473
theorem B1633211 : Blo 722323 1633211 := bstep (se 1 (by rfl) ⟨1224908, by rfl⟩ : syracuseStep 1633211 = 2449817) B2449817
theorem B3533843 : Blo 722323 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B1633337 : Blo 722323 1633337 := bstep (se 2 (by rfl) ⟨612501, by rfl⟩ : syracuseStep 1633337 = 1225003) B1225003
theorem B814279 : Blo 722323 814279 := bstep (se 1 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 814279 = 1221419) B1221419
theorem B2747753 : Blo 722323 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B1633679 : Blo 722323 1633679 := bstep (se 1 (by rfl) ⟨1225259, by rfl⟩ : syracuseStep 1633679 = 2450519) B2450519
theorem B1469915 : Blo 722323 1469915 := bstep (se 1 (by rfl) ⟨1102436, by rfl⟩ : syracuseStep 1469915 = 2204873) B2204873
theorem B1371667 : Blo 722323 1371667 := bstep (se 1 (by rfl) ⟨1028750, by rfl⟩ : syracuseStep 1371667 = 2057501) B2057501
theorem B1830539 : Blo 722323 1830539 := bstep (se 1 (by rfl) ⟨1372904, by rfl⟩ : syracuseStep 1830539 = 2745809) B2745809
theorem B1634003 : Blo 722323 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B2748269 : Blo 722323 2748269 := bstep (se 3 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 2748269 = 1030601) B1030601
theorem B1306511 : Blo 722323 1306511 := bstep (se 1 (by rfl) ⟨979883, by rfl⟩ : syracuseStep 1306511 = 1959767) B1959767
theorem B2355119 : Blo 722323 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B4943825 : Blo 722323 4943825 := bstep (se 2 (by rfl) ⟨1853934, by rfl⟩ : syracuseStep 4943825 = 3707869) B3707869
theorem B815143 : Blo 722323 815143 := bstep (se 1 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 815143 = 1222715) B1222715
theorem B880763 : Blo 722323 880763 := bstep (se 1 (by rfl) ⟨660572, by rfl⟩ : syracuseStep 880763 = 1321145) B1321145
theorem B2322749 : Blo 722323 2322749 := bstep (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) B871031
theorem B2781677 : Blo 722323 2781677 := bstep (se 3 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 2781677 = 1043129) B1043129
theorem B2748937 : Blo 722323 2748937 := bstep (se 2 (by rfl) ⟨1030851, by rfl⟩ : syracuseStep 2748937 = 2061703) B2061703
theorem B1831673 : Blo 722323 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B2683757 : Blo 722323 2683757 := bstep (se 3 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 2683757 = 1006409) B1006409
theorem B1962913 : Blo 722323 1962913 := bstep (se 2 (by rfl) ⟨736092, by rfl⟩ : syracuseStep 1962913 = 1472185) B1472185
theorem B1831855 : Blo 722323 1831855 := bstep (se 1 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 1831855 = 2747783) B2747783
theorem B24146909 : Blo 722323 24146909 := bstep (se 3 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 24146909 = 9055091) B9055091
theorem B4649957 : Blo 722323 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B4125775 : Blo 722323 4125775 := bstep (se 1 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 4125775 = 6188663) B6188663
theorem B30078307 : Blo 722323 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B1832321 : Blo 722323 1832321 := bstep (se 2 (by rfl) ⟨687120, by rfl⟩ : syracuseStep 1832321 = 1374241) B1374241
theorem B980407 : Blo 722323 980407 := bstep (se 1 (by rfl) ⟨735305, by rfl⟩ : syracuseStep 980407 = 1470611) B1470611
theorem B915067 : Blo 722323 915067 := bstep (se 1 (by rfl) ⟨686300, by rfl⟩ : syracuseStep 915067 = 1372601) B1372601
theorem B816763 : Blo 722323 816763 := bstep (se 1 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 816763 = 1225145) B1225145
theorem B5863211 : Blo 722323 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B1832777 : Blo 722323 1832777 := bstep (se 2 (by rfl) ⟨687291, by rfl⟩ : syracuseStep 1832777 = 1374583) B1374583
theorem B915295 : Blo 722323 915295 := bstep (se 1 (by rfl) ⟨686471, by rfl⟩ : syracuseStep 915295 = 1372943) B1372943
theorem B1374059 : Blo 722323 1374059 := bstep (se 1 (by rfl) ⟨1030544, by rfl⟩ : syracuseStep 1374059 = 2061089) B2061089
theorem B4945799 : Blo 722323 4945799 := bstep (se 1 (by rfl) ⟨3709349, by rfl⟩ : syracuseStep 4945799 = 7418699) B7418699
theorem B2750395 : Blo 722323 2750395 := bstep (se 1 (by rfl) ⟨2062796, by rfl⟩ : syracuseStep 2750395 = 4125593) B4125593
theorem B6944717 : Blo 722323 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B6191261 : Blo 722323 6191261 := bstep (se 3 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 6191261 = 2321723) B2321723
theorem B1833131 : Blo 722323 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B2324747 : Blo 722323 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B6977897 : Blo 722323 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B915887 : Blo 722323 915887 := bstep (se 1 (by rfl) ⟨686915, by rfl⟩ : syracuseStep 915887 = 1373831) B1373831
theorem B1374727 : Blo 722323 1374727 := bstep (se 1 (by rfl) ⟨1031045, by rfl⟩ : syracuseStep 1374727 = 2062091) B2062091
theorem B3668489 : Blo 722323 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B2751185 : Blo 722323 2751185 := bstep (se 2 (by rfl) ⟨1031694, by rfl⟩ : syracuseStep 2751185 = 2063389) B2063389
theorem B1833911 : Blo 722323 1833911 := bstep (se 1 (by rfl) ⟨1375433, by rfl⟩ : syracuseStep 1833911 = 2750867) B2750867
theorem B1375289 : Blo 722323 1375289 := bstep (se 2 (by rfl) ⟨515733, by rfl⟩ : syracuseStep 1375289 = 1031467) B1031467
theorem B2751641 : Blo 722323 2751641 := bstep (se 2 (by rfl) ⟨1031865, by rfl⟩ : syracuseStep 2751641 = 2063731) B2063731
theorem B181140941 : Blo 722323 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1834913 : Blo 722323 1834913 := bstep (se 2 (by rfl) ⟨688092, by rfl⟩ : syracuseStep 1834913 = 1376185) B1376185
theorem B3669947 : Blo 722323 3669947 := bstep (se 1 (by rfl) ⟨2752460, by rfl⟩ : syracuseStep 3669947 = 5504921) B5504921
theorem B1376831 : Blo 722323 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B13959863 : Blo 722323 13959863 := bstep (se 1 (by rfl) ⟨10469897, by rfl⟩ : syracuseStep 13959863 = 20939795) B20939795
theorem B1835743 : Blo 722323 1835743 := bstep (se 1 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 1835743 = 2753615) B2753615
theorem B1835855 : Blo 722323 1835855 := bstep (se 1 (by rfl) ⟨1376891, by rfl⟩ : syracuseStep 1835855 = 2753783) B2753783
theorem B918479 : Blo 722323 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B3474589 : Blo 722323 3474589 := bstep (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) B1302971
theorem B1377499 : Blo 722323 1377499 := bstep (se 1 (by rfl) ⟨1033124, by rfl⟩ : syracuseStep 1377499 = 2066249) B2066249
theorem B3474665 : Blo 722323 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B18580751 : Blo 722323 18580751 := bstep (se 1 (by rfl) ⟨13935563, by rfl⟩ : syracuseStep 18580751 = 27871127) B27871127
theorem B3671405 : Blo 722323 3671405 := bstep (se 3 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 3671405 = 1376777) B1376777
theorem B722343 : Blo 722323 722343 := bstep (se 1 (by rfl) ⟨541757, by rfl⟩ : syracuseStep 722343 = 1083515) B1083515
theorem B1738199 : Blo 722323 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B1836503 : Blo 722323 1836503 := bstep (se 1 (by rfl) ⟨1377377, by rfl⟩ : syracuseStep 1836503 = 2754755) B2754755
theorem B722427 : Blo 722323 722427 := bstep (se 1 (by rfl) ⟨541820, by rfl⟩ : syracuseStep 722427 = 1083641) B1083641
theorem B722495 : Blo 722323 722495 := bstep (se 1 (by rfl) ⟨541871, by rfl⟩ : syracuseStep 722495 = 1083743) B1083743
theorem B722503 : Blo 722323 722503 := bstep (se 1 (by rfl) ⟨541877, by rfl⟩ : syracuseStep 722503 = 1083755) B1083755
theorem B2066077 : Blo 722323 2066077 := bstep (se 3 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 2066077 = 774779) B774779
theorem B722655 : Blo 722323 722655 := bstep (se 1 (by rfl) ⟨541991, by rfl⟩ : syracuseStep 722655 = 1083983) B1083983
theorem B722735 : Blo 722323 722735 := bstep (se 1 (by rfl) ⟨542051, by rfl⟩ : syracuseStep 722735 = 1084103) B1084103
theorem B1836857 : Blo 722323 1836857 := bstep (se 2 (by rfl) ⟨688821, by rfl⟩ : syracuseStep 1836857 = 1377643) B1377643
theorem B722843 : Blo 722323 722843 := bstep (se 1 (by rfl) ⟨542132, by rfl⟩ : syracuseStep 722843 = 1084265) B1084265
theorem B722895 : Blo 722323 722895 := bstep (se 1 (by rfl) ⟨542171, by rfl⟩ : syracuseStep 722895 = 1084343) B1084343
theorem B722919 : Blo 722323 722919 := bstep (se 1 (by rfl) ⟨542189, by rfl⟩ : syracuseStep 722919 = 1084379) B1084379
theorem B1083497 : Blo 722323 1083497 := bstep (se 2 (by rfl) ⟨406311, by rfl⟩ : syracuseStep 1083497 = 812623) B812623
theorem B5212289 : Blo 722323 5212289 := bstep (se 2 (by rfl) ⟨1954608, by rfl⟩ : syracuseStep 5212289 = 3909217) B3909217
theorem B723231 : Blo 722323 723231 := bstep (se 1 (by rfl) ⟨542423, by rfl⟩ : syracuseStep 723231 = 1084847) B1084847
theorem B723291 : Blo 722323 723291 := bstep (se 1 (by rfl) ⟨542468, by rfl⟩ : syracuseStep 723291 = 1084937) B1084937
theorem B723311 : Blo 722323 723311 := bstep (se 1 (by rfl) ⟨542483, by rfl⟩ : syracuseStep 723311 = 1084967) B1084967
theorem B1083815 : Blo 722323 1083815 := bstep (se 1 (by rfl) ⟨812861, by rfl⟩ : syracuseStep 1083815 = 1625723) B1625723
theorem B723367 : Blo 722323 723367 := bstep (se 1 (by rfl) ⟨542525, by rfl⟩ : syracuseStep 723367 = 1085051) B1085051
theorem B1083899 : Blo 722323 1083899 := bstep (se 1 (by rfl) ⟨812924, by rfl⟩ : syracuseStep 1083899 = 1625849) B1625849
theorem B723451 : Blo 722323 723451 := bstep (se 1 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 723451 = 1085177) B1085177
theorem B723519 : Blo 722323 723519 := bstep (se 1 (by rfl) ⟨542639, by rfl⟩ : syracuseStep 723519 = 1085279) B1085279
theorem B723527 : Blo 722323 723527 := bstep (se 1 (by rfl) ⟨542645, by rfl⟩ : syracuseStep 723527 = 1085291) B1085291
theorem B1084025 : Blo 722323 1084025 := bstep (se 2 (by rfl) ⟨406509, by rfl⟩ : syracuseStep 1084025 = 813019) B813019
theorem B1542827 : Blo 722323 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B1084079 : Blo 722323 1084079 := bstep (se 1 (by rfl) ⟨813059, by rfl⟩ : syracuseStep 1084079 = 1626119) B1626119
theorem B1084127 : Blo 722323 1084127 := bstep (se 1 (by rfl) ⟨813095, by rfl⟩ : syracuseStep 1084127 = 1626191) B1626191
theorem B723679 : Blo 722323 723679 := bstep (se 1 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 723679 = 1085519) B1085519
theorem B4131607 : Blo 722323 4131607 := bstep (se 1 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 4131607 = 6197411) B6197411
theorem B723759 : Blo 722323 723759 := bstep (se 1 (by rfl) ⟨542819, by rfl⟩ : syracuseStep 723759 = 1085639) B1085639
theorem B723867 : Blo 722323 723867 := bstep (se 1 (by rfl) ⟨542900, by rfl⟩ : syracuseStep 723867 = 1085801) B1085801
theorem B723919 : Blo 722323 723919 := bstep (se 1 (by rfl) ⟨542939, by rfl⟩ : syracuseStep 723919 = 1085879) B1085879
theorem B1084391 : Blo 722323 1084391 := bstep (se 1 (by rfl) ⟨813293, by rfl⟩ : syracuseStep 1084391 = 1626587) B1626587
theorem B723943 : Blo 722323 723943 := bstep (se 1 (by rfl) ⟨542957, by rfl⟩ : syracuseStep 723943 = 1085915) B1085915
theorem B1084649 : Blo 722323 1084649 := bstep (se 2 (by rfl) ⟨406743, by rfl⟩ : syracuseStep 1084649 = 813487) B813487
theorem B1084703 : Blo 722323 1084703 := bstep (se 1 (by rfl) ⟨813527, by rfl⟩ : syracuseStep 1084703 = 1627055) B1627055
theorem B724255 : Blo 722323 724255 := bstep (se 1 (by rfl) ⟨543191, by rfl⟩ : syracuseStep 724255 = 1086383) B1086383
theorem B724315 : Blo 722323 724315 := bstep (se 1 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 724315 = 1086473) B1086473
theorem B724335 : Blo 722323 724335 := bstep (se 1 (by rfl) ⟨543251, by rfl⟩ : syracuseStep 724335 = 1086503) B1086503
theorem B1838497 : Blo 722323 1838497 := bstep (se 2 (by rfl) ⟨689436, by rfl⟩ : syracuseStep 1838497 = 1378873) B1378873
theorem B724391 : Blo 722323 724391 := bstep (se 1 (by rfl) ⟨543293, by rfl⟩ : syracuseStep 724391 = 1086587) B1086587
theorem B1084871 : Blo 722323 1084871 := bstep (se 1 (by rfl) ⟨813653, by rfl⟩ : syracuseStep 1084871 = 1627307) B1627307
theorem B1543673 : Blo 722323 1543673 := bstep (se 2 (by rfl) ⟨578877, by rfl⟩ : syracuseStep 1543673 = 1157755) B1157755
theorem B724475 : Blo 722323 724475 := bstep (se 1 (by rfl) ⟨543356, by rfl⟩ : syracuseStep 724475 = 1086713) B1086713
theorem B724543 : Blo 722323 724543 := bstep (se 1 (by rfl) ⟨543407, by rfl⟩ : syracuseStep 724543 = 1086815) B1086815
theorem B724551 : Blo 722323 724551 := bstep (se 1 (by rfl) ⟨543413, by rfl⟩ : syracuseStep 724551 = 1086827) B1086827
theorem B724703 : Blo 722323 724703 := bstep (se 1 (by rfl) ⟨543527, by rfl⟩ : syracuseStep 724703 = 1087055) B1087055
theorem B3673835 : Blo 722323 3673835 := bstep (se 1 (by rfl) ⟨2755376, by rfl⟩ : syracuseStep 3673835 = 5510753) B5510753
theorem B1085225 : Blo 722323 1085225 := bstep (se 2 (by rfl) ⟨406959, by rfl⟩ : syracuseStep 1085225 = 813919) B813919
theorem B1085231 : Blo 722323 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B724783 : Blo 722323 724783 := bstep (se 1 (by rfl) ⟨543587, by rfl⟩ : syracuseStep 724783 = 1087175) B1087175
theorem B6360941 : Blo 722323 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B724891 : Blo 722323 724891 := bstep (se 1 (by rfl) ⟨543668, by rfl⟩ : syracuseStep 724891 = 1087337) B1087337
theorem B724943 : Blo 722323 724943 := bstep (se 1 (by rfl) ⟨543707, by rfl⟩ : syracuseStep 724943 = 1087415) B1087415
theorem B35229653 : Blo 722323 35229653 := bstep (se 7 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 35229653 = 825695) B825695
theorem B724967 : Blo 722323 724967 := bstep (se 1 (by rfl) ⟨543725, by rfl⟩ : syracuseStep 724967 = 1087451) B1087451
theorem B2756713 : Blo 722323 2756713 := bstep (se 2 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 2756713 = 2067535) B2067535
theorem B3674321 : Blo 722323 3674321 := bstep (se 2 (by rfl) ⟨1377870, by rfl⟩ : syracuseStep 3674321 = 2755741) B2755741
theorem B1085705 : Blo 722323 1085705 := bstep (se 2 (by rfl) ⟨407139, by rfl⟩ : syracuseStep 1085705 = 814279) B814279
theorem B725279 : Blo 722323 725279 := bstep (se 1 (by rfl) ⟨543959, by rfl⟩ : syracuseStep 725279 = 1087919) B1087919
theorem B725339 : Blo 722323 725339 := bstep (se 1 (by rfl) ⟨544004, by rfl⟩ : syracuseStep 725339 = 1088009) B1088009
theorem B1085807 : Blo 722323 1085807 := bstep (se 1 (by rfl) ⟨814355, by rfl⟩ : syracuseStep 1085807 = 1628711) B1628711
theorem B725359 : Blo 722323 725359 := bstep (se 1 (by rfl) ⟨544019, by rfl⟩ : syracuseStep 725359 = 1088039) B1088039
theorem B725415 : Blo 722323 725415 := bstep (se 1 (by rfl) ⟨544061, by rfl⟩ : syracuseStep 725415 = 1088123) B1088123
theorem B4133339 : Blo 722323 4133339 := bstep (se 1 (by rfl) ⟨3100004, by rfl⟩ : syracuseStep 4133339 = 6200009) B6200009
theorem B725499 : Blo 722323 725499 := bstep (se 1 (by rfl) ⟨544124, by rfl⟩ : syracuseStep 725499 = 1088249) B1088249
theorem B725567 : Blo 722323 725567 := bstep (se 1 (by rfl) ⟨544175, by rfl⟩ : syracuseStep 725567 = 1088351) B1088351
theorem B1086023 : Blo 722323 1086023 := bstep (se 1 (by rfl) ⟨814517, by rfl⟩ : syracuseStep 1086023 = 1629035) B1629035
theorem B725575 : Blo 722323 725575 := bstep (se 1 (by rfl) ⟨544181, by rfl⟩ : syracuseStep 725575 = 1088363) B1088363
theorem B1086059 : Blo 722323 1086059 := bstep (se 1 (by rfl) ⟨814544, by rfl⟩ : syracuseStep 1086059 = 1629089) B1629089
theorem B3674807 : Blo 722323 3674807 := bstep (se 1 (by rfl) ⟨2756105, by rfl⟩ : syracuseStep 3674807 = 5512211) B5512211
theorem B725727 : Blo 722323 725727 := bstep (se 1 (by rfl) ⟨544295, by rfl⟩ : syracuseStep 725727 = 1088591) B1088591
theorem B725807 : Blo 722323 725807 := bstep (se 1 (by rfl) ⟨544355, by rfl⟩ : syracuseStep 725807 = 1088711) B1088711
theorem B1086287 : Blo 722323 1086287 := bstep (se 1 (by rfl) ⟨814715, by rfl⟩ : syracuseStep 1086287 = 1629431) B1629431
theorem B725915 : Blo 722323 725915 := bstep (se 1 (by rfl) ⟨544436, by rfl⟩ : syracuseStep 725915 = 1088873) B1088873
theorem B725967 : Blo 722323 725967 := bstep (se 1 (by rfl) ⟨544475, by rfl⟩ : syracuseStep 725967 = 1088951) B1088951
theorem B725991 : Blo 722323 725991 := bstep (se 1 (by rfl) ⟨544493, by rfl⟩ : syracuseStep 725991 = 1088987) B1088987
theorem B1545313 : Blo 722323 1545313 := bstep (se 2 (by rfl) ⟨579492, by rfl⟩ : syracuseStep 1545313 = 1158985) B1158985
theorem B3675293 : Blo 722323 3675293 := bstep (se 3 (by rfl) ⟨689117, by rfl⟩ : syracuseStep 3675293 = 1378235) B1378235
theorem B1742023 : Blo 722323 1742023 := bstep (se 1 (by rfl) ⟨1306517, by rfl⟩ : syracuseStep 1742023 = 2613035) B2613035
theorem B1086683 : Blo 722323 1086683 := bstep (se 1 (by rfl) ⟨815012, by rfl⟩ : syracuseStep 1086683 = 1630025) B1630025
theorem B726303 : Blo 722323 726303 := bstep (se 1 (by rfl) ⟨544727, by rfl⟩ : syracuseStep 726303 = 1089455) B1089455
theorem B1086857 : Blo 722323 1086857 := bstep (se 2 (by rfl) ⟨407571, by rfl⟩ : syracuseStep 1086857 = 815143) B815143
theorem B1087211 : Blo 722323 1087211 := bstep (se 1 (by rfl) ⟨815408, by rfl⟩ : syracuseStep 1087211 = 1630817) B1630817
theorem B15898427 : Blo 722323 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B1087439 : Blo 722323 1087439 := bstep (se 1 (by rfl) ⟨815579, by rfl⟩ : syracuseStep 1087439 = 1631159) B1631159
theorem B6199325 : Blo 722323 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B3348559 : Blo 722323 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B6625415 : Blo 722323 6625415 := bstep (se 1 (by rfl) ⟨4969061, by rfl⟩ : syracuseStep 6625415 = 9938123) B9938123
theorem B1087835 : Blo 722323 1087835 := bstep (se 1 (by rfl) ⟨815876, by rfl⟩ : syracuseStep 1087835 = 1631753) B1631753
theorem B2202023 : Blo 722323 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B3676589 : Blo 722323 3676589 := bstep (se 3 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 3676589 = 1378721) B1378721
theorem B1088063 : Blo 722323 1088063 := bstep (se 1 (by rfl) ⟨816047, by rfl⟩ : syracuseStep 1088063 = 1632095) B1632095
theorem B3676751 : Blo 722323 3676751 := bstep (se 1 (by rfl) ⟨2757563, by rfl⟩ : syracuseStep 3676751 = 5515127) B5515127
theorem B1546859 : Blo 722323 1546859 := bstep (se 1 (by rfl) ⟨1160144, by rfl⟩ : syracuseStep 1546859 = 2320289) B2320289
theorem B1088183 : Blo 722323 1088183 := bstep (se 1 (by rfl) ⟨816137, by rfl⟩ : syracuseStep 1088183 = 1632275) B1632275
theorem B4135799 : Blo 722323 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B2202511 : Blo 722323 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B1088411 : Blo 722323 1088411 := bstep (se 1 (by rfl) ⟨816308, by rfl⟩ : syracuseStep 1088411 = 1632617) B1632617
theorem B8231867 : Blo 722323 8231867 := bstep (se 1 (by rfl) ⟨6173900, by rfl⟩ : syracuseStep 8231867 = 12347801) B12347801
theorem B1743859 : Blo 722323 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B7445627 : Blo 722323 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B2006155 : Blo 722323 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B1088807 : Blo 722323 1088807 := bstep (se 1 (by rfl) ⟨816605, by rfl⟩ : syracuseStep 1088807 = 1633211) B1633211
theorem B1088891 : Blo 722323 1088891 := bstep (se 1 (by rfl) ⟨816668, by rfl⟩ : syracuseStep 1088891 = 1633337) B1633337
theorem B1220089 : Blo 722323 1220089 := bstep (se 2 (by rfl) ⟨457533, by rfl⟩ : syracuseStep 1220089 = 915067) B915067
theorem B5512697 : Blo 722323 5512697 := bstep (se 2 (by rfl) ⟨2067261, by rfl⟩ : syracuseStep 5512697 = 4134523) B4134523
theorem B1089017 : Blo 722323 1089017 := bstep (se 2 (by rfl) ⟨408381, by rfl⟩ : syracuseStep 1089017 = 816763) B816763
theorem B41688593 : Blo 722323 41688593 := bstep (se 2 (by rfl) ⟨15633222, by rfl⟩ : syracuseStep 41688593 = 31266445) B31266445
theorem B4136507 : Blo 722323 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B1089119 : Blo 722323 1089119 := bstep (se 1 (by rfl) ⟨816839, by rfl⟩ : syracuseStep 1089119 = 1633679) B1633679
theorem B1220359 : Blo 722323 1220359 := bstep (se 1 (by rfl) ⟨915269, by rfl⟩ : syracuseStep 1220359 = 1830539) B1830539
theorem B3481355 : Blo 722323 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1220393 : Blo 722323 1220393 := bstep (se 2 (by rfl) ⟨457647, by rfl⟩ : syracuseStep 1220393 = 915295) B915295
theorem B1089335 : Blo 722323 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B1548089 : Blo 722323 1548089 := bstep (se 2 (by rfl) ⟨580533, by rfl⟩ : syracuseStep 1548089 = 1161067) B1161067
theorem B3088489 : Blo 722323 3088489 := bstep (se 2 (by rfl) ⟨1158183, by rfl⟩ : syracuseStep 3088489 = 2316367) B2316367
theorem B1548499 : Blo 722323 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B1221115 : Blo 722323 1221115 := bstep (se 1 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 1221115 = 1831673) B1831673
theorem B3482183 : Blo 722323 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B10429073 : Blo 722323 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B16097939 : Blo 722323 16097939 := bstep (se 1 (by rfl) ⟨12073454, by rfl⟩ : syracuseStep 16097939 = 24146909) B24146909
theorem B4399865 : Blo 722323 4399865 := bstep (se 2 (by rfl) ⟨1649949, by rfl⟩ : syracuseStep 4399865 = 3299899) B3299899
theorem B1647503 : Blo 722323 1647503 := bstep (se 1 (by rfl) ⟨1235627, by rfl⟩ : syracuseStep 1647503 = 2471255) B2471255
theorem B1221547 : Blo 722323 1221547 := bstep (se 1 (by rfl) ⟨916160, by rfl⟩ : syracuseStep 1221547 = 1832321) B1832321
theorem B3908807 : Blo 722323 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B1221851 : Blo 722323 1221851 := bstep (se 1 (by rfl) ⟨916388, by rfl⟩ : syracuseStep 1221851 = 1832777) B1832777
theorem B4629811 : Blo 722323 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B1549729 : Blo 722323 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B1222087 : Blo 722323 1222087 := bstep (se 1 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 1222087 = 1833131) B1833131
theorem B1222607 : Blo 722323 1222607 := bstep (se 1 (by rfl) ⟨916955, by rfl⟩ : syracuseStep 1222607 = 1833911) B1833911
theorem B120760627 : Blo 722323 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B3090899 : Blo 722323 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B3091051 : Blo 722323 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B1223275 : Blo 722323 1223275 := bstep (se 1 (by rfl) ⟨917456, by rfl⟩ : syracuseStep 1223275 = 1834913) B1834913
theorem B1223579 : Blo 722323 1223579 := bstep (se 1 (by rfl) ⟨917684, by rfl⟩ : syracuseStep 1223579 = 1835369) B1835369
theorem B12365297 : Blo 722323 12365297 := bstep (se 2 (by rfl) ⟨4636986, by rfl⟩ : syracuseStep 12365297 = 9273973) B9273973
theorem B12922739 : Blo 722323 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B13938641 : Blo 722323 13938641 := bstep (se 2 (by rfl) ⟨5226990, by rfl⟩ : syracuseStep 13938641 = 10453981) B10453981
theorem B3092539 : Blo 722323 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B6959171 : Blo 722323 6959171 := bstep (se 1 (by rfl) ⟨5219378, by rfl⟩ : syracuseStep 6959171 = 10438757) B10438757
theorem B1356257 : Blo 722323 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B5878291 : Blo 722323 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B1324007 : Blo 722323 1324007 := bstep (se 1 (by rfl) ⟨993005, by rfl⟩ : syracuseStep 1324007 = 1986011) B1986011
theorem B1160183 : Blo 722323 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B1160939 : Blo 722323 1160939 := bstep (se 1 (by rfl) ⟨870704, by rfl⟩ : syracuseStep 1160939 = 1741409) B1741409
theorem B1029935 : Blo 722323 1029935 := bstep (se 1 (by rfl) ⟨772451, by rfl⟩ : syracuseStep 1029935 = 1544903) B1544903
theorem B2439017 : Blo 722323 2439017 := bstep (se 2 (by rfl) ⟨914631, by rfl⟩ : syracuseStep 2439017 = 1829263) B1829263
theorem B48215969 : Blo 722323 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B2439449 : Blo 722323 2439449 := bstep (se 2 (by rfl) ⟨914793, by rfl⟩ : syracuseStep 2439449 = 1829587) B1829587
theorem B5880761 : Blo 722323 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B4767113 : Blo 722323 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B2440799 : Blo 722323 2440799 := bstep (se 1 (by rfl) ⟨1830599, by rfl⟩ : syracuseStep 2440799 = 3661199) B3661199
theorem B7520003 : Blo 722323 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B12369671 : Blo 722323 12369671 := bstep (se 1 (by rfl) ⟨9277253, by rfl⟩ : syracuseStep 12369671 = 18554507) B18554507
theorem B1163015 : Blo 722323 1163015 := bstep (se 1 (by rfl) ⟨872261, by rfl⟩ : syracuseStep 1163015 = 1744523) B1744523
theorem B7814971 : Blo 722323 7814971 := bstep (se 1 (by rfl) ⟨5861228, by rfl⟩ : syracuseStep 7814971 = 11722457) B11722457
theorem B5586995 : Blo 722323 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B3522619 : Blo 722323 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B3097271 : Blo 722323 3097271 := bstep (se 1 (by rfl) ⟨2322953, by rfl⟩ : syracuseStep 3097271 = 4645907) B4645907
theorem B2442203 : Blo 722323 2442203 := bstep (se 1 (by rfl) ⟨1831652, by rfl⟩ : syracuseStep 2442203 = 3663305) B3663305
theorem B2442365 : Blo 722323 2442365 := bstep (se 3 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 2442365 = 915887) B915887
theorem B2442473 : Blo 722323 2442473 := bstep (se 2 (by rfl) ⟨915927, by rfl⟩ : syracuseStep 2442473 = 1831855) B1831855
theorem B3523945 : Blo 722323 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B771439 : Blo 722323 771439 := bstep (se 1 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 771439 = 1157159) B1157159
theorem B2442635 : Blo 722323 2442635 := bstep (se 1 (by rfl) ⟨1831976, by rfl⟩ : syracuseStep 2442635 = 3663953) B3663953
theorem B1099207 : Blo 722323 1099207 := bstep (se 1 (by rfl) ⟨824405, by rfl⟩ : syracuseStep 1099207 = 1648811) B1648811
theorem B12404663 : Blo 722323 12404663 := bstep (se 1 (by rfl) ⟨9303497, by rfl⟩ : syracuseStep 12404663 = 18606995) B18606995
theorem B26364149 : Blo 722323 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B5228837 : Blo 722323 5228837 := bstep (se 4 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 5228837 = 980407) B980407
theorem B871007 : Blo 722323 871007 := bstep (se 1 (by rfl) ⟨653255, by rfl⟩ : syracuseStep 871007 = 1306511) B1306511
theorem B3295883 : Blo 722323 3295883 := bstep (se 1 (by rfl) ⟨2471912, by rfl⟩ : syracuseStep 3295883 = 4943825) B4943825
theorem B1854451 : Blo 722323 1854451 := bstep (se 1 (by rfl) ⟨1390838, by rfl⟩ : syracuseStep 1854451 = 2781677) B2781677
theorem B1789171 : Blo 722323 1789171 := bstep (se 1 (by rfl) ⟨1341878, by rfl⟩ : syracuseStep 1789171 = 2683757) B2683757
theorem B3099971 : Blo 722323 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B1625543 : Blo 722323 1625543 := bstep (se 1 (by rfl) ⟨1219157, by rfl⟩ : syracuseStep 1625543 = 2438315) B2438315
theorem B3657311 : Blo 722323 3657311 := bstep (se 1 (by rfl) ⟨2742983, by rfl⟩ : syracuseStep 3657311 = 5485967) B5485967
theorem B1101547 : Blo 722323 1101547 := bstep (se 1 (by rfl) ⟨826160, by rfl⟩ : syracuseStep 1101547 = 1652321) B1652321
theorem B1625903 : Blo 722323 1625903 := bstep (se 1 (by rfl) ⟨1219427, by rfl⟩ : syracuseStep 1625903 = 2438855) B2438855
theorem B21221189 : Blo 722323 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B3297199 : Blo 722323 3297199 := bstep (se 1 (by rfl) ⟨2472899, by rfl⟩ : syracuseStep 3297199 = 4945799) B4945799
theorem B12374045 : Blo 722323 12374045 := bstep (se 3 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 12374045 = 4640267) B4640267
theorem B8376425 : Blo 722323 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B2445659 : Blo 722323 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B1626479 : Blo 722323 1626479 := bstep (se 1 (by rfl) ⟨1219859, by rfl⟩ : syracuseStep 1626479 = 2439719) B2439719
theorem B774523 : Blo 722323 774523 := bstep (se 1 (by rfl) ⟨580892, by rfl⟩ : syracuseStep 774523 = 1161785) B1161785
theorem B1626551 : Blo 722323 1626551 := bstep (se 1 (by rfl) ⟨1219913, by rfl⟩ : syracuseStep 1626551 = 2439827) B2439827
theorem B2609633 : Blo 722323 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B2478593 : Blo 722323 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B1626695 : Blo 722323 1626695 := bstep (se 1 (by rfl) ⟨1220021, by rfl⟩ : syracuseStep 1626695 = 2440043) B2440043
theorem B1626731 : Blo 722323 1626731 := bstep (se 1 (by rfl) ⟨1220048, by rfl⟩ : syracuseStep 1626731 = 2440097) B2440097
theorem B2610139 : Blo 722323 2610139 := bstep (se 1 (by rfl) ⟨1957604, by rfl⟩ : syracuseStep 2610139 = 3915209) B3915209
theorem B1627127 : Blo 722323 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B2446631 : Blo 722323 2446631 := bstep (se 1 (by rfl) ⟨1834973, by rfl⟩ : syracuseStep 2446631 = 3669947) B3669947
theorem B1627487 : Blo 722323 1627487 := bstep (se 1 (by rfl) ⟨1220615, by rfl⟩ : syracuseStep 1627487 = 2441231) B2441231
theorem B114349603 : Blo 722323 114349603 := bstep (se 1 (by rfl) ⟨85762202, by rfl⟩ : syracuseStep 114349603 = 171524405) B171524405
theorem B1955411 : Blo 722323 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B1627883 : Blo 722323 1627883 := bstep (se 1 (by rfl) ⟨1220912, by rfl⟩ : syracuseStep 1627883 = 2441825) B2441825
theorem B15652601 : Blo 722323 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B1628009 : Blo 722323 1628009 := bstep (se 2 (by rfl) ⟨610503, by rfl⟩ : syracuseStep 1628009 = 1221007) B1221007
theorem B2316239 : Blo 722323 2316239 := bstep (se 1 (by rfl) ⟨1737179, by rfl⟩ : syracuseStep 2316239 = 3474359) B3474359
theorem B2447495 : Blo 722323 2447495 := bstep (se 1 (by rfl) ⟨1835621, by rfl⟩ : syracuseStep 2447495 = 3671243) B3671243
theorem B1988819 : Blo 722323 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B7428631 : Blo 722323 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B1464895 : Blo 722323 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B9394805 : Blo 722323 9394805 := bstep (se 5 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 9394805 = 880763) B880763
theorem B1628855 : Blo 722323 1628855 := bstep (se 1 (by rfl) ⟨1221641, by rfl⟩ : syracuseStep 1628855 = 2443283) B2443283
theorem B1629071 : Blo 722323 1629071 := bstep (se 1 (by rfl) ⟨1221803, by rfl⟩ : syracuseStep 1629071 = 2443607) B2443607
theorem B2448737 : Blo 722323 2448737 := bstep (se 2 (by rfl) ⟨918276, by rfl⟩ : syracuseStep 2448737 = 1836553) B1836553
theorem B6610447 : Blo 722323 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B11296351 : Blo 722323 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B1629791 : Blo 722323 1629791 := bstep (se 1 (by rfl) ⟨1222343, by rfl⟩ : syracuseStep 1629791 = 2444687) B2444687
theorem B3661523 : Blo 722323 3661523 := bstep (se 1 (by rfl) ⟨2746142, by rfl⟩ : syracuseStep 3661523 = 5492285) B5492285
theorem B1630007 : Blo 722323 1630007 := bstep (se 1 (by rfl) ⟨1222505, by rfl⟩ : syracuseStep 1630007 = 2445011) B2445011
theorem B1630313 : Blo 722323 1630313 := bstep (se 2 (by rfl) ⟨611367, by rfl⟩ : syracuseStep 1630313 = 1222735) B1222735
theorem B3662171 : Blo 722323 3662171 := bstep (se 1 (by rfl) ⟨2746628, by rfl⟩ : syracuseStep 3662171 = 5493257) B5493257
theorem B2384219 : Blo 722323 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B2318699 : Blo 722323 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1630799 : Blo 722323 1630799 := bstep (se 1 (by rfl) ⟨1223099, by rfl⟩ : syracuseStep 1630799 = 2446199) B2446199
theorem B9298577 : Blo 722323 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B2482859 : Blo 722323 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B1630943 : Blo 722323 1630943 := bstep (se 1 (by rfl) ⟨1223207, by rfl⟩ : syracuseStep 1630943 = 2446415) B2446415
theorem B1631195 : Blo 722323 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B6710369 : Blo 722323 6710369 := bstep (se 2 (by rfl) ⟨2516388, by rfl⟩ : syracuseStep 6710369 = 5032777) B5032777
theorem B1631375 : Blo 722323 1631375 := bstep (se 1 (by rfl) ⟨1223531, by rfl⟩ : syracuseStep 1631375 = 2447063) B2447063
theorem B1631465 : Blo 722323 1631465 := bstep (se 2 (by rfl) ⟨611799, by rfl⟩ : syracuseStep 1631465 = 1223599) B1223599
theorem B2450681 : Blo 722323 2450681 := bstep (se 2 (by rfl) ⟨919005, by rfl⟩ : syracuseStep 2450681 = 1838011) B1838011
theorem B1631519 : Blo 722323 1631519 := bstep (se 1 (by rfl) ⟨1223639, by rfl⟩ : syracuseStep 1631519 = 2447279) B2447279
theorem B3663143 : Blo 722323 3663143 := bstep (se 1 (by rfl) ⟨2747357, by rfl⟩ : syracuseStep 3663143 = 5494715) B5494715
theorem B4646267 : Blo 722323 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B2450951 : Blo 722323 2450951 := bstep (se 1 (by rfl) ⟨1838213, by rfl⟩ : syracuseStep 2450951 = 3676427) B3676427
theorem B2319929 : Blo 722323 2319929 := bstep (se 2 (by rfl) ⟨869973, by rfl⟩ : syracuseStep 2319929 = 1739947) B1739947
theorem B1304147 : Blo 722323 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B812767 : Blo 722323 812767 := bstep (se 1 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 812767 = 1219151) B1219151
theorem B1828615 : Blo 722323 1828615 := bstep (se 1 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 1828615 = 2742923) B2742923
theorem B1632041 : Blo 722323 1632041 := bstep (se 2 (by rfl) ⟨612015, by rfl⟩ : syracuseStep 1632041 = 1224031) B1224031
theorem B6186887 : Blo 722323 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B1828889 : Blo 722323 1828889 := bstep (se 2 (by rfl) ⟨685833, by rfl⟩ : syracuseStep 1828889 = 1371667) B1371667
theorem B813343 : Blo 722323 813343 := bstep (se 1 (by rfl) ⟨610007, by rfl⟩ : syracuseStep 813343 = 1220015) B1220015
theorem B813631 : Blo 722323 813631 := bstep (se 1 (by rfl) ⟨610223, by rfl⟩ : syracuseStep 813631 = 1220447) B1220447
theorem B1633103 : Blo 722323 1633103 := bstep (se 1 (by rfl) ⟨1224827, by rfl⟩ : syracuseStep 1633103 = 2449655) B2449655
theorem B3140471 : Blo 722323 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B1633319 : Blo 722323 1633319 := bstep (se 1 (by rfl) ⟨1224989, by rfl⟩ : syracuseStep 1633319 = 2449979) B2449979
theorem B1633499 : Blo 722323 1633499 := bstep (se 1 (by rfl) ⟨1225124, by rfl⟩ : syracuseStep 1633499 = 2450249) B2450249
theorem B1371431 : Blo 722323 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B3665249 : Blo 722323 3665249 := bstep (se 2 (by rfl) ⟨1374468, by rfl⟩ : syracuseStep 3665249 = 2748937) B2748937
theorem B814459 : Blo 722323 814459 := bstep (se 1 (by rfl) ⟨610844, by rfl⟩ : syracuseStep 814459 = 1221689) B1221689
theorem B1633697 : Blo 722323 1633697 := bstep (se 2 (by rfl) ⟨612636, by rfl⟩ : syracuseStep 1633697 = 1225273) B1225273
theorem B4943663 : Blo 722323 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B978743 : Blo 722323 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B814927 : Blo 722323 814927 := bstep (se 1 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 814927 = 1222391) B1222391
theorem B2617217 : Blo 722323 2617217 := bstep (se 2 (by rfl) ⟨981456, by rfl⟩ : syracuseStep 2617217 = 1962913) B1962913
theorem B1830863 : Blo 722323 1830863 := bstep (se 1 (by rfl) ⟨1373147, by rfl⟩ : syracuseStep 1830863 = 2746295) B2746295
theorem B7827515 : Blo 722323 7827515 := bstep (se 1 (by rfl) ⟨5870636, by rfl⟩ : syracuseStep 7827515 = 11741273) B11741273
theorem B7073851 : Blo 722323 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B5501033 : Blo 722323 5501033 := bstep (se 2 (by rfl) ⟨2062887, by rfl⟩ : syracuseStep 5501033 = 4125775) B4125775
theorem B4124843 : Blo 722323 4124843 := bstep (se 1 (by rfl) ⟨3093632, by rfl⟩ : syracuseStep 4124843 = 6187265) B6187265
theorem B815323 : Blo 722323 815323 := bstep (se 1 (by rfl) ⟨611492, by rfl⟩ : syracuseStep 815323 = 1222985) B1222985
theorem B40104409 : Blo 722323 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B815611 : Blo 722323 815611 := bstep (se 1 (by rfl) ⟨611708, by rfl⟩ : syracuseStep 815611 = 1223417) B1223417
theorem B10711601 : Blo 722323 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B1831531 : Blo 722323 1831531 := bstep (se 1 (by rfl) ⟨1373648, by rfl⟩ : syracuseStep 1831531 = 2747297) B2747297
theorem B815791 : Blo 722323 815791 := bstep (se 1 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 815791 = 1223687) B1223687
theorem B2355895 : Blo 722323 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B1831835 : Blo 722323 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B816079 : Blo 722323 816079 := bstep (se 1 (by rfl) ⟨612059, by rfl⟩ : syracuseStep 816079 = 1224119) B1224119
theorem B979943 : Blo 722323 979943 := bstep (se 1 (by rfl) ⟨734957, by rfl⟩ : syracuseStep 979943 = 1469915) B1469915
theorem B1832179 : Blo 722323 1832179 := bstep (se 1 (by rfl) ⟨1374134, by rfl⟩ : syracuseStep 1832179 = 2748269) B2748269
theorem B3667193 : Blo 722323 3667193 := bstep (se 2 (by rfl) ⟨1375197, by rfl⟩ : syracuseStep 3667193 = 2750395) B2750395
theorem B1570079 : Blo 722323 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B816475 : Blo 722323 816475 := bstep (se 1 (by rfl) ⟨612356, by rfl⟩ : syracuseStep 816475 = 1224713) B1224713
theorem B816583 : Blo 722323 816583 := bstep (se 1 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 816583 = 1224875) B1224875
theorem B816943 : Blo 722323 816943 := bstep (se 1 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 816943 = 1225415) B1225415
theorem B817051 : Blo 722323 817051 := bstep (se 1 (by rfl) ⟨612788, by rfl⟩ : syracuseStep 817051 = 1225577) B1225577
theorem B1832969 : Blo 722323 1832969 := bstep (se 2 (by rfl) ⟨687363, by rfl⟩ : syracuseStep 1832969 = 1374727) B1374727
theorem B5863757 : Blo 722323 5863757 := bstep (se 3 (by rfl) ⟨1099454, by rfl⟩ : syracuseStep 5863757 = 2198909) B2198909
theorem B6191639 : Blo 722323 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B916039 : Blo 722323 916039 := bstep (se 1 (by rfl) ⟨687029, by rfl⟩ : syracuseStep 916039 = 1374059) B1374059
theorem B4127507 : Blo 722323 4127507 := bstep (se 1 (by rfl) ⟨3095630, by rfl⟩ : syracuseStep 4127507 = 6191261) B6191261
theorem B4651931 : Blo 722323 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B1834123 : Blo 722323 1834123 := bstep (se 1 (by rfl) ⟨1375592, by rfl⟩ : syracuseStep 1834123 = 2751185) B2751185
theorem B2063549 : Blo 722323 2063549 := bstep (se 3 (by rfl) ⟨386915, by rfl⟩ : syracuseStep 2063549 = 773831) B773831
theorem B916859 : Blo 722323 916859 := bstep (se 1 (by rfl) ⟨687644, by rfl⟩ : syracuseStep 916859 = 1375289) B1375289
theorem B1834427 : Blo 722323 1834427 := bstep (se 1 (by rfl) ⟨1375820, by rfl⟩ : syracuseStep 1834427 = 2751641) B2751641
theorem B4652569 : Blo 722323 4652569 := bstep (se 2 (by rfl) ⟨1744713, by rfl⟩ : syracuseStep 4652569 = 3489427) B3489427
theorem B1736353 : Blo 722323 1736353 := bstep (se 2 (by rfl) ⟨651132, by rfl⟩ : syracuseStep 1736353 = 1302265) B1302265
theorem B1376041 : Blo 722323 1376041 := bstep (se 2 (by rfl) ⟨516015, by rfl⟩ : syracuseStep 1376041 = 1032031) B1032031
theorem B2064665 : Blo 722323 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B917887 : Blo 722323 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B17858981 : Blo 722323 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B2064847 : Blo 722323 2064847 := bstep (se 1 (by rfl) ⟨1548635, by rfl⟩ : syracuseStep 2064847 = 3097271) B3097271
theorem B9306575 : Blo 722323 9306575 := bstep (se 1 (by rfl) ⟨6979931, by rfl⟩ : syracuseStep 9306575 = 13959863) B13959863
theorem B12387167 : Blo 722323 12387167 := bstep (se 1 (by rfl) ⟨9290375, by rfl⟩ : syracuseStep 12387167 = 18580751) B18580751
theorem B6357917 : Blo 722323 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B722331 : Blo 722323 722331 := bstep (se 1 (by rfl) ⟨541748, by rfl⟩ : syracuseStep 722331 = 1083497) B1083497
theorem B3474859 : Blo 722323 3474859 := bstep (se 1 (by rfl) ⟨2606144, by rfl⟩ : syracuseStep 3474859 = 5212289) B5212289
theorem B722543 : Blo 722323 722543 := bstep (se 1 (by rfl) ⟨541907, by rfl⟩ : syracuseStep 722543 = 1083815) B1083815
theorem B1836665 : Blo 722323 1836665 := bstep (se 2 (by rfl) ⟨688749, by rfl⟩ : syracuseStep 1836665 = 1377499) B1377499
theorem B722599 : Blo 722323 722599 := bstep (se 1 (by rfl) ⟨541949, by rfl⟩ : syracuseStep 722599 = 1083899) B1083899
theorem B722683 : Blo 722323 722683 := bstep (se 1 (by rfl) ⟨542012, by rfl⟩ : syracuseStep 722683 = 1084025) B1084025
theorem B2197255 : Blo 722323 2197255 := bstep (se 1 (by rfl) ⟨1647941, by rfl⟩ : syracuseStep 2197255 = 3295883) B3295883
theorem B6620957 : Blo 722323 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B722719 : Blo 722323 722719 := bstep (se 1 (by rfl) ⟨542039, by rfl⟩ : syracuseStep 722719 = 1084079) B1084079
theorem B722751 : Blo 722323 722751 := bstep (se 1 (by rfl) ⟨542063, by rfl⟩ : syracuseStep 722751 = 1084127) B1084127
theorem B2066305 : Blo 722323 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B722927 : Blo 722323 722927 := bstep (se 1 (by rfl) ⟨542195, by rfl⟩ : syracuseStep 722927 = 1084391) B1084391
theorem B723099 : Blo 722323 723099 := bstep (se 1 (by rfl) ⟨542324, by rfl⟩ : syracuseStep 723099 = 1084649) B1084649
theorem B723135 : Blo 722323 723135 := bstep (se 1 (by rfl) ⟨542351, by rfl⟩ : syracuseStep 723135 = 1084703) B1084703
theorem B2754769 : Blo 722323 2754769 := bstep (se 2 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 2754769 = 2066077) B2066077
theorem B2066647 : Blo 722323 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1083689 : Blo 722323 1083689 := bstep (se 2 (by rfl) ⟨406383, by rfl⟩ : syracuseStep 1083689 = 812767) B812767
theorem B1083695 : Blo 722323 1083695 := bstep (se 1 (by rfl) ⟨812771, by rfl⟩ : syracuseStep 1083695 = 1625543) B1625543
theorem B723247 : Blo 722323 723247 := bstep (se 1 (by rfl) ⟨542435, by rfl⟩ : syracuseStep 723247 = 1084871) B1084871
theorem B723483 : Blo 722323 723483 := bstep (se 1 (by rfl) ⟨542612, by rfl⟩ : syracuseStep 723483 = 1085225) B1085225
theorem B1083935 : Blo 722323 1083935 := bstep (se 1 (by rfl) ⟨812951, by rfl⟩ : syracuseStep 1083935 = 1625903) B1625903
theorem B723487 : Blo 722323 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B723803 : Blo 722323 723803 := bstep (se 1 (by rfl) ⟨542852, by rfl⟩ : syracuseStep 723803 = 1085705) B1085705
theorem B1084319 : Blo 722323 1084319 := bstep (se 1 (by rfl) ⟨813239, by rfl⟩ : syracuseStep 1084319 = 1626479) B1626479
theorem B723871 : Blo 722323 723871 := bstep (se 1 (by rfl) ⟨542903, by rfl⟩ : syracuseStep 723871 = 1085807) B1085807
theorem B17894317 : Blo 722323 17894317 := bstep (se 3 (by rfl) ⟨3355184, by rfl⟩ : syracuseStep 17894317 = 6710369) B6710369
theorem B1084367 : Blo 722323 1084367 := bstep (se 1 (by rfl) ⟨813275, by rfl⟩ : syracuseStep 1084367 = 1626551) B1626551
theorem B2755559 : Blo 722323 2755559 := bstep (se 1 (by rfl) ⟨2066669, by rfl⟩ : syracuseStep 2755559 = 4133339) B4133339
theorem B1739755 : Blo 722323 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B1084457 : Blo 722323 1084457 := bstep (se 2 (by rfl) ⟨406671, by rfl⟩ : syracuseStep 1084457 = 813343) B813343
theorem B1084463 : Blo 722323 1084463 := bstep (se 1 (by rfl) ⟨813347, by rfl⟩ : syracuseStep 1084463 = 1626695) B1626695
theorem B724015 : Blo 722323 724015 := bstep (se 1 (by rfl) ⟨543011, by rfl⟩ : syracuseStep 724015 = 1086023) B1086023
theorem B1084487 : Blo 722323 1084487 := bstep (se 1 (by rfl) ⟨813365, by rfl⟩ : syracuseStep 1084487 = 1626731) B1626731
theorem B724039 : Blo 722323 724039 := bstep (se 1 (by rfl) ⟨543029, by rfl⟩ : syracuseStep 724039 = 1086059) B1086059
theorem B724191 : Blo 722323 724191 := bstep (se 1 (by rfl) ⟨543143, by rfl⟩ : syracuseStep 724191 = 1086287) B1086287
theorem B1084751 : Blo 722323 1084751 := bstep (se 1 (by rfl) ⟨813563, by rfl⟩ : syracuseStep 1084751 = 1627127) B1627127
theorem B1084841 : Blo 722323 1084841 := bstep (se 2 (by rfl) ⟨406815, by rfl⟩ : syracuseStep 1084841 = 813631) B813631
theorem B724455 : Blo 722323 724455 := bstep (se 1 (by rfl) ⟨543341, by rfl⟩ : syracuseStep 724455 = 1086683) B1086683
theorem B1084991 : Blo 722323 1084991 := bstep (se 1 (by rfl) ⟨813743, by rfl⟩ : syracuseStep 1084991 = 1627487) B1627487
theorem B724571 : Blo 722323 724571 := bstep (se 1 (by rfl) ⟨543428, by rfl⟩ : syracuseStep 724571 = 1086857) B1086857
theorem B5508809 : Blo 722323 5508809 := bstep (se 2 (by rfl) ⟨2065803, by rfl⟩ : syracuseStep 5508809 = 4131607) B4131607
theorem B1085255 : Blo 722323 1085255 := bstep (se 1 (by rfl) ⟨813941, by rfl⟩ : syracuseStep 1085255 = 1627883) B1627883
theorem B724807 : Blo 722323 724807 := bstep (se 1 (by rfl) ⟨543605, by rfl⟩ : syracuseStep 724807 = 1087211) B1087211
theorem B1085339 : Blo 722323 1085339 := bstep (se 1 (by rfl) ⟨814004, by rfl⟩ : syracuseStep 1085339 = 1628009) B1628009
theorem B1544159 : Blo 722323 1544159 := bstep (se 1 (by rfl) ⟨1158119, by rfl⟩ : syracuseStep 1544159 = 2316239) B2316239
theorem B724959 : Blo 722323 724959 := bstep (se 1 (by rfl) ⟨543719, by rfl⟩ : syracuseStep 724959 = 1087439) B1087439
theorem B4132883 : Blo 722323 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B3477725 : Blo 722323 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B725223 : Blo 722323 725223 := bstep (se 1 (by rfl) ⟨543917, by rfl⟩ : syracuseStep 725223 = 1087835) B1087835
theorem B725375 : Blo 722323 725375 := bstep (se 1 (by rfl) ⟨544031, by rfl⟩ : syracuseStep 725375 = 1088063) B1088063
theorem B6263203 : Blo 722323 6263203 := bstep (se 1 (by rfl) ⟨4697402, by rfl⟩ : syracuseStep 6263203 = 9394805) B9394805
theorem B1085903 : Blo 722323 1085903 := bstep (se 1 (by rfl) ⟨814427, by rfl⟩ : syracuseStep 1085903 = 1628855) B1628855
theorem B725455 : Blo 722323 725455 := bstep (se 1 (by rfl) ⟨544091, by rfl⟩ : syracuseStep 725455 = 1088183) B1088183
theorem B1085945 : Blo 722323 1085945 := bstep (se 2 (by rfl) ⟨407229, by rfl⟩ : syracuseStep 1085945 = 814459) B814459
theorem B2757199 : Blo 722323 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B1086047 : Blo 722323 1086047 := bstep (se 1 (by rfl) ⟨814535, by rfl⟩ : syracuseStep 1086047 = 1629071) B1629071
theorem B725607 : Blo 722323 725607 := bstep (se 1 (by rfl) ⟨544205, by rfl⟩ : syracuseStep 725607 = 1088411) B1088411
theorem B725871 : Blo 722323 725871 := bstep (se 1 (by rfl) ⟨544403, by rfl⟩ : syracuseStep 725871 = 1088807) B1088807
theorem B725927 : Blo 722323 725927 := bstep (se 1 (by rfl) ⟨544445, by rfl⟩ : syracuseStep 725927 = 1088891) B1088891
theorem B3675131 : Blo 722323 3675131 := bstep (se 1 (by rfl) ⟨2756348, by rfl⟩ : syracuseStep 3675131 = 5512697) B5512697
theorem B726011 : Blo 722323 726011 := bstep (se 1 (by rfl) ⟨544508, by rfl⟩ : syracuseStep 726011 = 1089017) B1089017
theorem B27792395 : Blo 722323 27792395 := bstep (se 1 (by rfl) ⟨20844296, by rfl⟩ : syracuseStep 27792395 = 41688593) B41688593
theorem B2757671 : Blo 722323 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B1086527 : Blo 722323 1086527 := bstep (se 1 (by rfl) ⟨814895, by rfl⟩ : syracuseStep 1086527 = 1629791) B1629791
theorem B726079 : Blo 722323 726079 := bstep (se 1 (by rfl) ⟨544559, by rfl⟩ : syracuseStep 726079 = 1089119) B1089119
theorem B1086569 : Blo 722323 1086569 := bstep (se 2 (by rfl) ⟨407463, by rfl⟩ : syracuseStep 1086569 = 814927) B814927
theorem B1086671 : Blo 722323 1086671 := bstep (se 1 (by rfl) ⟨815003, by rfl⟩ : syracuseStep 1086671 = 1630007) B1630007
theorem B726223 : Blo 722323 726223 := bstep (se 1 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 726223 = 1089335) B1089335
theorem B4396265 : Blo 722323 4396265 := bstep (se 2 (by rfl) ⟨1648599, by rfl⟩ : syracuseStep 4396265 = 3297199) B3297199
theorem B1086875 : Blo 722323 1086875 := bstep (se 1 (by rfl) ⟨815156, by rfl⟩ : syracuseStep 1086875 = 1630313) B1630313
theorem B3675617 : Blo 722323 3675617 := bstep (se 2 (by rfl) ⟨1378356, by rfl⟩ : syracuseStep 3675617 = 2756713) B2756713
theorem B1545799 : Blo 722323 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B1087097 : Blo 722323 1087097 := bstep (se 2 (by rfl) ⟨407661, by rfl⟩ : syracuseStep 1087097 = 815323) B815323
theorem B1087199 : Blo 722323 1087199 := bstep (se 1 (by rfl) ⟨815399, by rfl⟩ : syracuseStep 1087199 = 1630799) B1630799
theorem B6952715 : Blo 722323 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B6199051 : Blo 722323 6199051 := bstep (se 1 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 6199051 = 9298577) B9298577
theorem B1087295 : Blo 722323 1087295 := bstep (se 1 (by rfl) ⟨815471, by rfl⟩ : syracuseStep 1087295 = 1630943) B1630943
theorem B1087463 : Blo 722323 1087463 := bstep (se 1 (by rfl) ⟨815597, by rfl⟩ : syracuseStep 1087463 = 1631195) B1631195
theorem B1087481 : Blo 722323 1087481 := bstep (se 2 (by rfl) ⟨407805, by rfl⟩ : syracuseStep 1087481 = 815611) B815611
theorem B7837721 : Blo 722323 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1087583 : Blo 722323 1087583 := bstep (se 1 (by rfl) ⟨815687, by rfl⟩ : syracuseStep 1087583 = 1631375) B1631375
theorem B1087643 : Blo 722323 1087643 := bstep (se 1 (by rfl) ⟨815732, by rfl⟩ : syracuseStep 1087643 = 1631465) B1631465
theorem B1087679 : Blo 722323 1087679 := bstep (se 1 (by rfl) ⟨815759, by rfl⟩ : syracuseStep 1087679 = 1631519) B1631519
theorem B15636685 : Blo 722323 15636685 := bstep (se 3 (by rfl) ⟨2931878, by rfl⟩ : syracuseStep 15636685 = 5863757) B5863757
theorem B1087721 : Blo 722323 1087721 := bstep (se 2 (by rfl) ⟨407895, by rfl⟩ : syracuseStep 1087721 = 815791) B815791
theorem B1546619 : Blo 722323 1546619 := bstep (se 1 (by rfl) ⟨1159964, by rfl⟩ : syracuseStep 1546619 = 2319929) B2319929
theorem B5872061 : Blo 722323 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B1088027 : Blo 722323 1088027 := bstep (se 1 (by rfl) ⟨816020, by rfl⟩ : syracuseStep 1088027 = 1632041) B1632041
theorem B1088105 : Blo 722323 1088105 := bstep (se 2 (by rfl) ⟨408039, by rfl⟩ : syracuseStep 1088105 = 816079) B816079
theorem B3480185 : Blo 722323 3480185 := bstep (se 2 (by rfl) ⟨1305069, by rfl⟩ : syracuseStep 3480185 = 2610139) B2610139
theorem B1219259 : Blo 722323 1219259 := bstep (se 1 (by rfl) ⟨914444, by rfl⟩ : syracuseStep 1219259 = 1828889) B1828889
theorem B1088633 : Blo 722323 1088633 := bstep (se 2 (by rfl) ⟨408237, by rfl⟩ : syracuseStep 1088633 = 816475) B816475
theorem B1088735 : Blo 722323 1088735 := bstep (se 1 (by rfl) ⟨816551, by rfl⟩ : syracuseStep 1088735 = 1633103) B1633103
theorem B1088777 : Blo 722323 1088777 := bstep (se 2 (by rfl) ⟨408291, by rfl⟩ : syracuseStep 1088777 = 816583) B816583
theorem B1088879 : Blo 722323 1088879 := bstep (se 1 (by rfl) ⟨816659, by rfl⟩ : syracuseStep 1088879 = 1633319) B1633319
theorem B1088999 : Blo 722323 1088999 := bstep (se 1 (by rfl) ⟨816749, by rfl⟩ : syracuseStep 1088999 = 1633499) B1633499
theorem B1089131 : Blo 722323 1089131 := bstep (se 1 (by rfl) ⟨816848, by rfl⟩ : syracuseStep 1089131 = 1633697) B1633697
theorem B1089257 : Blo 722323 1089257 := bstep (se 2 (by rfl) ⟨408471, by rfl⟩ : syracuseStep 1089257 = 816943) B816943
theorem B1089401 : Blo 722323 1089401 := bstep (se 2 (by rfl) ⟨408525, by rfl⟩ : syracuseStep 1089401 = 817051) B817051
theorem B1744811 : Blo 722323 1744811 := bstep (se 1 (by rfl) ⟨1308608, by rfl⟩ : syracuseStep 1744811 = 2617217) B2617217
theorem B1220575 : Blo 722323 1220575 := bstep (se 1 (by rfl) ⟨915431, by rfl⟩ : syracuseStep 1220575 = 1830863) B1830863
theorem B5218343 : Blo 722323 5218343 := bstep (se 1 (by rfl) ⟨3913757, by rfl⟩ : syracuseStep 5218343 = 7827515) B7827515
theorem B1221223 : Blo 722323 1221223 := bstep (se 1 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 1221223 = 1831835) B1831835
theorem B9904841 : Blo 722323 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B1221385 : Blo 722323 1221385 := bstep (se 2 (by rfl) ⟨458019, by rfl⟩ : syracuseStep 1221385 = 916039) B916039
theorem B1221979 : Blo 722323 1221979 := bstep (se 1 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 1221979 = 1832969) B1832969
theorem B17573365 : Blo 722323 17573365 := bstep (se 5 (by rfl) ⟨823751, by rfl⟩ : syracuseStep 17573365 = 1647503) B1647503
theorem B6203425 : Blo 722323 6203425 := bstep (se 2 (by rfl) ⟨2326284, by rfl⟩ : syracuseStep 6203425 = 4652569) B4652569
theorem B1222951 : Blo 722323 1222951 := bstep (se 1 (by rfl) ⟨917213, by rfl⟩ : syracuseStep 1222951 = 1834427) B1834427
theorem B18787301 : Blo 722323 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B1223903 : Blo 722323 1223903 := bstep (se 1 (by rfl) ⟨917927, by rfl⟩ : syracuseStep 1223903 = 1835855) B1835855
theorem B1158799 : Blo 722323 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B1224335 : Blo 722323 1224335 := bstep (se 1 (by rfl) ⟨918251, by rfl⟩ : syracuseStep 1224335 = 1836503) B1836503
theorem B1224571 : Blo 722323 1224571 := bstep (se 1 (by rfl) ⟨918428, by rfl⟩ : syracuseStep 1224571 = 1836857) B1836857
theorem B8269775 : Blo 722323 8269775 := bstep (se 1 (by rfl) ⟨6202331, by rfl⟩ : syracuseStep 8269775 = 12404663) B12404663
theorem B17576099 : Blo 722323 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B3485891 : Blo 722323 3485891 := bstep (se 1 (by rfl) ⟨2614418, by rfl⟩ : syracuseStep 3485891 = 5228837) B5228837
theorem B4632785 : Blo 722323 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B6173081 : Blo 722323 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B1028551 : Blo 722323 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B4698593 : Blo 722323 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B1028585 : Blo 722323 1028585 := bstep (se 2 (by rfl) ⟨385719, by rfl⟩ : syracuseStep 1028585 = 771439) B771439
theorem B1029115 : Blo 722323 1029115 := bstep (se 1 (by rfl) ⟨771836, by rfl⟩ : syracuseStep 1029115 = 1543673) B1543673
theorem B2438153 : Blo 722323 2438153 := bstep (se 2 (by rfl) ⟨914307, by rfl⟩ : syracuseStep 2438153 = 1828615) B1828615
theorem B2438207 : Blo 722323 2438207 := bstep (se 1 (by rfl) ⟨1828655, by rfl⟩ : syracuseStep 2438207 = 3657311) B3657311
theorem B3093821 : Blo 722323 3093821 := bstep (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) B1160183
theorem B5584283 : Blo 722323 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B1652395 : Blo 722323 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B10435067 : Blo 722323 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B10598951 : Blo 722323 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B2472601 : Blo 722323 2472601 := bstep (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) B1854451
theorem B1325879 : Blo 722323 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B1031239 : Blo 722323 1031239 := bstep (se 1 (by rfl) ⟨773429, by rfl⟩ : syracuseStep 1031239 = 1546859) B1546859
theorem B5487911 : Blo 722323 5487911 := bstep (se 1 (by rfl) ⟨4115933, by rfl⟩ : syracuseStep 5487911 = 8231867) B8231867
theorem B4963751 : Blo 722323 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B2441015 : Blo 722323 2441015 := bstep (se 1 (by rfl) ⟨1830761, by rfl⟩ : syracuseStep 2441015 = 3661523) B3661523
theorem B1032059 : Blo 722323 1032059 := bstep (se 1 (by rfl) ⟨774044, by rfl⟩ : syracuseStep 1032059 = 1548089) B1548089
theorem B2441447 : Blo 722323 2441447 := bstep (se 1 (by rfl) ⟨1831085, by rfl⟩ : syracuseStep 2441447 = 3662171) B3662171
theorem B10731959 : Blo 722323 10731959 := bstep (se 1 (by rfl) ⟨8048969, by rfl⟩ : syracuseStep 10731959 = 16097939) B16097939
theorem B1032697 : Blo 722323 1032697 := bstep (se 2 (by rfl) ⟨387261, by rfl⟩ : syracuseStep 1032697 = 774523) B774523
theorem B2933243 : Blo 722323 2933243 := bstep (se 1 (by rfl) ⟨2199932, by rfl⟩ : syracuseStep 2933243 = 4399865) B4399865
theorem B2605871 : Blo 722323 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B2442041 : Blo 722323 2442041 := bstep (se 2 (by rfl) ⟨915765, by rfl⟩ : syracuseStep 2442041 = 1831531) B1831531
theorem B2442095 : Blo 722323 2442095 := bstep (se 1 (by rfl) ⟨1831571, by rfl⟩ : syracuseStep 2442095 = 3663143) B3663143
theorem B3097511 : Blo 722323 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B2442905 : Blo 722323 2442905 := bstep (se 2 (by rfl) ⟨916089, by rfl⟩ : syracuseStep 2442905 = 1832179) B1832179
theorem B2443499 : Blo 722323 2443499 := bstep (se 1 (by rfl) ⟨1832624, by rfl⟩ : syracuseStep 2443499 = 3665249) B3665249
theorem B8243531 : Blo 722323 8243531 := bstep (se 1 (by rfl) ⟨6182648, by rfl⟩ : syracuseStep 8243531 = 12365297) B12365297
theorem B3295775 : Blo 722323 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B9292427 : Blo 722323 9292427 := bstep (se 1 (by rfl) ⟨6969320, by rfl⟩ : syracuseStep 9292427 = 13938641) B13938641
theorem B4639447 : Blo 722323 4639447 := bstep (se 1 (by rfl) ⟨3479585, by rfl⟩ : syracuseStep 4639447 = 6959171) B6959171
theorem B904171 : Blo 722323 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B1953193 : Blo 722323 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B3657149 : Blo 722323 3657149 := bstep (se 3 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 3657149 = 1371431) B1371431
theorem B2444795 : Blo 722323 2444795 := bstep (se 1 (by rfl) ⟨1833596, by rfl⟩ : syracuseStep 2444795 = 3667193) B3667193
theorem B2444957 : Blo 722323 2444957 := bstep (se 3 (by rfl) ⟨458429, by rfl⟩ : syracuseStep 2444957 = 916859) B916859
theorem B773959 : Blo 722323 773959 := bstep (se 1 (by rfl) ⟨580469, by rfl⟩ : syracuseStep 773959 = 1160939) B1160939
theorem B2936681 : Blo 722323 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B1626011 : Blo 722323 1626011 := bstep (se 1 (by rfl) ⟨1219508, by rfl⟩ : syracuseStep 1626011 = 2439017) B2439017
theorem B2674873 : Blo 722323 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B2445497 : Blo 722323 2445497 := bstep (se 2 (by rfl) ⟨917061, by rfl⟩ : syracuseStep 2445497 = 1834123) B1834123
theorem B1626299 : Blo 722323 1626299 := bstep (se 1 (by rfl) ⟨1219724, by rfl⟩ : syracuseStep 1626299 = 2439449) B2439449
theorem B3101287 : Blo 722323 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B3920507 : Blo 722323 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B1626785 : Blo 722323 1626785 := bstep (se 2 (by rfl) ⟨610044, by rfl⟩ : syracuseStep 1626785 = 1220089) B1220089
theorem B15061801 : Blo 722323 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B2609981 : Blo 722323 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B2315137 : Blo 722323 2315137 := bstep (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) B1736353
theorem B16962509 : Blo 722323 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B1627145 : Blo 722323 1627145 := bstep (se 2 (by rfl) ⟨610179, by rfl⟩ : syracuseStep 1627145 = 1220359) B1220359
theorem B1627199 : Blo 722323 1627199 := bstep (se 1 (by rfl) ⟨1220399, by rfl⟩ : syracuseStep 1627199 = 2440799) B2440799
theorem B8246447 : Blo 722323 8246447 := bstep (se 1 (by rfl) ⟨6184835, by rfl⟩ : syracuseStep 8246447 = 12369671) B12369671
theorem B775343 : Blo 722323 775343 := bstep (se 1 (by rfl) ⟨581507, by rfl⟩ : syracuseStep 775343 = 1163015) B1163015
theorem B3724663 : Blo 722323 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B4117985 : Blo 722323 4117985 := bstep (se 2 (by rfl) ⟨1544244, by rfl⟩ : syracuseStep 4117985 = 3088489) B3088489
theorem B1628135 : Blo 722323 1628135 := bstep (se 1 (by rfl) ⟨1221101, by rfl⟩ : syracuseStep 1628135 = 2442203) B2442203
theorem B1628153 : Blo 722323 1628153 := bstep (se 2 (by rfl) ⟨610557, by rfl⟩ : syracuseStep 1628153 = 1221115) B1221115
theorem B1628243 : Blo 722323 1628243 := bstep (se 1 (by rfl) ⟨1221182, by rfl⟩ : syracuseStep 1628243 = 2442365) B2442365
theorem B2316443 : Blo 722323 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B1628315 : Blo 722323 1628315 := bstep (se 1 (by rfl) ⟨1221236, by rfl⟩ : syracuseStep 1628315 = 2442473) B2442473
theorem B2447603 : Blo 722323 2447603 := bstep (se 1 (by rfl) ⟨1835702, by rfl⟩ : syracuseStep 2447603 = 3671405) B3671405
theorem B1628423 : Blo 722323 1628423 := bstep (se 1 (by rfl) ⟨1221317, by rfl⟩ : syracuseStep 1628423 = 2442635) B2442635
theorem B2447657 : Blo 722323 2447657 := bstep (se 2 (by rfl) ⟨917871, by rfl⟩ : syracuseStep 2447657 = 1835743) B1835743
theorem B1628729 : Blo 722323 1628729 := bstep (se 2 (by rfl) ⟨610773, by rfl⟩ : syracuseStep 1628729 = 1221547) B1221547
theorem B1465609 : Blo 722323 1465609 := bstep (se 2 (by rfl) ⟨549603, by rfl⟩ : syracuseStep 1465609 = 1099207) B1099207
theorem B1629449 : Blo 722323 1629449 := bstep (se 2 (by rfl) ⟨611043, by rfl⟩ : syracuseStep 1629449 = 1222087) B1222087
theorem B2449223 : Blo 722323 2449223 := bstep (se 1 (by rfl) ⟨1836917, by rfl⟩ : syracuseStep 2449223 = 3673835) B3673835
theorem B2449277 : Blo 722323 2449277 := bstep (se 3 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 2449277 = 918479) B918479
theorem B14147459 : Blo 722323 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B2613181 : Blo 722323 2613181 := bstep (se 3 (by rfl) ⟨489971, by rfl⟩ : syracuseStep 2613181 = 979943) B979943
theorem B23486435 : Blo 722323 23486435 := bstep (se 1 (by rfl) ⟨17614826, by rfl⟩ : syracuseStep 23486435 = 35229653) B35229653
theorem B8249363 : Blo 722323 8249363 := bstep (se 1 (by rfl) ⟨6187022, by rfl⟩ : syracuseStep 8249363 = 12374045) B12374045
theorem B2449547 : Blo 722323 2449547 := bstep (se 1 (by rfl) ⟨1837160, by rfl⟩ : syracuseStep 2449547 = 3674321) B3674321
theorem B1630439 : Blo 722323 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B161014169 : Blo 722323 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B2449871 : Blo 722323 2449871 := bstep (se 1 (by rfl) ⟨1837403, by rfl⟩ : syracuseStep 2449871 = 3674807) B3674807
theorem B2450195 : Blo 722323 2450195 := bstep (se 1 (by rfl) ⟨1837646, by rfl⟩ : syracuseStep 2450195 = 3675293) B3675293
theorem B4121401 : Blo 722323 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B1631033 : Blo 722323 1631033 := bstep (se 2 (by rfl) ⟨611637, by rfl⟩ : syracuseStep 1631033 = 1223275) B1223275
theorem B1631087 : Blo 722323 1631087 := bstep (se 1 (by rfl) ⟨1223315, by rfl⟩ : syracuseStep 1631087 = 2446631) B2446631
theorem B1303607 : Blo 722323 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B1631663 : Blo 722323 1631663 := bstep (se 1 (by rfl) ⟨1223747, by rfl⟩ : syracuseStep 1631663 = 2447495) B2447495
theorem B4416943 : Blo 722323 4416943 := bstep (se 1 (by rfl) ⟨3312707, by rfl⟩ : syracuseStep 4416943 = 6625415) B6625415
theorem B2451059 : Blo 722323 2451059 := bstep (se 1 (by rfl) ⟨1838294, by rfl⟩ : syracuseStep 2451059 = 3676589) B3676589
theorem B2451167 : Blo 722323 2451167 := bstep (se 1 (by rfl) ⟨1838375, by rfl⟩ : syracuseStep 2451167 = 3676751) B3676751
theorem B2451329 : Blo 722323 2451329 := bstep (se 2 (by rfl) ⟨919248, by rfl⟩ : syracuseStep 2451329 = 1838497) B1838497
theorem B2746493 : Blo 722323 2746493 := bstep (se 3 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 2746493 = 1029935) B1029935
theorem B1632491 : Blo 722323 1632491 := bstep (se 1 (by rfl) ⟨1224368, by rfl⟩ : syracuseStep 1632491 = 2448737) B2448737
theorem B1468729 : Blo 722323 1468729 := bstep (se 2 (by rfl) ⟨550773, by rfl⟩ : syracuseStep 1468729 = 1101547) B1101547
theorem B38168981 : Blo 722323 38168981 := bstep (se 6 (by rfl) ⟨894585, by rfl⟩ : syracuseStep 38168981 = 1789171) B1789171
theorem B2320903 : Blo 722323 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B813595 : Blo 722323 813595 := bstep (se 1 (by rfl) ⟨610196, by rfl⟩ : syracuseStep 813595 = 1220393) B1220393
theorem B9300581 : Blo 722323 9300581 := bstep (se 4 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 9300581 = 1743859) B1743859
theorem B4123385 : Blo 722323 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B9431801 : Blo 722323 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B2321455 : Blo 722323 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B53472545 : Blo 722323 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B814567 : Blo 722323 814567 := bstep (se 1 (by rfl) ⟨610925, by rfl⟩ : syracuseStep 814567 = 1221851) B1221851
theorem B1633787 : Blo 722323 1633787 := bstep (se 1 (by rfl) ⟨1225340, by rfl⟩ : syracuseStep 1633787 = 2450681) B2450681
theorem B3141193 : Blo 722323 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B1633967 : Blo 722323 1633967 := bstep (se 1 (by rfl) ⟨1225475, by rfl⟩ : syracuseStep 1633967 = 2450951) B2450951
theorem B4124591 : Blo 722323 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B815071 : Blo 722323 815071 := bstep (se 1 (by rfl) ⟨611303, by rfl⟩ : syracuseStep 815071 = 1222607) B1222607
theorem B2060417 : Blo 722323 2060417 := bstep (se 2 (by rfl) ⟨772656, by rfl⟩ : syracuseStep 2060417 = 1545313) B1545313
theorem B2322685 : Blo 722323 2322685 := bstep (se 3 (by rfl) ⟨435503, by rfl⟩ : syracuseStep 2322685 = 871007) B871007
theorem B2322697 : Blo 722323 2322697 := bstep (se 2 (by rfl) ⟨871011, by rfl⟩ : syracuseStep 2322697 = 1742023) B1742023
theorem B2060599 : Blo 722323 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B2093647 : Blo 722323 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B815719 : Blo 722323 815719 := bstep (se 1 (by rfl) ⟨611789, by rfl⟩ : syracuseStep 815719 = 1223579) B1223579
theorem B152466137 : Blo 722323 152466137 := bstep (se 2 (by rfl) ⟨57174801, by rfl⟩ : syracuseStep 152466137 = 114349603) B114349603
theorem B8615159 : Blo 722323 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B3667355 : Blo 722323 3667355 := bstep (se 1 (by rfl) ⟨2750516, by rfl⟩ : syracuseStep 3667355 = 5501033) B5501033
theorem B2749895 : Blo 722323 2749895 := bstep (se 1 (by rfl) ⟨2062421, by rfl⟩ : syracuseStep 2749895 = 4124843) B4124843
theorem B7141067 : Blo 722323 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B882671 : Blo 722323 882671 := bstep (se 1 (by rfl) ⟨662003, by rfl⟩ : syracuseStep 882671 = 1324007) B1324007
theorem B1046719 : Blo 722323 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B12712301 : Blo 722323 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B32143979 : Blo 722323 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B4127759 : Blo 722323 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B2751671 : Blo 722323 2751671 := bstep (se 1 (by rfl) ⟨2063753, by rfl⟩ : syracuseStep 2751671 = 4127507) B4127507
theorem B8813929 : Blo 722323 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B1375699 : Blo 722323 1375699 := bstep (se 1 (by rfl) ⟨1031774, by rfl⟩ : syracuseStep 1375699 = 2063549) B2063549
theorem B1834721 : Blo 722323 1834721 := bstep (se 2 (by rfl) ⟨688020, by rfl⟩ : syracuseStep 1834721 = 1376041) B1376041
theorem B10419961 : Blo 722323 10419961 := bstep (se 2 (by rfl) ⟨3907485, by rfl⟩ : syracuseStep 10419961 = 7814971) B7814971
theorem B5013335 : Blo 722323 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B1376443 : Blo 722323 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B8258111 : Blo 722323 8258111 := bstep (se 1 (by rfl) ⟨6193583, by rfl⟩ : syracuseStep 8258111 = 12387167) B12387167
theorem B2753129 : Blo 722323 2753129 := bstep (se 2 (by rfl) ⟨1032423, by rfl⟩ : syracuseStep 2753129 = 2064847) B2064847
theorem B2065007 : Blo 722323 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B1376929 : Blo 722323 1376929 := bstep (se 2 (by rfl) ⟨516348, by rfl⟩ : syracuseStep 1376929 = 1032697) B1032697
theorem B722459 : Blo 722323 722459 := bstep (se 1 (by rfl) ⟨541844, by rfl⟩ : syracuseStep 722459 = 1083689) B1083689
theorem B722463 : Blo 722323 722463 := bstep (se 1 (by rfl) ⟨541847, by rfl⟩ : syracuseStep 722463 = 1083695) B1083695
theorem B722623 : Blo 722323 722623 := bstep (se 1 (by rfl) ⟨541967, by rfl⟩ : syracuseStep 722623 = 1083935) B1083935
theorem B6194951 : Blo 722323 6194951 := bstep (se 1 (by rfl) ⟨4646213, by rfl⟩ : syracuseStep 6194951 = 9292427) B9292427
theorem B722879 : Blo 722323 722879 := bstep (se 1 (by rfl) ⟨542159, by rfl⟩ : syracuseStep 722879 = 1084319) B1084319
theorem B722911 : Blo 722323 722911 := bstep (se 1 (by rfl) ⟨542183, by rfl⟩ : syracuseStep 722911 = 1084367) B1084367
theorem B1837039 : Blo 722323 1837039 := bstep (se 1 (by rfl) ⟨1377779, by rfl⟩ : syracuseStep 1837039 = 2755559) B2755559
theorem B23431153 : Blo 722323 23431153 := bstep (se 2 (by rfl) ⟨8786682, by rfl⟩ : syracuseStep 23431153 = 17573365) B17573365
theorem B722971 : Blo 722323 722971 := bstep (se 1 (by rfl) ⟨542228, by rfl⟩ : syracuseStep 722971 = 1084457) B1084457
theorem B722975 : Blo 722323 722975 := bstep (se 1 (by rfl) ⟨542231, by rfl⟩ : syracuseStep 722975 = 1084463) B1084463
theorem B722991 : Blo 722323 722991 := bstep (se 1 (by rfl) ⟨542243, by rfl⟩ : syracuseStep 722991 = 1084487) B1084487
theorem B6948989 : Blo 722323 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B723167 : Blo 722323 723167 := bstep (se 1 (by rfl) ⟨542375, by rfl⟩ : syracuseStep 723167 = 1084751) B1084751
theorem B723227 : Blo 722323 723227 := bstep (se 1 (by rfl) ⟨542420, by rfl⟩ : syracuseStep 723227 = 1084841) B1084841
theorem B723327 : Blo 722323 723327 := bstep (se 1 (by rfl) ⟨542495, by rfl⟩ : syracuseStep 723327 = 1084991) B1084991
theorem B3672539 : Blo 722323 3672539 := bstep (se 1 (by rfl) ⟨2754404, by rfl⟩ : syracuseStep 3672539 = 5508809) B5508809
theorem B2755073 : Blo 722323 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B723503 : Blo 722323 723503 := bstep (se 1 (by rfl) ⟨542627, by rfl⟩ : syracuseStep 723503 = 1085255) B1085255
theorem B1084007 : Blo 722323 1084007 := bstep (se 1 (by rfl) ⟨813005, by rfl⟩ : syracuseStep 1084007 = 1626011) B1626011
theorem B723559 : Blo 722323 723559 := bstep (se 1 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 723559 = 1085339) B1085339
theorem B2755255 : Blo 722323 2755255 := bstep (se 1 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 2755255 = 4132883) B4132883
theorem B1084199 : Blo 722323 1084199 := bstep (se 1 (by rfl) ⟨813149, by rfl⟩ : syracuseStep 1084199 = 1626299) B1626299
theorem B3673025 : Blo 722323 3673025 := bstep (se 2 (by rfl) ⟨1377384, by rfl⟩ : syracuseStep 3673025 = 2754769) B2754769
theorem B2755529 : Blo 722323 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B723935 : Blo 722323 723935 := bstep (se 1 (by rfl) ⟨542951, by rfl⟩ : syracuseStep 723935 = 1085903) B1085903
theorem B723963 : Blo 722323 723963 := bstep (se 1 (by rfl) ⟨542972, by rfl⟩ : syracuseStep 723963 = 1085945) B1085945
theorem B724031 : Blo 722323 724031 := bstep (se 1 (by rfl) ⟨543023, by rfl⟩ : syracuseStep 724031 = 1086047) B1086047
theorem B1084523 : Blo 722323 1084523 := bstep (se 1 (by rfl) ⟨813392, by rfl⟩ : syracuseStep 1084523 = 1626785) B1626785
theorem B2067581 : Blo 722323 2067581 := bstep (se 3 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 2067581 = 775343) B775343
theorem B1739987 : Blo 722323 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B11308339 : Blo 722323 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B1084763 : Blo 722323 1084763 := bstep (se 1 (by rfl) ⟨813572, by rfl⟩ : syracuseStep 1084763 = 1627145) B1627145
theorem B1838447 : Blo 722323 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B1084793 : Blo 722323 1084793 := bstep (se 2 (by rfl) ⟨406797, by rfl⟩ : syracuseStep 1084793 = 813595) B813595
theorem B1084799 : Blo 722323 1084799 := bstep (se 1 (by rfl) ⟨813599, by rfl⟩ : syracuseStep 1084799 = 1627199) B1627199
theorem B724351 : Blo 722323 724351 := bstep (se 1 (by rfl) ⟨543263, by rfl⟩ : syracuseStep 724351 = 1086527) B1086527
theorem B724379 : Blo 722323 724379 := bstep (se 1 (by rfl) ⟨543284, by rfl⟩ : syracuseStep 724379 = 1086569) B1086569
theorem B724447 : Blo 722323 724447 := bstep (se 1 (by rfl) ⟨543335, by rfl⟩ : syracuseStep 724447 = 1086671) B1086671
theorem B724583 : Blo 722323 724583 := bstep (se 1 (by rfl) ⟨543437, by rfl⟩ : syracuseStep 724583 = 1086875) B1086875
theorem B724731 : Blo 722323 724731 := bstep (se 1 (by rfl) ⟨543548, by rfl⟩ : syracuseStep 724731 = 1087097) B1087097
theorem B724799 : Blo 722323 724799 := bstep (se 1 (by rfl) ⟨543599, by rfl⟩ : syracuseStep 724799 = 1087199) B1087199
theorem B724863 : Blo 722323 724863 := bstep (se 1 (by rfl) ⟨543647, by rfl⟩ : syracuseStep 724863 = 1087295) B1087295
theorem B23859089 : Blo 722323 23859089 := bstep (se 2 (by rfl) ⟨8947158, by rfl⟩ : syracuseStep 23859089 = 17894317) B17894317
theorem B1085423 : Blo 722323 1085423 := bstep (se 1 (by rfl) ⟨814067, by rfl⟩ : syracuseStep 1085423 = 1628135) B1628135
theorem B724975 : Blo 722323 724975 := bstep (se 1 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 724975 = 1087463) B1087463
theorem B1085435 : Blo 722323 1085435 := bstep (se 1 (by rfl) ⟨814076, by rfl⟩ : syracuseStep 1085435 = 1628153) B1628153
theorem B724987 : Blo 722323 724987 := bstep (se 1 (by rfl) ⟨543740, by rfl⟩ : syracuseStep 724987 = 1087481) B1087481
theorem B1085495 : Blo 722323 1085495 := bstep (se 1 (by rfl) ⟨814121, by rfl⟩ : syracuseStep 1085495 = 1628243) B1628243
theorem B725055 : Blo 722323 725055 := bstep (se 1 (by rfl) ⟨543791, by rfl⟩ : syracuseStep 725055 = 1087583) B1087583
theorem B1085543 : Blo 722323 1085543 := bstep (se 1 (by rfl) ⟨814157, by rfl⟩ : syracuseStep 1085543 = 1628315) B1628315
theorem B725095 : Blo 722323 725095 := bstep (se 1 (by rfl) ⟨543821, by rfl⟩ : syracuseStep 725095 = 1087643) B1087643
theorem B725119 : Blo 722323 725119 := bstep (se 1 (by rfl) ⟨543839, by rfl⟩ : syracuseStep 725119 = 1087679) B1087679
theorem B725147 : Blo 722323 725147 := bstep (se 1 (by rfl) ⟨543860, by rfl⟩ : syracuseStep 725147 = 1087721) B1087721
theorem B1085615 : Blo 722323 1085615 := bstep (se 1 (by rfl) ⟨814211, by rfl⟩ : syracuseStep 1085615 = 1628423) B1628423
theorem B725351 : Blo 722323 725351 := bstep (se 1 (by rfl) ⟨544013, by rfl⟩ : syracuseStep 725351 = 1088027) B1088027
theorem B1085819 : Blo 722323 1085819 := bstep (se 1 (by rfl) ⟨814364, by rfl⟩ : syracuseStep 1085819 = 1628729) B1628729
theorem B725403 : Blo 722323 725403 := bstep (se 1 (by rfl) ⟨544052, by rfl⟩ : syracuseStep 725403 = 1088105) B1088105
theorem B1086089 : Blo 722323 1086089 := bstep (se 2 (by rfl) ⟨407283, by rfl⟩ : syracuseStep 1086089 = 814567) B814567
theorem B725755 : Blo 722323 725755 := bstep (se 1 (by rfl) ⟨544316, by rfl⟩ : syracuseStep 725755 = 1088633) B1088633
theorem B725823 : Blo 722323 725823 := bstep (se 1 (by rfl) ⟨544367, by rfl⟩ : syracuseStep 725823 = 1088735) B1088735
theorem B1086299 : Blo 722323 1086299 := bstep (se 1 (by rfl) ⟨814724, by rfl⟩ : syracuseStep 1086299 = 1629449) B1629449
theorem B725851 : Blo 722323 725851 := bstep (se 1 (by rfl) ⟨544388, by rfl⟩ : syracuseStep 725851 = 1088777) B1088777
theorem B1545065 : Blo 722323 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B725919 : Blo 722323 725919 := bstep (se 1 (by rfl) ⟨544439, by rfl⟩ : syracuseStep 725919 = 1088879) B1088879
theorem B725999 : Blo 722323 725999 := bstep (se 1 (by rfl) ⟨544499, by rfl⟩ : syracuseStep 725999 = 1088999) B1088999
theorem B726087 : Blo 722323 726087 := bstep (se 1 (by rfl) ⟨544565, by rfl⟩ : syracuseStep 726087 = 1089131) B1089131
theorem B726171 : Blo 722323 726171 := bstep (se 1 (by rfl) ⟨544628, by rfl⟩ : syracuseStep 726171 = 1089257) B1089257
theorem B726267 : Blo 722323 726267 := bstep (se 1 (by rfl) ⟨544700, by rfl⟩ : syracuseStep 726267 = 1089401) B1089401
theorem B1086761 : Blo 722323 1086761 := bstep (se 2 (by rfl) ⟨407535, by rfl⟩ : syracuseStep 1086761 = 815071) B815071
theorem B3478895 : Blo 722323 3478895 := bstep (se 1 (by rfl) ⟨2609171, by rfl⟩ : syracuseStep 3478895 = 5218343) B5218343
theorem B1086959 : Blo 722323 1086959 := bstep (se 1 (by rfl) ⟨815219, by rfl⟩ : syracuseStep 1086959 = 1630439) B1630439
theorem B1087355 : Blo 722323 1087355 := bstep (se 1 (by rfl) ⟨815516, by rfl⟩ : syracuseStep 1087355 = 1631033) B1631033
theorem B1087391 : Blo 722323 1087391 := bstep (se 1 (by rfl) ⟨815543, by rfl⟩ : syracuseStep 1087391 = 1631087) B1631087
theorem B2791529 : Blo 722323 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B3676265 : Blo 722323 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B1087625 : Blo 722323 1087625 := bstep (se 2 (by rfl) ⟨407859, by rfl⟩ : syracuseStep 1087625 = 815719) B815719
theorem B4135049 : Blo 722323 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B1087775 : Blo 722323 1087775 := bstep (se 1 (by rfl) ⟨815831, by rfl⟩ : syracuseStep 1087775 = 1631663) B1631663
theorem B3086849 : Blo 722323 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B8788733 : Blo 722323 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B1088327 : Blo 722323 1088327 := bstep (se 1 (by rfl) ⟨816245, by rfl⟩ : syracuseStep 1088327 = 1632491) B1632491
theorem B6200387 : Blo 722323 6200387 := bstep (se 1 (by rfl) ⟨4650290, by rfl⟩ : syracuseStep 6200387 = 9300581) B9300581
theorem B12524867 : Blo 722323 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B2203193 : Blo 722323 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B1089191 : Blo 722323 1089191 := bstep (se 1 (by rfl) ⟨816893, by rfl⟩ : syracuseStep 1089191 = 1633787) B1633787
theorem B8265401 : Blo 722323 8265401 := bstep (se 2 (by rfl) ⟨3099525, by rfl⟩ : syracuseStep 8265401 = 6199051) B6199051
theorem B1089311 : Blo 722323 1089311 := bstep (se 1 (by rfl) ⟨816983, by rfl⟩ : syracuseStep 1089311 = 1633967) B1633967
theorem B5513183 : Blo 722323 5513183 := bstep (se 1 (by rfl) ⟨4134887, by rfl⟩ : syracuseStep 5513183 = 8269775) B8269775
theorem B3088523 : Blo 722323 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B20848913 : Blo 722323 20848913 := bstep (se 2 (by rfl) ⟨7818342, by rfl⟩ : syracuseStep 20848913 = 15636685) B15636685
theorem B5743439 : Blo 722323 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B4760711 : Blo 722323 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B6956711 : Blo 722323 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B1223147 : Blo 722323 1223147 := bstep (se 1 (by rfl) ⟨917360, by rfl⟩ : syracuseStep 1223147 = 1834721) B1834721
theorem B9415157 : Blo 722323 9415157 := bstep (se 5 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 9415157 = 882671) B882671
theorem B3484241 : Blo 722323 3484241 := bstep (se 2 (by rfl) ⟨1306590, by rfl⟩ : syracuseStep 3484241 = 2613181) B2613181
theorem B11905987 : Blo 722323 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B7154639 : Blo 722323 7154639 := bstep (se 1 (by rfl) ⟨5365979, by rfl⟩ : syracuseStep 7154639 = 10731959) B10731959
theorem B6204383 : Blo 722323 6204383 := bstep (se 1 (by rfl) ⟨4653287, by rfl⟩ : syracuseStep 6204383 = 9306575) B9306575
theorem B1223849 : Blo 722323 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B4238611 : Blo 722323 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B1224443 : Blo 722323 1224443 := bstep (se 1 (by rfl) ⟨918332, by rfl⟩ : syracuseStep 1224443 = 1836665) B1836665
theorem B4633145 : Blo 722323 4633145 := bstep (se 2 (by rfl) ⟨1737429, by rfl⟩ : syracuseStep 4633145 = 3474859) B3474859
theorem B2438099 : Blo 722323 2438099 := bstep (se 1 (by rfl) ⟨1828574, by rfl⟩ : syracuseStep 2438099 = 3657149) B3657149
theorem B2929673 : Blo 722323 2929673 := bstep (se 2 (by rfl) ⟨1098627, by rfl⟩ : syracuseStep 2929673 = 2197255) B2197255
theorem B1029439 : Blo 722323 1029439 := bstep (se 1 (by rfl) ⟨772079, by rfl⟩ : syracuseStep 1029439 = 1544159) B1544159
theorem B8271233 : Blo 722323 8271233 := bstep (se 2 (by rfl) ⟨3101712, by rfl⟩ : syracuseStep 8271233 = 6203425) B6203425
theorem B18528263 : Blo 722323 18528263 := bstep (se 1 (by rfl) ⟨13896197, by rfl⟩ : syracuseStep 18528263 = 27792395) B27792395
theorem B3094537 : Blo 722323 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B2930843 : Blo 722323 2930843 := bstep (se 1 (by rfl) ⟨2198132, by rfl⟩ : syracuseStep 2930843 = 4396265) B4396265
theorem B4635143 : Blo 722323 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B5225147 : Blo 722323 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B3095273 : Blo 722323 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B2604257 : Blo 722323 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B1031945 : Blo 722323 1031945 := bstep (se 2 (by rfl) ⟨386979, by rfl⟩ : syracuseStep 1031945 = 773959) B773959
theorem B1163207 : Blo 722323 1163207 := bstep (se 1 (by rfl) ⟨872405, by rfl⟩ : syracuseStep 1163207 = 1744811) B1744811
theorem B3096913 : Blo 722323 3096913 := bstep (se 2 (by rfl) ⟨1161342, by rfl⟩ : syracuseStep 3096913 = 2322685) B2322685
theorem B3096929 : Blo 722323 3096929 := bstep (se 2 (by rfl) ⟨1161348, by rfl⟩ : syracuseStep 3096929 = 2322697) B2322697
theorem B6177181 : Blo 722323 6177181 := bstep (se 3 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 6177181 = 2316443) B2316443
theorem B6603227 : Blo 722323 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B869071 : Blo 722323 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B25445987 : Blo 722323 25445987 := bstep (se 1 (by rfl) ⟨19084490, by rfl⟩ : syracuseStep 25445987 = 38168981) B38168981
theorem B4966217 : Blo 722323 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B11717399 : Blo 722323 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1395625 : Blo 722323 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B4115387 : Blo 722323 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B3132395 : Blo 722323 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B1625435 : Blo 722323 1625435 := bstep (se 1 (by rfl) ⟨1219076, by rfl⟩ : syracuseStep 1625435 = 2438153) B2438153
theorem B1625471 : Blo 722323 1625471 := bstep (se 1 (by rfl) ⟨1219103, by rfl⟩ : syracuseStep 1625471 = 2438207) B2438207
theorem B3296801 : Blo 722323 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B2444903 : Blo 722323 2444903 := bstep (se 1 (by rfl) ⟨1833677, by rfl⟩ : syracuseStep 2444903 = 3667355) B3667355
theorem B3722855 : Blo 722323 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B8474867 : Blo 722323 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B1954145 : Blo 722323 1954145 := bstep (se 2 (by rfl) ⟨732804, by rfl⟩ : syracuseStep 1954145 = 1465609) B1465609
theorem B7065967 : Blo 722323 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B11751905 : Blo 722323 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B3658607 : Blo 722323 3658607 := bstep (se 1 (by rfl) ⟨2743955, by rfl⟩ : syracuseStep 3658607 = 5487911) B5487911
theorem B1627343 : Blo 722323 1627343 := bstep (se 1 (by rfl) ⟨1220507, by rfl⟩ : syracuseStep 1627343 = 2441015) B2441015
theorem B1627433 : Blo 722323 1627433 := bstep (se 2 (by rfl) ⟨610287, by rfl⟩ : syracuseStep 1627433 = 1220575) B1220575
theorem B1627631 : Blo 722323 1627631 := bstep (se 1 (by rfl) ⟨1220723, by rfl⟩ : syracuseStep 1627631 = 2441447) B2441447
theorem B1955495 : Blo 722323 1955495 := bstep (se 1 (by rfl) ⟨1466621, by rfl⟩ : syracuseStep 1955495 = 2933243) B2933243
theorem B1628027 : Blo 722323 1628027 := bstep (se 1 (by rfl) ⟨1221020, by rfl⟩ : syracuseStep 1628027 = 2442041) B2442041
theorem B1628063 : Blo 722323 1628063 := bstep (se 1 (by rfl) ⟨1221047, by rfl⟩ : syracuseStep 1628063 = 2442095) B2442095
theorem B1628297 : Blo 722323 1628297 := bstep (se 2 (by rfl) ⟨610611, by rfl⟩ : syracuseStep 1628297 = 1221223) B1221223
theorem B1628513 : Blo 722323 1628513 := bstep (se 2 (by rfl) ⟨610692, by rfl⟩ : syracuseStep 1628513 = 1221385) B1221385
theorem B5495201 : Blo 722323 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B1628603 : Blo 722323 1628603 := bstep (se 1 (by rfl) ⟨1221452, by rfl⟩ : syracuseStep 1628603 = 2442905) B2442905
theorem B4413971 : Blo 722323 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B2742893 : Blo 722323 2742893 := bstep (se 3 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 2742893 = 1028585) B1028585
theorem B1628999 : Blo 722323 1628999 := bstep (se 1 (by rfl) ⟨1221749, by rfl⟩ : syracuseStep 1628999 = 2443499) B2443499
theorem B5495687 : Blo 722323 5495687 := bstep (se 1 (by rfl) ⟨4121765, by rfl⟩ : syracuseStep 5495687 = 8243531) B8243531
theorem B1629305 : Blo 722323 1629305 := bstep (se 2 (by rfl) ⟨610989, by rfl⟩ : syracuseStep 1629305 = 1221979) B1221979
theorem B5889257 : Blo 722323 5889257 := bstep (se 2 (by rfl) ⟨2208471, by rfl⟩ : syracuseStep 5889257 = 4416943) B4416943
theorem B1629863 : Blo 722323 1629863 := bstep (se 1 (by rfl) ⟨1222397, by rfl⟩ : syracuseStep 1629863 = 2444795) B2444795
theorem B1629971 : Blo 722323 1629971 := bstep (se 1 (by rfl) ⟨1222478, by rfl⟩ : syracuseStep 1629971 = 2444957) B2444957
theorem B1957787 : Blo 722323 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B1630331 : Blo 722323 1630331 := bstep (se 1 (by rfl) ⟨1222748, by rfl⟩ : syracuseStep 1630331 = 2445497) B2445497
theorem B2318483 : Blo 722323 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B1630601 : Blo 722323 1630601 := bstep (se 2 (by rfl) ⟨611475, by rfl⟩ : syracuseStep 1630601 = 1222951) B1222951
theorem B1958305 : Blo 722323 1958305 := bstep (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) B1468729
theorem B2613671 : Blo 722323 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B2450087 : Blo 722323 2450087 := bstep (se 1 (by rfl) ⟨1837565, by rfl⟩ : syracuseStep 2450087 = 3675131) B3675131
theorem B5497631 : Blo 722323 5497631 := bstep (se 1 (by rfl) ⟨4123223, by rfl⟩ : syracuseStep 5497631 = 8246447) B8246447
theorem B6185929 : Blo 722323 6185929 := bstep (se 2 (by rfl) ⟨2319723, by rfl⟩ : syracuseStep 6185929 = 4639447) B4639447
theorem B2745323 : Blo 722323 2745323 := bstep (se 1 (by rfl) ⟨2058992, by rfl⟩ : syracuseStep 2745323 = 4117985) B4117985
theorem B2450411 : Blo 722323 2450411 := bstep (se 1 (by rfl) ⟨1837808, by rfl⟩ : syracuseStep 2450411 = 3675617) B3675617
theorem B1205561 : Blo 722323 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B2319673 : Blo 722323 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B1631735 : Blo 722323 1631735 := bstep (se 1 (by rfl) ⟨1223801, by rfl⟩ : syracuseStep 1631735 = 2447603) B2447603
theorem B1631771 : Blo 722323 1631771 := bstep (se 1 (by rfl) ⟨1223828, by rfl⟩ : syracuseStep 1631771 = 2447657) B2447657
theorem B2320123 : Blo 722323 2320123 := bstep (se 1 (by rfl) ⟨1740092, by rfl⟩ : syracuseStep 2320123 = 3480185) B3480185
theorem B812839 : Blo 722323 812839 := bstep (se 1 (by rfl) ⟨609629, by rfl⟩ : syracuseStep 812839 = 1219259) B1219259
theorem B4188257 : Blo 722323 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B1632761 : Blo 722323 1632761 := bstep (se 2 (by rfl) ⟨612285, by rfl⟩ : syracuseStep 1632761 = 1224571) B1224571
theorem B1632815 : Blo 722323 1632815 := bstep (se 1 (by rfl) ⟨1224611, by rfl⟩ : syracuseStep 1632815 = 2449223) B2449223
theorem B1632851 : Blo 722323 1632851 := bstep (se 1 (by rfl) ⟨1224638, by rfl⟩ : syracuseStep 1632851 = 2449277) B2449277
theorem B9431639 : Blo 722323 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B15657623 : Blo 722323 15657623 := bstep (se 1 (by rfl) ⟨11743217, by rfl⟩ : syracuseStep 15657623 = 23486435) B23486435
theorem B5499575 : Blo 722323 5499575 := bstep (se 1 (by rfl) ⟨4124681, by rfl⟩ : syracuseStep 5499575 = 8249363) B8249363
theorem B1633031 : Blo 722323 1633031 := bstep (se 1 (by rfl) ⟨1224773, by rfl⟩ : syracuseStep 1633031 = 2449547) B2449547
theorem B3566497 : Blo 722323 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B107342779 : Blo 722323 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B1633247 : Blo 722323 1633247 := bstep (se 1 (by rfl) ⟨1224935, by rfl⟩ : syracuseStep 1633247 = 2449871) B2449871
theorem B2747465 : Blo 722323 2747465 := bstep (se 2 (by rfl) ⟨1030299, by rfl⟩ : syracuseStep 2747465 = 2060599) B2060599
theorem B1633463 : Blo 722323 1633463 := bstep (se 1 (by rfl) ⟨1225097, by rfl⟩ : syracuseStep 1633463 = 2450195) B2450195
theorem B8350937 : Blo 722323 8350937 := bstep (se 2 (by rfl) ⟨3131601, by rfl⟩ : syracuseStep 8350937 = 6263203) B6263203
theorem B1371401 : Blo 722323 1371401 := bstep (se 2 (by rfl) ⟨514275, by rfl⟩ : syracuseStep 1371401 = 1028551) B1028551
theorem B4124317 : Blo 722323 4124317 := bstep (se 3 (by rfl) ⟨773309, by rfl⟩ : syracuseStep 4124317 = 1546619) B1546619
theorem B20082401 : Blo 722323 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B1634039 : Blo 722323 1634039 := bstep (se 1 (by rfl) ⟨1225529, by rfl⟩ : syracuseStep 1634039 = 2451059) B2451059
theorem B1634111 : Blo 722323 1634111 := bstep (se 1 (by rfl) ⟨1225583, by rfl⟩ : syracuseStep 1634111 = 2451167) B2451167
theorem B15658829 : Blo 722323 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B1634219 : Blo 722323 1634219 := bstep (se 1 (by rfl) ⟨1225664, by rfl⟩ : syracuseStep 1634219 = 2451329) B2451329
theorem B1372153 : Blo 722323 1372153 := bstep (se 2 (by rfl) ⟨514557, by rfl⟩ : syracuseStep 1372153 = 1029115) B1029115
theorem B1830995 : Blo 722323 1830995 := bstep (se 1 (by rfl) ⟨1373246, by rfl⟩ : syracuseStep 1830995 = 2746493) B2746493
theorem B2748923 : Blo 722323 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B6287867 : Blo 722323 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B2061065 : Blo 722323 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B815935 : Blo 722323 815935 := bstep (se 1 (by rfl) ⟨611951, by rfl⟩ : syracuseStep 815935 = 1223903) B1223903
theorem B35648363 : Blo 722323 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B816223 : Blo 722323 816223 := bstep (se 1 (by rfl) ⟨612167, by rfl⟩ : syracuseStep 816223 = 1224335) B1224335
theorem B2749727 : Blo 722323 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B1373611 : Blo 722323 1373611 := bstep (se 1 (by rfl) ⟨1030208, by rfl⟩ : syracuseStep 1373611 = 2060417) B2060417
theorem B2323927 : Blo 722323 2323927 := bstep (se 1 (by rfl) ⟨1742945, by rfl⟩ : syracuseStep 2323927 = 3485891) B3485891
theorem B101644091 : Blo 722323 101644091 := bstep (se 1 (by rfl) ⟨76233068, by rfl⟩ : syracuseStep 101644091 = 152466137) B152466137
theorem B2062547 : Blo 722323 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B1833263 : Blo 722323 1833263 := bstep (se 1 (by rfl) ⟨1374947, by rfl⟩ : syracuseStep 1833263 = 2749895) B2749895
theorem B1374985 : Blo 722323 1374985 := bstep (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) B1031239
theorem B21429319 : Blo 722323 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B883919 : Blo 722323 883919 := bstep (se 1 (by rfl) ⟨662939, by rfl⟩ : syracuseStep 883919 = 1325879) B1325879
theorem B1834265 : Blo 722323 1834265 := bstep (se 2 (by rfl) ⟨687849, by rfl⟩ : syracuseStep 1834265 = 1375699) B1375699
theorem B2751839 : Blo 722323 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B1834447 : Blo 722323 1834447 := bstep (se 1 (by rfl) ⟨1375835, by rfl⟩ : syracuseStep 1834447 = 2751671) B2751671
theorem B3309167 : Blo 722323 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B2752157 : Blo 722323 2752157 := bstep (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) B1032059
theorem B13893281 : Blo 722323 13893281 := bstep (se 2 (by rfl) ⟨5209980, by rfl⟩ : syracuseStep 13893281 = 10419961) B10419961
theorem B3342223 : Blo 722323 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B2064619 : Blo 722323 2064619 := bstep (se 1 (by rfl) ⟨1548464, by rfl⟩ : syracuseStep 2064619 = 3096929) B3096929
theorem B1835257 : Blo 722323 1835257 := bstep (se 2 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 1835257 = 1376443) B1376443
theorem B5505407 : Blo 722323 5505407 := bstep (se 1 (by rfl) ⟨4129055, by rfl⟩ : syracuseStep 5505407 = 8258111) B8258111
theorem B1835419 : Blo 722323 1835419 := bstep (se 1 (by rfl) ⟨1376564, by rfl⟩ : syracuseStep 1835419 = 2753129) B2753129
theorem B1376671 : Blo 722323 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B4129217 : Blo 722323 4129217 := bstep (se 2 (by rfl) ⟨1548456, by rfl⟩ : syracuseStep 4129217 = 3096913) B3096913
theorem B1835905 : Blo 722323 1835905 := bstep (se 2 (by rfl) ⟨688464, by rfl⟩ : syracuseStep 1835905 = 1376929) B1376929
theorem B5211053 : Blo 722323 5211053 := bstep (se 3 (by rfl) ⟨977072, by rfl⟩ : syracuseStep 5211053 = 1954145) B1954145
theorem B4129967 : Blo 722323 4129967 := bstep (se 1 (by rfl) ⟨3097475, by rfl⟩ : syracuseStep 4129967 = 6194951) B6194951
theorem B3310811 : Blo 722323 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B1836715 : Blo 722323 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B722671 : Blo 722323 722671 := bstep (se 1 (by rfl) ⟨542003, by rfl⟩ : syracuseStep 722671 = 1084007) B1084007
theorem B722799 : Blo 722323 722799 := bstep (se 1 (by rfl) ⟨542099, by rfl⟩ : syracuseStep 722799 = 1084199) B1084199
theorem B1837019 : Blo 722323 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B723015 : Blo 722323 723015 := bstep (se 1 (by rfl) ⟨542261, by rfl⟩ : syracuseStep 723015 = 1084523) B1084523
theorem B1378387 : Blo 722323 1378387 := bstep (se 1 (by rfl) ⟨1033790, by rfl⟩ : syracuseStep 1378387 = 2067581) B2067581
theorem B1083623 : Blo 722323 1083623 := bstep (se 1 (by rfl) ⟨812717, by rfl⟩ : syracuseStep 1083623 = 1625435) B1625435
theorem B723175 : Blo 722323 723175 := bstep (se 1 (by rfl) ⟨542381, by rfl⟩ : syracuseStep 723175 = 1084763) B1084763
theorem B723195 : Blo 722323 723195 := bstep (se 1 (by rfl) ⟨542396, by rfl⟩ : syracuseStep 723195 = 1084793) B1084793
theorem B1083647 : Blo 722323 1083647 := bstep (se 1 (by rfl) ⟨812735, by rfl⟩ : syracuseStep 1083647 = 1625471) B1625471
theorem B723199 : Blo 722323 723199 := bstep (se 1 (by rfl) ⟨542399, by rfl⟩ : syracuseStep 723199 = 1084799) B1084799
theorem B2197867 : Blo 722323 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B1083785 : Blo 722323 1083785 := bstep (se 2 (by rfl) ⟨406419, by rfl⟩ : syracuseStep 1083785 = 812839) B812839
theorem B723615 : Blo 722323 723615 := bstep (se 1 (by rfl) ⟨542711, by rfl⟩ : syracuseStep 723615 = 1085423) B1085423
theorem B723623 : Blo 722323 723623 := bstep (se 1 (by rfl) ⟨542717, by rfl⟩ : syracuseStep 723623 = 1085435) B1085435
theorem B723663 : Blo 722323 723663 := bstep (se 1 (by rfl) ⟨542747, by rfl⟩ : syracuseStep 723663 = 1085495) B1085495
theorem B723695 : Blo 722323 723695 := bstep (se 1 (by rfl) ⟨542771, by rfl⟩ : syracuseStep 723695 = 1085543) B1085543
theorem B723743 : Blo 722323 723743 := bstep (se 1 (by rfl) ⟨542807, by rfl⟩ : syracuseStep 723743 = 1085615) B1085615
theorem B723879 : Blo 722323 723879 := bstep (se 1 (by rfl) ⟨542909, by rfl⟩ : syracuseStep 723879 = 1085819) B1085819
theorem B724059 : Blo 722323 724059 := bstep (se 1 (by rfl) ⟨543044, by rfl⟩ : syracuseStep 724059 = 1086089) B1086089
theorem B724199 : Blo 722323 724199 := bstep (se 1 (by rfl) ⟨543149, by rfl⟩ : syracuseStep 724199 = 1086299) B1086299
theorem B1084895 : Blo 722323 1084895 := bstep (se 1 (by rfl) ⟨813671, by rfl⟩ : syracuseStep 1084895 = 1627343) B1627343
theorem B3214829 : Blo 722323 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B1084955 : Blo 722323 1084955 := bstep (se 1 (by rfl) ⟨813716, by rfl⟩ : syracuseStep 1084955 = 1627433) B1627433
theorem B724507 : Blo 722323 724507 := bstep (se 1 (by rfl) ⟨543380, by rfl⟩ : syracuseStep 724507 = 1086761) B1086761
theorem B3673673 : Blo 722323 3673673 := bstep (se 2 (by rfl) ⟨1377627, by rfl⟩ : syracuseStep 3673673 = 2755255) B2755255
theorem B1085087 : Blo 722323 1085087 := bstep (se 1 (by rfl) ⟨813815, by rfl⟩ : syracuseStep 1085087 = 1627631) B1627631
theorem B724639 : Blo 722323 724639 := bstep (se 1 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 724639 = 1086959) B1086959
theorem B4755329 : Blo 722323 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B1085351 : Blo 722323 1085351 := bstep (se 1 (by rfl) ⟨814013, by rfl⟩ : syracuseStep 1085351 = 1628027) B1628027
theorem B724903 : Blo 722323 724903 := bstep (se 1 (by rfl) ⟨543677, by rfl⟩ : syracuseStep 724903 = 1087355) B1087355
theorem B1085375 : Blo 722323 1085375 := bstep (se 1 (by rfl) ⟨814031, by rfl⟩ : syracuseStep 1085375 = 1628063) B1628063
theorem B724927 : Blo 722323 724927 := bstep (se 1 (by rfl) ⟨543695, by rfl⟩ : syracuseStep 724927 = 1087391) B1087391
theorem B1085531 : Blo 722323 1085531 := bstep (se 1 (by rfl) ⟨814148, by rfl⟩ : syracuseStep 1085531 = 1628297) B1628297
theorem B725083 : Blo 722323 725083 := bstep (se 1 (by rfl) ⟨543812, by rfl⟩ : syracuseStep 725083 = 1087625) B1087625
theorem B2756699 : Blo 722323 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B725183 : Blo 722323 725183 := bstep (se 1 (by rfl) ⟨543887, by rfl⟩ : syracuseStep 725183 = 1087775) B1087775
theorem B1085675 : Blo 722323 1085675 := bstep (se 1 (by rfl) ⟨814256, by rfl⟩ : syracuseStep 1085675 = 1628513) B1628513
theorem B1085735 : Blo 722323 1085735 := bstep (se 1 (by rfl) ⟨814301, by rfl⟩ : syracuseStep 1085735 = 1628603) B1628603
theorem B1085999 : Blo 722323 1085999 := bstep (se 1 (by rfl) ⟨814499, by rfl⟩ : syracuseStep 1085999 = 1628999) B1628999
theorem B725551 : Blo 722323 725551 := bstep (se 1 (by rfl) ⟨544163, by rfl⟩ : syracuseStep 725551 = 1088327) B1088327
theorem B4133591 : Blo 722323 4133591 := bstep (se 1 (by rfl) ⟨3100193, by rfl⟩ : syracuseStep 4133591 = 6200387) B6200387
theorem B1086203 : Blo 722323 1086203 := bstep (se 1 (by rfl) ⟨814652, by rfl⟩ : syracuseStep 1086203 = 1629305) B1629305
theorem B1086575 : Blo 722323 1086575 := bstep (se 1 (by rfl) ⟨814931, by rfl⟩ : syracuseStep 1086575 = 1629863) B1629863
theorem B726127 : Blo 722323 726127 := bstep (se 1 (by rfl) ⟨544595, by rfl⟩ : syracuseStep 726127 = 1089191) B1089191
theorem B5510267 : Blo 722323 5510267 := bstep (se 1 (by rfl) ⟨4132700, by rfl⟩ : syracuseStep 5510267 = 8265401) B8265401
theorem B1086647 : Blo 722323 1086647 := bstep (se 1 (by rfl) ⟨814985, by rfl⟩ : syracuseStep 1086647 = 1629971) B1629971
theorem B726207 : Blo 722323 726207 := bstep (se 1 (by rfl) ⟨544655, by rfl⟩ : syracuseStep 726207 = 1089311) B1089311
theorem B3675455 : Blo 722323 3675455 := bstep (se 1 (by rfl) ⟨2756591, by rfl⟩ : syracuseStep 3675455 = 5513183) B5513183
theorem B1086887 : Blo 722323 1086887 := bstep (se 1 (by rfl) ⟨815165, by rfl⟩ : syracuseStep 1086887 = 1630331) B1630331
theorem B1545655 : Blo 722323 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B13899275 : Blo 722323 13899275 := bstep (se 1 (by rfl) ⟨10424456, by rfl⟩ : syracuseStep 13899275 = 20848913) B20848913
theorem B1087067 : Blo 722323 1087067 := bstep (se 1 (by rfl) ⟨815300, by rfl⟩ : syracuseStep 1087067 = 1630601) B1630601
theorem B1742447 : Blo 722323 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B1087823 : Blo 722323 1087823 := bstep (se 1 (by rfl) ⟨815867, by rfl⟩ : syracuseStep 1087823 = 1631735) B1631735
theorem B1087847 : Blo 722323 1087847 := bstep (se 1 (by rfl) ⟨815885, by rfl⟩ : syracuseStep 1087847 = 1631771) B1631771
theorem B1087913 : Blo 722323 1087913 := bstep (se 2 (by rfl) ⟨407967, by rfl⟩ : syracuseStep 1087913 = 815935) B815935
theorem B25107085 : Blo 722323 25107085 := bstep (se 3 (by rfl) ⟨4707578, by rfl⟩ : syracuseStep 25107085 = 9415157) B9415157
theorem B11770589 : Blo 722323 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B2792171 : Blo 722323 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B1088297 : Blo 722323 1088297 := bstep (se 2 (by rfl) ⟨408111, by rfl⟩ : syracuseStep 1088297 = 816223) B816223
theorem B1088507 : Blo 722323 1088507 := bstep (se 1 (by rfl) ⟨816380, by rfl⟩ : syracuseStep 1088507 = 1632761) B1632761
theorem B1088543 : Blo 722323 1088543 := bstep (se 1 (by rfl) ⟨816407, by rfl⟩ : syracuseStep 1088543 = 1632815) B1632815
theorem B1088567 : Blo 722323 1088567 := bstep (se 1 (by rfl) ⟨816425, by rfl⟩ : syracuseStep 1088567 = 1632851) B1632851
theorem B1088687 : Blo 722323 1088687 := bstep (se 1 (by rfl) ⟨816515, by rfl⟩ : syracuseStep 1088687 = 1633031) B1633031
theorem B1088831 : Blo 722323 1088831 := bstep (se 1 (by rfl) ⟨816623, by rfl⟩ : syracuseStep 1088831 = 1633247) B1633247
theorem B4136255 : Blo 722323 4136255 := bstep (se 1 (by rfl) ⟨3102191, by rfl⟩ : syracuseStep 4136255 = 6204383) B6204383
theorem B1088975 : Blo 722323 1088975 := bstep (se 1 (by rfl) ⟨816731, by rfl⟩ : syracuseStep 1088975 = 1633463) B1633463
theorem B1089359 : Blo 722323 1089359 := bstep (se 1 (by rfl) ⟨817019, by rfl⟩ : syracuseStep 1089359 = 1634039) B1634039
theorem B1089407 : Blo 722323 1089407 := bstep (se 1 (by rfl) ⟨817055, by rfl⟩ : syracuseStep 1089407 = 1634111) B1634111
theorem B1089479 : Blo 722323 1089479 := bstep (se 1 (by rfl) ⟨817109, by rfl⟩ : syracuseStep 1089479 = 1634219) B1634219
theorem B1220663 : Blo 722323 1220663 := bstep (se 1 (by rfl) ⟨915497, by rfl⟩ : syracuseStep 1220663 = 1830995) B1830995
theorem B3088763 : Blo 722323 3088763 := bstep (se 1 (by rfl) ⟨2316572, by rfl⟩ : syracuseStep 3088763 = 4633145) B4633145
theorem B23765575 : Blo 722323 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B5514155 : Blo 722323 5514155 := bstep (se 1 (by rfl) ⟨4135616, by rfl⟩ : syracuseStep 5514155 = 8271233) B8271233
theorem B1222175 : Blo 722323 1222175 := bstep (se 1 (by rfl) ⟨916631, by rfl⟩ : syracuseStep 1222175 = 1833263) B1833263
theorem B3090095 : Blo 722323 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B3483431 : Blo 722323 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B1222843 : Blo 722323 1222843 := bstep (se 1 (by rfl) ⟨917132, by rfl⟩ : syracuseStep 1222843 = 1834265) B1834265
theorem B2206111 : Blo 722323 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B4402151 : Blo 722323 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B8236241 : Blo 722323 8236241 := bstep (se 2 (by rfl) ⟨3088590, by rfl⟩ : syracuseStep 8236241 = 6177181) B6177181
theorem B1158761 : Blo 722323 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B31338413 : Blo 722323 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B4632659 : Blo 722323 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B3092897 : Blo 722323 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B7811599 : Blo 722323 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B1159991 : Blo 722323 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B1225631 : Blo 722323 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B3093497 : Blo 722323 3093497 := bstep (se 2 (by rfl) ⟨1160061, by rfl⟩ : syracuseStep 3093497 = 2320123) B2320123
theorem B15906059 : Blo 722323 15906059 := bstep (se 1 (by rfl) ⟨11929544, by rfl⟩ : syracuseStep 15906059 = 23859089) B23859089
theorem B31241537 : Blo 722323 31241537 := bstep (se 2 (by rfl) ⟨11715576, by rfl⟩ : syracuseStep 31241537 = 23431153) B23431153
theorem B5649911 : Blo 722323 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B1030043 : Blo 722323 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B2439071 : Blo 722323 2439071 := bstep (se 1 (by rfl) ⟨1829303, by rfl⟩ : syracuseStep 2439071 = 3658607) B3658607
theorem B15874649 : Blo 722323 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B9421289 : Blo 722323 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B4637807 : Blo 722323 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B60311141 : Blo 722323 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B5490341 : Blo 722323 5490341 := bstep (se 4 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 5490341 = 1029439) B1029439
theorem B10438415 : Blo 722323 10438415 := bstep (se 1 (by rfl) ⟨7828811, by rfl⟩ : syracuseStep 10438415 = 15657623) B15657623
theorem B3098569 : Blo 722323 3098569 := bstep (se 2 (by rfl) ⟨1161963, by rfl⟩ : syracuseStep 3098569 = 2323927) B2323927
theorem B4769759 : Blo 722323 4769759 := bstep (se 1 (by rfl) ⟨3577319, by rfl⟩ : syracuseStep 4769759 = 7154639) B7154639
theorem B13388267 : Blo 722323 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B10439219 : Blo 722323 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B1625399 : Blo 722323 1625399 := bstep (se 1 (by rfl) ⟨1219049, by rfl⟩ : syracuseStep 1625399 = 2438099) B2438099
theorem B1953115 : Blo 722323 1953115 := bstep (se 1 (by rfl) ⟨1464836, by rfl⟩ : syracuseStep 1953115 = 2929673) B2929673
theorem B1953895 : Blo 722323 1953895 := bstep (se 1 (by rfl) ⟨1465421, by rfl⟩ : syracuseStep 1953895 = 2930843) B2930843
theorem B2445929 : Blo 722323 2445929 := bstep (se 2 (by rfl) ⟨917223, by rfl⟩ : syracuseStep 2445929 = 1834447) B1834447
theorem B9262187 : Blo 722323 9262187 := bstep (se 1 (by rfl) ⟨6946640, by rfl⟩ : syracuseStep 9262187 = 13893281) B13893281
theorem B3101885 : Blo 722323 3101885 := bstep (se 3 (by rfl) ⟨581603, by rfl⟩ : syracuseStep 3101885 = 1163207) B1163207
theorem B2611073 : Blo 722323 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B16963991 : Blo 722323 16963991 := bstep (se 1 (by rfl) ⟨12722993, by rfl⟩ : syracuseStep 16963991 = 25445987) B25445987
theorem B8247905 : Blo 722323 8247905 := bstep (se 2 (by rfl) ⟨3092964, by rfl⟩ : syracuseStep 8247905 = 6185929) B6185929
theorem B2448359 : Blo 722323 2448359 := bstep (se 1 (by rfl) ⟨1836269, by rfl⟩ : syracuseStep 2448359 = 3672539) B3672539
theorem B2743591 : Blo 722323 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B2448683 : Blo 722323 2448683 := bstep (se 1 (by rfl) ⟨1836512, by rfl⟩ : syracuseStep 2448683 = 3673025) B3673025
theorem B2088263 : Blo 722323 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B5496173 : Blo 722323 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B1629935 : Blo 722323 1629935 := bstep (se 1 (by rfl) ⟨1222451, by rfl⟩ : syracuseStep 1629935 = 2444903) B2444903
theorem B2449385 : Blo 722323 2449385 := bstep (se 2 (by rfl) ⟨918519, by rfl⟩ : syracuseStep 2449385 = 1837039) B1837039
theorem B2319263 : Blo 722323 2319263 := bstep (se 1 (by rfl) ⟨1739447, by rfl⟩ : syracuseStep 2319263 = 3478895) B3478895
theorem B1303663 : Blo 722323 1303663 := bstep (se 1 (by rfl) ⟨977747, by rfl⟩ : syracuseStep 1303663 = 1955495) B1955495
theorem B1860833 : Blo 722323 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B143123705 : Blo 722323 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B1861019 : Blo 722323 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B2450843 : Blo 722323 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B3663467 : Blo 722323 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B2057899 : Blo 722323 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B1828595 : Blo 722323 1828595 := bstep (se 1 (by rfl) ⟨1371446, by rfl⟩ : syracuseStep 1828595 = 2742893) B2742893
theorem B5859155 : Blo 722323 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B3663791 : Blo 722323 3663791 := bstep (se 1 (by rfl) ⟨2747843, by rfl⟩ : syracuseStep 3663791 = 5495687) B5495687
theorem B3926171 : Blo 722323 3926171 := bstep (se 1 (by rfl) ⟨2944628, by rfl⟩ : syracuseStep 3926171 = 5889257) B5889257
theorem B5499089 : Blo 722323 5499089 := bstep (se 2 (by rfl) ⟨2062158, by rfl⟩ : syracuseStep 5499089 = 4124317) B4124317
theorem B8349911 : Blo 722323 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B1468795 : Blo 722323 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B1305191 : Blo 722323 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B1829537 : Blo 722323 1829537 := bstep (se 2 (by rfl) ⟨686076, by rfl⟩ : syracuseStep 1829537 = 1372153) B1372153
theorem B2059015 : Blo 722323 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B1633391 : Blo 722323 1633391 := bstep (se 1 (by rfl) ⟨1225043, by rfl⟩ : syracuseStep 1633391 = 2450087) B2450087
theorem B3665087 : Blo 722323 3665087 := bstep (se 1 (by rfl) ⟨2748815, by rfl⟩ : syracuseStep 3665087 = 5497631) B5497631
theorem B3828959 : Blo 722323 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B1830215 : Blo 722323 1830215 := bstep (se 1 (by rfl) ⟨1372661, by rfl⟩ : syracuseStep 1830215 = 2745323) B2745323
theorem B1633607 : Blo 722323 1633607 := bstep (se 1 (by rfl) ⟨1225205, by rfl⟩ : syracuseStep 1633607 = 2450411) B2450411
theorem B3173807 : Blo 722323 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B22605925 : Blo 722323 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B815431 : Blo 722323 815431 := bstep (se 1 (by rfl) ⟨611573, by rfl⟩ : syracuseStep 815431 = 1223147) B1223147
theorem B2322827 : Blo 722323 2322827 := bstep (se 1 (by rfl) ⟨1742120, by rfl⟩ : syracuseStep 2322827 = 3484241) B3484241
theorem B6287759 : Blo 722323 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B3666383 : Blo 722323 3666383 := bstep (se 1 (by rfl) ⟨2749787, by rfl⟩ : syracuseStep 3666383 = 5499575) B5499575
theorem B1831481 : Blo 722323 1831481 := bstep (se 2 (by rfl) ⟨686805, by rfl⟩ : syracuseStep 1831481 = 1373611) B1373611
theorem B1831643 : Blo 722323 1831643 := bstep (se 1 (by rfl) ⟨1373732, by rfl⟩ : syracuseStep 1831643 = 2747465) B2747465
theorem B815899 : Blo 722323 815899 := bstep (se 1 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 815899 = 1223849) B1223849
theorem B5567291 : Blo 722323 5567291 := bstep (se 1 (by rfl) ⟨4175468, by rfl⟩ : syracuseStep 5567291 = 8350937) B8350937
theorem B914267 : Blo 722323 914267 := bstep (se 1 (by rfl) ⟨685700, by rfl⟩ : syracuseStep 914267 = 1371401) B1371401
theorem B816295 : Blo 722323 816295 := bstep (se 1 (by rfl) ⟨612221, by rfl⟩ : syracuseStep 816295 = 1224443) B1224443
theorem B4126049 : Blo 722323 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B1832615 : Blo 722323 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B4191911 : Blo 722323 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B2357117 : Blo 722323 2357117 := bstep (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) B883919
theorem B1833151 : Blo 722323 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B1833313 : Blo 722323 1833313 := bstep (se 2 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 1833313 = 1374985) B1374985
theorem B67762727 : Blo 722323 67762727 := bstep (se 1 (by rfl) ⟨50822045, by rfl⟩ : syracuseStep 67762727 = 101644091) B101644091
theorem B12352175 : Blo 722323 12352175 := bstep (se 1 (by rfl) ⟨9264131, by rfl⟩ : syracuseStep 12352175 = 18528263) B18528263
theorem B28572425 : Blo 722323 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B1375031 : Blo 722323 1375031 := bstep (se 1 (by rfl) ⟨1031273, by rfl⟩ : syracuseStep 1375031 = 2062547) B2062547
theorem B9927613 : Blo 722323 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B2063515 : Blo 722323 2063515 := bstep (se 1 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 2063515 = 3095273) B3095273
theorem B2751853 : Blo 722323 2751853 := bstep (se 3 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 2751853 = 1031945) B1031945
theorem B1736171 : Blo 722323 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1834559 : Blo 722323 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B1834771 : Blo 722323 1834771 := bstep (se 1 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 1834771 = 2752157) B2752157
theorem B4456297 : Blo 722323 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B3670271 : Blo 722323 3670271 := bstep (se 1 (by rfl) ⟨2752703, by rfl⟩ : syracuseStep 3670271 = 5505407) B5505407
theorem B2752811 : Blo 722323 2752811 := bstep (se 1 (by rfl) ⟨2064608, by rfl⟩ : syracuseStep 2752811 = 4129217) B4129217
theorem B2752825 : Blo 722323 2752825 := bstep (se 2 (by rfl) ⟨1032309, by rfl⟩ : syracuseStep 2752825 = 2064619) B2064619
theorem B1835561 : Blo 722323 1835561 := bstep (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) B1376671
theorem B3474035 : Blo 722323 3474035 := bstep (se 1 (by rfl) ⟨2605526, by rfl⟩ : syracuseStep 3474035 = 5211053) B5211053
theorem B31687433 : Blo 722323 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B2753311 : Blo 722323 2753311 := bstep (se 1 (by rfl) ⟨2064983, by rfl⟩ : syracuseStep 2753311 = 4129967) B4129967
theorem B40207427 : Blo 722323 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B3179839 : Blo 722323 3179839 := bstep (se 1 (by rfl) ⟨2384879, by rfl⟩ : syracuseStep 3179839 = 4769759) B4769759
theorem B1738217 : Blo 722323 1738217 := bstep (se 2 (by rfl) ⟨651831, by rfl⟩ : syracuseStep 1738217 = 1303663) B1303663
theorem B722415 : Blo 722323 722415 := bstep (se 1 (by rfl) ⟨541811, by rfl⟩ : syracuseStep 722415 = 1083623) B1083623
theorem B722431 : Blo 722323 722431 := bstep (se 1 (by rfl) ⟨541823, by rfl⟩ : syracuseStep 722431 = 1083647) B1083647
theorem B722523 : Blo 722323 722523 := bstep (se 1 (by rfl) ⟨541892, by rfl⟩ : syracuseStep 722523 = 1083785) B1083785
theorem B1083599 : Blo 722323 1083599 := bstep (se 1 (by rfl) ⟨812699, by rfl⟩ : syracuseStep 1083599 = 1625399) B1625399
theorem B723263 : Blo 722323 723263 := bstep (se 1 (by rfl) ⟨542447, by rfl⟩ : syracuseStep 723263 = 1084895) B1084895
theorem B723303 : Blo 722323 723303 := bstep (se 1 (by rfl) ⟨542477, by rfl⟩ : syracuseStep 723303 = 1084955) B1084955
theorem B723391 : Blo 722323 723391 := bstep (se 1 (by rfl) ⟨542543, by rfl⟩ : syracuseStep 723391 = 1085087) B1085087
theorem B4131425 : Blo 722323 4131425 := bstep (se 2 (by rfl) ⟨1549284, by rfl⟩ : syracuseStep 4131425 = 3098569) B3098569
theorem B723567 : Blo 722323 723567 := bstep (se 1 (by rfl) ⟨542675, by rfl⟩ : syracuseStep 723567 = 1085351) B1085351
theorem B723583 : Blo 722323 723583 := bstep (se 1 (by rfl) ⟨542687, by rfl⟩ : syracuseStep 723583 = 1085375) B1085375
theorem B723687 : Blo 722323 723687 := bstep (se 1 (by rfl) ⟨542765, by rfl⟩ : syracuseStep 723687 = 1085531) B1085531
theorem B1837799 : Blo 722323 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B1837849 : Blo 722323 1837849 := bstep (se 2 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 1837849 = 1378387) B1378387
theorem B723783 : Blo 722323 723783 := bstep (se 1 (by rfl) ⟨542837, by rfl⟩ : syracuseStep 723783 = 1085675) B1085675
theorem B723823 : Blo 722323 723823 := bstep (se 1 (by rfl) ⟨542867, by rfl⟩ : syracuseStep 723823 = 1085735) B1085735
theorem B723999 : Blo 722323 723999 := bstep (se 1 (by rfl) ⟨542999, by rfl⟩ : syracuseStep 723999 = 1085999) B1085999
theorem B2755727 : Blo 722323 2755727 := bstep (se 1 (by rfl) ⟨2066795, by rfl⟩ : syracuseStep 2755727 = 4133591) B4133591
theorem B724135 : Blo 722323 724135 := bstep (se 1 (by rfl) ⟨543101, by rfl⟩ : syracuseStep 724135 = 1086203) B1086203
theorem B724383 : Blo 722323 724383 := bstep (se 1 (by rfl) ⟨543287, by rfl⟩ : syracuseStep 724383 = 1086575) B1086575
theorem B3673511 : Blo 722323 3673511 := bstep (se 1 (by rfl) ⟨2755133, by rfl⟩ : syracuseStep 3673511 = 5510267) B5510267
theorem B724431 : Blo 722323 724431 := bstep (se 1 (by rfl) ⟨543323, by rfl⟩ : syracuseStep 724431 = 1086647) B1086647
theorem B2067923 : Blo 722323 2067923 := bstep (se 1 (by rfl) ⟨1550942, by rfl⟩ : syracuseStep 2067923 = 3101885) B3101885
theorem B724591 : Blo 722323 724591 := bstep (se 1 (by rfl) ⟨543443, by rfl⟩ : syracuseStep 724591 = 1086887) B1086887
theorem B724711 : Blo 722323 724711 := bstep (se 1 (by rfl) ⟨543533, by rfl⟩ : syracuseStep 724711 = 1087067) B1087067
theorem B725215 : Blo 722323 725215 := bstep (se 1 (by rfl) ⟨543911, by rfl⟩ : syracuseStep 725215 = 1087823) B1087823
theorem B725231 : Blo 722323 725231 := bstep (se 1 (by rfl) ⟨543923, by rfl⟩ : syracuseStep 725231 = 1087847) B1087847
theorem B11309327 : Blo 722323 11309327 := bstep (se 1 (by rfl) ⟨8481995, by rfl⟩ : syracuseStep 11309327 = 16963991) B16963991
theorem B725275 : Blo 722323 725275 := bstep (se 1 (by rfl) ⟨543956, by rfl⟩ : syracuseStep 725275 = 1087913) B1087913
theorem B725531 : Blo 722323 725531 := bstep (se 1 (by rfl) ⟨544148, by rfl⟩ : syracuseStep 725531 = 1088297) B1088297
theorem B725671 : Blo 722323 725671 := bstep (se 1 (by rfl) ⟨544253, by rfl⟩ : syracuseStep 725671 = 1088507) B1088507
theorem B725695 : Blo 722323 725695 := bstep (se 1 (by rfl) ⟨544271, by rfl⟩ : syracuseStep 725695 = 1088543) B1088543
theorem B725711 : Blo 722323 725711 := bstep (se 1 (by rfl) ⟨544283, by rfl⟩ : syracuseStep 725711 = 1088567) B1088567
theorem B725791 : Blo 722323 725791 := bstep (se 1 (by rfl) ⟨544343, by rfl⟩ : syracuseStep 725791 = 1088687) B1088687
theorem B725887 : Blo 722323 725887 := bstep (se 1 (by rfl) ⟨544415, by rfl⟩ : syracuseStep 725887 = 1088831) B1088831
theorem B2757503 : Blo 722323 2757503 := bstep (se 1 (by rfl) ⟨2068127, by rfl⟩ : syracuseStep 2757503 = 4136255) B4136255
theorem B725983 : Blo 722323 725983 := bstep (se 1 (by rfl) ⟨544487, by rfl⟩ : syracuseStep 725983 = 1088975) B1088975
theorem B1086623 : Blo 722323 1086623 := bstep (se 1 (by rfl) ⟨814967, by rfl⟩ : syracuseStep 1086623 = 1629935) B1629935
theorem B726239 : Blo 722323 726239 := bstep (se 1 (by rfl) ⟨544679, by rfl⟩ : syracuseStep 726239 = 1089359) B1089359
theorem B726271 : Blo 722323 726271 := bstep (se 1 (by rfl) ⟨544703, by rfl⟩ : syracuseStep 726271 = 1089407) B1089407
theorem B726319 : Blo 722323 726319 := bstep (se 1 (by rfl) ⟨544739, by rfl⟩ : syracuseStep 726319 = 1089479) B1089479
theorem B1087241 : Blo 722323 1087241 := bstep (se 2 (by rfl) ⟨407715, by rfl⟩ : syracuseStep 1087241 = 815431) B815431
theorem B1546175 : Blo 722323 1546175 := bstep (se 1 (by rfl) ⟨1159631, by rfl⟩ : syracuseStep 1546175 = 2319263) B2319263
theorem B3676103 : Blo 722323 3676103 := bstep (se 1 (by rfl) ⟨2757077, by rfl⟩ : syracuseStep 3676103 = 5514155) B5514155
theorem B1087865 : Blo 722323 1087865 := bstep (se 2 (by rfl) ⟨407949, by rfl⟩ : syracuseStep 1087865 = 815899) B815899
theorem B1219063 : Blo 722323 1219063 := bstep (se 1 (by rfl) ⟨914297, by rfl⟩ : syracuseStep 1219063 = 1828595) B1828595
theorem B3906103 : Blo 722323 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B1088393 : Blo 722323 1088393 := bstep (se 2 (by rfl) ⟨408147, by rfl⟩ : syracuseStep 1088393 = 816295) B816295
theorem B3480509 : Blo 722323 3480509 := bstep (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) B1305191
theorem B1219691 : Blo 722323 1219691 := bstep (se 1 (by rfl) ⟨914768, by rfl⟩ : syracuseStep 1219691 = 1829537) B1829537
theorem B7445789 : Blo 722323 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B1088927 : Blo 722323 1088927 := bstep (se 1 (by rfl) ⟨816695, by rfl⟩ : syracuseStep 1088927 = 1633391) B1633391
theorem B1220143 : Blo 722323 1220143 := bstep (se 1 (by rfl) ⟨915107, by rfl⟩ : syracuseStep 1220143 = 1830215) B1830215
theorem B1089071 : Blo 722323 1089071 := bstep (se 1 (by rfl) ⟨816803, by rfl⟩ : syracuseStep 1089071 = 1633607) B1633607
theorem B3088439 : Blo 722323 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B1548551 : Blo 722323 1548551 := bstep (se 1 (by rfl) ⟨1161413, by rfl⟩ : syracuseStep 1548551 = 2322827) B2322827
theorem B1220987 : Blo 722323 1220987 := bstep (se 1 (by rfl) ⟨915740, by rfl⟩ : syracuseStep 1220987 = 1831481) B1831481
theorem B1221095 : Blo 722323 1221095 := bstep (se 1 (by rfl) ⟨915821, by rfl⟩ : syracuseStep 1221095 = 1831643) B1831643
theorem B3711527 : Blo 722323 3711527 := bstep (se 1 (by rfl) ⟨2783645, by rfl⟩ : syracuseStep 3711527 = 5567291) B5567291
theorem B1221743 : Blo 722323 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B2794607 : Blo 722323 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B8463485 : Blo 722323 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B8234783 : Blo 722323 8234783 := bstep (se 1 (by rfl) ⟨6176087, by rfl⟩ : syracuseStep 8234783 = 12352175) B12352175
theorem B19048283 : Blo 722323 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B1157447 : Blo 722323 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B1223039 : Blo 722323 1223039 := bstep (se 1 (by rfl) ⟨917279, by rfl⟩ : syracuseStep 1223039 = 1834559) B1834559
theorem B5941729 : Blo 722323 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B3091871 : Blo 722323 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B2207207 : Blo 722323 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B6958943 : Blo 722323 6958943 := bstep (se 1 (by rfl) ⟨5219207, by rfl⟩ : syracuseStep 6958943 = 10438415) B10438415
theorem B1224679 : Blo 722323 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B6959479 : Blo 722323 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B2438045 : Blo 722323 2438045 := bstep (se 3 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 2438045 = 914267) B914267
theorem B2143219 : Blo 722323 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B2930489 : Blo 722323 2930489 := bstep (se 2 (by rfl) ⟨1098933, by rfl⟩ : syracuseStep 2930489 = 2197867) B2197867
theorem B4962221 : Blo 722323 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B6174791 : Blo 722323 6174791 := bstep (se 1 (by rfl) ⟨4631093, by rfl⟩ : syracuseStep 6174791 = 9262187) B9262187
theorem B1161631 : Blo 722323 1161631 := bstep (se 1 (by rfl) ⟨871223, by rfl⟩ : syracuseStep 1161631 = 1742447) B1742447
theorem B7847059 : Blo 722323 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B1392175 : Blo 722323 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B6962861 : Blo 722323 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B2605193 : Blo 722323 2605193 := bstep (se 2 (by rfl) ⟨976947, by rfl⟩ : syracuseStep 2605193 = 1953895) B1953895
theorem B2442311 : Blo 722323 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B35702045 : Blo 722323 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B2442527 : Blo 722323 2442527 := bstep (se 1 (by rfl) ⟨1831895, by rfl⟩ : syracuseStep 2442527 = 3663791) B3663791
theorem B2934767 : Blo 722323 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2443391 : Blo 722323 2443391 := bstep (se 1 (by rfl) ⟨1832543, by rfl⟩ : syracuseStep 2443391 = 3665087) B3665087
theorem B5490827 : Blo 722323 5490827 := bstep (se 1 (by rfl) ⟨4118120, by rfl⟩ : syracuseStep 5490827 = 8236241) B8236241
theorem B772507 : Blo 722323 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B20892275 : Blo 722323 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B2444201 : Blo 722323 2444201 := bstep (se 2 (by rfl) ⟨916575, by rfl⟩ : syracuseStep 2444201 = 1833151) B1833151
theorem B2444255 : Blo 722323 2444255 := bstep (se 1 (by rfl) ⟨1833191, by rfl⟩ : syracuseStep 2444255 = 3666383) B3666383
theorem B2444417 : Blo 722323 2444417 := bstep (se 2 (by rfl) ⟨916656, by rfl⟩ : syracuseStep 2444417 = 1833313) B1833313
theorem B773327 : Blo 722323 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B10604039 : Blo 722323 10604039 := bstep (se 1 (by rfl) ⟨7953029, by rfl⟩ : syracuseStep 10604039 = 15906059) B15906059
theorem B33476113 : Blo 722323 33476113 := bstep (se 2 (by rfl) ⟨12553542, by rfl⟩ : syracuseStep 33476113 = 25107085) B25107085
theorem B20827691 : Blo 722323 20827691 := bstep (se 1 (by rfl) ⟨15620768, by rfl⟩ : syracuseStep 20827691 = 31241537) B31241537
theorem B1626047 : Blo 722323 1626047 := bstep (se 1 (by rfl) ⟨1219535, by rfl⟩ : syracuseStep 1626047 = 2439071) B2439071
theorem B45175151 : Blo 722323 45175151 := bstep (se 1 (by rfl) ⟨33881363, by rfl⟩ : syracuseStep 45175151 = 67762727) B67762727
theorem B3658121 : Blo 722323 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B2446361 : Blo 722323 2446361 := bstep (se 2 (by rfl) ⟨917385, by rfl⟩ : syracuseStep 2446361 = 1834771) B1834771
theorem B6280859 : Blo 722323 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B2447009 : Blo 722323 2447009 := bstep (se 2 (by rfl) ⟨917628, by rfl⟩ : syracuseStep 2447009 = 1835257) B1835257
theorem B2447225 : Blo 722323 2447225 := bstep (se 2 (by rfl) ⟨917709, by rfl⟩ : syracuseStep 2447225 = 1835419) B1835419
theorem B3660227 : Blo 722323 3660227 := bstep (se 1 (by rfl) ⟨2745170, by rfl⟩ : syracuseStep 3660227 = 5490341) B5490341
theorem B2447873 : Blo 722323 2447873 := bstep (se 2 (by rfl) ⟨917952, by rfl⟩ : syracuseStep 2447873 = 1835905) B1835905
theorem B2743865 : Blo 722323 2743865 := bstep (se 2 (by rfl) ⟨1028949, by rfl⟩ : syracuseStep 2743865 = 2057899) B2057899
theorem B2448953 : Blo 722323 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B2449115 : Blo 722323 2449115 := bstep (se 1 (by rfl) ⟨1836836, by rfl⟩ : syracuseStep 2449115 = 3673673) B3673673
theorem B3170219 : Blo 722323 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B1630457 : Blo 722323 1630457 := bstep (se 2 (by rfl) ⟨611421, by rfl⟩ : syracuseStep 1630457 = 1222843) B1222843
theorem B1630619 : Blo 722323 1630619 := bstep (se 1 (by rfl) ⟨1222964, by rfl⟩ : syracuseStep 1630619 = 2445929) B2445929
theorem B1958393 : Blo 722323 1958393 := bstep (se 2 (by rfl) ⟨734397, by rfl⟩ : syracuseStep 1958393 = 1468795) B1468795
theorem B2941481 : Blo 722323 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B2450303 : Blo 722323 2450303 := bstep (se 1 (by rfl) ⟨1837727, by rfl⟩ : syracuseStep 2450303 = 3675455) B3675455
theorem B9266183 : Blo 722323 9266183 := bstep (se 1 (by rfl) ⟨6949637, by rfl⟩ : syracuseStep 9266183 = 13899275) B13899275
theorem B2745353 : Blo 722323 2745353 := bstep (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) B2059015
theorem B5498603 : Blo 722323 5498603 := bstep (se 1 (by rfl) ⟨4123952, by rfl⟩ : syracuseStep 5498603 = 8247905) B8247905
theorem B1632239 : Blo 722323 1632239 := bstep (se 1 (by rfl) ⟨1224179, by rfl⟩ : syracuseStep 1632239 = 2448359) B2448359
theorem B1632455 : Blo 722323 1632455 := bstep (se 1 (by rfl) ⟨1224341, by rfl⟩ : syracuseStep 1632455 = 2448683) B2448683
theorem B3664115 : Blo 722323 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B2746781 : Blo 722323 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B1632923 : Blo 722323 1632923 := bstep (se 1 (by rfl) ⟨1224692, by rfl⟩ : syracuseStep 1632923 = 2449385) B2449385
theorem B813775 : Blo 722323 813775 := bstep (se 1 (by rfl) ⟨610331, by rfl⟩ : syracuseStep 813775 = 1220663) B1220663
theorem B30141233 : Blo 722323 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B2059175 : Blo 722323 2059175 := bstep (se 1 (by rfl) ⟨1544381, by rfl⟩ : syracuseStep 2059175 = 3088763) B3088763
theorem B10415465 : Blo 722323 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B95415803 : Blo 722323 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B1240679 : Blo 722323 1240679 := bstep (se 1 (by rfl) ⟨930509, by rfl⟩ : syracuseStep 1240679 = 1861019) B1861019
theorem B1633895 : Blo 722323 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B814783 : Blo 722323 814783 := bstep (se 1 (by rfl) ⟨611087, by rfl⟩ : syracuseStep 814783 = 1222175) B1222175
theorem B2060063 : Blo 722323 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B2322287 : Blo 722323 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B2617447 : Blo 722323 2617447 := bstep (se 1 (by rfl) ⟨1963085, by rfl⟩ : syracuseStep 2617447 = 3926171) B3926171
theorem B3666059 : Blo 722323 3666059 := bstep (se 1 (by rfl) ⟨2749544, by rfl⟩ : syracuseStep 3666059 = 5499089) B5499089
theorem B5566607 : Blo 722323 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B10416613 : Blo 722323 10416613 := bstep (se 4 (by rfl) ⟨976557, by rfl⟩ : syracuseStep 10416613 = 1953115) B1953115
theorem B2060873 : Blo 722323 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B2552639 : Blo 722323 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B4191839 : Blo 722323 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B2061931 : Blo 722323 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B817087 : Blo 722323 817087 := bstep (se 1 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 817087 = 1225631) B1225631
theorem B2062331 : Blo 722323 2062331 := bstep (se 1 (by rfl) ⟨1546748, by rfl⟩ : syracuseStep 2062331 = 3093497) B3093497
theorem B2750699 : Blo 722323 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B3766607 : Blo 722323 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B13236817 : Blo 722323 13236817 := bstep (se 2 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 13236817 = 9927613) B9927613
theorem B1571411 : Blo 722323 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B2751353 : Blo 722323 2751353 := bstep (se 2 (by rfl) ⟨1031757, by rfl⟩ : syracuseStep 2751353 = 2063515) B2063515
theorem B10583099 : Blo 722323 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B3669137 : Blo 722323 3669137 := bstep (se 2 (by rfl) ⟨1375926, by rfl⟩ : syracuseStep 3669137 = 2751853) B2751853
theorem B916687 : Blo 722323 916687 := bstep (se 1 (by rfl) ⟨687515, by rfl⟩ : syracuseStep 916687 = 1375031) B1375031
theorem B1736795 : Blo 722323 1736795 := bstep (se 1 (by rfl) ⟨1302596, by rfl⟩ : syracuseStep 1736795 = 2605193) B2605193
theorem B1835207 : Blo 722323 1835207 := bstep (se 1 (by rfl) ⟨1376405, by rfl⟩ : syracuseStep 1835207 = 2752811) B2752811
theorem B3670433 : Blo 722323 3670433 := bstep (se 2 (by rfl) ⟨1376412, by rfl⟩ : syracuseStep 3670433 = 2752825) B2752825
theorem B26804951 : Blo 722323 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B3671081 : Blo 722323 3671081 := bstep (se 2 (by rfl) ⟨1376655, by rfl⟩ : syracuseStep 3671081 = 2753311) B2753311
theorem B722399 : Blo 722323 722399 := bstep (se 1 (by rfl) ⟨541799, by rfl⟩ : syracuseStep 722399 = 1083599) B1083599
theorem B2754283 : Blo 722323 2754283 := bstep (se 1 (by rfl) ⟨2065712, by rfl⟩ : syracuseStep 2754283 = 4131425) B4131425
theorem B13928183 : Blo 722323 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B1837151 : Blo 722323 1837151 := bstep (se 1 (by rfl) ⟨1377863, by rfl⟩ : syracuseStep 1837151 = 2755727) B2755727
theorem B1378615 : Blo 722323 1378615 := bstep (se 1 (by rfl) ⟨1033961, by rfl⟩ : syracuseStep 1378615 = 2067923) B2067923
theorem B1084031 : Blo 722323 1084031 := bstep (se 1 (by rfl) ⟨813023, by rfl⟩ : syracuseStep 1084031 = 1626047) B1626047
theorem B7539551 : Blo 722323 7539551 := bstep (se 1 (by rfl) ⟨5654663, by rfl⟩ : syracuseStep 7539551 = 11309327) B11309327
theorem B30116767 : Blo 722323 30116767 := bstep (se 1 (by rfl) ⟨22587575, by rfl⟩ : syracuseStep 30116767 = 45175151) B45175151
theorem B1838335 : Blo 722323 1838335 := bstep (se 1 (by rfl) ⟨1378751, by rfl⟩ : syracuseStep 1838335 = 2757503) B2757503
theorem B724415 : Blo 722323 724415 := bstep (se 1 (by rfl) ⟨543311, by rfl⟩ : syracuseStep 724415 = 1086623) B1086623
theorem B1085033 : Blo 722323 1085033 := bstep (se 2 (by rfl) ⟨406887, by rfl⟩ : syracuseStep 1085033 = 813775) B813775
theorem B724827 : Blo 722323 724827 := bstep (se 1 (by rfl) ⟨543620, by rfl⟩ : syracuseStep 724827 = 1087241) B1087241
theorem B725243 : Blo 722323 725243 := bstep (se 1 (by rfl) ⟨543932, by rfl⟩ : syracuseStep 725243 = 1087865) B1087865
theorem B16748957 : Blo 722323 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B725595 : Blo 722323 725595 := bstep (se 1 (by rfl) ⟨544196, by rfl⟩ : syracuseStep 725595 = 1088393) B1088393
theorem B44634817 : Blo 722323 44634817 := bstep (se 2 (by rfl) ⟨16738056, by rfl⟩ : syracuseStep 44634817 = 33476113) B33476113
theorem B1086377 : Blo 722323 1086377 := bstep (se 2 (by rfl) ⟨407391, by rfl⟩ : syracuseStep 1086377 = 814783) B814783
theorem B725951 : Blo 722323 725951 := bstep (se 1 (by rfl) ⟨544463, by rfl⟩ : syracuseStep 725951 = 1088927) B1088927
theorem B726047 : Blo 722323 726047 := bstep (se 1 (by rfl) ⟨544535, by rfl⟩ : syracuseStep 726047 = 1089071) B1089071
theorem B1086971 : Blo 722323 1086971 := bstep (se 1 (by rfl) ⟨815228, by rfl⟩ : syracuseStep 1086971 = 1630457) B1630457
theorem B1087079 : Blo 722323 1087079 := bstep (se 1 (by rfl) ⟨815309, by rfl⟩ : syracuseStep 1087079 = 1630619) B1630619
theorem B9279305 : Blo 722323 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B3086525 : Blo 722323 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B2857625 : Blo 722323 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B1088159 : Blo 722323 1088159 := bstep (se 1 (by rfl) ⟨816119, by rfl⟩ : syracuseStep 1088159 = 1632239) B1632239
theorem B1088303 : Blo 722323 1088303 := bstep (se 1 (by rfl) ⟨816227, by rfl⟩ : syracuseStep 1088303 = 1632455) B1632455
theorem B1088615 : Blo 722323 1088615 := bstep (se 1 (by rfl) ⟨816461, by rfl⟩ : syracuseStep 1088615 = 1632923) B1632923
theorem B20094155 : Blo 722323 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B63610535 : Blo 722323 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B827119 : Blo 722323 827119 := bstep (se 1 (by rfl) ⟨620339, by rfl⟩ : syracuseStep 827119 = 1240679) B1240679
theorem B1089263 : Blo 722323 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B1548191 : Blo 722323 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B1089449 : Blo 722323 1089449 := bstep (se 2 (by rfl) ⟨408543, by rfl⟩ : syracuseStep 1089449 = 817087) B817087
theorem B3711071 : Blo 722323 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B1548841 : Blo 722323 1548841 := bstep (se 2 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 1548841 = 1161631) B1161631
theorem B2794559 : Blo 722323 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B10462745 : Blo 722323 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B1222249 : Blo 722323 1222249 := bstep (se 2 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 1222249 = 916687) B916687
theorem B7055399 : Blo 722323 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B1223707 : Blo 722323 1223707 := bstep (se 1 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 1223707 = 1835561) B1835561
theorem B23801363 : Blo 722323 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B7843949 : Blo 722323 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B4239785 : Blo 722323 4239785 := bstep (se 2 (by rfl) ⟨1589919, by rfl⟩ : syracuseStep 4239785 = 3179839) B3179839
theorem B1225199 : Blo 722323 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B2438747 : Blo 722323 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B1030009 : Blo 722323 1030009 := bstep (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) B772507
theorem B4635245 : Blo 722323 4635245 := bstep (se 3 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 4635245 = 1738217) B1738217
theorem B2440151 : Blo 722323 2440151 := bstep (se 1 (by rfl) ⟨1830113, by rfl⟩ : syracuseStep 2440151 = 3660227) B3660227
theorem B4963859 : Blo 722323 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B3489929 : Blo 722323 3489929 := bstep (se 2 (by rfl) ⟨1308723, by rfl⟩ : syracuseStep 3489929 = 2617447) B2617447
theorem B1032367 : Blo 722323 1032367 := bstep (se 1 (by rfl) ⟨774275, by rfl⟩ : syracuseStep 1032367 = 1548551) B1548551
theorem B2474351 : Blo 722323 2474351 := bstep (se 1 (by rfl) ⟨1855763, by rfl⟩ : syracuseStep 2474351 = 3711527) B3711527
theorem B6177455 : Blo 722323 6177455 := bstep (se 1 (by rfl) ⟨4633091, by rfl⟩ : syracuseStep 6177455 = 9266183) B9266183
theorem B5489855 : Blo 722323 5489855 := bstep (se 1 (by rfl) ⟨4117391, by rfl⟩ : syracuseStep 5489855 = 8234783) B8234783
theorem B12698855 : Blo 722323 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B2442743 : Blo 722323 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B4639295 : Blo 722323 4639295 := bstep (se 1 (by rfl) ⟨3479471, by rfl⟩ : syracuseStep 4639295 = 6958943) B6958943
theorem B2444039 : Blo 722323 2444039 := bstep (se 1 (by rfl) ⟨1833029, by rfl⟩ : syracuseStep 2444039 = 3666059) B3666059
theorem B1625363 : Blo 722323 1625363 := bstep (se 1 (by rfl) ⟨1219022, by rfl⟩ : syracuseStep 1625363 = 2438045) B2438045
theorem B1625417 : Blo 722323 1625417 := bstep (se 2 (by rfl) ⟨609531, by rfl⟩ : syracuseStep 1625417 = 1219063) B1219063
theorem B17649089 : Blo 722323 17649089 := bstep (se 2 (by rfl) ⟨6618408, by rfl⟩ : syracuseStep 17649089 = 13236817) B13236817
theorem B8244989 : Blo 722323 8244989 := bstep (se 3 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 8244989 = 3091871) B3091871
theorem B1953659 : Blo 722323 1953659 := bstep (se 1 (by rfl) ⟨1465244, by rfl⟩ : syracuseStep 1953659 = 2930489) B2930489
theorem B5885885 : Blo 722323 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B4116527 : Blo 722323 4116527 := bstep (se 1 (by rfl) ⟨3087395, by rfl⟩ : syracuseStep 4116527 = 6174791) B6174791
theorem B2511071 : Blo 722323 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B18567629 : Blo 722323 18567629 := bstep (se 3 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 18567629 = 6962861) B6962861
theorem B1626857 : Blo 722323 1626857 := bstep (se 2 (by rfl) ⟨610071, by rfl⟩ : syracuseStep 1626857 = 1220143) B1220143
theorem B1856233 : Blo 722323 1856233 := bstep (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) B1392175
theorem B2446091 : Blo 722323 2446091 := bstep (se 1 (by rfl) ⟨1834568, by rfl⟩ : syracuseStep 2446091 = 3669137) B3669137
theorem B2446847 : Blo 722323 2446847 := bstep (se 1 (by rfl) ⟨1835135, by rfl⟩ : syracuseStep 2446847 = 3670271) B3670271
theorem B2316023 : Blo 722323 2316023 := bstep (se 1 (by rfl) ⟨1737017, by rfl⟩ : syracuseStep 2316023 = 3474035) B3474035
theorem B21124955 : Blo 722323 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B1628207 : Blo 722323 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B1628351 : Blo 722323 1628351 := bstep (se 1 (by rfl) ⟨1221263, by rfl⟩ : syracuseStep 1628351 = 2442527) B2442527
theorem B1956511 : Blo 722323 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B1628927 : Blo 722323 1628927 := bstep (se 1 (by rfl) ⟨1221695, by rfl⟩ : syracuseStep 1628927 = 2443391) B2443391
theorem B3660551 : Blo 722323 3660551 := bstep (se 1 (by rfl) ⟨2745413, by rfl⟩ : syracuseStep 3660551 = 5490827) B5490827
theorem B1629467 : Blo 722323 1629467 := bstep (se 1 (by rfl) ⟨1222100, by rfl⟩ : syracuseStep 1629467 = 2444201) B2444201
theorem B1629503 : Blo 722323 1629503 := bstep (se 1 (by rfl) ⟨1222127, by rfl⟩ : syracuseStep 1629503 = 2444255) B2444255
theorem B1629611 : Blo 722323 1629611 := bstep (se 1 (by rfl) ⟨1222208, by rfl⟩ : syracuseStep 1629611 = 2444417) B2444417
theorem B2449007 : Blo 722323 2449007 := bstep (se 1 (by rfl) ⟨1836755, by rfl⟩ : syracuseStep 2449007 = 3673511) B3673511
theorem B13885127 : Blo 722323 13885127 := bstep (se 1 (by rfl) ⟨10413845, by rfl⟩ : syracuseStep 13885127 = 20827691) B20827691
theorem B22569293 : Blo 722323 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B7922305 : Blo 722323 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B1630907 : Blo 722323 1630907 := bstep (se 1 (by rfl) ⟨1223180, by rfl⟩ : syracuseStep 1630907 = 2446361) B2446361
theorem B2450465 : Blo 722323 2450465 := bstep (se 2 (by rfl) ⟨918924, by rfl⟩ : syracuseStep 2450465 = 1837849) B1837849
theorem B1631339 : Blo 722323 1631339 := bstep (se 1 (by rfl) ⟨1223504, by rfl⟩ : syracuseStep 1631339 = 2447009) B2447009
theorem B1631483 : Blo 722323 1631483 := bstep (se 1 (by rfl) ⟨1223612, by rfl⟩ : syracuseStep 1631483 = 2447225) B2447225
theorem B2450735 : Blo 722323 2450735 := bstep (se 1 (by rfl) ⟨1838051, by rfl⟩ : syracuseStep 2450735 = 3676103) B3676103
theorem B1631915 : Blo 722323 1631915 := bstep (se 1 (by rfl) ⟨1223936, by rfl⟩ : syracuseStep 1631915 = 2447873) B2447873
theorem B2320339 : Blo 722323 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B813127 : Blo 722323 813127 := bstep (se 1 (by rfl) ⟨609845, by rfl⟩ : syracuseStep 813127 = 1219691) B1219691
theorem B1829243 : Blo 722323 1829243 := bstep (se 1 (by rfl) ⟨1371932, by rfl⟩ : syracuseStep 1829243 = 2743865) B2743865
theorem B1632635 : Blo 722323 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B1632743 : Blo 722323 1632743 := bstep (se 1 (by rfl) ⟨1224557, by rfl⟩ : syracuseStep 1632743 = 2449115) B2449115
theorem B4123133 : Blo 722323 4123133 := bstep (se 3 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 4123133 = 1546175) B1546175
theorem B1632905 : Blo 722323 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B2058959 : Blo 722323 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B813991 : Blo 722323 813991 := bstep (se 1 (by rfl) ⟨610493, by rfl⟩ : syracuseStep 813991 = 1220987) B1220987
theorem B814063 : Blo 722323 814063 := bstep (se 1 (by rfl) ⟨610547, by rfl⟩ : syracuseStep 814063 = 1221095) B1221095
theorem B1305595 : Blo 722323 1305595 := bstep (se 1 (by rfl) ⟨979196, by rfl⟩ : syracuseStep 1305595 = 1958393) B1958393
theorem B1633535 : Blo 722323 1633535 := bstep (se 1 (by rfl) ⟨1225151, by rfl⟩ : syracuseStep 1633535 = 2450303) B2450303
theorem B13888817 : Blo 722323 13888817 := bstep (se 2 (by rfl) ⟨5208306, by rfl⟩ : syracuseStep 13888817 = 10416613) B10416613
theorem B1830235 : Blo 722323 1830235 := bstep (se 1 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 1830235 = 2745353) B2745353
theorem B814495 : Blo 722323 814495 := bstep (se 1 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 814495 = 1221743) B1221743
theorem B1863071 : Blo 722323 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B3665735 : Blo 722323 3665735 := bstep (se 1 (by rfl) ⟨2749301, by rfl⟩ : syracuseStep 3665735 = 5498603) B5498603
theorem B4190429 : Blo 722323 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B815359 : Blo 722323 815359 := bstep (se 1 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 815359 = 1223039) B1223039
theorem B1831187 : Blo 722323 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B1372783 : Blo 722323 1372783 := bstep (se 1 (by rfl) ⟨1029587, by rfl⟩ : syracuseStep 1372783 = 2059175) B2059175
theorem B2749241 : Blo 722323 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B6943643 : Blo 722323 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B1373375 : Blo 722323 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B1373915 : Blo 722323 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B2062205 : Blo 722323 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B27228149 : Blo 722323 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B5208137 : Blo 722323 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B3308147 : Blo 722323 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B1374887 : Blo 722323 1374887 := bstep (se 1 (by rfl) ⟨1031165, by rfl⟩ : syracuseStep 1374887 = 2062331) B2062331
theorem B28277437 : Blo 722323 28277437 := bstep (se 3 (by rfl) ⟨5302019, by rfl⟩ : syracuseStep 28277437 = 10604039) B10604039
theorem B1833799 : Blo 722323 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B1834235 : Blo 722323 1834235 := bstep (se 1 (by rfl) ⟨1375676, by rfl⟩ : syracuseStep 1834235 = 2751353) B2751353
theorem B8453917 : Blo 722323 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B2326619 : Blo 722323 2326619 := bstep (se 1 (by rfl) ⟨1744964, by rfl⟩ : syracuseStep 2326619 = 3489929) B3489929
theorem B1376489 : Blo 722323 1376489 := bstep (se 2 (by rfl) ⟨516183, by rfl⟩ : syracuseStep 1376489 = 1032367) B1032367
theorem B2065121 : Blo 722323 2065121 := bstep (se 2 (by rfl) ⟨774420, by rfl⟩ : syracuseStep 2065121 = 1548841) B1548841
theorem B44663885 : Blo 722323 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B722687 : Blo 722323 722687 := bstep (se 1 (by rfl) ⟨542015, by rfl⟩ : syracuseStep 722687 = 1084031) B1084031
theorem B1083575 : Blo 722323 1083575 := bstep (se 1 (by rfl) ⟨812681, by rfl⟩ : syracuseStep 1083575 = 1625363) B1625363
theorem B1083611 : Blo 722323 1083611 := bstep (se 1 (by rfl) ⟨812708, by rfl⟩ : syracuseStep 1083611 = 1625417) B1625417
theorem B11766059 : Blo 722323 11766059 := bstep (se 1 (by rfl) ⟨8824544, by rfl⟩ : syracuseStep 11766059 = 17649089) B17649089
theorem B3672377 : Blo 722323 3672377 := bstep (se 2 (by rfl) ⟨1377141, by rfl⟩ : syracuseStep 3672377 = 2754283) B2754283
theorem B723355 : Blo 722323 723355 := bstep (se 1 (by rfl) ⟨542516, by rfl⟩ : syracuseStep 723355 = 1085033) B1085033
theorem B1084169 : Blo 722323 1084169 := bstep (se 2 (by rfl) ⟨406563, by rfl⟩ : syracuseStep 1084169 = 813127) B813127
theorem B1674047 : Blo 722323 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B1838153 : Blo 722323 1838153 := bstep (se 2 (by rfl) ⟨689307, by rfl⟩ : syracuseStep 1838153 = 1378615) B1378615
theorem B1084571 : Blo 722323 1084571 := bstep (se 1 (by rfl) ⟨813428, by rfl⟩ : syracuseStep 1084571 = 1626857) B1626857
theorem B724251 : Blo 722323 724251 := bstep (se 1 (by rfl) ⟨543188, by rfl⟩ : syracuseStep 724251 = 1086377) B1086377
theorem B724647 : Blo 722323 724647 := bstep (se 1 (by rfl) ⟨543485, by rfl⟩ : syracuseStep 724647 = 1086971) B1086971
theorem B724719 : Blo 722323 724719 := bstep (se 1 (by rfl) ⟨543539, by rfl⟩ : syracuseStep 724719 = 1087079) B1087079
theorem B1544015 : Blo 722323 1544015 := bstep (se 1 (by rfl) ⟨1158011, by rfl⟩ : syracuseStep 1544015 = 2316023) B2316023
theorem B1085321 : Blo 722323 1085321 := bstep (se 2 (by rfl) ⟨406995, by rfl⟩ : syracuseStep 1085321 = 813991) B813991
theorem B1085417 : Blo 722323 1085417 := bstep (se 2 (by rfl) ⟨407031, by rfl⟩ : syracuseStep 1085417 = 814063) B814063
theorem B1740793 : Blo 722323 1740793 := bstep (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) B1305595
theorem B1085471 : Blo 722323 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B1085567 : Blo 722323 1085567 := bstep (se 1 (by rfl) ⟨814175, by rfl⟩ : syracuseStep 1085567 = 1628351) B1628351
theorem B1905083 : Blo 722323 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B725439 : Blo 722323 725439 := bstep (se 1 (by rfl) ⟨544079, by rfl⟩ : syracuseStep 725439 = 1088159) B1088159
theorem B1085951 : Blo 722323 1085951 := bstep (se 1 (by rfl) ⟨814463, by rfl⟩ : syracuseStep 1085951 = 1628927) B1628927
theorem B725535 : Blo 722323 725535 := bstep (se 1 (by rfl) ⟨544151, by rfl⟩ : syracuseStep 725535 = 1088303) B1088303
theorem B1085993 : Blo 722323 1085993 := bstep (se 2 (by rfl) ⟨407247, by rfl⟩ : syracuseStep 1085993 = 814495) B814495
theorem B725743 : Blo 722323 725743 := bstep (se 1 (by rfl) ⟨544307, by rfl⟩ : syracuseStep 725743 = 1088615) B1088615
theorem B1086311 : Blo 722323 1086311 := bstep (se 1 (by rfl) ⟨814733, by rfl⟩ : syracuseStep 1086311 = 1629467) B1629467
theorem B1086335 : Blo 722323 1086335 := bstep (se 1 (by rfl) ⟨814751, by rfl⟩ : syracuseStep 1086335 = 1629503) B1629503
theorem B1086407 : Blo 722323 1086407 := bstep (se 1 (by rfl) ⟨814805, by rfl⟩ : syracuseStep 1086407 = 1629611) B1629611
theorem B42407023 : Blo 722323 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B726175 : Blo 722323 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B726299 : Blo 722323 726299 := bstep (se 1 (by rfl) ⟨544724, by rfl⟩ : syracuseStep 726299 = 1089449) B1089449
theorem B15046195 : Blo 722323 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B1087145 : Blo 722323 1087145 := bstep (se 2 (by rfl) ⟨407679, by rfl⟩ : syracuseStep 1087145 = 815359) B815359
theorem B1087271 : Blo 722323 1087271 := bstep (se 1 (by rfl) ⟨815453, by rfl⟩ : syracuseStep 1087271 = 1630907) B1630907
theorem B1087559 : Blo 722323 1087559 := bstep (se 1 (by rfl) ⟨815669, by rfl⟩ : syracuseStep 1087559 = 1631339) B1631339
theorem B1087655 : Blo 722323 1087655 := bstep (se 1 (by rfl) ⟨815741, by rfl⟩ : syracuseStep 1087655 = 1631483) B1631483
theorem B59513089 : Blo 722323 59513089 := bstep (se 2 (by rfl) ⟨22317408, by rfl⟩ : syracuseStep 59513089 = 44634817) B44634817
theorem B1087943 : Blo 722323 1087943 := bstep (se 1 (by rfl) ⟨815957, by rfl⟩ : syracuseStep 1087943 = 1631915) B1631915
theorem B1219495 : Blo 722323 1219495 := bstep (se 1 (by rfl) ⟨914621, by rfl⟩ : syracuseStep 1219495 = 1829243) B1829243
theorem B1088423 : Blo 722323 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B1088495 : Blo 722323 1088495 := bstep (se 1 (by rfl) ⟨816371, by rfl⟩ : syracuseStep 1088495 = 1632743) B1632743
theorem B1088603 : Blo 722323 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B1089023 : Blo 722323 1089023 := bstep (se 1 (by rfl) ⟨816767, by rfl⟩ : syracuseStep 1089023 = 1633535) B1633535
theorem B15867575 : Blo 722323 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B2793619 : Blo 722323 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B1220791 : Blo 722323 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B2826523 : Blo 722323 2826523 := bstep (se 1 (by rfl) ⟨2119892, by rfl⟩ : syracuseStep 2826523 = 4239785) B4239785
theorem B4629095 : Blo 722323 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B3090163 : Blo 722323 3090163 := bstep (se 1 (by rfl) ⟨2317622, by rfl⟩ : syracuseStep 3090163 = 4635245) B4635245
theorem B2205431 : Blo 722323 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B1222823 : Blo 722323 1222823 := bstep (se 1 (by rfl) ⟨917117, by rfl⟩ : syracuseStep 1222823 = 1834235) B1834235
theorem B1157863 : Blo 722323 1157863 := bstep (se 1 (by rfl) ⟨868397, by rfl⟩ : syracuseStep 1157863 = 1736795) B1736795
theorem B1223471 : Blo 722323 1223471 := bstep (se 1 (by rfl) ⟨917603, by rfl⟩ : syracuseStep 1223471 = 1835207) B1835207
theorem B1649567 : Blo 722323 1649567 := bstep (se 1 (by rfl) ⟨1237175, by rfl⟩ : syracuseStep 1649567 = 2474351) B2474351
theorem B17869967 : Blo 722323 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B8465903 : Blo 722323 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B9285455 : Blo 722323 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B1224767 : Blo 722323 1224767 := bstep (se 1 (by rfl) ⟨918575, by rfl⟩ : syracuseStep 1224767 = 1837151) B1837151
theorem B3092863 : Blo 722323 3092863 := bstep (se 1 (by rfl) ⟨2319647, by rfl⟩ : syracuseStep 3092863 = 4639295) B4639295
theorem B5026367 : Blo 722323 5026367 := bstep (se 1 (by rfl) ⟨3769775, by rfl⟩ : syracuseStep 5026367 = 7539551) B7539551
theorem B3093785 : Blo 722323 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B7452157 : Blo 722323 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B42252293 : Blo 722323 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B40155689 : Blo 722323 40155689 := bstep (se 2 (by rfl) ⟨15058383, by rfl⟩ : syracuseStep 40155689 = 30116767) B30116767
theorem B2440313 : Blo 722323 2440313 := bstep (se 2 (by rfl) ⟨915117, by rfl⟩ : syracuseStep 2440313 = 1830235) B1830235
theorem B2440367 : Blo 722323 2440367 := bstep (se 1 (by rfl) ⟨1830275, by rfl⟩ : syracuseStep 2440367 = 3660551) B3660551
theorem B9256751 : Blo 722323 9256751 := bstep (se 1 (by rfl) ⟨6942563, by rfl⟩ : syracuseStep 9256751 = 13885127) B13885127
theorem B2474047 : Blo 722323 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B2474977 : Blo 722323 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B4703599 : Blo 722323 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B9259211 : Blo 722323 9259211 := bstep (se 1 (by rfl) ⟨6944408, by rfl⟩ : syracuseStep 9259211 = 13888817) B13888817
theorem B2443823 : Blo 722323 2443823 := bstep (se 1 (by rfl) ⟨1832867, by rfl⟩ : syracuseStep 2443823 = 3665735) B3665735
theorem B5229299 : Blo 722323 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B2608681 : Blo 722323 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B37703249 : Blo 722323 37703249 := bstep (se 2 (by rfl) ⟨14138718, by rfl⟩ : syracuseStep 37703249 = 28277437) B28277437
theorem B1625831 : Blo 722323 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B2445065 : Blo 722323 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B1626767 : Blo 722323 1626767 := bstep (se 1 (by rfl) ⟨1220075, by rfl⟩ : syracuseStep 1626767 = 2440151) B2440151
theorem B1102825 : Blo 722323 1102825 := bstep (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) B827119
theorem B2446955 : Blo 722323 2446955 := bstep (se 1 (by rfl) ⟨1835216, by rfl⟩ : syracuseStep 2446955 = 3670433) B3670433
theorem B4118303 : Blo 722323 4118303 := bstep (se 1 (by rfl) ⟨3088727, by rfl⟩ : syracuseStep 4118303 = 6177455) B6177455
theorem B2447387 : Blo 722323 2447387 := bstep (se 1 (by rfl) ⟨1835540, by rfl⟩ : syracuseStep 2447387 = 3671081) B3671081
theorem B3659903 : Blo 722323 3659903 := bstep (se 1 (by rfl) ⟨2744927, by rfl⟩ : syracuseStep 3659903 = 5489855) B5489855
theorem B1628495 : Blo 722323 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B1629359 : Blo 722323 1629359 := bstep (se 1 (by rfl) ⟨1222019, by rfl⟩ : syracuseStep 1629359 = 2444039) B2444039
theorem B1629665 : Blo 722323 1629665 := bstep (se 2 (by rfl) ⟨611124, by rfl⟩ : syracuseStep 1629665 = 1222249) B1222249
theorem B5496659 : Blo 722323 5496659 := bstep (se 1 (by rfl) ⟨4122494, by rfl⟩ : syracuseStep 5496659 = 8244989) B8244989
theorem B1302439 : Blo 722323 1302439 := bstep (se 1 (by rfl) ⟨976829, by rfl⟩ : syracuseStep 1302439 = 1953659) B1953659
theorem B3923923 : Blo 722323 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B2744351 : Blo 722323 2744351 := bstep (se 1 (by rfl) ⟨2058263, by rfl⟩ : syracuseStep 2744351 = 4116527) B4116527
theorem B12378419 : Blo 722323 12378419 := bstep (se 1 (by rfl) ⟨9283814, by rfl⟩ : syracuseStep 12378419 = 18567629) B18567629
theorem B3662333 : Blo 722323 3662333 := bstep (se 3 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 3662333 = 1373375) B1373375
theorem B1630727 : Blo 722323 1630727 := bstep (se 1 (by rfl) ⟨1223045, by rfl⟩ : syracuseStep 1630727 = 2446091) B2446091
theorem B1631231 : Blo 722323 1631231 := bstep (se 1 (by rfl) ⟨1223423, by rfl⟩ : syracuseStep 1631231 = 2446847) B2446847
theorem B6186203 : Blo 722323 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B14083303 : Blo 722323 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B1631609 : Blo 722323 1631609 := bstep (se 2 (by rfl) ⟨611853, by rfl⟩ : syracuseStep 1631609 = 1223707) B1223707
theorem B2057683 : Blo 722323 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B2451113 : Blo 722323 2451113 := bstep (se 2 (by rfl) ⟨919167, by rfl⟩ : syracuseStep 2451113 = 1838335) B1838335
theorem B13396103 : Blo 722323 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B1632671 : Blo 722323 1632671 := bstep (se 1 (by rfl) ⟨1224503, by rfl⟩ : syracuseStep 1632671 = 2449007) B2449007
theorem B1633643 : Blo 722323 1633643 := bstep (se 1 (by rfl) ⟨1225232, by rfl⟩ : syracuseStep 1633643 = 2450465) B2450465
theorem B1830377 : Blo 722323 1830377 := bstep (se 2 (by rfl) ⟨686391, by rfl⟩ : syracuseStep 1830377 = 1372783) B1372783
theorem B1633823 : Blo 722323 1633823 := bstep (se 1 (by rfl) ⟨1225367, by rfl⟩ : syracuseStep 1633823 = 2450735) B2450735
theorem B6975163 : Blo 722323 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B2748755 : Blo 722323 2748755 := bstep (se 1 (by rfl) ⟨2061566, by rfl⟩ : syracuseStep 2748755 = 4123133) B4123133
theorem B1372639 : Blo 722323 1372639 := bstep (se 1 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 1372639 = 2058959) B2058959
theorem B1242047 : Blo 722323 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B1373345 : Blo 722323 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B816799 : Blo 722323 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B1832827 : Blo 722323 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B915943 : Blo 722323 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B1374803 : Blo 722323 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B18152099 : Blo 722323 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B3472091 : Blo 722323 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B916591 : Blo 722323 916591 := bstep (se 1 (by rfl) ⟨687443, by rfl⟩ : syracuseStep 916591 = 1374887) B1374887
theorem B3309239 : Blo 722323 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B11271889 : Blo 722323 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B4128509 : Blo 722323 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B917659 : Blo 722323 917659 := bstep (se 1 (by rfl) ⟨688244, by rfl⟩ : syracuseStep 917659 = 1376489) B1376489
theorem B3768697 : Blo 722323 3768697 := bstep (se 2 (by rfl) ⟨1413261, by rfl⟩ : syracuseStep 3768697 = 2826523) B2826523
theorem B1376747 : Blo 722323 1376747 := bstep (se 1 (by rfl) ⟨1032560, by rfl⟩ : syracuseStep 1376747 = 2065121) B2065121
theorem B722383 : Blo 722323 722383 := bstep (se 1 (by rfl) ⟨541787, by rfl⟩ : syracuseStep 722383 = 1083575) B1083575
theorem B722407 : Blo 722323 722407 := bstep (se 1 (by rfl) ⟨541805, by rfl⟩ : syracuseStep 722407 = 1083611) B1083611
theorem B18777737 : Blo 722323 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B722779 : Blo 722323 722779 := bstep (se 1 (by rfl) ⟨542084, by rfl⟩ : syracuseStep 722779 = 1084169) B1084169
theorem B1116031 : Blo 722323 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B723047 : Blo 722323 723047 := bstep (se 1 (by rfl) ⟨542285, by rfl⟩ : syracuseStep 723047 = 1084571) B1084571
theorem B25135499 : Blo 722323 25135499 := bstep (se 1 (by rfl) ⟨18851624, by rfl⟩ : syracuseStep 25135499 = 37703249) B37703249
theorem B1083887 : Blo 722323 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B723547 : Blo 722323 723547 := bstep (se 1 (by rfl) ⟨542660, by rfl⟩ : syracuseStep 723547 = 1085321) B1085321
theorem B723611 : Blo 722323 723611 := bstep (se 1 (by rfl) ⟨542708, by rfl⟩ : syracuseStep 723611 = 1085417) B1085417
theorem B723647 : Blo 722323 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B723711 : Blo 722323 723711 := bstep (se 1 (by rfl) ⟨542783, by rfl⟩ : syracuseStep 723711 = 1085567) B1085567
theorem B723967 : Blo 722323 723967 := bstep (se 1 (by rfl) ⟨542975, by rfl⟩ : syracuseStep 723967 = 1085951) B1085951
theorem B723995 : Blo 722323 723995 := bstep (se 1 (by rfl) ⟨542996, by rfl⟩ : syracuseStep 723995 = 1085993) B1085993
theorem B1084511 : Blo 722323 1084511 := bstep (se 1 (by rfl) ⟨813383, by rfl⟩ : syracuseStep 1084511 = 1626767) B1626767
theorem B724207 : Blo 722323 724207 := bstep (se 1 (by rfl) ⟨543155, by rfl⟩ : syracuseStep 724207 = 1086311) B1086311
theorem B724223 : Blo 722323 724223 := bstep (se 1 (by rfl) ⟨543167, by rfl⟩ : syracuseStep 724223 = 1086335) B1086335
theorem B724271 : Blo 722323 724271 := bstep (se 1 (by rfl) ⟨543203, by rfl⟩ : syracuseStep 724271 = 1086407) B1086407
theorem B1543817 : Blo 722323 1543817 := bstep (se 2 (by rfl) ⟨578931, by rfl⟩ : syracuseStep 1543817 = 1157863) B1157863
theorem B724763 : Blo 722323 724763 := bstep (se 1 (by rfl) ⟨543572, by rfl⟩ : syracuseStep 724763 = 1087145) B1087145
theorem B724847 : Blo 722323 724847 := bstep (se 1 (by rfl) ⟨543635, by rfl⟩ : syracuseStep 724847 = 1087271) B1087271
theorem B725039 : Blo 722323 725039 := bstep (se 1 (by rfl) ⟨543779, by rfl⟩ : syracuseStep 725039 = 1087559) B1087559
theorem B725103 : Blo 722323 725103 := bstep (se 1 (by rfl) ⟨543827, by rfl⟩ : syracuseStep 725103 = 1087655) B1087655
theorem B1085663 : Blo 722323 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B725295 : Blo 722323 725295 := bstep (se 1 (by rfl) ⟨543971, by rfl⟩ : syracuseStep 725295 = 1087943) B1087943
theorem B725615 : Blo 722323 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B725663 : Blo 722323 725663 := bstep (se 1 (by rfl) ⟨544247, by rfl⟩ : syracuseStep 725663 = 1088495) B1088495
theorem B3478241 : Blo 722323 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B725735 : Blo 722323 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B1086239 : Blo 722323 1086239 := bstep (se 1 (by rfl) ⟨814679, by rfl⟩ : syracuseStep 1086239 = 1629359) B1629359
theorem B1086443 : Blo 722323 1086443 := bstep (se 1 (by rfl) ⟨814832, by rfl⟩ : syracuseStep 1086443 = 1629665) B1629665
theorem B726015 : Blo 722323 726015 := bstep (se 1 (by rfl) ⟨544511, by rfl⟩ : syracuseStep 726015 = 1089023) B1089023
theorem B1087151 : Blo 722323 1087151 := bstep (se 1 (by rfl) ⟨815363, by rfl⟩ : syracuseStep 1087151 = 1630727) B1630727
theorem B3086063 : Blo 722323 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B1087487 : Blo 722323 1087487 := bstep (se 1 (by rfl) ⟨815615, by rfl⟩ : syracuseStep 1087487 = 1631231) B1631231
theorem B1087739 : Blo 722323 1087739 := bstep (se 1 (by rfl) ⟨815804, by rfl⟩ : syracuseStep 1087739 = 1631609) B1631609
theorem B1088447 : Blo 722323 1088447 := bstep (se 1 (by rfl) ⟨816335, by rfl⟩ : syracuseStep 1088447 = 1632671) B1632671
theorem B9936209 : Blo 722323 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B20061593 : Blo 722323 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B1089065 : Blo 722323 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B1089095 : Blo 722323 1089095 := bstep (se 1 (by rfl) ⟨816821, by rfl⟩ : syracuseStep 1089095 = 1633643) B1633643
theorem B1220251 : Blo 722323 1220251 := bstep (se 1 (by rfl) ⟨915188, by rfl⟩ : syracuseStep 1220251 = 1830377) B1830377
theorem B5643935 : Blo 722323 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B1089215 : Blo 722323 1089215 := bstep (se 1 (by rfl) ⟨816911, by rfl⟩ : syracuseStep 1089215 = 1633823) B1633823
theorem B3350911 : Blo 722323 3350911 := bstep (se 1 (by rfl) ⟨2513183, by rfl⟩ : syracuseStep 3350911 = 5026367) B5026367
theorem B828031 : Blo 722323 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B1221257 : Blo 722323 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B1222121 : Blo 722323 1222121 := bstep (se 2 (by rfl) ⟨458295, by rfl⟩ : syracuseStep 1222121 = 916591) B916591
theorem B12101399 : Blo 722323 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B2206159 : Blo 722323 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B6171167 : Blo 722323 6171167 := bstep (se 1 (by rfl) ⟨4628375, by rfl⟩ : syracuseStep 6171167 = 9256751) B9256751
theorem B1551079 : Blo 722323 1551079 := bstep (se 1 (by rfl) ⟨1163309, by rfl⟩ : syracuseStep 1551079 = 2326619) B2326619
theorem B6172807 : Blo 722323 6172807 := bstep (se 1 (by rfl) ⟨4629605, by rfl⟩ : syracuseStep 6172807 = 9259211) B9259211
theorem B7844039 : Blo 722323 7844039 := bstep (se 1 (by rfl) ⟨5883029, by rfl⟩ : syracuseStep 7844039 = 11766059) B11766059
theorem B3486199 : Blo 722323 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B1225435 : Blo 722323 1225435 := bstep (se 1 (by rfl) ⟨919076, by rfl⟩ : syracuseStep 1225435 = 1838153) B1838153
theorem B1029343 : Blo 722323 1029343 := bstep (se 1 (by rfl) ⟨772007, by rfl⟩ : syracuseStep 1029343 = 1544015) B1544015
theorem B2439935 : Blo 722323 2439935 := bstep (se 1 (by rfl) ⟨1829951, by rfl⟩ : syracuseStep 2439935 = 3659903) B3659903
theorem B5881733 : Blo 722323 5881733 := bstep (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) B1102825
theorem B2441555 : Blo 722323 2441555 := bstep (se 1 (by rfl) ⟨1831166, by rfl⟩ : syracuseStep 2441555 = 3662333) B3662333
theorem B8930735 : Blo 722323 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B56542697 : Blo 722323 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B25085861 : Blo 722323 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B1099711 : Blo 722323 1099711 := bstep (se 1 (by rfl) ⟨824783, by rfl⟩ : syracuseStep 1099711 = 1649567) B1649567
theorem B11913311 : Blo 722323 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B2443769 : Blo 722323 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B79350785 : Blo 722323 79350785 := bstep (se 2 (by rfl) ⟨29756544, by rfl⟩ : syracuseStep 79350785 = 59513089) B59513089
theorem B1625993 : Blo 722323 1625993 := bstep (se 2 (by rfl) ⟨609747, by rfl⟩ : syracuseStep 1625993 = 1219495) B1219495
theorem B28168195 : Blo 722323 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B2314727 : Blo 722323 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B1626875 : Blo 722323 1626875 := bstep (se 1 (by rfl) ⟨1220156, by rfl⟩ : syracuseStep 1626875 = 2440313) B2440313
theorem B1626911 : Blo 722323 1626911 := bstep (se 1 (by rfl) ⟨1220183, by rfl⟩ : syracuseStep 1626911 = 2440367) B2440367
theorem B15029185 : Blo 722323 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B5231897 : Blo 722323 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B3298729 : Blo 722323 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B1627721 : Blo 722323 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B29775923 : Blo 722323 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B14899301 : Blo 722323 14899301 := bstep (se 4 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 14899301 = 2793619) B2793619
theorem B3299969 : Blo 722323 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B2448251 : Blo 722323 2448251 := bstep (se 1 (by rfl) ⟨1836188, by rfl⟩ : syracuseStep 2448251 = 3672377) B3672377
theorem B1629215 : Blo 722323 1629215 := bstep (se 1 (by rfl) ⟨1221911, by rfl⟩ : syracuseStep 1629215 = 2443823) B2443823
theorem B2743577 : Blo 722323 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B4120217 : Blo 722323 4120217 := bstep (se 2 (by rfl) ⟨1545081, by rfl⟩ : syracuseStep 4120217 = 3090163) B3090163
theorem B1630043 : Blo 722323 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B1270055 : Blo 722323 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B1631303 : Blo 722323 1631303 := bstep (se 1 (by rfl) ⟨1223477, by rfl⟩ : syracuseStep 1631303 = 2446955) B2446955
theorem B2745535 : Blo 722323 2745535 := bstep (se 1 (by rfl) ⟨2059151, by rfl⟩ : syracuseStep 2745535 = 4118303) B4118303
theorem B1631591 : Blo 722323 1631591 := bstep (se 1 (by rfl) ⟨1223693, by rfl⟩ : syracuseStep 1631591 = 2447387) B2447387
theorem B9300217 : Blo 722323 9300217 := bstep (se 2 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 9300217 = 6975163) B6975163
theorem B10578383 : Blo 722323 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B3664439 : Blo 722323 3664439 := bstep (se 1 (by rfl) ⟨2748329, by rfl⟩ : syracuseStep 3664439 = 5496659) B5496659
theorem B2321057 : Blo 722323 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B1829567 : Blo 722323 1829567 := bstep (se 1 (by rfl) ⟨1372175, by rfl⟩ : syracuseStep 1829567 = 2744351) B2744351
theorem B8252279 : Blo 722323 8252279 := bstep (se 1 (by rfl) ⟨6189209, by rfl⟩ : syracuseStep 8252279 = 12378419) B12378419
theorem B4123817 : Blo 722323 4123817 := bstep (se 2 (by rfl) ⟨1546431, by rfl⟩ : syracuseStep 4123817 = 3092863) B3092863
theorem B1830185 : Blo 722323 1830185 := bstep (se 2 (by rfl) ⟨686319, by rfl⟩ : syracuseStep 1830185 = 1372639) B1372639
theorem B4124135 : Blo 722323 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B1634075 : Blo 722323 1634075 := bstep (se 1 (by rfl) ⟨1225556, by rfl⟩ : syracuseStep 1634075 = 2451113) B2451113
theorem B1470287 : Blo 722323 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B815215 : Blo 722323 815215 := bstep (se 1 (by rfl) ⟨611411, by rfl⟩ : syracuseStep 815215 = 1222823) B1222823
theorem B815647 : Blo 722323 815647 := bstep (se 1 (by rfl) ⟨611735, by rfl⟩ : syracuseStep 815647 = 1223471) B1223471
theorem B6190303 : Blo 722323 6190303 := bstep (se 1 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 6190303 = 9285455) B9285455
theorem B816511 : Blo 722323 816511 := bstep (se 1 (by rfl) ⟨612383, by rfl⟩ : syracuseStep 816511 = 1224767) B1224767
theorem B1832503 : Blo 722323 1832503 := bstep (se 1 (by rfl) ⟨1374377, by rfl⟩ : syracuseStep 1832503 = 2748755) B2748755
theorem B915563 : Blo 722323 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B2062523 : Blo 722323 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B26770459 : Blo 722323 26770459 := bstep (se 1 (by rfl) ⟨20077844, by rfl⟩ : syracuseStep 26770459 = 40155689) B40155689
theorem B916535 : Blo 722323 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B2752339 : Blo 722323 2752339 := bstep (se 1 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 2752339 = 4128509) B4128509
theorem B1736585 : Blo 722323 1736585 := bstep (se 2 (by rfl) ⟨651219, by rfl⟩ : syracuseStep 1736585 = 1302439) B1302439
theorem B917831 : Blo 722323 917831 := bstep (se 1 (by rfl) ⟨688373, by rfl⟩ : syracuseStep 917831 = 1376747) B1376747
theorem B12518491 : Blo 722323 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B722591 : Blo 722323 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B9275309 : Blo 722323 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B723007 : Blo 722323 723007 := bstep (se 1 (by rfl) ⟨542255, by rfl⟩ : syracuseStep 723007 = 1084511) B1084511
theorem B11766181 : Blo 722323 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B1083995 : Blo 722323 1083995 := bstep (se 1 (by rfl) ⟨812996, by rfl⟩ : syracuseStep 1083995 = 1625993) B1625993
theorem B723775 : Blo 722323 723775 := bstep (se 1 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 723775 = 1085663) B1085663
theorem B1543151 : Blo 722323 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B1084583 : Blo 722323 1084583 := bstep (se 1 (by rfl) ⟨813437, by rfl⟩ : syracuseStep 1084583 = 1626875) B1626875
theorem B1084607 : Blo 722323 1084607 := bstep (se 1 (by rfl) ⟨813455, by rfl⟩ : syracuseStep 1084607 = 1626911) B1626911
theorem B724159 : Blo 722323 724159 := bstep (se 1 (by rfl) ⟨543119, by rfl⟩ : syracuseStep 724159 = 1086239) B1086239
theorem B724295 : Blo 722323 724295 := bstep (se 1 (by rfl) ⟨543221, by rfl⟩ : syracuseStep 724295 = 1086443) B1086443
theorem B2068105 : Blo 722323 2068105 := bstep (se 2 (by rfl) ⟨775539, by rfl⟩ : syracuseStep 2068105 = 1551079) B1551079
theorem B1085147 : Blo 722323 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B724767 : Blo 722323 724767 := bstep (se 1 (by rfl) ⟨543575, by rfl⟩ : syracuseStep 724767 = 1087151) B1087151
theorem B724991 : Blo 722323 724991 := bstep (se 1 (by rfl) ⟨543743, by rfl⟩ : syracuseStep 724991 = 1087487) B1087487
theorem B9932867 : Blo 722323 9932867 := bstep (se 1 (by rfl) ⟨7449650, by rfl⟩ : syracuseStep 9932867 = 14899301) B14899301
theorem B725159 : Blo 722323 725159 := bstep (se 1 (by rfl) ⟨543869, by rfl⟩ : syracuseStep 725159 = 1087739) B1087739
theorem B2199979 : Blo 722323 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B725631 : Blo 722323 725631 := bstep (se 1 (by rfl) ⟨544223, by rfl⟩ : syracuseStep 725631 = 1088447) B1088447
theorem B1086143 : Blo 722323 1086143 := bstep (se 1 (by rfl) ⟨814607, by rfl⟩ : syracuseStep 1086143 = 1629215) B1629215
theorem B6624139 : Blo 722323 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B13374395 : Blo 722323 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B726043 : Blo 722323 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B726063 : Blo 722323 726063 := bstep (se 1 (by rfl) ⟨544547, by rfl⟩ : syracuseStep 726063 = 1089095) B1089095
theorem B726143 : Blo 722323 726143 := bstep (se 1 (by rfl) ⟨544607, by rfl⟩ : syracuseStep 726143 = 1089215) B1089215
theorem B1086695 : Blo 722323 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B37557593 : Blo 722323 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B1086953 : Blo 722323 1086953 := bstep (se 2 (by rfl) ⟨407607, by rfl⟩ : syracuseStep 1086953 = 815215) B815215
theorem B8230409 : Blo 722323 8230409 := bstep (se 2 (by rfl) ⟨3086403, by rfl⟩ : syracuseStep 8230409 = 6172807) B6172807
theorem B1087529 : Blo 722323 1087529 := bstep (se 2 (by rfl) ⟨407823, by rfl⟩ : syracuseStep 1087529 = 815647) B815647
theorem B1087535 : Blo 722323 1087535 := bstep (se 1 (by rfl) ⟨815651, by rfl⟩ : syracuseStep 1087535 = 1631303) B1631303
theorem B1087727 : Blo 722323 1087727 := bstep (se 1 (by rfl) ⟨815795, by rfl⟩ : syracuseStep 1087727 = 1631591) B1631591
theorem B8067599 : Blo 722323 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B7052255 : Blo 722323 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B1547371 : Blo 722323 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B1219711 : Blo 722323 1219711 := bstep (se 1 (by rfl) ⟨914783, by rfl⟩ : syracuseStep 1219711 = 1829567) B1829567
theorem B1088681 : Blo 722323 1088681 := bstep (se 2 (by rfl) ⟨408255, by rfl⟩ : syracuseStep 1088681 = 816511) B816511
theorem B4398305 : Blo 722323 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B1220123 : Blo 722323 1220123 := bstep (se 1 (by rfl) ⟨915092, by rfl⟩ : syracuseStep 1220123 = 1830185) B1830185
theorem B1089383 : Blo 722323 1089383 := bstep (se 1 (by rfl) ⟨817037, by rfl⟩ : syracuseStep 1089383 = 1634075) B1634075
theorem B35693945 : Blo 722323 35693945 := bstep (se 2 (by rfl) ⟨13385229, by rfl⟩ : syracuseStep 35693945 = 26770459) B26770459
theorem B1157723 : Blo 722323 1157723 := bstep (se 1 (by rfl) ⟨868292, by rfl⟩ : syracuseStep 1157723 = 1736585) B1736585
theorem B1223545 : Blo 722323 1223545 := bstep (se 2 (by rfl) ⟨458829, by rfl⟩ : syracuseStep 1223545 = 917659) B917659
theorem B5024929 : Blo 722323 5024929 := bstep (se 2 (by rfl) ⟨1884348, by rfl⟩ : syracuseStep 5024929 = 3768697) B3768697
theorem B4467881 : Blo 722323 4467881 := bstep (se 2 (by rfl) ⟨1675455, by rfl⟩ : syracuseStep 4467881 = 3350911) B3350911
theorem B37695131 : Blo 722323 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B16723907 : Blo 722323 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B7942207 : Blo 722323 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B16756999 : Blo 722323 16756999 := bstep (se 1 (by rfl) ⟨12567749, by rfl⟩ : syracuseStep 16756999 = 25135499) B25135499
theorem B52900523 : Blo 722323 52900523 := bstep (se 1 (by rfl) ⟨39675392, by rfl⟩ : syracuseStep 52900523 = 79350785) B79350785
theorem B1488041 : Blo 722323 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B12400289 : Blo 722323 12400289 := bstep (se 2 (by rfl) ⟨4650108, by rfl⟩ : syracuseStep 12400289 = 9300217) B9300217
theorem B3487931 : Blo 722323 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B2441501 : Blo 722323 2441501 := bstep (se 3 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 2441501 = 915563) B915563
theorem B20038913 : Blo 722323 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B4114111 : Blo 722323 4114111 := bstep (se 1 (by rfl) ⟨3085583, by rfl⟩ : syracuseStep 4114111 = 6171167) B6171167
theorem B2442959 : Blo 722323 2442959 := bstep (se 1 (by rfl) ⟨1832219, by rfl⟩ : syracuseStep 2442959 = 3664439) B3664439
theorem B2443337 : Blo 722323 2443337 := bstep (se 2 (by rfl) ⟨916251, by rfl⟩ : syracuseStep 2443337 = 1832503) B1832503
theorem B5229359 : Blo 722323 5229359 := bstep (se 1 (by rfl) ⟨3922019, by rfl⟩ : syracuseStep 5229359 = 7844039) B7844039
theorem B2444093 : Blo 722323 2444093 := bstep (se 3 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 2444093 = 916535) B916535
theorem B4116845 : Blo 722323 4116845 := bstep (se 3 (by rfl) ⟨771908, by rfl⟩ : syracuseStep 4116845 = 1543817) B1543817
theorem B1626623 : Blo 722323 1626623 := bstep (se 1 (by rfl) ⟨1219967, by rfl⟩ : syracuseStep 1626623 = 2439935) B2439935
theorem B1627001 : Blo 722323 1627001 := bstep (se 2 (by rfl) ⟨610125, by rfl⟩ : syracuseStep 1627001 = 1220251) B1220251
theorem B3921155 : Blo 722323 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B1627703 : Blo 722323 1627703 := bstep (se 1 (by rfl) ⟨1220777, by rfl⟩ : syracuseStep 1627703 = 2441555) B2441555
theorem B1104041 : Blo 722323 1104041 := bstep (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) B828031
theorem B5953823 : Blo 722323 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B3660713 : Blo 722323 3660713 := bstep (se 2 (by rfl) ⟨1372767, by rfl⟩ : syracuseStep 3660713 = 2745535) B2745535
theorem B1629179 : Blo 722323 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B1466281 : Blo 722323 1466281 := bstep (se 2 (by rfl) ⟨549855, by rfl⟩ : syracuseStep 1466281 = 1099711) B1099711
theorem B2057375 : Blo 722323 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B19850615 : Blo 722323 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B1632167 : Blo 722323 1632167 := bstep (se 1 (by rfl) ⟨1224125, by rfl⟩ : syracuseStep 1632167 = 2448251) B2448251
theorem B1829051 : Blo 722323 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B2746811 : Blo 722323 2746811 := bstep (se 1 (by rfl) ⟨2060108, by rfl⟩ : syracuseStep 2746811 = 4120217) B4120217
theorem B3762623 : Blo 722323 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B846703 : Blo 722323 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B814171 : Blo 722323 814171 := bstep (se 1 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 814171 = 1221257) B1221257
theorem B5500061 : Blo 722323 5500061 := bstep (se 3 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 5500061 = 2062523) B2062523
theorem B4648265 : Blo 722323 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B1633913 : Blo 722323 1633913 := bstep (se 2 (by rfl) ⟨612717, by rfl⟩ : syracuseStep 1633913 = 1225435) B1225435
theorem B814747 : Blo 722323 814747 := bstep (se 1 (by rfl) ⟨611060, by rfl⟩ : syracuseStep 814747 = 1222121) B1222121
theorem B1372457 : Blo 722323 1372457 := bstep (se 2 (by rfl) ⟨514671, by rfl⟩ : syracuseStep 1372457 = 1029343) B1029343
theorem B8253737 : Blo 722323 8253737 := bstep (se 2 (by rfl) ⟨3095151, by rfl⟩ : syracuseStep 8253737 = 6190303) B6190303
theorem B5501519 : Blo 722323 5501519 := bstep (se 1 (by rfl) ⟨4126139, by rfl⟩ : syracuseStep 5501519 = 8252279) B8252279
theorem B2749211 : Blo 722323 2749211 := bstep (se 1 (by rfl) ⟨2061908, by rfl⟩ : syracuseStep 2749211 = 4123817) B4123817
theorem B2749423 : Blo 722323 2749423 := bstep (se 1 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 2749423 = 4124135) B4124135
theorem B980191 : Blo 722323 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B3669785 : Blo 722323 3669785 := bstep (se 2 (by rfl) ⟨1376169, by rfl⟩ : syracuseStep 3669785 = 2752339) B2752339
theorem B722663 : Blo 722323 722663 := bstep (se 1 (by rfl) ⟨541997, by rfl⟩ : syracuseStep 722663 = 1083995) B1083995
theorem B723055 : Blo 722323 723055 := bstep (se 1 (by rfl) ⟨542291, by rfl⟩ : syracuseStep 723055 = 1084583) B1084583
theorem B723071 : Blo 722323 723071 := bstep (se 1 (by rfl) ⟨542303, by rfl⟩ : syracuseStep 723071 = 1084607) B1084607
theorem B11733221 : Blo 722323 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B723431 : Blo 722323 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B6621911 : Blo 722323 6621911 := bstep (se 1 (by rfl) ⟨4966433, by rfl⟩ : syracuseStep 6621911 = 9932867) B9932867
theorem B1084415 : Blo 722323 1084415 := bstep (se 1 (by rfl) ⟨813311, by rfl⟩ : syracuseStep 1084415 = 1626623) B1626623
theorem B724095 : Blo 722323 724095 := bstep (se 1 (by rfl) ⟨543071, by rfl⟩ : syracuseStep 724095 = 1086143) B1086143
theorem B1084667 : Blo 722323 1084667 := bstep (se 1 (by rfl) ⟨813500, by rfl⟩ : syracuseStep 1084667 = 1627001) B1627001
theorem B8916263 : Blo 722323 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B724463 : Blo 722323 724463 := bstep (se 1 (by rfl) ⟨543347, by rfl⟩ : syracuseStep 724463 = 1086695) B1086695
theorem B25038395 : Blo 722323 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B724635 : Blo 722323 724635 := bstep (se 1 (by rfl) ⟨543476, by rfl⟩ : syracuseStep 724635 = 1086953) B1086953
theorem B1085135 : Blo 722323 1085135 := bstep (se 1 (by rfl) ⟨813851, by rfl⟩ : syracuseStep 1085135 = 1627703) B1627703
theorem B725019 : Blo 722323 725019 := bstep (se 1 (by rfl) ⟨543764, by rfl⟩ : syracuseStep 725019 = 1087529) B1087529
theorem B725023 : Blo 722323 725023 := bstep (se 1 (by rfl) ⟨543767, by rfl⟩ : syracuseStep 725023 = 1087535) B1087535
theorem B1085561 : Blo 722323 1085561 := bstep (se 2 (by rfl) ⟨407085, by rfl⟩ : syracuseStep 1085561 = 814171) B814171
theorem B725151 : Blo 722323 725151 := bstep (se 1 (by rfl) ⟨543863, by rfl⟩ : syracuseStep 725151 = 1087727) B1087727
theorem B3969215 : Blo 722323 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B5378399 : Blo 722323 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B1086119 : Blo 722323 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B725787 : Blo 722323 725787 := bstep (se 1 (by rfl) ⟨544340, by rfl⟩ : syracuseStep 725787 = 1088681) B1088681
theorem B2757473 : Blo 722323 2757473 := bstep (se 2 (by rfl) ⟨1034052, by rfl⟩ : syracuseStep 2757473 = 2068105) B2068105
theorem B1086329 : Blo 722323 1086329 := bstep (se 2 (by rfl) ⟨407373, by rfl⟩ : syracuseStep 1086329 = 814747) B814747
theorem B726255 : Blo 722323 726255 := bstep (se 1 (by rfl) ⟨544691, by rfl⟩ : syracuseStep 726255 = 1089383) B1089383
theorem B10589609 : Blo 722323 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B23795963 : Blo 722323 23795963 := bstep (se 1 (by rfl) ⟨17846972, by rfl⟩ : syracuseStep 23795963 = 35693945) B35693945
theorem B1088111 : Blo 722323 1088111 := bstep (se 1 (by rfl) ⟨816083, by rfl⟩ : syracuseStep 1088111 = 1632167) B1632167
theorem B1219367 : Blo 722323 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B1089275 : Blo 722323 1089275 := bstep (se 1 (by rfl) ⟨816956, by rfl⟩ : syracuseStep 1089275 = 1633913) B1633913
theorem B11149271 : Blo 722323 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B35267015 : Blo 722323 35267015 := bstep (se 1 (by rfl) ⟨26450261, by rfl⟩ : syracuseStep 35267015 = 52900523) B52900523
theorem B992027 : Blo 722323 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B8266859 : Blo 722323 8266859 := bstep (se 1 (by rfl) ⟨6200144, by rfl⟩ : syracuseStep 8266859 = 12400289) B12400289
theorem B89370661 : Blo 722323 89370661 := bstep (se 4 (by rfl) ⟨8378499, by rfl⟩ : syracuseStep 89370661 = 16756999) B16756999
theorem B16691321 : Blo 722323 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B3486239 : Blo 722323 3486239 := bstep (se 1 (by rfl) ⟨2614679, by rfl⟩ : syracuseStep 3486239 = 5229359) B5229359
theorem B5485481 : Blo 722323 5485481 := bstep (se 2 (by rfl) ⟨2057055, by rfl⟩ : syracuseStep 5485481 = 4114111) B4114111
theorem B5486939 : Blo 722323 5486939 := bstep (se 1 (by rfl) ⟨4115204, by rfl⟩ : syracuseStep 5486939 = 8230409) B8230409
theorem B6699905 : Blo 722323 6699905 := bstep (se 2 (by rfl) ⟨2512464, by rfl⟩ : syracuseStep 6699905 = 5024929) B5024929
theorem B2440475 : Blo 722323 2440475 := bstep (se 1 (by rfl) ⟨1830356, by rfl⟩ : syracuseStep 2440475 = 3660713) B3660713
theorem B4701503 : Blo 722323 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B8832185 : Blo 722323 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B2508415 : Blo 722323 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B771815 : Blo 722323 771815 := bstep (se 1 (by rfl) ⟨578861, by rfl⟩ : syracuseStep 771815 = 1157723) B1157723
theorem B3098843 : Blo 722323 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B4115069 : Blo 722323 4115069 := bstep (se 3 (by rfl) ⟨771575, by rfl⟩ : syracuseStep 4115069 = 1543151) B1543151
theorem B1626281 : Blo 722323 1626281 := bstep (se 2 (by rfl) ⟨609855, by rfl⟩ : syracuseStep 1626281 = 1219711) B1219711
theorem B7820165 : Blo 722323 7820165 := bstep (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) B1466281
theorem B2446523 : Blo 722323 2446523 := bstep (se 1 (by rfl) ⟨1834892, by rfl⟩ : syracuseStep 2446523 = 3669785) B3669785
theorem B1627667 : Blo 722323 1627667 := bstep (se 1 (by rfl) ⟨1220750, by rfl⟩ : syracuseStep 1627667 = 2441501) B2441501
theorem B13359275 : Blo 722323 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B2447549 : Blo 722323 2447549 := bstep (se 3 (by rfl) ⟨458915, by rfl⟩ : syracuseStep 2447549 = 917831) B917831
theorem B1628639 : Blo 722323 1628639 := bstep (se 1 (by rfl) ⟨1221479, by rfl⟩ : syracuseStep 1628639 = 2442959) B2442959
theorem B6183539 : Blo 722323 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B1628891 : Blo 722323 1628891 := bstep (se 1 (by rfl) ⟨1221668, by rfl⟩ : syracuseStep 1628891 = 2443337) B2443337
theorem B1629395 : Blo 722323 1629395 := bstep (se 1 (by rfl) ⟨1222046, by rfl⟩ : syracuseStep 1629395 = 2444093) B2444093
theorem B2744563 : Blo 722323 2744563 := bstep (se 1 (by rfl) ⟨2058422, by rfl⟩ : syracuseStep 2744563 = 4116845) B4116845
theorem B15688241 : Blo 722323 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B2614103 : Blo 722323 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B1631393 : Blo 722323 1631393 := bstep (se 2 (by rfl) ⟨611772, by rfl⟩ : syracuseStep 1631393 = 1223545) B1223545
theorem B4515749 : Blo 722323 4515749 := bstep (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) B846703
theorem B813415 : Blo 722323 813415 := bstep (se 1 (by rfl) ⟨610061, by rfl⟩ : syracuseStep 813415 = 1220123) B1220123
theorem B2944109 : Blo 722323 2944109 := bstep (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) B1104041
theorem B1371583 : Blo 722323 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B13233743 : Blo 722323 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B3665897 : Blo 722323 3665897 := bstep (se 2 (by rfl) ⟨1374711, by rfl⟩ : syracuseStep 3665897 = 2749423) B2749423
theorem B1831207 : Blo 722323 1831207 := bstep (se 1 (by rfl) ⟨1373405, by rfl⟩ : syracuseStep 1831207 = 2746811) B2746811
theorem B1306921 : Blo 722323 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B3666707 : Blo 722323 3666707 := bstep (se 1 (by rfl) ⟨2750030, by rfl⟩ : syracuseStep 3666707 = 5500061) B5500061
theorem B2978587 : Blo 722323 2978587 := bstep (se 1 (by rfl) ⟨2233940, by rfl⟩ : syracuseStep 2978587 = 4467881) B4467881
theorem B25130087 : Blo 722323 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B914971 : Blo 722323 914971 := bstep (se 1 (by rfl) ⟨686228, by rfl⟩ : syracuseStep 914971 = 1372457) B1372457
theorem B5502491 : Blo 722323 5502491 := bstep (se 1 (by rfl) ⟨4126868, by rfl⟩ : syracuseStep 5502491 = 8253737) B8253737
theorem B3667679 : Blo 722323 3667679 := bstep (se 1 (by rfl) ⟨2750759, by rfl⟩ : syracuseStep 3667679 = 5501519) B5501519
theorem B1832807 : Blo 722323 1832807 := bstep (se 1 (by rfl) ⟨1374605, by rfl⟩ : syracuseStep 1832807 = 2749211) B2749211
theorem B11728813 : Blo 722323 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B2325287 : Blo 722323 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B2063161 : Blo 722323 2063161 := bstep (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) B1547371
theorem B2065895 : Blo 722323 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B722943 : Blo 722323 722943 := bstep (se 1 (by rfl) ⟨542207, by rfl⟩ : syracuseStep 722943 = 1084415) B1084415
theorem B723111 : Blo 722323 723111 := bstep (se 1 (by rfl) ⟨542333, by rfl⟩ : syracuseStep 723111 = 1084667) B1084667
theorem B723423 : Blo 722323 723423 := bstep (se 1 (by rfl) ⟨542567, by rfl⟩ : syracuseStep 723423 = 1085135) B1085135
theorem B723707 : Blo 722323 723707 := bstep (se 1 (by rfl) ⟨542780, by rfl⟩ : syracuseStep 723707 = 1085561) B1085561
theorem B1084187 : Blo 722323 1084187 := bstep (se 1 (by rfl) ⟨813140, by rfl⟩ : syracuseStep 1084187 = 1626281) B1626281
theorem B724079 : Blo 722323 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B1084553 : Blo 722323 1084553 := bstep (se 2 (by rfl) ⟨406707, by rfl⟩ : syracuseStep 1084553 = 813415) B813415
theorem B1838315 : Blo 722323 1838315 := bstep (se 1 (by rfl) ⟨1378736, by rfl⟩ : syracuseStep 1838315 = 2757473) B2757473
theorem B724219 : Blo 722323 724219 := bstep (se 1 (by rfl) ⟨543164, by rfl⟩ : syracuseStep 724219 = 1086329) B1086329
theorem B5213443 : Blo 722323 5213443 := bstep (se 1 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 5213443 = 7820165) B7820165
theorem B1085111 : Blo 722323 1085111 := bstep (se 1 (by rfl) ⟨813833, by rfl⟩ : syracuseStep 1085111 = 1627667) B1627667
theorem B15863975 : Blo 722323 15863975 := bstep (se 1 (by rfl) ⟨11897981, by rfl⟩ : syracuseStep 15863975 = 23795963) B23795963
theorem B1085759 : Blo 722323 1085759 := bstep (se 1 (by rfl) ⟨814319, by rfl⟩ : syracuseStep 1085759 = 1628639) B1628639
theorem B725407 : Blo 722323 725407 := bstep (se 1 (by rfl) ⟨544055, by rfl⟩ : syracuseStep 725407 = 1088111) B1088111
theorem B1085927 : Blo 722323 1085927 := bstep (se 1 (by rfl) ⟨814445, by rfl⟩ : syracuseStep 1085927 = 1628891) B1628891
theorem B1086263 : Blo 722323 1086263 := bstep (se 1 (by rfl) ⟨814697, by rfl⟩ : syracuseStep 1086263 = 1629395) B1629395
theorem B726183 : Blo 722323 726183 := bstep (se 1 (by rfl) ⟨544637, by rfl⟩ : syracuseStep 726183 = 1089275) B1089275
theorem B10458827 : Blo 722323 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B1742561 : Blo 722323 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B1742735 : Blo 722323 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B5511239 : Blo 722323 5511239 := bstep (se 1 (by rfl) ⟨4133429, by rfl⟩ : syracuseStep 5511239 = 8266859) B8266859
theorem B1087595 : Blo 722323 1087595 := bstep (se 1 (by rfl) ⟨815696, by rfl⟩ : syracuseStep 1087595 = 1631393) B1631393
theorem B3971449 : Blo 722323 3971449 := bstep (se 2 (by rfl) ⟨1489293, by rfl⟩ : syracuseStep 3971449 = 2978587) B2978587
theorem B1219961 : Blo 722323 1219961 := bstep (se 2 (by rfl) ⟨457485, by rfl⟩ : syracuseStep 1219961 = 914971) B914971
theorem B8822495 : Blo 722323 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B15638417 : Blo 722323 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B13378213 : Blo 722323 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B16753391 : Blo 722323 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B1221871 : Blo 722323 1221871 := bstep (se 1 (by rfl) ⟨916403, by rfl⟩ : syracuseStep 1221871 = 1832807) B1832807
theorem B1550191 : Blo 722323 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B4466603 : Blo 722323 4466603 := bstep (se 1 (by rfl) ⟨3349952, by rfl⟩ : syracuseStep 4466603 = 6699905) B6699905
theorem B5944175 : Blo 722323 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B16692263 : Blo 722323 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B3585599 : Blo 722323 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B7059739 : Blo 722323 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B119160881 : Blo 722323 119160881 := bstep (se 2 (by rfl) ⟨44685330, by rfl⟩ : syracuseStep 119160881 = 89370661) B89370661
theorem B23511343 : Blo 722323 23511343 := bstep (se 1 (by rfl) ⟨17633507, by rfl⟩ : syracuseStep 23511343 = 35267015) B35267015
theorem B2441609 : Blo 722323 2441609 := bstep (se 2 (by rfl) ⟨915603, by rfl⟩ : syracuseStep 2441609 = 1831207) B1831207
theorem B2443931 : Blo 722323 2443931 := bstep (se 1 (by rfl) ⟨1832948, by rfl⟩ : syracuseStep 2443931 = 3665897) B3665897
theorem B11127547 : Blo 722323 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B2444471 : Blo 722323 2444471 := bstep (se 1 (by rfl) ⟨1833353, by rfl⟩ : syracuseStep 2444471 = 3666707) B3666707
theorem B3656987 : Blo 722323 3656987 := bstep (se 1 (by rfl) ⟨2742740, by rfl⟩ : syracuseStep 3656987 = 5485481) B5485481
theorem B12537341 : Blo 722323 12537341 := bstep (se 3 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 12537341 = 4701503) B4701503
theorem B2445119 : Blo 722323 2445119 := bstep (se 1 (by rfl) ⟨1833839, by rfl⟩ : syracuseStep 2445119 = 3667679) B3667679
theorem B3657959 : Blo 722323 3657959 := bstep (se 1 (by rfl) ⟨2743469, by rfl⟩ : syracuseStep 3657959 = 5486939) B5486939
theorem B1626983 : Blo 722323 1626983 := bstep (se 1 (by rfl) ⟨1220237, by rfl⟩ : syracuseStep 1626983 = 2440475) B2440475
theorem B3659417 : Blo 722323 3659417 := bstep (se 2 (by rfl) ⟨1372281, by rfl⟩ : syracuseStep 3659417 = 2744563) B2744563
theorem B5888123 : Blo 722323 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B2743379 : Blo 722323 2743379 := bstep (se 1 (by rfl) ⟨2057534, by rfl⟩ : syracuseStep 2743379 = 4115069) B4115069
theorem B4414607 : Blo 722323 4414607 := bstep (se 1 (by rfl) ⟨3310955, by rfl⟩ : syracuseStep 4414607 = 6621911) B6621911
theorem B2645405 : Blo 722323 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B2646143 : Blo 722323 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B1631015 : Blo 722323 1631015 := bstep (se 1 (by rfl) ⟨1223261, by rfl⟩ : syracuseStep 1631015 = 2446523) B2446523
theorem B8906183 : Blo 722323 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B1631699 : Blo 722323 1631699 := bstep (se 1 (by rfl) ⟨1223774, by rfl⟩ : syracuseStep 1631699 = 2447549) B2447549
theorem B4122359 : Blo 722323 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B812911 : Blo 722323 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B1828777 : Blo 722323 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B2058173 : Blo 722323 2058173 := bstep (se 3 (by rfl) ⟨385907, by rfl⟩ : syracuseStep 2058173 = 771815) B771815
theorem B7432847 : Blo 722323 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B31288589 : Blo 722323 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B3010499 : Blo 722323 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B1962739 : Blo 722323 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B2324159 : Blo 722323 2324159 := bstep (se 1 (by rfl) ⟨1743119, by rfl⟩ : syracuseStep 2324159 = 3486239) B3486239
theorem B3668327 : Blo 722323 3668327 := bstep (se 1 (by rfl) ⟨2751245, by rfl⟩ : syracuseStep 3668327 = 5502491) B5502491
theorem B2750881 : Blo 722323 2750881 := bstep (se 2 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 2750881 = 2063161) B2063161
theorem B1377263 : Blo 722323 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B722791 : Blo 722323 722791 := bstep (se 1 (by rfl) ⟨542093, by rfl⟩ : syracuseStep 722791 = 1084187) B1084187
theorem B723035 : Blo 722323 723035 := bstep (se 1 (by rfl) ⟨542276, by rfl⟩ : syracuseStep 723035 = 1084553) B1084553
theorem B8358227 : Blo 722323 8358227 := bstep (se 1 (by rfl) ⟨6268670, by rfl⟩ : syracuseStep 8358227 = 12537341) B12537341
theorem B723407 : Blo 722323 723407 := bstep (se 1 (by rfl) ⟨542555, by rfl⟩ : syracuseStep 723407 = 1085111) B1085111
theorem B1083881 : Blo 722323 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B2066921 : Blo 722323 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B723839 : Blo 722323 723839 := bstep (se 1 (by rfl) ⟨542879, by rfl⟩ : syracuseStep 723839 = 1085759) B1085759
theorem B723951 : Blo 722323 723951 := bstep (se 1 (by rfl) ⟨542963, by rfl⟩ : syracuseStep 723951 = 1085927) B1085927
theorem B724175 : Blo 722323 724175 := bstep (se 1 (by rfl) ⟨543131, by rfl⟩ : syracuseStep 724175 = 1086263) B1086263
theorem B1084655 : Blo 722323 1084655 := bstep (se 1 (by rfl) ⟨813491, by rfl⟩ : syracuseStep 1084655 = 1626983) B1626983
theorem B3674159 : Blo 722323 3674159 := bstep (se 1 (by rfl) ⟨2755619, by rfl⟩ : syracuseStep 3674159 = 5511239) B5511239
theorem B725063 : Blo 722323 725063 := bstep (se 1 (by rfl) ⟨543797, by rfl⟩ : syracuseStep 725063 = 1087595) B1087595
theorem B6951257 : Blo 722323 6951257 := bstep (se 2 (by rfl) ⟨2606721, by rfl⟩ : syracuseStep 6951257 = 5213443) B5213443
theorem B10425611 : Blo 722323 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B1087343 : Blo 722323 1087343 := bstep (se 1 (by rfl) ⟨815507, by rfl⟩ : syracuseStep 1087343 = 1631015) B1631015
theorem B5937455 : Blo 722323 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B1087799 : Blo 722323 1087799 := bstep (se 1 (by rfl) ⟨815849, by rfl⟩ : syracuseStep 1087799 = 1631699) B1631699
theorem B4955231 : Blo 722323 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B2006999 : Blo 722323 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B9412985 : Blo 722323 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B1549439 : Blo 722323 1549439 := bstep (se 1 (by rfl) ⟨1162079, by rfl⟩ : syracuseStep 1549439 = 2324159) B2324159
theorem B79440587 : Blo 722323 79440587 := bstep (se 1 (by rfl) ⟨59580440, by rfl⟩ : syracuseStep 79440587 = 119160881) B119160881
theorem B17837617 : Blo 722323 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B28225525 : Blo 722323 28225525 := bstep (se 5 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 28225525 = 2646143) B2646143
theorem B21181061 : Blo 722323 21181061 := bstep (se 4 (by rfl) ⟨1985724, by rfl⟩ : syracuseStep 21181061 = 3971449) B3971449
theorem B1225543 : Blo 722323 1225543 := bstep (se 1 (by rfl) ⟨919157, by rfl⟩ : syracuseStep 1225543 = 1838315) B1838315
theorem B2437991 : Blo 722323 2437991 := bstep (se 1 (by rfl) ⟨1828493, by rfl⟩ : syracuseStep 2437991 = 3656987) B3656987
theorem B2438369 : Blo 722323 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B2438639 : Blo 722323 2438639 := bstep (se 1 (by rfl) ⟨1828979, by rfl⟩ : syracuseStep 2438639 = 3657959) B3657959
theorem B2439611 : Blo 722323 2439611 := bstep (se 1 (by rfl) ⟨1829708, by rfl⟩ : syracuseStep 2439611 = 3659417) B3659417
theorem B1161707 : Blo 722323 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B5881663 : Blo 722323 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B20859059 : Blo 722323 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B11128175 : Blo 722323 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B2445551 : Blo 722323 2445551 := bstep (se 1 (by rfl) ⟨1834163, by rfl⟩ : syracuseStep 2445551 = 3668327) B3668327
theorem B1627739 : Blo 722323 1627739 := bstep (se 1 (by rfl) ⟨1220804, by rfl⟩ : syracuseStep 1627739 = 2441609) B2441609
theorem B31348457 : Blo 722323 31348457 := bstep (se 2 (by rfl) ⟨11755671, by rfl⟩ : syracuseStep 31348457 = 23511343) B23511343
theorem B1629161 : Blo 722323 1629161 := bstep (se 2 (by rfl) ⟨610935, by rfl⟩ : syracuseStep 1629161 = 1221871) B1221871
theorem B1629287 : Blo 722323 1629287 := bstep (se 1 (by rfl) ⟨1221965, by rfl⟩ : syracuseStep 1629287 = 2443931) B2443931
theorem B1629647 : Blo 722323 1629647 := bstep (se 1 (by rfl) ⟨1222235, by rfl⟩ : syracuseStep 1629647 = 2444471) B2444471
theorem B1630079 : Blo 722323 1630079 := bstep (se 1 (by rfl) ⟨1222559, by rfl⟩ : syracuseStep 1630079 = 2445119) B2445119
theorem B10575983 : Blo 722323 10575983 := bstep (se 1 (by rfl) ⟨7931987, by rfl⟩ : syracuseStep 10575983 = 15863975) B15863975
theorem B14836729 : Blo 722323 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B6972551 : Blo 722323 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B3925415 : Blo 722323 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B1828919 : Blo 722323 1828919 := bstep (se 1 (by rfl) ⟨1371689, by rfl⟩ : syracuseStep 1828919 = 2743379) B2743379
theorem B2943071 : Blo 722323 2943071 := bstep (se 1 (by rfl) ⟨2207303, by rfl⟩ : syracuseStep 2943071 = 4414607) B4414607
theorem B813307 : Blo 722323 813307 := bstep (se 1 (by rfl) ⟨609980, by rfl⟩ : syracuseStep 813307 = 1219961) B1219961
theorem B1763603 : Blo 722323 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B4647293 : Blo 722323 4647293 := bstep (se 3 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 4647293 = 1742735) B1742735
theorem B11168927 : Blo 722323 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B2616985 : Blo 722323 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B2748239 : Blo 722323 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B2977735 : Blo 722323 2977735 := bstep (se 1 (by rfl) ⟨2233301, by rfl⟩ : syracuseStep 2977735 = 4466603) B4466603
theorem B1372115 : Blo 722323 1372115 := bstep (se 1 (by rfl) ⟨1029086, by rfl⟩ : syracuseStep 1372115 = 2058173) B2058173
theorem B3667841 : Blo 722323 3667841 := bstep (se 2 (by rfl) ⟨1375440, by rfl⟩ : syracuseStep 3667841 = 2750881) B2750881
theorem B3962783 : Blo 722323 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B2390399 : Blo 722323 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B5572151 : Blo 722323 5572151 := bstep (se 1 (by rfl) ⟨4179113, by rfl⟩ : syracuseStep 5572151 = 8358227) B8358227
theorem B722587 : Blo 722323 722587 := bstep (se 1 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 722587 = 1083881) B1083881
theorem B1377947 : Blo 722323 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B723103 : Blo 722323 723103 := bstep (se 1 (by rfl) ⟨542327, by rfl⟩ : syracuseStep 723103 = 1084655) B1084655
theorem B3672701 : Blo 722323 3672701 := bstep (se 3 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 3672701 = 1377263) B1377263
theorem B1084409 : Blo 722323 1084409 := bstep (se 2 (by rfl) ⟨406653, by rfl⟩ : syracuseStep 1084409 = 813307) B813307
theorem B6950407 : Blo 722323 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B1085159 : Blo 722323 1085159 := bstep (se 1 (by rfl) ⟨813869, by rfl⟩ : syracuseStep 1085159 = 1627739) B1627739
theorem B724895 : Blo 722323 724895 := bstep (se 1 (by rfl) ⟨543671, by rfl⟩ : syracuseStep 724895 = 1087343) B1087343
theorem B725199 : Blo 722323 725199 := bstep (se 1 (by rfl) ⟨543899, by rfl⟩ : syracuseStep 725199 = 1087799) B1087799
theorem B1086107 : Blo 722323 1086107 := bstep (se 1 (by rfl) ⟨814580, by rfl⟩ : syracuseStep 1086107 = 1629161) B1629161
theorem B1086191 : Blo 722323 1086191 := bstep (se 1 (by rfl) ⟨814643, by rfl⟩ : syracuseStep 1086191 = 1629287) B1629287
theorem B1086431 : Blo 722323 1086431 := bstep (se 1 (by rfl) ⟨814823, by rfl⟩ : syracuseStep 1086431 = 1629647) B1629647
theorem B12391541 : Blo 722323 12391541 := bstep (se 5 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 12391541 = 1161707) B1161707
theorem B1086719 : Blo 722323 1086719 := bstep (se 1 (by rfl) ⟨815039, by rfl⟩ : syracuseStep 1086719 = 1630079) B1630079
theorem B3970313 : Blo 722323 3970313 := bstep (se 2 (by rfl) ⟨1488867, by rfl⟩ : syracuseStep 3970313 = 2977735) B2977735
theorem B7050655 : Blo 722323 7050655 := bstep (se 1 (by rfl) ⟨5287991, by rfl⟩ : syracuseStep 7050655 = 10575983) B10575983
theorem B1219279 : Blo 722323 1219279 := bstep (se 1 (by rfl) ⟨914459, by rfl⟩ : syracuseStep 1219279 = 1828919) B1828919
theorem B52960391 : Blo 722323 52960391 := bstep (se 1 (by rfl) ⟨39720293, by rfl⟩ : syracuseStep 52960391 = 79440587) B79440587
theorem B7445951 : Blo 722323 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B13213949 : Blo 722323 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B7842217 : Blo 722323 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B13906039 : Blo 722323 13906039 := bstep (se 1 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 13906039 = 20859059) B20859059
theorem B7418783 : Blo 722323 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B4634171 : Blo 722323 4634171 := bstep (se 1 (by rfl) ⟨3475628, by rfl⟩ : syracuseStep 4634171 = 6951257) B6951257
theorem B3489313 : Blo 722323 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B37634033 : Blo 722323 37634033 := bstep (se 2 (by rfl) ⟨14112762, by rfl⟩ : syracuseStep 37634033 = 28225525) B28225525
theorem B6275323 : Blo 722323 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B1032959 : Blo 722323 1032959 := bstep (se 1 (by rfl) ⟨774719, by rfl⟩ : syracuseStep 1032959 = 1549439) B1549439
theorem B3098195 : Blo 722323 3098195 := bstep (se 1 (by rfl) ⟨2323646, by rfl⟩ : syracuseStep 3098195 = 4647293) B4647293
theorem B1625327 : Blo 722323 1625327 := bstep (se 1 (by rfl) ⟨1218995, by rfl⟩ : syracuseStep 1625327 = 2437991) B2437991
theorem B1625579 : Blo 722323 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B1625759 : Blo 722323 1625759 := bstep (se 1 (by rfl) ⟨1219319, by rfl⟩ : syracuseStep 1625759 = 2438639) B2438639
theorem B2445227 : Blo 722323 2445227 := bstep (se 1 (by rfl) ⟨1833920, by rfl⟩ : syracuseStep 2445227 = 3667841) B3667841
theorem B2641855 : Blo 722323 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B1593599 : Blo 722323 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B1626407 : Blo 722323 1626407 := bstep (se 1 (by rfl) ⟨1219805, by rfl⟩ : syracuseStep 1626407 = 2439611) B2439611
theorem B19782305 : Blo 722323 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B56482829 : Blo 722323 56482829 := bstep (se 3 (by rfl) ⟨10590530, by rfl⟩ : syracuseStep 56482829 = 21181061) B21181061
theorem B2449439 : Blo 722323 2449439 := bstep (se 1 (by rfl) ⟨1837079, by rfl⟩ : syracuseStep 2449439 = 3674159) B3674159
theorem B1630367 : Blo 722323 1630367 := bstep (se 1 (by rfl) ⟨1222775, by rfl⟩ : syracuseStep 1630367 = 2445551) B2445551
theorem B20898971 : Blo 722323 20898971 := bstep (se 1 (by rfl) ⟨15674228, by rfl⟩ : syracuseStep 20898971 = 31348457) B31348457
theorem B3958303 : Blo 722323 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B23783489 : Blo 722323 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B1337999 : Blo 722323 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B4648367 : Blo 722323 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B2616943 : Blo 722323 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B1634057 : Blo 722323 1634057 := bstep (se 2 (by rfl) ⟨612771, by rfl⟩ : syracuseStep 1634057 = 1225543) B1225543
theorem B1962047 : Blo 722323 1962047 := bstep (se 1 (by rfl) ⟨1471535, by rfl⟩ : syracuseStep 1962047 = 2943071) B2943071
theorem B1175735 : Blo 722323 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B1832159 : Blo 722323 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B914743 : Blo 722323 914743 := bstep (se 1 (by rfl) ⟨686057, by rfl⟩ : syracuseStep 914743 = 1372115) B1372115
theorem B2065463 : Blo 722323 2065463 := bstep (se 1 (by rfl) ⟨1549097, by rfl⟩ : syracuseStep 2065463 = 3098195) B3098195
theorem B918631 : Blo 722323 918631 := bstep (se 1 (by rfl) ⟨688973, by rfl⟩ : syracuseStep 918631 = 1377947) B1377947
theorem B722939 : Blo 722323 722939 := bstep (se 1 (by rfl) ⟨542204, by rfl⟩ : syracuseStep 722939 = 1084409) B1084409
theorem B2754557 : Blo 722323 2754557 := bstep (se 3 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 2754557 = 1032959) B1032959
theorem B5277737 : Blo 722323 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B1083551 : Blo 722323 1083551 := bstep (se 1 (by rfl) ⟨812663, by rfl⟩ : syracuseStep 1083551 = 1625327) B1625327
theorem B1083719 : Blo 722323 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B1083839 : Blo 722323 1083839 := bstep (se 1 (by rfl) ⟨812879, by rfl⟩ : syracuseStep 1083839 = 1625759) B1625759
theorem B723439 : Blo 722323 723439 := bstep (se 1 (by rfl) ⟨542579, by rfl⟩ : syracuseStep 723439 = 1085159) B1085159
theorem B1084271 : Blo 722323 1084271 := bstep (se 1 (by rfl) ⟨813203, by rfl⟩ : syracuseStep 1084271 = 1626407) B1626407
theorem B724071 : Blo 722323 724071 := bstep (se 1 (by rfl) ⟨543053, by rfl⟩ : syracuseStep 724071 = 1086107) B1086107
theorem B724127 : Blo 722323 724127 := bstep (se 1 (by rfl) ⟨543095, by rfl⟩ : syracuseStep 724127 = 1086191) B1086191
theorem B10456289 : Blo 722323 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B724287 : Blo 722323 724287 := bstep (se 1 (by rfl) ⟨543215, by rfl⟩ : syracuseStep 724287 = 1086431) B1086431
theorem B8261027 : Blo 722323 8261027 := bstep (se 1 (by rfl) ⟨6195770, by rfl⟩ : syracuseStep 8261027 = 12391541) B12391541
theorem B724479 : Blo 722323 724479 := bstep (se 1 (by rfl) ⟨543359, by rfl⟩ : syracuseStep 724479 = 1086719) B1086719
theorem B37655219 : Blo 722323 37655219 := bstep (se 1 (by rfl) ⟨28241414, by rfl⟩ : syracuseStep 37655219 = 56482829) B56482829
theorem B1086911 : Blo 722323 1086911 := bstep (se 1 (by rfl) ⟨815183, by rfl⟩ : syracuseStep 1086911 = 1630367) B1630367
theorem B13932647 : Blo 722323 13932647 := bstep (se 1 (by rfl) ⟨10449485, by rfl⟩ : syracuseStep 13932647 = 20898971) B20898971
theorem B1219657 : Blo 722323 1219657 := bstep (se 2 (by rfl) ⟨457371, by rfl⟩ : syracuseStep 1219657 = 914743) B914743
theorem B1089371 : Blo 722323 1089371 := bstep (se 1 (by rfl) ⟨817028, by rfl⟩ : syracuseStep 1089371 = 1634057) B1634057
theorem B1221439 : Blo 722323 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B3089447 : Blo 722323 3089447 := bstep (se 1 (by rfl) ⟨2317085, by rfl⟩ : syracuseStep 3089447 = 4634171) B4634171
theorem B8367097 : Blo 722323 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B35237197 : Blo 722323 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B3714767 : Blo 722323 3714767 := bstep (se 1 (by rfl) ⟨2786075, by rfl⟩ : syracuseStep 3714767 = 5572151) B5572151
theorem B13188203 : Blo 722323 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B35306927 : Blo 722323 35306927 := bstep (se 1 (by rfl) ⟨26480195, by rfl⟩ : syracuseStep 35306927 = 52960391) B52960391
theorem B3489257 : Blo 722323 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B4963967 : Blo 722323 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B3522473 : Blo 722323 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B3098911 : Blo 722323 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B1625705 : Blo 722323 1625705 := bstep (se 2 (by rfl) ⟨609639, by rfl⟩ : syracuseStep 1625705 = 1219279) B1219279
theorem B25089355 : Blo 722323 25089355 := bstep (se 1 (by rfl) ⟨18817016, by rfl⟩ : syracuseStep 25089355 = 37634033) B37634033
theorem B3135293 : Blo 722323 3135293 := bstep (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) B1175735
theorem B4249597 : Blo 722323 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B2448467 : Blo 722323 2448467 := bstep (se 1 (by rfl) ⟨1836350, by rfl⟩ : syracuseStep 2448467 = 3672701) B3672701
theorem B1630151 : Blo 722323 1630151 := bstep (se 1 (by rfl) ⟨1222613, by rfl⟩ : syracuseStep 1630151 = 2445227) B2445227
theorem B2646875 : Blo 722323 2646875 := bstep (se 1 (by rfl) ⟨1985156, by rfl⟩ : syracuseStep 2646875 = 3970313) B3970313
theorem B9267209 : Blo 722323 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B1632959 : Blo 722323 1632959 := bstep (se 1 (by rfl) ⟨1224719, by rfl⟩ : syracuseStep 1632959 = 2449439) B2449439
theorem B18541385 : Blo 722323 18541385 := bstep (se 2 (by rfl) ⟨6953019, by rfl⟩ : syracuseStep 18541385 = 13906039) B13906039
theorem B15855659 : Blo 722323 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B3567997 : Blo 722323 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B9400873 : Blo 722323 9400873 := bstep (se 2 (by rfl) ⟨3525327, by rfl⟩ : syracuseStep 9400873 = 7050655) B7050655
theorem B1308031 : Blo 722323 1308031 := bstep (se 1 (by rfl) ⟨981023, by rfl⟩ : syracuseStep 1308031 = 1962047) B1962047
theorem B4945855 : Blo 722323 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B4652417 : Blo 722323 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B1376975 : Blo 722323 1376975 := bstep (se 1 (by rfl) ⟨1032731, by rfl⟩ : syracuseStep 1376975 = 2065463) B2065463
theorem B1836371 : Blo 722323 1836371 := bstep (se 1 (by rfl) ⟨1377278, by rfl⟩ : syracuseStep 1836371 = 2754557) B2754557
theorem B722367 : Blo 722323 722367 := bstep (se 1 (by rfl) ⟨541775, by rfl⟩ : syracuseStep 722367 = 1083551) B1083551
theorem B722479 : Blo 722323 722479 := bstep (se 1 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 722479 = 1083719) B1083719
theorem B722559 : Blo 722323 722559 := bstep (se 1 (by rfl) ⟨541919, by rfl⟩ : syracuseStep 722559 = 1083839) B1083839
theorem B722847 : Blo 722323 722847 := bstep (se 1 (by rfl) ⟨542135, by rfl⟩ : syracuseStep 722847 = 1084271) B1084271
theorem B5507351 : Blo 722323 5507351 := bstep (se 1 (by rfl) ⟨4130513, by rfl⟩ : syracuseStep 5507351 = 8261027) B8261027
theorem B1083803 : Blo 722323 1083803 := bstep (se 1 (by rfl) ⟨812852, by rfl⟩ : syracuseStep 1083803 = 1625705) B1625705
theorem B4131881 : Blo 722323 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B25103479 : Blo 722323 25103479 := bstep (se 1 (by rfl) ⟨18827609, by rfl⟩ : syracuseStep 25103479 = 37655219) B37655219
theorem B724607 : Blo 722323 724607 := bstep (se 1 (by rfl) ⟨543455, by rfl⟩ : syracuseStep 724607 = 1086911) B1086911
theorem B726247 : Blo 722323 726247 := bstep (se 1 (by rfl) ⟨544685, by rfl⟩ : syracuseStep 726247 = 1089371) B1089371
theorem B1086767 : Blo 722323 1086767 := bstep (se 1 (by rfl) ⟨815075, by rfl⟩ : syracuseStep 1086767 = 1630151) B1630151
theorem B4757329 : Blo 722323 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B1088639 : Blo 722323 1088639 := bstep (se 1 (by rfl) ⟨816479, by rfl⟩ : syracuseStep 1088639 = 1632959) B1632959
theorem B12360923 : Blo 722323 12360923 := bstep (se 1 (by rfl) ⟨9270692, by rfl⟩ : syracuseStep 12360923 = 18541385) B18541385
theorem B6594473 : Blo 722323 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B8792135 : Blo 722323 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B23537951 : Blo 722323 23537951 := bstep (se 1 (by rfl) ⟨17653463, by rfl⟩ : syracuseStep 23537951 = 35306927) B35306927
theorem B3518491 : Blo 722323 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B1224841 : Blo 722323 1224841 := bstep (se 2 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 1224841 = 918631) B918631
theorem B7058333 : Blo 722323 7058333 := bstep (se 3 (by rfl) ⟨1323437, by rfl⟩ : syracuseStep 7058333 = 2646875) B2646875
theorem B11156129 : Blo 722323 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B9288431 : Blo 722323 9288431 := bstep (se 1 (by rfl) ⟨6966323, by rfl⟩ : syracuseStep 9288431 = 13932647) B13932647
theorem B12534497 : Blo 722323 12534497 := bstep (se 2 (by rfl) ⟨4700436, by rfl⟩ : syracuseStep 12534497 = 9400873) B9400873
theorem B6178139 : Blo 722323 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B2476511 : Blo 722323 2476511 := bstep (se 1 (by rfl) ⟨1857383, by rfl⟩ : syracuseStep 2476511 = 3714767) B3714767
theorem B10570439 : Blo 722323 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B1626209 : Blo 722323 1626209 := bstep (se 2 (by rfl) ⟨609828, by rfl⟩ : syracuseStep 1626209 = 1219657) B1219657
theorem B3101611 : Blo 722323 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B2348315 : Blo 722323 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B1628585 : Blo 722323 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B6970859 : Blo 722323 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B2090195 : Blo 722323 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B46982929 : Blo 722323 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B1632311 : Blo 722323 1632311 := bstep (se 1 (by rfl) ⟨1224233, by rfl⟩ : syracuseStep 1632311 = 2448467) B2448467
theorem B2059631 : Blo 722323 2059631 := bstep (se 1 (by rfl) ⟨1544723, by rfl⟩ : syracuseStep 2059631 = 3089447) B3089447
theorem B33452473 : Blo 722323 33452473 := bstep (se 2 (by rfl) ⟨12544677, by rfl⟩ : syracuseStep 33452473 = 25089355) B25089355
theorem B6976165 : Blo 722323 6976165 := bstep (se 4 (by rfl) ⟨654015, by rfl⟩ : syracuseStep 6976165 = 1308031) B1308031
theorem B5666129 : Blo 722323 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B2326171 : Blo 722323 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B3309311 : Blo 722323 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B917983 : Blo 722323 917983 := bstep (se 1 (by rfl) ⟨688487, by rfl⟩ : syracuseStep 917983 = 1376975) B1376975
theorem B8356331 : Blo 722323 8356331 := bstep (se 1 (by rfl) ⟨6267248, by rfl⟩ : syracuseStep 8356331 = 12534497) B12534497
theorem B3671567 : Blo 722323 3671567 := bstep (se 1 (by rfl) ⟨2753675, by rfl⟩ : syracuseStep 3671567 = 5507351) B5507351
theorem B722535 : Blo 722323 722535 := bstep (se 1 (by rfl) ⟨541901, by rfl⟩ : syracuseStep 722535 = 1083803) B1083803
theorem B7046959 : Blo 722323 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B2754587 : Blo 722323 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B1084139 : Blo 722323 1084139 := bstep (se 1 (by rfl) ⟨813104, by rfl⟩ : syracuseStep 1084139 = 1626209) B1626209
theorem B724511 : Blo 722323 724511 := bstep (se 1 (by rfl) ⟨543383, by rfl⟩ : syracuseStep 724511 = 1086767) B1086767
theorem B1085723 : Blo 722323 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B725759 : Blo 722323 725759 := bstep (se 1 (by rfl) ⟨544319, by rfl⟩ : syracuseStep 725759 = 1088639) B1088639
theorem B4396315 : Blo 722323 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B4691321 : Blo 722323 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B44603297 : Blo 722323 44603297 := bstep (se 2 (by rfl) ⟨16726236, by rfl⟩ : syracuseStep 44603297 = 33452473) B33452473
theorem B4135481 : Blo 722323 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B1088207 : Blo 722323 1088207 := bstep (se 1 (by rfl) ⟨816155, by rfl⟩ : syracuseStep 1088207 = 1632311) B1632311
theorem B3777419 : Blo 722323 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B2206207 : Blo 722323 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B1224247 : Blo 722323 1224247 := bstep (se 1 (by rfl) ⟨918185, by rfl⟩ : syracuseStep 1224247 = 1836371) B1836371
theorem B1651007 : Blo 722323 1651007 := bstep (se 1 (by rfl) ⟨1238255, by rfl⟩ : syracuseStep 1651007 = 2476511) B2476511
theorem B33471305 : Blo 722323 33471305 := bstep (se 2 (by rfl) ⟨12551739, by rfl⟩ : syracuseStep 33471305 = 25103479) B25103479
theorem B8240615 : Blo 722323 8240615 := bstep (se 1 (by rfl) ⟨6180461, by rfl⟩ : syracuseStep 8240615 = 12360923) B12360923
theorem B1393463 : Blo 722323 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B6343105 : Blo 722323 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B4705555 : Blo 722323 4705555 := bstep (se 1 (by rfl) ⟨3529166, by rfl⟩ : syracuseStep 4705555 = 7058333) B7058333
theorem B3101561 : Blo 722323 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B4118759 : Blo 722323 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B62643905 : Blo 722323 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B1565543 : Blo 722323 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B4647239 : Blo 722323 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B1633121 : Blo 722323 1633121 := bstep (se 2 (by rfl) ⟨612420, by rfl⟩ : syracuseStep 1633121 = 1224841) B1224841
theorem B9301553 : Blo 722323 9301553 := bstep (se 2 (by rfl) ⟨3488082, by rfl⟩ : syracuseStep 9301553 = 6976165) B6976165
theorem B5861423 : Blo 722323 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B15691967 : Blo 722323 15691967 := bstep (se 1 (by rfl) ⟨11768975, by rfl⟩ : syracuseStep 15691967 = 23537951) B23537951
theorem B1373087 : Blo 722323 1373087 := bstep (se 1 (by rfl) ⟨1029815, by rfl⟩ : syracuseStep 1373087 = 2059631) B2059631
theorem B7437419 : Blo 722323 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B6192287 : Blo 722323 6192287 := bstep (se 1 (by rfl) ⟨4644215, by rfl⟩ : syracuseStep 6192287 = 9288431) B9288431
theorem B22283549 : Blo 722323 22283549 := bstep (se 3 (by rfl) ⟨4178165, by rfl⟩ : syracuseStep 22283549 = 8356331) B8356331
theorem B1836391 : Blo 722323 1836391 := bstep (se 1 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 1836391 = 2754587) B2754587
theorem B722759 : Blo 722323 722759 := bstep (se 1 (by rfl) ⟨542069, by rfl⟩ : syracuseStep 722759 = 1084139) B1084139
theorem B11766437 : Blo 722323 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B723815 : Blo 722323 723815 := bstep (se 1 (by rfl) ⟨542861, by rfl⟩ : syracuseStep 723815 = 1085723) B1085723
theorem B2067707 : Blo 722323 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B8457473 : Blo 722323 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B2756987 : Blo 722323 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B725471 : Blo 722323 725471 := bstep (se 1 (by rfl) ⟨544103, by rfl⟩ : syracuseStep 725471 = 1088207) B1088207
theorem B1088747 : Blo 722323 1088747 := bstep (se 1 (by rfl) ⟨816560, by rfl⟩ : syracuseStep 1088747 = 1633121) B1633121
theorem B6201035 : Blo 722323 6201035 := bstep (se 1 (by rfl) ⟨4650776, by rfl⟩ : syracuseStep 6201035 = 9301553) B9301553
theorem B3907615 : Blo 722323 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B10461311 : Blo 722323 10461311 := bstep (se 1 (by rfl) ⟨7845983, by rfl⟩ : syracuseStep 10461311 = 15691967) B15691967
theorem B4958279 : Blo 722323 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B928975 : Blo 722323 928975 := bstep (se 1 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 928975 = 1393463) B1393463
theorem B1223977 : Blo 722323 1223977 := bstep (se 2 (by rfl) ⟨458991, by rfl⟩ : syracuseStep 1223977 = 917983) B917983
theorem B10073117 : Blo 722323 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B3127547 : Blo 722323 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B29735531 : Blo 722323 29735531 := bstep (se 1 (by rfl) ⟨22301648, by rfl⟩ : syracuseStep 29735531 = 44603297) B44603297
theorem B6274073 : Blo 722323 6274073 := bstep (se 2 (by rfl) ⟨2352777, by rfl⟩ : syracuseStep 6274073 = 4705555) B4705555
theorem B41762603 : Blo 722323 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B3098159 : Blo 722323 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B1100671 : Blo 722323 1100671 := bstep (se 1 (by rfl) ⟨825503, by rfl⟩ : syracuseStep 1100671 = 1651007) B1651007
theorem B5493743 : Blo 722323 5493743 := bstep (se 1 (by rfl) ⟨4120307, by rfl⟩ : syracuseStep 5493743 = 8240615) B8240615
theorem B2447711 : Blo 722323 2447711 := bstep (se 1 (by rfl) ⟨1835783, by rfl⟩ : syracuseStep 2447711 = 3671567) B3671567
theorem B9395945 : Blo 722323 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B2745839 : Blo 722323 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B1632329 : Blo 722323 1632329 := bstep (se 2 (by rfl) ⟨612123, by rfl⟩ : syracuseStep 1632329 = 1224247) B1224247
theorem B1043695 : Blo 722323 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B5861753 : Blo 722323 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B915391 : Blo 722323 915391 := bstep (se 1 (by rfl) ⟨686543, by rfl⟩ : syracuseStep 915391 = 1373087) B1373087
theorem B22314203 : Blo 722323 22314203 := bstep (se 1 (by rfl) ⟨16735652, by rfl⟩ : syracuseStep 22314203 = 33471305) B33471305
theorem B4128191 : Blo 722323 4128191 := bstep (se 1 (by rfl) ⟨3096143, by rfl⟩ : syracuseStep 4128191 = 6192287) B6192287
theorem B5210153 : Blo 722323 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B2065439 : Blo 722323 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B1378471 : Blo 722323 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B1837991 : Blo 722323 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B5870245 : Blo 722323 5870245 := bstep (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) B1100671
theorem B725831 : Blo 722323 725831 := bstep (se 1 (by rfl) ⟨544373, by rfl⟩ : syracuseStep 725831 = 1088747) B1088747
theorem B4134023 : Blo 722323 4134023 := bstep (se 1 (by rfl) ⟨3100517, by rfl⟩ : syracuseStep 4134023 = 6201035) B6201035
theorem B6263963 : Blo 722323 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B1088219 : Blo 722323 1088219 := bstep (se 1 (by rfl) ⟨816164, by rfl⟩ : syracuseStep 1088219 = 1632329) B1632329
theorem B1220521 : Blo 722323 1220521 := bstep (se 2 (by rfl) ⟨457695, by rfl⟩ : syracuseStep 1220521 = 915391) B915391
theorem B3907835 : Blo 722323 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B22553261 : Blo 722323 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B14855699 : Blo 722323 14855699 := bstep (se 1 (by rfl) ⟨11141774, by rfl⟩ : syracuseStep 14855699 = 22283549) B22283549
theorem B7844291 : Blo 722323 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B1391593 : Blo 722323 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B2085031 : Blo 722323 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B4182715 : Blo 722323 4182715 := bstep (se 1 (by rfl) ⟨3137036, by rfl⟩ : syracuseStep 4182715 = 6274073) B6274073
theorem B27841735 : Blo 722323 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B2448521 : Blo 722323 2448521 := bstep (se 2 (by rfl) ⟨918195, by rfl⟩ : syracuseStep 2448521 = 1836391) B1836391
theorem B26861645 : Blo 722323 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B3662495 : Blo 722323 3662495 := bstep (se 1 (by rfl) ⟨2746871, by rfl⟩ : syracuseStep 3662495 = 5493743) B5493743
theorem B1631807 : Blo 722323 1631807 := bstep (se 1 (by rfl) ⟨1223855, by rfl⟩ : syracuseStep 1631807 = 2447711) B2447711
theorem B1238633 : Blo 722323 1238633 := bstep (se 2 (by rfl) ⟨464487, by rfl⟩ : syracuseStep 1238633 = 928975) B928975
theorem B1631969 : Blo 722323 1631969 := bstep (se 2 (by rfl) ⟨611988, by rfl⟩ : syracuseStep 1631969 = 1223977) B1223977
theorem B6974207 : Blo 722323 6974207 := bstep (se 1 (by rfl) ⟨5230655, by rfl⟩ : syracuseStep 6974207 = 10461311) B10461311
theorem B1830559 : Blo 722323 1830559 := bstep (se 1 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 1830559 = 2745839) B2745839
theorem B3305519 : Blo 722323 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B19823687 : Blo 722323 19823687 := bstep (se 1 (by rfl) ⟨14867765, by rfl⟩ : syracuseStep 19823687 = 29735531) B29735531
theorem B14876135 : Blo 722323 14876135 := bstep (se 1 (by rfl) ⟨11157101, by rfl⟩ : syracuseStep 14876135 = 22314203) B22314203
theorem B2752127 : Blo 722323 2752127 := bstep (se 1 (by rfl) ⟨2064095, by rfl⟩ : syracuseStep 2752127 = 4128191) B4128191
theorem B3473435 : Blo 722323 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B71631053 : Blo 722323 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B5507837 : Blo 722323 5507837 := bstep (se 3 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 5507837 = 2065439) B2065439
theorem B1837961 : Blo 722323 1837961 := bstep (se 2 (by rfl) ⟨689235, by rfl⟩ : syracuseStep 1837961 = 1378471) B1378471
theorem B2756015 : Blo 722323 2756015 := bstep (se 1 (by rfl) ⟨2067011, by rfl⟩ : syracuseStep 2756015 = 4134023) B4134023
theorem B725479 : Blo 722323 725479 := bstep (se 1 (by rfl) ⟨544109, by rfl⟩ : syracuseStep 725479 = 1088219) B1088219
theorem B5576953 : Blo 722323 5576953 := bstep (se 2 (by rfl) ⟨2091357, by rfl⟩ : syracuseStep 5576953 = 4182715) B4182715
theorem B1087871 : Blo 722323 1087871 := bstep (se 1 (by rfl) ⟨815903, by rfl⟩ : syracuseStep 1087871 = 1631807) B1631807
theorem B825755 : Blo 722323 825755 := bstep (se 1 (by rfl) ⟨619316, by rfl⟩ : syracuseStep 825755 = 1238633) B1238633
theorem B1087979 : Blo 722323 1087979 := bstep (se 1 (by rfl) ⟨815984, by rfl⟩ : syracuseStep 1087979 = 1631969) B1631969
theorem B9903799 : Blo 722323 9903799 := bstep (se 1 (by rfl) ⟨7427849, by rfl⟩ : syracuseStep 9903799 = 14855699) B14855699
theorem B2203679 : Blo 722323 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B13215791 : Blo 722323 13215791 := bstep (se 1 (by rfl) ⟨9911843, by rfl⟩ : syracuseStep 13215791 = 19823687) B19823687
theorem B11120165 : Blo 722323 11120165 := bstep (se 4 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 11120165 = 2085031) B2085031
theorem B1225327 : Blo 722323 1225327 := bstep (se 1 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 1225327 = 1837991) B1837991
theorem B4175975 : Blo 722323 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B2440745 : Blo 722323 2440745 := bstep (se 2 (by rfl) ⟨915279, by rfl⟩ : syracuseStep 2440745 = 1830559) B1830559
theorem B2605223 : Blo 722323 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B2441663 : Blo 722323 2441663 := bstep (se 1 (by rfl) ⟨1831247, by rfl⟩ : syracuseStep 2441663 = 3662495) B3662495
theorem B5229527 : Blo 722323 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B1855457 : Blo 722323 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B9917423 : Blo 722323 9917423 := bstep (se 1 (by rfl) ⟨7438067, by rfl⟩ : syracuseStep 9917423 = 14876135) B14876135
theorem B1627361 : Blo 722323 1627361 := bstep (se 2 (by rfl) ⟨610260, by rfl⟩ : syracuseStep 1627361 = 1220521) B1220521
theorem B1632347 : Blo 722323 1632347 := bstep (se 1 (by rfl) ⟨1224260, by rfl⟩ : syracuseStep 1632347 = 2448521) B2448521
theorem B15035507 : Blo 722323 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B7826993 : Blo 722323 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B37122313 : Blo 722323 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B4649471 : Blo 722323 4649471 := bstep (se 1 (by rfl) ⟨3487103, by rfl⟩ : syracuseStep 4649471 = 6974207) B6974207
theorem B1834751 : Blo 722323 1834751 := bstep (se 1 (by rfl) ⟨1376063, by rfl⟩ : syracuseStep 1834751 = 2752127) B2752127
theorem B1736815 : Blo 722323 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B3671891 : Blo 722323 3671891 := bstep (se 1 (by rfl) ⟨2753918, by rfl⟩ : syracuseStep 3671891 = 5507837) B5507837
theorem B1837343 : Blo 722323 1837343 := bstep (se 1 (by rfl) ⟨1378007, by rfl⟩ : syracuseStep 1837343 = 2756015) B2756015
theorem B1084907 : Blo 722323 1084907 := bstep (se 1 (by rfl) ⟨813680, by rfl⟩ : syracuseStep 1084907 = 1627361) B1627361
theorem B725247 : Blo 722323 725247 := bstep (se 1 (by rfl) ⟨543935, by rfl⟩ : syracuseStep 725247 = 1087871) B1087871
theorem B725319 : Blo 722323 725319 := bstep (se 1 (by rfl) ⟨543989, by rfl⟩ : syracuseStep 725319 = 1087979) B1087979
theorem B2202013 : Blo 722323 2202013 := bstep (se 3 (by rfl) ⟨412877, by rfl⟩ : syracuseStep 2202013 = 825755) B825755
theorem B1088231 : Blo 722323 1088231 := bstep (se 1 (by rfl) ⟨816173, by rfl⟩ : syracuseStep 1088231 = 1632347) B1632347
theorem B7413443 : Blo 722323 7413443 := bstep (se 1 (by rfl) ⟨5560082, by rfl⟩ : syracuseStep 7413443 = 11120165) B11120165
theorem B5217995 : Blo 722323 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B1223167 : Blo 722323 1223167 := bstep (se 1 (by rfl) ⟨917375, by rfl⟩ : syracuseStep 1223167 = 1834751) B1834751
theorem B47754035 : Blo 722323 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B1225307 : Blo 722323 1225307 := bstep (se 1 (by rfl) ⟨918980, by rfl⟩ : syracuseStep 1225307 = 1837961) B1837961
theorem B49496417 : Blo 722323 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B13945405 : Blo 722323 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B3099647 : Blo 722323 3099647 := bstep (se 1 (by rfl) ⟨2324735, by rfl⟩ : syracuseStep 3099647 = 4649471) B4649471
theorem B1627163 : Blo 722323 1627163 := bstep (se 1 (by rfl) ⟨1220372, by rfl⟩ : syracuseStep 1627163 = 2440745) B2440745
theorem B2315623 : Blo 722323 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B1627775 : Blo 722323 1627775 := bstep (se 1 (by rfl) ⟨1220831, by rfl⟩ : syracuseStep 1627775 = 2441663) B2441663
theorem B1236971 : Blo 722323 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B6611615 : Blo 722323 6611615 := bstep (se 1 (by rfl) ⟨4958711, by rfl⟩ : syracuseStep 6611615 = 9917423) B9917423
theorem B1469119 : Blo 722323 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B1633769 : Blo 722323 1633769 := bstep (se 2 (by rfl) ⟨612663, by rfl⟩ : syracuseStep 1633769 = 1225327) B1225327
theorem B8810527 : Blo 722323 8810527 := bstep (se 1 (by rfl) ⟨6607895, by rfl⟩ : syracuseStep 8810527 = 13215791) B13215791
theorem B10023671 : Blo 722323 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B7435937 : Blo 722323 7435937 := bstep (se 2 (by rfl) ⟨2788476, by rfl⟩ : syracuseStep 7435937 = 5576953) B5576953
theorem B2783983 : Blo 722323 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B13205065 : Blo 722323 13205065 := bstep (se 2 (by rfl) ⟨4951899, by rfl⟩ : syracuseStep 13205065 = 9903799) B9903799
theorem B32997611 : Blo 722323 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B2066431 : Blo 722323 2066431 := bstep (se 1 (by rfl) ⟨1549823, by rfl⟩ : syracuseStep 2066431 = 3099647) B3099647
theorem B723271 : Blo 722323 723271 := bstep (se 1 (by rfl) ⟨542453, by rfl⟩ : syracuseStep 723271 = 1084907) B1084907
theorem B1084775 : Blo 722323 1084775 := bstep (se 1 (by rfl) ⟨813581, by rfl⟩ : syracuseStep 1084775 = 1627163) B1627163
theorem B1085183 : Blo 722323 1085183 := bstep (se 1 (by rfl) ⟨813887, by rfl⟩ : syracuseStep 1085183 = 1627775) B1627775
theorem B725487 : Blo 722323 725487 := bstep (se 1 (by rfl) ⟨544115, by rfl⟩ : syracuseStep 725487 = 1088231) B1088231
theorem B3478663 : Blo 722323 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B3087497 : Blo 722323 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B1089179 : Blo 722323 1089179 := bstep (se 1 (by rfl) ⟨816884, by rfl⟩ : syracuseStep 1089179 = 1633769) B1633769
theorem B3711977 : Blo 722323 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B4957291 : Blo 722323 4957291 := bstep (se 1 (by rfl) ⟨3717968, by rfl⟩ : syracuseStep 4957291 = 7435937) B7435937
theorem B17606753 : Blo 722323 17606753 := bstep (se 2 (by rfl) ⟨6602532, by rfl⟩ : syracuseStep 17606753 = 13205065) B13205065
theorem B1224895 : Blo 722323 1224895 := bstep (se 1 (by rfl) ⟨918671, by rfl⟩ : syracuseStep 1224895 = 1837343) B1837343
theorem B18593873 : Blo 722323 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B11747369 : Blo 722323 11747369 := bstep (se 2 (by rfl) ⟨4405263, by rfl⟩ : syracuseStep 11747369 = 8810527) B8810527
theorem B4407743 : Blo 722323 4407743 := bstep (se 1 (by rfl) ⟨3305807, by rfl⟩ : syracuseStep 4407743 = 6611615) B6611615
theorem B31836023 : Blo 722323 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B2936017 : Blo 722323 2936017 := bstep (se 2 (by rfl) ⟨1101006, by rfl⟩ : syracuseStep 2936017 = 2202013) B2202013
theorem B3298589 : Blo 722323 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B2315753 : Blo 722323 2315753 := bstep (se 2 (by rfl) ⟨868407, by rfl⟩ : syracuseStep 2315753 = 1736815) B1736815
theorem B2447927 : Blo 722323 2447927 := bstep (se 1 (by rfl) ⟨1835945, by rfl⟩ : syracuseStep 2447927 = 3671891) B3671891
theorem B1630889 : Blo 722323 1630889 := bstep (se 2 (by rfl) ⟨611583, by rfl⟩ : syracuseStep 1630889 = 1223167) B1223167
theorem B1958825 : Blo 722323 1958825 := bstep (se 2 (by rfl) ⟨734559, by rfl⟩ : syracuseStep 1958825 = 1469119) B1469119
theorem B4942295 : Blo 722323 4942295 := bstep (se 1 (by rfl) ⟨3706721, by rfl⟩ : syracuseStep 4942295 = 7413443) B7413443
theorem B816871 : Blo 722323 816871 := bstep (se 1 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 816871 = 1225307) B1225307
theorem B6682447 : Blo 722323 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B7831579 : Blo 722323 7831579 := bstep (se 1 (by rfl) ⟨5873684, by rfl⟩ : syracuseStep 7831579 = 11747369) B11747369
theorem B723183 : Blo 722323 723183 := bstep (se 1 (by rfl) ⟨542387, by rfl⟩ : syracuseStep 723183 = 1084775) B1084775
theorem B723455 : Blo 722323 723455 := bstep (se 1 (by rfl) ⟨542591, by rfl⟩ : syracuseStep 723455 = 1085183) B1085183
theorem B2755241 : Blo 722323 2755241 := bstep (se 2 (by rfl) ⟨1033215, by rfl⟩ : syracuseStep 2755241 = 2066431) B2066431
theorem B2199059 : Blo 722323 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B1543835 : Blo 722323 1543835 := bstep (se 1 (by rfl) ⟨1157876, by rfl⟩ : syracuseStep 1543835 = 2315753) B2315753
theorem B726119 : Blo 722323 726119 := bstep (se 1 (by rfl) ⟨544589, by rfl⟩ : syracuseStep 726119 = 1089179) B1089179
theorem B1087259 : Blo 722323 1087259 := bstep (se 1 (by rfl) ⟨815444, by rfl⟩ : syracuseStep 1087259 = 1630889) B1630889
theorem B11737835 : Blo 722323 11737835 := bstep (se 1 (by rfl) ⟨8803376, by rfl⟩ : syracuseStep 11737835 = 17606753) B17606753
theorem B1089161 : Blo 722323 1089161 := bstep (se 2 (by rfl) ⟨408435, by rfl⟩ : syracuseStep 1089161 = 816871) B816871
theorem B8233325 : Blo 722323 8233325 := bstep (se 3 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 8233325 = 3087497) B3087497
theorem B12395915 : Blo 722323 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B21998407 : Blo 722323 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B3914689 : Blo 722323 3914689 := bstep (se 2 (by rfl) ⟨1468008, by rfl⟩ : syracuseStep 3914689 = 2936017) B2936017
theorem B2474651 : Blo 722323 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B4638217 : Blo 722323 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B3294863 : Blo 722323 3294863 := bstep (se 1 (by rfl) ⟨2471147, by rfl⟩ : syracuseStep 3294863 = 4942295) B4942295
theorem B11753981 : Blo 722323 11753981 := bstep (se 3 (by rfl) ⟨2203871, by rfl⟩ : syracuseStep 11753981 = 4407743) B4407743
theorem B21224015 : Blo 722323 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B1631951 : Blo 722323 1631951 := bstep (se 1 (by rfl) ⟨1223963, by rfl⟩ : syracuseStep 1631951 = 2447927) B2447927
theorem B1633193 : Blo 722323 1633193 := bstep (se 2 (by rfl) ⟨612447, by rfl⟩ : syracuseStep 1633193 = 1224895) B1224895
theorem B26438885 : Blo 722323 26438885 := bstep (se 4 (by rfl) ⟨2478645, by rfl⟩ : syracuseStep 26438885 = 4957291) B4957291
theorem B1305883 : Blo 722323 1305883 := bstep (se 1 (by rfl) ⟨979412, by rfl⟩ : syracuseStep 1305883 = 1958825) B1958825
theorem B8909929 : Blo 722323 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B2196575 : Blo 722323 2196575 := bstep (se 1 (by rfl) ⟨1647431, by rfl⟩ : syracuseStep 2196575 = 3294863) B3294863
theorem B1836827 : Blo 722323 1836827 := bstep (se 1 (by rfl) ⟨1377620, by rfl⟩ : syracuseStep 1836827 = 2755241) B2755241
theorem B29331209 : Blo 722323 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B724839 : Blo 722323 724839 := bstep (se 1 (by rfl) ⟨543629, by rfl⟩ : syracuseStep 724839 = 1087259) B1087259
theorem B7835987 : Blo 722323 7835987 := bstep (se 1 (by rfl) ⟨5876990, by rfl⟩ : syracuseStep 7835987 = 11753981) B11753981
theorem B1741177 : Blo 722323 1741177 := bstep (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) B1305883
theorem B726107 : Blo 722323 726107 := bstep (se 1 (by rfl) ⟨544580, by rfl⟩ : syracuseStep 726107 = 1089161) B1089161
theorem B8263943 : Blo 722323 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B1087967 : Blo 722323 1087967 := bstep (se 1 (by rfl) ⟨815975, by rfl⟩ : syracuseStep 1087967 = 1631951) B1631951
theorem B1088795 : Blo 722323 1088795 := bstep (se 1 (by rfl) ⟨816596, by rfl⟩ : syracuseStep 1088795 = 1633193) B1633193
theorem B5219585 : Blo 722323 5219585 := bstep (se 2 (by rfl) ⟨1957344, by rfl⟩ : syracuseStep 5219585 = 3914689) B3914689
theorem B6599069 : Blo 722323 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B1029223 : Blo 722323 1029223 := bstep (se 1 (by rfl) ⟨771917, by rfl⟩ : syracuseStep 1029223 = 1543835) B1543835
theorem B5488883 : Blo 722323 5488883 := bstep (se 1 (by rfl) ⟨4116662, by rfl⟩ : syracuseStep 5488883 = 8233325) B8233325
theorem B11879905 : Blo 722323 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B10442105 : Blo 722323 10442105 := bstep (se 2 (by rfl) ⟨3915789, by rfl⟩ : syracuseStep 10442105 = 7831579) B7831579
theorem B6184289 : Blo 722323 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B1466039 : Blo 722323 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B14149343 : Blo 722323 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B7825223 : Blo 722323 7825223 := bstep (se 1 (by rfl) ⟨5868917, by rfl⟩ : syracuseStep 7825223 = 11737835) B11737835
theorem B17625923 : Blo 722323 17625923 := bstep (se 1 (by rfl) ⟨13219442, by rfl⟩ : syracuseStep 17625923 = 26438885) B26438885
theorem B5509295 : Blo 722323 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B725311 : Blo 722323 725311 := bstep (se 1 (by rfl) ⟨543983, by rfl⟩ : syracuseStep 725311 = 1087967) B1087967
theorem B725863 : Blo 722323 725863 := bstep (se 1 (by rfl) ⟨544397, by rfl⟩ : syracuseStep 725863 = 1088795) B1088795
theorem B3479723 : Blo 722323 3479723 := bstep (se 1 (by rfl) ⟨2609792, by rfl⟩ : syracuseStep 3479723 = 5219585) B5219585
theorem B5216815 : Blo 722323 5216815 := bstep (se 1 (by rfl) ⟨3912611, by rfl⟩ : syracuseStep 5216815 = 7825223) B7825223
theorem B4399379 : Blo 722323 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B1224551 : Blo 722323 1224551 := bstep (se 1 (by rfl) ⟨918413, by rfl⟩ : syracuseStep 1224551 = 1836827) B1836827
theorem B15839873 : Blo 722323 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B6961403 : Blo 722323 6961403 := bstep (se 1 (by rfl) ⟨5221052, by rfl⟩ : syracuseStep 6961403 = 10442105) B10442105
theorem B11750615 : Blo 722323 11750615 := bstep (se 1 (by rfl) ⟨8812961, by rfl⟩ : syracuseStep 11750615 = 17625923) B17625923
theorem B3659255 : Blo 722323 3659255 := bstep (se 1 (by rfl) ⟨2744441, by rfl⟩ : syracuseStep 3659255 = 5488883) B5488883
theorem B1464383 : Blo 722323 1464383 := bstep (se 1 (by rfl) ⟨1098287, by rfl⟩ : syracuseStep 1464383 = 2196575) B2196575
theorem B20895965 : Blo 722323 20895965 := bstep (se 3 (by rfl) ⟨3917993, by rfl⟩ : syracuseStep 20895965 = 7835987) B7835987
theorem B19554139 : Blo 722323 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B4122859 : Blo 722323 4122859 := bstep (se 1 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 4122859 = 6184289) B6184289
theorem B977359 : Blo 722323 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B2321569 : Blo 722323 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B9432895 : Blo 722323 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B1372297 : Blo 722323 1372297 := bstep (se 2 (by rfl) ⟨514611, by rfl⟩ : syracuseStep 1372297 = 1029223) B1029223
theorem B7833743 : Blo 722323 7833743 := bstep (se 1 (by rfl) ⟨5875307, by rfl⟩ : syracuseStep 7833743 = 11750615) B11750615
theorem B3672863 : Blo 722323 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B13930643 : Blo 722323 13930643 := bstep (se 1 (by rfl) ⟨10447982, by rfl⟩ : syracuseStep 13930643 = 20895965) B20895965
theorem B10559915 : Blo 722323 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B6955753 : Blo 722323 6955753 := bstep (se 2 (by rfl) ⟨2608407, by rfl⟩ : syracuseStep 6955753 = 5216815) B5216815
theorem B2439503 : Blo 722323 2439503 := bstep (se 1 (by rfl) ⟨1829627, by rfl⟩ : syracuseStep 2439503 = 3659255) B3659255
theorem B3095425 : Blo 722323 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B2932919 : Blo 722323 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B4640935 : Blo 722323 4640935 := bstep (se 1 (by rfl) ⟨3480701, by rfl⟩ : syracuseStep 4640935 = 6961403) B6961403
theorem B104288741 : Blo 722323 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B5497145 : Blo 722323 5497145 := bstep (se 2 (by rfl) ⟨2061429, by rfl⟩ : syracuseStep 5497145 = 4122859) B4122859
theorem B1303145 : Blo 722323 1303145 := bstep (se 2 (by rfl) ⟨488679, by rfl⟩ : syracuseStep 1303145 = 977359) B977359
theorem B976255 : Blo 722323 976255 := bstep (se 1 (by rfl) ⟨732191, by rfl⟩ : syracuseStep 976255 = 1464383) B1464383
theorem B2319815 : Blo 722323 2319815 := bstep (se 1 (by rfl) ⟨1739861, by rfl⟩ : syracuseStep 2319815 = 3479723) B3479723
theorem B12577193 : Blo 722323 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B1829729 : Blo 722323 1829729 := bstep (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) B1372297
theorem B816367 : Blo 722323 816367 := bstep (se 1 (by rfl) ⟨612275, by rfl⟩ : syracuseStep 816367 = 1224551) B1224551
theorem B9274337 : Blo 722323 9274337 := bstep (se 2 (by rfl) ⟨3477876, by rfl⟩ : syracuseStep 9274337 = 6955753) B6955753
theorem B1546543 : Blo 722323 1546543 := bstep (se 1 (by rfl) ⟨1159907, by rfl⟩ : syracuseStep 1546543 = 2319815) B2319815
theorem B1088489 : Blo 722323 1088489 := bstep (se 2 (by rfl) ⟨408183, by rfl⟩ : syracuseStep 1088489 = 816367) B816367
theorem B1219819 : Blo 722323 1219819 := bstep (se 1 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 1219819 = 1829729) B1829729
theorem B5222495 : Blo 722323 5222495 := bstep (se 1 (by rfl) ⟨3916871, by rfl⟩ : syracuseStep 5222495 = 7833743) B7833743
theorem B9287095 : Blo 722323 9287095 := bstep (se 1 (by rfl) ⟨6965321, by rfl⟩ : syracuseStep 9287095 = 13930643) B13930643
theorem B868763 : Blo 722323 868763 := bstep (se 1 (by rfl) ⟨651572, by rfl⟩ : syracuseStep 868763 = 1303145) B1303145
theorem B1626335 : Blo 722323 1626335 := bstep (se 1 (by rfl) ⟨1219751, by rfl⟩ : syracuseStep 1626335 = 2439503) B2439503
theorem B1955279 : Blo 722323 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B2448575 : Blo 722323 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B69525827 : Blo 722323 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B3664763 : Blo 722323 3664763 := bstep (se 1 (by rfl) ⟨2748572, by rfl⟩ : syracuseStep 3664763 = 5497145) B5497145
theorem B6187913 : Blo 722323 6187913 := bstep (se 2 (by rfl) ⟨2320467, by rfl⟩ : syracuseStep 6187913 = 4640935) B4640935
theorem B7039943 : Blo 722323 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B8384795 : Blo 722323 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B5206693 : Blo 722323 5206693 := bstep (se 4 (by rfl) ⟨488127, by rfl⟩ : syracuseStep 5206693 = 976255) B976255
theorem B4127233 : Blo 722323 4127233 := bstep (se 2 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 4127233 = 3095425) B3095425
theorem B1084223 : Blo 722323 1084223 := bstep (se 1 (by rfl) ⟨813167, by rfl⟩ : syracuseStep 1084223 = 1626335) B1626335
theorem B725659 : Blo 722323 725659 := bstep (se 1 (by rfl) ⟨544244, by rfl⟩ : syracuseStep 725659 = 1088489) B1088489
theorem B4693295 : Blo 722323 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B3481663 : Blo 722323 3481663 := bstep (se 1 (by rfl) ⟨2611247, by rfl⟩ : syracuseStep 3481663 = 5222495) B5222495
theorem B46350551 : Blo 722323 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B2443175 : Blo 722323 2443175 := bstep (se 1 (by rfl) ⟨1832381, by rfl⟩ : syracuseStep 2443175 = 3664763) B3664763
theorem B5589863 : Blo 722323 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B1626425 : Blo 722323 1626425 := bstep (se 2 (by rfl) ⟨609909, by rfl⟩ : syracuseStep 1626425 = 1219819) B1219819
theorem B6182891 : Blo 722323 6182891 := bstep (se 1 (by rfl) ⟨4637168, by rfl⟩ : syracuseStep 6182891 = 9274337) B9274337
theorem B2316701 : Blo 722323 2316701 := bstep (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) B868763
theorem B1303519 : Blo 722323 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B1632383 : Blo 722323 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B6942257 : Blo 722323 6942257 := bstep (se 2 (by rfl) ⟨2603346, by rfl⟩ : syracuseStep 6942257 = 5206693) B5206693
theorem B12382793 : Blo 722323 12382793 := bstep (se 2 (by rfl) ⟨4643547, by rfl⟩ : syracuseStep 12382793 = 9287095) B9287095
theorem B4125275 : Blo 722323 4125275 := bstep (se 1 (by rfl) ⟨3093956, by rfl⟩ : syracuseStep 4125275 = 6187913) B6187913
theorem B2062057 : Blo 722323 2062057 := bstep (se 2 (by rfl) ⟨773271, by rfl⟩ : syracuseStep 2062057 = 1546543) B1546543
theorem B5502977 : Blo 722323 5502977 := bstep (se 2 (by rfl) ⟨2063616, by rfl⟩ : syracuseStep 5502977 = 4127233) B4127233
theorem B30900367 : Blo 722323 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B1738025 : Blo 722323 1738025 := bstep (se 2 (by rfl) ⟨651759, by rfl⟩ : syracuseStep 1738025 = 1303519) B1303519
theorem B722815 : Blo 722323 722815 := bstep (se 1 (by rfl) ⟨542111, by rfl⟩ : syracuseStep 722815 = 1084223) B1084223
theorem B1084283 : Blo 722323 1084283 := bstep (se 1 (by rfl) ⟨813212, by rfl⟩ : syracuseStep 1084283 = 1626425) B1626425
theorem B1544467 : Blo 722323 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B1088255 : Blo 722323 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B4628171 : Blo 722323 4628171 := bstep (se 1 (by rfl) ⟨3471128, by rfl⟩ : syracuseStep 4628171 = 6942257) B6942257
theorem B3128863 : Blo 722323 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B4642217 : Blo 722323 4642217 := bstep (se 2 (by rfl) ⟨1740831, by rfl⟩ : syracuseStep 4642217 = 3481663) B3481663
theorem B1628783 : Blo 722323 1628783 := bstep (se 1 (by rfl) ⟨1221587, by rfl⟩ : syracuseStep 1628783 = 2443175) B2443175
theorem B3726575 : Blo 722323 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B4121927 : Blo 722323 4121927 := bstep (se 1 (by rfl) ⟨3091445, by rfl⟩ : syracuseStep 4121927 = 6182891) B6182891
theorem B2749409 : Blo 722323 2749409 := bstep (se 2 (by rfl) ⟨1031028, by rfl⟩ : syracuseStep 2749409 = 2062057) B2062057
theorem B8255195 : Blo 722323 8255195 := bstep (se 1 (by rfl) ⟨6191396, by rfl⟩ : syracuseStep 8255195 = 12382793) B12382793
theorem B2750183 : Blo 722323 2750183 := bstep (se 1 (by rfl) ⟨2062637, by rfl⟩ : syracuseStep 2750183 = 4125275) B4125275
theorem B3668651 : Blo 722323 3668651 := bstep (se 1 (by rfl) ⟨2751488, by rfl⟩ : syracuseStep 3668651 = 5502977) B5502977
theorem B722855 : Blo 722323 722855 := bstep (se 1 (by rfl) ⟨542141, by rfl⟩ : syracuseStep 722855 = 1084283) B1084283
theorem B1085855 : Blo 722323 1085855 := bstep (se 1 (by rfl) ⟨814391, by rfl⟩ : syracuseStep 1085855 = 1628783) B1628783
theorem B725503 : Blo 722323 725503 := bstep (se 1 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 725503 = 1088255) B1088255
theorem B3085447 : Blo 722323 3085447 := bstep (se 1 (by rfl) ⟨2314085, by rfl⟩ : syracuseStep 3085447 = 4628171) B4628171
theorem B4171817 : Blo 722323 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B41200489 : Blo 722323 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B1158683 : Blo 722323 1158683 := bstep (se 1 (by rfl) ⟨869012, by rfl⟩ : syracuseStep 1158683 = 1738025) B1738025
theorem B3094811 : Blo 722323 3094811 := bstep (se 1 (by rfl) ⟨2321108, by rfl⟩ : syracuseStep 3094811 = 4642217) B4642217
theorem B2445767 : Blo 722323 2445767 := bstep (se 1 (by rfl) ⟨1834325, by rfl⟩ : syracuseStep 2445767 = 3668651) B3668651
theorem B2484383 : Blo 722323 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B2059289 : Blo 722323 2059289 := bstep (se 2 (by rfl) ⟨772233, by rfl⟩ : syracuseStep 2059289 = 1544467) B1544467
theorem B2747951 : Blo 722323 2747951 := bstep (se 1 (by rfl) ⟨2060963, by rfl⟩ : syracuseStep 2747951 = 4121927) B4121927
theorem B1832939 : Blo 722323 1832939 := bstep (se 1 (by rfl) ⟨1374704, by rfl⟩ : syracuseStep 1832939 = 2749409) B2749409
theorem B5503463 : Blo 722323 5503463 := bstep (se 1 (by rfl) ⟨4127597, by rfl⟩ : syracuseStep 5503463 = 8255195) B8255195
theorem B1833455 : Blo 722323 1833455 := bstep (se 1 (by rfl) ⟨1375091, by rfl⟩ : syracuseStep 1833455 = 2750183) B2750183
theorem B723903 : Blo 722323 723903 := bstep (se 1 (by rfl) ⟨542927, by rfl⟩ : syracuseStep 723903 = 1085855) B1085855
theorem B6625021 : Blo 722323 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B1221959 : Blo 722323 1221959 := bstep (se 1 (by rfl) ⟨916469, by rfl⟩ : syracuseStep 1221959 = 1832939) B1832939
theorem B3089821 : Blo 722323 3089821 := bstep (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) B1158683
theorem B1222303 : Blo 722323 1222303 := bstep (se 1 (by rfl) ⟨916727, by rfl⟩ : syracuseStep 1222303 = 1833455) B1833455
theorem B54933985 : Blo 722323 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B4113929 : Blo 722323 4113929 := bstep (se 2 (by rfl) ⟨1542723, by rfl⟩ : syracuseStep 4113929 = 3085447) B3085447
theorem B1630511 : Blo 722323 1630511 := bstep (se 1 (by rfl) ⟨1222883, by rfl⟩ : syracuseStep 1630511 = 2445767) B2445767
theorem B2781211 : Blo 722323 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B1372859 : Blo 722323 1372859 := bstep (se 1 (by rfl) ⟨1029644, by rfl⟩ : syracuseStep 1372859 = 2059289) B2059289
theorem B1831967 : Blo 722323 1831967 := bstep (se 1 (by rfl) ⟨1373975, by rfl⟩ : syracuseStep 1831967 = 2747951) B2747951
theorem B2063207 : Blo 722323 2063207 := bstep (se 1 (by rfl) ⟨1547405, by rfl⟩ : syracuseStep 2063207 = 3094811) B3094811
theorem B3668975 : Blo 722323 3668975 := bstep (se 1 (by rfl) ⟨2751731, by rfl⟩ : syracuseStep 3668975 = 5503463) B5503463
theorem B141333781 : Blo 722323 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B3708281 : Blo 722323 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B1087007 : Blo 722323 1087007 := bstep (se 1 (by rfl) ⟨815255, by rfl⟩ : syracuseStep 1087007 = 1630511) B1630511
theorem B73245313 : Blo 722323 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B1221311 : Blo 722323 1221311 := bstep (se 1 (by rfl) ⟨915983, by rfl⟩ : syracuseStep 1221311 = 1831967) B1831967
theorem B2445983 : Blo 722323 2445983 := bstep (se 1 (by rfl) ⟨1834487, by rfl⟩ : syracuseStep 2445983 = 3668975) B3668975
theorem B2742619 : Blo 722323 2742619 := bstep (se 1 (by rfl) ⟨2056964, by rfl⟩ : syracuseStep 2742619 = 4113929) B4113929
theorem B4119761 : Blo 722323 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B1629737 : Blo 722323 1629737 := bstep (se 2 (by rfl) ⟨611151, by rfl⟩ : syracuseStep 1629737 = 1222303) B1222303
theorem B814639 : Blo 722323 814639 := bstep (se 1 (by rfl) ⟨610979, by rfl⟩ : syracuseStep 814639 = 1221959) B1221959
theorem B915239 : Blo 722323 915239 := bstep (se 1 (by rfl) ⟨686429, by rfl⟩ : syracuseStep 915239 = 1372859) B1372859
theorem B1375471 : Blo 722323 1375471 := bstep (se 1 (by rfl) ⟨1031603, by rfl⟩ : syracuseStep 1375471 = 2063207) B2063207
theorem B724671 : Blo 722323 724671 := bstep (se 1 (by rfl) ⟨543503, by rfl⟩ : syracuseStep 724671 = 1087007) B1087007
theorem B1086185 : Blo 722323 1086185 := bstep (se 2 (by rfl) ⟨407319, by rfl⟩ : syracuseStep 1086185 = 814639) B814639
theorem B1086491 : Blo 722323 1086491 := bstep (se 1 (by rfl) ⟨814868, by rfl⟩ : syracuseStep 1086491 = 1629737) B1629737
theorem B97660417 : Blo 722323 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B2440637 : Blo 722323 2440637 := bstep (se 3 (by rfl) ⟨457619, by rfl⟩ : syracuseStep 2440637 = 915239) B915239
theorem B3656825 : Blo 722323 3656825 := bstep (se 2 (by rfl) ⟨1371309, by rfl⟩ : syracuseStep 3656825 = 2742619) B2742619
theorem B1630655 : Blo 722323 1630655 := bstep (se 1 (by rfl) ⟨1222991, by rfl⟩ : syracuseStep 1630655 = 2445983) B2445983
theorem B9888749 : Blo 722323 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B2746507 : Blo 722323 2746507 := bstep (se 1 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 2746507 = 4119761) B4119761
theorem B814207 : Blo 722323 814207 := bstep (se 1 (by rfl) ⟨610655, by rfl⟩ : syracuseStep 814207 = 1221311) B1221311
theorem B188445041 : Blo 722323 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B1833961 : Blo 722323 1833961 := bstep (se 2 (by rfl) ⟨687735, by rfl⟩ : syracuseStep 1833961 = 1375471) B1375471
theorem B724123 : Blo 722323 724123 := bstep (se 1 (by rfl) ⟨543092, by rfl⟩ : syracuseStep 724123 = 1086185) B1086185
theorem B724327 : Blo 722323 724327 := bstep (se 1 (by rfl) ⟨543245, by rfl⟩ : syracuseStep 724327 = 1086491) B1086491
theorem B1085609 : Blo 722323 1085609 := bstep (se 2 (by rfl) ⟨407103, by rfl⟩ : syracuseStep 1085609 = 814207) B814207
theorem B1087103 : Blo 722323 1087103 := bstep (se 1 (by rfl) ⟨815327, by rfl⟩ : syracuseStep 1087103 = 1630655) B1630655
theorem B6592499 : Blo 722323 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B2437883 : Blo 722323 2437883 := bstep (se 1 (by rfl) ⟨1828412, by rfl⟩ : syracuseStep 2437883 = 3656825) B3656825
theorem B2445281 : Blo 722323 2445281 := bstep (se 2 (by rfl) ⟨916980, by rfl⟩ : syracuseStep 2445281 = 1833961) B1833961
theorem B1627091 : Blo 722323 1627091 := bstep (se 1 (by rfl) ⟨1220318, by rfl⟩ : syracuseStep 1627091 = 2440637) B2440637
theorem B3662009 : Blo 722323 3662009 := bstep (se 2 (by rfl) ⟨1373253, by rfl⟩ : syracuseStep 3662009 = 2746507) B2746507
theorem B130213889 : Blo 722323 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B125630027 : Blo 722323 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B723739 : Blo 722323 723739 := bstep (se 1 (by rfl) ⟨542804, by rfl⟩ : syracuseStep 723739 = 1085609) B1085609
theorem B1084727 : Blo 722323 1084727 := bstep (se 1 (by rfl) ⟨813545, by rfl⟩ : syracuseStep 1084727 = 1627091) B1627091
theorem B724735 : Blo 722323 724735 := bstep (se 1 (by rfl) ⟨543551, by rfl⟩ : syracuseStep 724735 = 1087103) B1087103
theorem B4394999 : Blo 722323 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B86809259 : Blo 722323 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B2441339 : Blo 722323 2441339 := bstep (se 1 (by rfl) ⟨1831004, by rfl⟩ : syracuseStep 2441339 = 3662009) B3662009
theorem B1625255 : Blo 722323 1625255 := bstep (se 1 (by rfl) ⟨1218941, by rfl⟩ : syracuseStep 1625255 = 2437883) B2437883
theorem B1630187 : Blo 722323 1630187 := bstep (se 1 (by rfl) ⟨1222640, by rfl⟩ : syracuseStep 1630187 = 2445281) B2445281
theorem B83753351 : Blo 722323 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B1083503 : Blo 722323 1083503 := bstep (se 1 (by rfl) ⟨812627, by rfl⟩ : syracuseStep 1083503 = 1625255) B1625255
theorem B723151 : Blo 722323 723151 := bstep (se 1 (by rfl) ⟨542363, by rfl⟩ : syracuseStep 723151 = 1084727) B1084727
theorem B57872839 : Blo 722323 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B1086791 : Blo 722323 1086791 := bstep (se 1 (by rfl) ⟨815093, by rfl⟩ : syracuseStep 1086791 = 1630187) B1630187
theorem B11719997 : Blo 722323 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B1627559 : Blo 722323 1627559 := bstep (se 1 (by rfl) ⟨1220669, by rfl⟩ : syracuseStep 1627559 = 2441339) B2441339
theorem B55835567 : Blo 722323 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B722335 : Blo 722323 722335 := bstep (se 1 (by rfl) ⟨541751, by rfl⟩ : syracuseStep 722335 = 1083503) B1083503
theorem B724527 : Blo 722323 724527 := bstep (se 1 (by rfl) ⟨543395, by rfl⟩ : syracuseStep 724527 = 1086791) B1086791
theorem B1085039 : Blo 722323 1085039 := bstep (se 1 (by rfl) ⟨813779, by rfl⟩ : syracuseStep 1085039 = 1627559) B1627559
theorem B7813331 : Blo 722323 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B77163785 : Blo 722323 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B37223711 : Blo 722323 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B723359 : Blo 722323 723359 := bstep (se 1 (by rfl) ⟨542519, by rfl⟩ : syracuseStep 723359 = 1085039) B1085039
theorem B24815807 : Blo 722323 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B51442523 : Blo 722323 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B5208887 : Blo 722323 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B34295015 : Blo 722323 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B16543871 : Blo 722323 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B3472591 : Blo 722323 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B4630121 : Blo 722323 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B11029247 : Blo 722323 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B22863343 : Blo 722323 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B3086747 : Blo 722323 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B30484457 : Blo 722323 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B7352831 : Blo 722323 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B20322971 : Blo 722323 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B4901887 : Blo 722323 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B2057831 : Blo 722323 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B6535849 : Blo 722323 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B13548647 : Blo 722323 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B1371887 : Blo 722323 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B36129725 : Blo 722323 36129725 := bstep (se 3 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 36129725 = 13548647) B13548647
theorem B914591 : Blo 722323 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B8714465 : Blo 722323 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B24086483 : Blo 722323 24086483 := bstep (se 1 (by rfl) ⟨18064862, by rfl⟩ : syracuseStep 24086483 = 36129725) B36129725
theorem B5809643 : Blo 722323 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B2438909 : Blo 722323 2438909 := bstep (se 3 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 2438909 = 914591) B914591
theorem B16057655 : Blo 722323 16057655 := bstep (se 1 (by rfl) ⟨12043241, by rfl⟩ : syracuseStep 16057655 = 24086483) B24086483
theorem B3873095 : Blo 722323 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B1625939 : Blo 722323 1625939 := bstep (se 1 (by rfl) ⟨1219454, by rfl⟩ : syracuseStep 1625939 = 2438909) B2438909
theorem B1083959 : Blo 722323 1083959 := bstep (se 1 (by rfl) ⟨812969, by rfl⟩ : syracuseStep 1083959 = 1625939) B1625939
theorem B10705103 : Blo 722323 10705103 := bstep (se 1 (by rfl) ⟨8028827, by rfl⟩ : syracuseStep 10705103 = 16057655) B16057655
theorem B2582063 : Blo 722323 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B722639 : Blo 722323 722639 := bstep (se 1 (by rfl) ⟨541979, by rfl⟩ : syracuseStep 722639 = 1083959) B1083959
theorem B1721375 : Blo 722323 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B114187765 : Blo 722323 114187765 := bstep (se 5 (by rfl) ⟨5352551, by rfl⟩ : syracuseStep 114187765 = 10705103) B10705103
theorem B1147583 : Blo 722323 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B152250353 : Blo 722323 152250353 := bstep (se 2 (by rfl) ⟨57093882, by rfl⟩ : syracuseStep 152250353 = 114187765) B114187765
theorem B765055 : Blo 722323 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B101500235 : Blo 722323 101500235 := bstep (se 1 (by rfl) ⟨76125176, by rfl⟩ : syracuseStep 101500235 = 152250353) B152250353
theorem B67666823 : Blo 722323 67666823 := bstep (se 1 (by rfl) ⟨50750117, by rfl⟩ : syracuseStep 67666823 = 101500235) B101500235
theorem B4080293 : Blo 722323 4080293 := bstep (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) B765055
theorem B2720195 : Blo 722323 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B45111215 : Blo 722323 45111215 := bstep (se 1 (by rfl) ⟨33833411, by rfl⟩ : syracuseStep 45111215 = 67666823) B67666823
theorem B120296573 : Blo 722323 120296573 := bstep (se 3 (by rfl) ⟨22555607, by rfl⟩ : syracuseStep 120296573 = 45111215) B45111215
theorem B1813463 : Blo 722323 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B80197715 : Blo 722323 80197715 := bstep (se 1 (by rfl) ⟨60148286, by rfl⟩ : syracuseStep 80197715 = 120296573) B120296573
theorem B1208975 : Blo 722323 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B12895733 : Blo 722323 12895733 := bstep (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) B1208975
theorem B53465143 : Blo 722323 53465143 := bstep (se 1 (by rfl) ⟨40098857, by rfl⟩ : syracuseStep 53465143 = 80197715) B80197715
theorem B34388621 : Blo 722323 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B71286857 : Blo 722323 71286857 := bstep (se 2 (by rfl) ⟨26732571, by rfl⟩ : syracuseStep 71286857 = 53465143) B53465143
theorem B47524571 : Blo 722323 47524571 := bstep (se 1 (by rfl) ⟨35643428, by rfl⟩ : syracuseStep 47524571 = 71286857) B71286857
theorem B22925747 : Blo 722323 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B15283831 : Blo 722323 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B31683047 : Blo 722323 31683047 := bstep (se 1 (by rfl) ⟨23762285, by rfl⟩ : syracuseStep 31683047 = 47524571) B47524571
theorem B84488125 : Blo 722323 84488125 := bstep (se 3 (by rfl) ⟨15841523, by rfl⟩ : syracuseStep 84488125 = 31683047) B31683047
theorem B20378441 : Blo 722323 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B13585627 : Blo 722323 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B112650833 : Blo 722323 112650833 := bstep (se 2 (by rfl) ⟨42244062, by rfl⟩ : syracuseStep 112650833 = 84488125) B84488125
theorem B72456677 : Blo 722323 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B75100555 : Blo 722323 75100555 := bstep (se 1 (by rfl) ⟨56325416, by rfl⟩ : syracuseStep 75100555 = 112650833) B112650833
theorem B48304451 : Blo 722323 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B100134073 : Blo 722323 100134073 := bstep (se 2 (by rfl) ⟨37550277, by rfl⟩ : syracuseStep 100134073 = 75100555) B75100555
theorem B133512097 : Blo 722323 133512097 := bstep (se 2 (by rfl) ⟨50067036, by rfl⟩ : syracuseStep 133512097 = 100134073) B100134073
theorem B32202967 : Blo 722323 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B42937289 : Blo 722323 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B178016129 : Blo 722323 178016129 := bstep (se 2 (by rfl) ⟨66756048, by rfl⟩ : syracuseStep 178016129 = 133512097) B133512097
theorem B28624859 : Blo 722323 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B118677419 : Blo 722323 118677419 := bstep (se 1 (by rfl) ⟨89008064, by rfl⟩ : syracuseStep 118677419 = 178016129) B178016129
theorem B19083239 : Blo 722323 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B79118279 : Blo 722323 79118279 := bstep (se 1 (by rfl) ⟨59338709, by rfl⟩ : syracuseStep 79118279 = 118677419) B118677419
theorem B12722159 : Blo 722323 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B52745519 : Blo 722323 52745519 := bstep (se 1 (by rfl) ⟨39559139, by rfl⟩ : syracuseStep 52745519 = 79118279) B79118279
theorem B35163679 : Blo 722323 35163679 := bstep (se 1 (by rfl) ⟨26372759, by rfl⟩ : syracuseStep 35163679 = 52745519) B52745519
theorem B8481439 : Blo 722323 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B11308585 : Blo 722323 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B46884905 : Blo 722323 46884905 := bstep (se 2 (by rfl) ⟨17581839, by rfl⟩ : syracuseStep 46884905 = 35163679) B35163679
theorem B15078113 : Blo 722323 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B31256603 : Blo 722323 31256603 := bstep (se 1 (by rfl) ⟨23442452, by rfl⟩ : syracuseStep 31256603 = 46884905) B46884905
theorem B10052075 : Blo 722323 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B20837735 : Blo 722323 20837735 := bstep (se 1 (by rfl) ⟨15628301, by rfl⟩ : syracuseStep 20837735 = 31256603) B31256603
theorem B6701383 : Blo 722323 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B13891823 : Blo 722323 13891823 := bstep (se 1 (by rfl) ⟨10418867, by rfl⟩ : syracuseStep 13891823 = 20837735) B20837735
theorem B9261215 : Blo 722323 9261215 := bstep (se 1 (by rfl) ⟨6945911, by rfl⟩ : syracuseStep 9261215 = 13891823) B13891823
theorem B8935177 : Blo 722323 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B6174143 : Blo 722323 6174143 := bstep (se 1 (by rfl) ⟨4630607, by rfl⟩ : syracuseStep 6174143 = 9261215) B9261215
theorem B11913569 : Blo 722323 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7942379 : Blo 722323 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B4116095 : Blo 722323 4116095 := bstep (se 1 (by rfl) ⟨3087071, by rfl⟩ : syracuseStep 4116095 = 6174143) B6174143
theorem B84718709 : Blo 722323 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B2744063 : Blo 722323 2744063 := bstep (se 1 (by rfl) ⟨2058047, by rfl⟩ : syracuseStep 2744063 = 4116095) B4116095
theorem B56479139 : Blo 722323 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B1829375 : Blo 722323 1829375 := bstep (se 1 (by rfl) ⟨1372031, by rfl⟩ : syracuseStep 1829375 = 2744063) B2744063
theorem B37652759 : Blo 722323 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B1219583 : Blo 722323 1219583 := bstep (se 1 (by rfl) ⟨914687, by rfl⟩ : syracuseStep 1219583 = 1829375) B1829375
theorem B25101839 : Blo 722323 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B813055 : Blo 722323 813055 := bstep (se 1 (by rfl) ⟨609791, by rfl⟩ : syracuseStep 813055 = 1219583) B1219583
theorem B1084073 : Blo 722323 1084073 := bstep (se 2 (by rfl) ⟨406527, by rfl⟩ : syracuseStep 1084073 = 813055) B813055
theorem B16734559 : Blo 722323 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B722715 : Blo 722323 722715 := bstep (se 1 (by rfl) ⟨542036, by rfl⟩ : syracuseStep 722715 = 1084073) B1084073
theorem B22312745 : Blo 722323 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B14875163 : Blo 722323 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B9916775 : Blo 722323 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B6611183 : Blo 722323 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B4407455 : Blo 722323 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2938303 : Blo 722323 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B3917737 : Blo 722323 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B5223649 : Blo 722323 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B6964865 : Blo 722323 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B4643243 : Blo 722323 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B3095495 : Blo 722323 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B2063663 : Blo 722323 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B1375775 : Blo 722323 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B917183 : Blo 722323 917183 := bstep (se 1 (by rfl) ⟨687887, by rfl⟩ : syracuseStep 917183 = 1375775) B1375775
theorem B2445821 : Blo 722323 2445821 := bstep (se 3 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 2445821 = 917183) B917183
theorem B1630547 : Blo 722323 1630547 := bstep (se 1 (by rfl) ⟨1222910, by rfl⟩ : syracuseStep 1630547 = 2445821) B2445821
theorem B1087031 : Blo 722323 1087031 := bstep (se 1 (by rfl) ⟨815273, by rfl⟩ : syracuseStep 1087031 = 1630547) B1630547
theorem B724687 : Blo 722323 724687 := bstep (se 1 (by rfl) ⟨543515, by rfl⟩ : syracuseStep 724687 = 1087031) B1087031

theorem C0 (j : ℕ) (h1 : 180580 ≤ j) (h2 : j ≤ 181279) : Blo 722323 (4 * j + 3) := by
  interval_cases j
  · exact B722323
  · exact B722327
  · exact B722331
  · exact B722335
  · exact B722339
  · exact B722343
  · exact B722347
  · exact B722351
  · exact B722355
  · exact B722359
  · exact B722363
  · exact B722367
  · exact B722371
  · exact B722375
  · exact B722379
  · exact B722383
  · exact B722387
  · exact B722391
  · exact B722395
  · exact B722399
  · exact B722403
  · exact B722407
  · exact B722411
  · exact B722415
  · exact B722419
  · exact B722423
  · exact B722427
  · exact B722431
  · exact B722435
  · exact B722439
  · exact B722443
  · exact B722447
  · exact B722451
  · exact B722455
  · exact B722459
  · exact B722463
  · exact B722467
  · exact B722471
  · exact B722475
  · exact B722479
  · exact B722483
  · exact B722487
  · exact B722491
  · exact B722495
  · exact B722499
  · exact B722503
  · exact B722507
  · exact B722511
  · exact B722515
  · exact B722519
  · exact B722523
  · exact B722527
  · exact B722531
  · exact B722535
  · exact B722539
  · exact B722543
  · exact B722547
  · exact B722551
  · exact B722555
  · exact B722559
  · exact B722563
  · exact B722567
  · exact B722571
  · exact B722575
  · exact B722579
  · exact B722583
  · exact B722587
  · exact B722591
  · exact B722595
  · exact B722599
  · exact B722603
  · exact B722607
  · exact B722611
  · exact B722615
  · exact B722619
  · exact B722623
  · exact B722627
  · exact B722631
  · exact B722635
  · exact B722639
  · exact B722643
  · exact B722647
  · exact B722651
  · exact B722655
  · exact B722659
  · exact B722663
  · exact B722667
  · exact B722671
  · exact B722675
  · exact B722679
  · exact B722683
  · exact B722687
  · exact B722691
  · exact B722695
  · exact B722699
  · exact B722703
  · exact B722707
  · exact B722711
  · exact B722715
  · exact B722719
  · exact B722723
  · exact B722727
  · exact B722731
  · exact B722735
  · exact B722739
  · exact B722743
  · exact B722747
  · exact B722751
  · exact B722755
  · exact B722759
  · exact B722763
  · exact B722767
  · exact B722771
  · exact B722775
  · exact B722779
  · exact B722783
  · exact B722787
  · exact B722791
  · exact B722795
  · exact B722799
  · exact B722803
  · exact B722807
  · exact B722811
  · exact B722815
  · exact B722819
  · exact B722823
  · exact B722827
  · exact B722831
  · exact B722835
  · exact B722839
  · exact B722843
  · exact B722847
  · exact B722851
  · exact B722855
  · exact B722859
  · exact B722863
  · exact B722867
  · exact B722871
  · exact B722875
  · exact B722879
  · exact B722883
  · exact B722887
  · exact B722891
  · exact B722895
  · exact B722899
  · exact B722903
  · exact B722907
  · exact B722911
  · exact B722915
  · exact B722919
  · exact B722923
  · exact B722927
  · exact B722931
  · exact B722935
  · exact B722939
  · exact B722943
  · exact B722947
  · exact B722951
  · exact B722955
  · exact B722959
  · exact B722963
  · exact B722967
  · exact B722971
  · exact B722975
  · exact B722979
  · exact B722983
  · exact B722987
  · exact B722991
  · exact B722995
  · exact B722999
  · exact B723003
  · exact B723007
  · exact B723011
  · exact B723015
  · exact B723019
  · exact B723023
  · exact B723027
  · exact B723031
  · exact B723035
  · exact B723039
  · exact B723043
  · exact B723047
  · exact B723051
  · exact B723055
  · exact B723059
  · exact B723063
  · exact B723067
  · exact B723071
  · exact B723075
  · exact B723079
  · exact B723083
  · exact B723087
  · exact B723091
  · exact B723095
  · exact B723099
  · exact B723103
  · exact B723107
  · exact B723111
  · exact B723115
  · exact B723119
  · exact B723123
  · exact B723127
  · exact B723131
  · exact B723135
  · exact B723139
  · exact B723143
  · exact B723147
  · exact B723151
  · exact B723155
  · exact B723159
  · exact B723163
  · exact B723167
  · exact B723171
  · exact B723175
  · exact B723179
  · exact B723183
  · exact B723187
  · exact B723191
  · exact B723195
  · exact B723199
  · exact B723203
  · exact B723207
  · exact B723211
  · exact B723215
  · exact B723219
  · exact B723223
  · exact B723227
  · exact B723231
  · exact B723235
  · exact B723239
  · exact B723243
  · exact B723247
  · exact B723251
  · exact B723255
  · exact B723259
  · exact B723263
  · exact B723267
  · exact B723271
  · exact B723275
  · exact B723279
  · exact B723283
  · exact B723287
  · exact B723291
  · exact B723295
  · exact B723299
  · exact B723303
  · exact B723307
  · exact B723311
  · exact B723315
  · exact B723319
  · exact B723323
  · exact B723327
  · exact B723331
  · exact B723335
  · exact B723339
  · exact B723343
  · exact B723347
  · exact B723351
  · exact B723355
  · exact B723359
  · exact B723363
  · exact B723367
  · exact B723371
  · exact B723375
  · exact B723379
  · exact B723383
  · exact B723387
  · exact B723391
  · exact B723395
  · exact B723399
  · exact B723403
  · exact B723407
  · exact B723411
  · exact B723415
  · exact B723419
  · exact B723423
  · exact B723427
  · exact B723431
  · exact B723435
  · exact B723439
  · exact B723443
  · exact B723447
  · exact B723451
  · exact B723455
  · exact B723459
  · exact B723463
  · exact B723467
  · exact B723471
  · exact B723475
  · exact B723479
  · exact B723483
  · exact B723487
  · exact B723491
  · exact B723495
  · exact B723499
  · exact B723503
  · exact B723507
  · exact B723511
  · exact B723515
  · exact B723519
  · exact B723523
  · exact B723527
  · exact B723531
  · exact B723535
  · exact B723539
  · exact B723543
  · exact B723547
  · exact B723551
  · exact B723555
  · exact B723559
  · exact B723563
  · exact B723567
  · exact B723571
  · exact B723575
  · exact B723579
  · exact B723583
  · exact B723587
  · exact B723591
  · exact B723595
  · exact B723599
  · exact B723603
  · exact B723607
  · exact B723611
  · exact B723615
  · exact B723619
  · exact B723623
  · exact B723627
  · exact B723631
  · exact B723635
  · exact B723639
  · exact B723643
  · exact B723647
  · exact B723651
  · exact B723655
  · exact B723659
  · exact B723663
  · exact B723667
  · exact B723671
  · exact B723675
  · exact B723679
  · exact B723683
  · exact B723687
  · exact B723691
  · exact B723695
  · exact B723699
  · exact B723703
  · exact B723707
  · exact B723711
  · exact B723715
  · exact B723719
  · exact B723723
  · exact B723727
  · exact B723731
  · exact B723735
  · exact B723739
  · exact B723743
  · exact B723747
  · exact B723751
  · exact B723755
  · exact B723759
  · exact B723763
  · exact B723767
  · exact B723771
  · exact B723775
  · exact B723779
  · exact B723783
  · exact B723787
  · exact B723791
  · exact B723795
  · exact B723799
  · exact B723803
  · exact B723807
  · exact B723811
  · exact B723815
  · exact B723819
  · exact B723823
  · exact B723827
  · exact B723831
  · exact B723835
  · exact B723839
  · exact B723843
  · exact B723847
  · exact B723851
  · exact B723855
  · exact B723859
  · exact B723863
  · exact B723867
  · exact B723871
  · exact B723875
  · exact B723879
  · exact B723883
  · exact B723887
  · exact B723891
  · exact B723895
  · exact B723899
  · exact B723903
  · exact B723907
  · exact B723911
  · exact B723915
  · exact B723919
  · exact B723923
  · exact B723927
  · exact B723931
  · exact B723935
  · exact B723939
  · exact B723943
  · exact B723947
  · exact B723951
  · exact B723955
  · exact B723959
  · exact B723963
  · exact B723967
  · exact B723971
  · exact B723975
  · exact B723979
  · exact B723983
  · exact B723987
  · exact B723991
  · exact B723995
  · exact B723999
  · exact B724003
  · exact B724007
  · exact B724011
  · exact B724015
  · exact B724019
  · exact B724023
  · exact B724027
  · exact B724031
  · exact B724035
  · exact B724039
  · exact B724043
  · exact B724047
  · exact B724051
  · exact B724055
  · exact B724059
  · exact B724063
  · exact B724067
  · exact B724071
  · exact B724075
  · exact B724079
  · exact B724083
  · exact B724087
  · exact B724091
  · exact B724095
  · exact B724099
  · exact B724103
  · exact B724107
  · exact B724111
  · exact B724115
  · exact B724119
  · exact B724123
  · exact B724127
  · exact B724131
  · exact B724135
  · exact B724139
  · exact B724143
  · exact B724147
  · exact B724151
  · exact B724155
  · exact B724159
  · exact B724163
  · exact B724167
  · exact B724171
  · exact B724175
  · exact B724179
  · exact B724183
  · exact B724187
  · exact B724191
  · exact B724195
  · exact B724199
  · exact B724203
  · exact B724207
  · exact B724211
  · exact B724215
  · exact B724219
  · exact B724223
  · exact B724227
  · exact B724231
  · exact B724235
  · exact B724239
  · exact B724243
  · exact B724247
  · exact B724251
  · exact B724255
  · exact B724259
  · exact B724263
  · exact B724267
  · exact B724271
  · exact B724275
  · exact B724279
  · exact B724283
  · exact B724287
  · exact B724291
  · exact B724295
  · exact B724299
  · exact B724303
  · exact B724307
  · exact B724311
  · exact B724315
  · exact B724319
  · exact B724323
  · exact B724327
  · exact B724331
  · exact B724335
  · exact B724339
  · exact B724343
  · exact B724347
  · exact B724351
  · exact B724355
  · exact B724359
  · exact B724363
  · exact B724367
  · exact B724371
  · exact B724375
  · exact B724379
  · exact B724383
  · exact B724387
  · exact B724391
  · exact B724395
  · exact B724399
  · exact B724403
  · exact B724407
  · exact B724411
  · exact B724415
  · exact B724419
  · exact B724423
  · exact B724427
  · exact B724431
  · exact B724435
  · exact B724439
  · exact B724443
  · exact B724447
  · exact B724451
  · exact B724455
  · exact B724459
  · exact B724463
  · exact B724467
  · exact B724471
  · exact B724475
  · exact B724479
  · exact B724483
  · exact B724487
  · exact B724491
  · exact B724495
  · exact B724499
  · exact B724503
  · exact B724507
  · exact B724511
  · exact B724515
  · exact B724519
  · exact B724523
  · exact B724527
  · exact B724531
  · exact B724535
  · exact B724539
  · exact B724543
  · exact B724547
  · exact B724551
  · exact B724555
  · exact B724559
  · exact B724563
  · exact B724567
  · exact B724571
  · exact B724575
  · exact B724579
  · exact B724583
  · exact B724587
  · exact B724591
  · exact B724595
  · exact B724599
  · exact B724603
  · exact B724607
  · exact B724611
  · exact B724615
  · exact B724619
  · exact B724623
  · exact B724627
  · exact B724631
  · exact B724635
  · exact B724639
  · exact B724643
  · exact B724647
  · exact B724651
  · exact B724655
  · exact B724659
  · exact B724663
  · exact B724667
  · exact B724671
  · exact B724675
  · exact B724679
  · exact B724683
  · exact B724687
  · exact B724691
  · exact B724695
  · exact B724699
  · exact B724703
  · exact B724707
  · exact B724711
  · exact B724715
  · exact B724719
  · exact B724723
  · exact B724727
  · exact B724731
  · exact B724735
  · exact B724739
  · exact B724743
  · exact B724747
  · exact B724751
  · exact B724755
  · exact B724759
  · exact B724763
  · exact B724767
  · exact B724771
  · exact B724775
  · exact B724779
  · exact B724783
  · exact B724787
  · exact B724791
  · exact B724795
  · exact B724799
  · exact B724803
  · exact B724807
  · exact B724811
  · exact B724815
  · exact B724819
  · exact B724823
  · exact B724827
  · exact B724831
  · exact B724835
  · exact B724839
  · exact B724843
  · exact B724847
  · exact B724851
  · exact B724855
  · exact B724859
  · exact B724863
  · exact B724867
  · exact B724871
  · exact B724875
  · exact B724879
  · exact B724883
  · exact B724887
  · exact B724891
  · exact B724895
  · exact B724899
  · exact B724903
  · exact B724907
  · exact B724911
  · exact B724915
  · exact B724919
  · exact B724923
  · exact B724927
  · exact B724931
  · exact B724935
  · exact B724939
  · exact B724943
  · exact B724947
  · exact B724951
  · exact B724955
  · exact B724959
  · exact B724963
  · exact B724967
  · exact B724971
  · exact B724975
  · exact B724979
  · exact B724983
  · exact B724987
  · exact B724991
  · exact B724995
  · exact B724999
  · exact B725003
  · exact B725007
  · exact B725011
  · exact B725015
  · exact B725019
  · exact B725023
  · exact B725027
  · exact B725031
  · exact B725035
  · exact B725039
  · exact B725043
  · exact B725047
  · exact B725051
  · exact B725055
  · exact B725059
  · exact B725063
  · exact B725067
  · exact B725071
  · exact B725075
  · exact B725079
  · exact B725083
  · exact B725087
  · exact B725091
  · exact B725095
  · exact B725099
  · exact B725103
  · exact B725107
  · exact B725111
  · exact B725115
  · exact B725119

theorem C1 (j : ℕ) (h1 : 181280 ≤ j) (h2 : j ≤ 181580) : Blo 722323 (4 * j + 3) := by
  interval_cases j
  · exact B725123
  · exact B725127
  · exact B725131
  · exact B725135
  · exact B725139
  · exact B725143
  · exact B725147
  · exact B725151
  · exact B725155
  · exact B725159
  · exact B725163
  · exact B725167
  · exact B725171
  · exact B725175
  · exact B725179
  · exact B725183
  · exact B725187
  · exact B725191
  · exact B725195
  · exact B725199
  · exact B725203
  · exact B725207
  · exact B725211
  · exact B725215
  · exact B725219
  · exact B725223
  · exact B725227
  · exact B725231
  · exact B725235
  · exact B725239
  · exact B725243
  · exact B725247
  · exact B725251
  · exact B725255
  · exact B725259
  · exact B725263
  · exact B725267
  · exact B725271
  · exact B725275
  · exact B725279
  · exact B725283
  · exact B725287
  · exact B725291
  · exact B725295
  · exact B725299
  · exact B725303
  · exact B725307
  · exact B725311
  · exact B725315
  · exact B725319
  · exact B725323
  · exact B725327
  · exact B725331
  · exact B725335
  · exact B725339
  · exact B725343
  · exact B725347
  · exact B725351
  · exact B725355
  · exact B725359
  · exact B725363
  · exact B725367
  · exact B725371
  · exact B725375
  · exact B725379
  · exact B725383
  · exact B725387
  · exact B725391
  · exact B725395
  · exact B725399
  · exact B725403
  · exact B725407
  · exact B725411
  · exact B725415
  · exact B725419
  · exact B725423
  · exact B725427
  · exact B725431
  · exact B725435
  · exact B725439
  · exact B725443
  · exact B725447
  · exact B725451
  · exact B725455
  · exact B725459
  · exact B725463
  · exact B725467
  · exact B725471
  · exact B725475
  · exact B725479
  · exact B725483
  · exact B725487
  · exact B725491
  · exact B725495
  · exact B725499
  · exact B725503
  · exact B725507
  · exact B725511
  · exact B725515
  · exact B725519
  · exact B725523
  · exact B725527
  · exact B725531
  · exact B725535
  · exact B725539
  · exact B725543
  · exact B725547
  · exact B725551
  · exact B725555
  · exact B725559
  · exact B725563
  · exact B725567
  · exact B725571
  · exact B725575
  · exact B725579
  · exact B725583
  · exact B725587
  · exact B725591
  · exact B725595
  · exact B725599
  · exact B725603
  · exact B725607
  · exact B725611
  · exact B725615
  · exact B725619
  · exact B725623
  · exact B725627
  · exact B725631
  · exact B725635
  · exact B725639
  · exact B725643
  · exact B725647
  · exact B725651
  · exact B725655
  · exact B725659
  · exact B725663
  · exact B725667
  · exact B725671
  · exact B725675
  · exact B725679
  · exact B725683
  · exact B725687
  · exact B725691
  · exact B725695
  · exact B725699
  · exact B725703
  · exact B725707
  · exact B725711
  · exact B725715
  · exact B725719
  · exact B725723
  · exact B725727
  · exact B725731
  · exact B725735
  · exact B725739
  · exact B725743
  · exact B725747
  · exact B725751
  · exact B725755
  · exact B725759
  · exact B725763
  · exact B725767
  · exact B725771
  · exact B725775
  · exact B725779
  · exact B725783
  · exact B725787
  · exact B725791
  · exact B725795
  · exact B725799
  · exact B725803
  · exact B725807
  · exact B725811
  · exact B725815
  · exact B725819
  · exact B725823
  · exact B725827
  · exact B725831
  · exact B725835
  · exact B725839
  · exact B725843
  · exact B725847
  · exact B725851
  · exact B725855
  · exact B725859
  · exact B725863
  · exact B725867
  · exact B725871
  · exact B725875
  · exact B725879
  · exact B725883
  · exact B725887
  · exact B725891
  · exact B725895
  · exact B725899
  · exact B725903
  · exact B725907
  · exact B725911
  · exact B725915
  · exact B725919
  · exact B725923
  · exact B725927
  · exact B725931
  · exact B725935
  · exact B725939
  · exact B725943
  · exact B725947
  · exact B725951
  · exact B725955
  · exact B725959
  · exact B725963
  · exact B725967
  · exact B725971
  · exact B725975
  · exact B725979
  · exact B725983
  · exact B725987
  · exact B725991
  · exact B725995
  · exact B725999
  · exact B726003
  · exact B726007
  · exact B726011
  · exact B726015
  · exact B726019
  · exact B726023
  · exact B726027
  · exact B726031
  · exact B726035
  · exact B726039
  · exact B726043
  · exact B726047
  · exact B726051
  · exact B726055
  · exact B726059
  · exact B726063
  · exact B726067
  · exact B726071
  · exact B726075
  · exact B726079
  · exact B726083
  · exact B726087
  · exact B726091
  · exact B726095
  · exact B726099
  · exact B726103
  · exact B726107
  · exact B726111
  · exact B726115
  · exact B726119
  · exact B726123
  · exact B726127
  · exact B726131
  · exact B726135
  · exact B726139
  · exact B726143
  · exact B726147
  · exact B726151
  · exact B726155
  · exact B726159
  · exact B726163
  · exact B726167
  · exact B726171
  · exact B726175
  · exact B726179
  · exact B726183
  · exact B726187
  · exact B726191
  · exact B726195
  · exact B726199
  · exact B726203
  · exact B726207
  · exact B726211
  · exact B726215
  · exact B726219
  · exact B726223
  · exact B726227
  · exact B726231
  · exact B726235
  · exact B726239
  · exact B726243
  · exact B726247
  · exact B726251
  · exact B726255
  · exact B726259
  · exact B726263
  · exact B726267
  · exact B726271
  · exact B726275
  · exact B726279
  · exact B726283
  · exact B726287
  · exact B726291
  · exact B726295
  · exact B726299
  · exact B726303
  · exact B726307
  · exact B726311
  · exact B726315
  · exact B726319
  · exact B726323

theorem solution (m : ℕ) (hlo : 722323 ≤ m) (hhi : m ≤ 726323) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 180580 ≤ j := by omega
    have hj2 : j ≤ 181580 := by omega
    have hb : Blo 722323 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 181280 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
