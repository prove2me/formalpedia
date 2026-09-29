-- Prove2me | solution 1 for syracuse_descends_range_638302_642302
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:43.090353+00:00
-- url     : https://prove2.me/submissions/2730f851-10c8-4530-8f23-f28727d2d6ce

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


theorem B720913 : Blo 638302 720913 := bbase (se 2 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 720913 = 540685) (by norm_num)
theorem B819245 : Blo 638302 819245 := bbase (se 3 (by rfl) ⟨153608, by rfl⟩ : syracuseStep 819245 = 307217) (by norm_num)
theorem B1081397 : Blo 638302 1081397 := bbase (se 5 (by rfl) ⟨50690, by rfl⟩ : syracuseStep 1081397 = 101381) (by norm_num)
theorem B720949 : Blo 638302 720949 := bbase (se 5 (by rfl) ⟨33794, by rfl⟩ : syracuseStep 720949 = 67589) (by norm_num)
theorem B1441853 : Blo 638302 1441853 := bbase (se 3 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 1441853 = 540695) (by norm_num)
theorem B720985 : Blo 638302 720985 := bbase (se 2 (by rfl) ⟨270369, by rfl⟩ : syracuseStep 720985 = 540739) (by norm_num)
theorem B1212509 : Blo 638302 1212509 := bbase (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) (by norm_num)
theorem B721021 : Blo 638302 721021 := bbase (se 3 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 721021 = 270383) (by norm_num)
theorem B1441925 : Blo 638302 1441925 := bbase (se 4 (by rfl) ⟨135180, by rfl⟩ : syracuseStep 1441925 = 270361) (by norm_num)
theorem B721057 : Blo 638302 721057 := bbase (se 2 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 721057 = 540793) (by norm_num)
theorem B1081525 : Blo 638302 1081525 := bbase (se 5 (by rfl) ⟨50696, by rfl⟩ : syracuseStep 1081525 = 101393) (by norm_num)
theorem B721093 : Blo 638302 721093 := bbase (se 4 (by rfl) ⟨67602, by rfl⟩ : syracuseStep 721093 = 135205) (by norm_num)
theorem B1441997 : Blo 638302 1441997 := bbase (se 3 (by rfl) ⟨270374, by rfl⟩ : syracuseStep 1441997 = 540749) (by norm_num)
theorem B721129 : Blo 638302 721129 := bbase (se 2 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 721129 = 540847) (by norm_num)
theorem B1212661 : Blo 638302 1212661 := bbase (se 5 (by rfl) ⟨56843, by rfl⟩ : syracuseStep 1212661 = 113687) (by norm_num)
theorem B2818309 : Blo 638302 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B1081613 : Blo 638302 1081613 := bbase (se 3 (by rfl) ⟨202802, by rfl⟩ : syracuseStep 1081613 = 405605) (by norm_num)
theorem B721165 : Blo 638302 721165 := bbase (se 3 (by rfl) ⟨135218, by rfl⟩ : syracuseStep 721165 = 270437) (by norm_num)
theorem B1442069 : Blo 638302 1442069 := bbase (se 6 (by rfl) ⟨33798, by rfl⟩ : syracuseStep 1442069 = 67597) (by norm_num)
theorem B721201 : Blo 638302 721201 := bbase (se 2 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 721201 = 540901) (by norm_num)
theorem B3244373 : Blo 638302 3244373 := bbase (se 10 (by rfl) ⟨4752, by rfl⟩ : syracuseStep 3244373 = 9505) (by norm_num)
theorem B721237 : Blo 638302 721237 := bbase (se 10 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 721237 = 2113) (by norm_num)
theorem B1442141 : Blo 638302 1442141 := bbase (se 3 (by rfl) ⟨270401, by rfl⟩ : syracuseStep 1442141 = 540803) (by norm_num)
theorem B721273 : Blo 638302 721273 := bbase (se 2 (by rfl) ⟨270477, by rfl⟩ : syracuseStep 721273 = 540955) (by norm_num)
theorem B2163077 : Blo 638302 2163077 := bbase (se 4 (by rfl) ⟨202788, by rfl⟩ : syracuseStep 2163077 = 405577) (by norm_num)
theorem B1081741 : Blo 638302 1081741 := bbase (se 3 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 1081741 = 405653) (by norm_num)
theorem B721309 : Blo 638302 721309 := bbase (se 3 (by rfl) ⟨135245, by rfl⟩ : syracuseStep 721309 = 270491) (by norm_num)
theorem B1442213 : Blo 638302 1442213 := bbase (se 4 (by rfl) ⟨135207, by rfl⟩ : syracuseStep 1442213 = 270415) (by norm_num)
theorem B721345 : Blo 638302 721345 := bbase (se 2 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 721345 = 541009) (by norm_num)
theorem B721381 : Blo 638302 721381 := bbase (se 4 (by rfl) ⟨67629, by rfl⟩ : syracuseStep 721381 = 135259) (by norm_num)
theorem B1081829 : Blo 638302 1081829 := bbase (se 4 (by rfl) ⟨101421, by rfl⟩ : syracuseStep 1081829 = 202843) (by norm_num)
theorem B1442285 : Blo 638302 1442285 := bbase (se 3 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 1442285 = 540857) (by norm_num)
theorem B721417 : Blo 638302 721417 := bbase (se 2 (by rfl) ⟨270531, by rfl⟩ : syracuseStep 721417 = 541063) (by norm_num)
theorem B1212965 : Blo 638302 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B721453 : Blo 638302 721453 := bbase (se 3 (by rfl) ⟨135272, by rfl⟩ : syracuseStep 721453 = 270545) (by norm_num)
theorem B1442357 : Blo 638302 1442357 := bbase (se 5 (by rfl) ⟨67610, by rfl⟩ : syracuseStep 1442357 = 135221) (by norm_num)
theorem B721489 : Blo 638302 721489 := bbase (se 2 (by rfl) ⟨270558, by rfl⟩ : syracuseStep 721489 = 541117) (by norm_num)
theorem B1081957 : Blo 638302 1081957 := bbase (se 4 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 1081957 = 202867) (by norm_num)
theorem B721525 : Blo 638302 721525 := bbase (se 5 (by rfl) ⟨33821, by rfl⟩ : syracuseStep 721525 = 67643) (by norm_num)
theorem B1442429 : Blo 638302 1442429 := bbase (se 3 (by rfl) ⟨270455, by rfl⟩ : syracuseStep 1442429 = 540911) (by norm_num)
theorem B721561 : Blo 638302 721561 := bbase (se 2 (by rfl) ⟨270585, by rfl⟩ : syracuseStep 721561 = 541171) (by norm_num)
theorem B2589349 : Blo 638302 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B721597 : Blo 638302 721597 := bbase (se 3 (by rfl) ⟨135299, by rfl⟩ : syracuseStep 721597 = 270599) (by norm_num)
theorem B1082045 : Blo 638302 1082045 := bbase (se 3 (by rfl) ⟨202883, by rfl⟩ : syracuseStep 1082045 = 405767) (by norm_num)
theorem B1442501 : Blo 638302 1442501 := bbase (se 4 (by rfl) ⟨135234, by rfl⟩ : syracuseStep 1442501 = 270469) (by norm_num)
theorem B721633 : Blo 638302 721633 := bbase (se 2 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 721633 = 541225) (by norm_num)
theorem B721669 : Blo 638302 721669 := bbase (se 4 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 721669 = 135313) (by norm_num)
theorem B1442573 : Blo 638302 1442573 := bbase (se 3 (by rfl) ⟨270482, by rfl⟩ : syracuseStep 1442573 = 540965) (by norm_num)
theorem B721705 : Blo 638302 721705 := bbase (se 2 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 721705 = 541279) (by norm_num)
theorem B2163509 : Blo 638302 2163509 := bbase (se 5 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 2163509 = 202829) (by norm_num)
theorem B1082173 : Blo 638302 1082173 := bbase (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) (by norm_num)
theorem B721741 : Blo 638302 721741 := bbase (se 3 (by rfl) ⟨135326, by rfl⟩ : syracuseStep 721741 = 270653) (by norm_num)
theorem B1442645 : Blo 638302 1442645 := bbase (se 9 (by rfl) ⟨4226, by rfl⟩ : syracuseStep 1442645 = 8453) (by norm_num)
theorem B721777 : Blo 638302 721777 := bbase (se 2 (by rfl) ⟨270666, by rfl⟩ : syracuseStep 721777 = 541333) (by norm_num)
theorem B2425733 : Blo 638302 2425733 := bbase (se 4 (by rfl) ⟨227412, by rfl⟩ : syracuseStep 2425733 = 454825) (by norm_num)
theorem B1082261 : Blo 638302 1082261 := bbase (se 6 (by rfl) ⟨25365, by rfl⟩ : syracuseStep 1082261 = 50731) (by norm_num)
theorem B721813 : Blo 638302 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B1442717 : Blo 638302 1442717 := bbase (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) (by norm_num)
theorem B721849 : Blo 638302 721849 := bbase (se 2 (by rfl) ⟨270693, by rfl⟩ : syracuseStep 721849 = 541387) (by norm_num)
theorem B721885 : Blo 638302 721885 := bbase (se 3 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 721885 = 270707) (by norm_num)
theorem B1442789 : Blo 638302 1442789 := bbase (se 4 (by rfl) ⟨135261, by rfl⟩ : syracuseStep 1442789 = 270523) (by norm_num)
theorem B721921 : Blo 638302 721921 := bbase (se 2 (by rfl) ⟨270720, by rfl⟩ : syracuseStep 721921 = 541441) (by norm_num)
theorem B1082389 : Blo 638302 1082389 := bbase (se 6 (by rfl) ⟨25368, by rfl⟩ : syracuseStep 1082389 = 50737) (by norm_num)
theorem B721957 : Blo 638302 721957 := bbase (se 4 (by rfl) ⟨67683, by rfl⟩ : syracuseStep 721957 = 135367) (by norm_num)
theorem B1442861 : Blo 638302 1442861 := bbase (se 3 (by rfl) ⟨270536, by rfl⟩ : syracuseStep 1442861 = 541073) (by norm_num)
theorem B721993 : Blo 638302 721993 := bbase (se 2 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 721993 = 541495) (by norm_num)
theorem B1082477 : Blo 638302 1082477 := bbase (se 3 (by rfl) ⟨202964, by rfl⟩ : syracuseStep 1082477 = 405929) (by norm_num)
theorem B722029 : Blo 638302 722029 := bbase (se 3 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 722029 = 270761) (by norm_num)
theorem B4097141 : Blo 638302 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B1442933 : Blo 638302 1442933 := bbase (se 5 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 1442933 = 135275) (by norm_num)
theorem B722065 : Blo 638302 722065 := bbase (se 2 (by rfl) ⟨270774, by rfl⟩ : syracuseStep 722065 = 541549) (by norm_num)
theorem B2426021 : Blo 638302 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B722101 : Blo 638302 722101 := bbase (se 5 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 722101 = 67697) (by norm_num)
theorem B1443005 : Blo 638302 1443005 := bbase (se 3 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 1443005 = 541127) (by norm_num)
theorem B722137 : Blo 638302 722137 := bbase (se 2 (by rfl) ⟨270801, by rfl⟩ : syracuseStep 722137 = 541603) (by norm_num)
theorem B2163941 : Blo 638302 2163941 := bbase (se 4 (by rfl) ⟨202869, by rfl⟩ : syracuseStep 2163941 = 405739) (by norm_num)
theorem B1082605 : Blo 638302 1082605 := bbase (se 3 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 1082605 = 405977) (by norm_num)
theorem B722173 : Blo 638302 722173 := bbase (se 3 (by rfl) ⟨135407, by rfl⟩ : syracuseStep 722173 = 270815) (by norm_num)
theorem B1443077 : Blo 638302 1443077 := bbase (se 4 (by rfl) ⟨135288, by rfl⟩ : syracuseStep 1443077 = 270577) (by norm_num)
theorem B1213717 : Blo 638302 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B722209 : Blo 638302 722209 := bbase (se 2 (by rfl) ⟨270828, by rfl⟩ : syracuseStep 722209 = 541657) (by norm_num)
theorem B1082693 : Blo 638302 1082693 := bbase (se 4 (by rfl) ⟨101502, by rfl⟩ : syracuseStep 1082693 = 203005) (by norm_num)
theorem B722245 : Blo 638302 722245 := bbase (se 4 (by rfl) ⟨67710, by rfl⟩ : syracuseStep 722245 = 135421) (by norm_num)
theorem B1443149 : Blo 638302 1443149 := bbase (se 3 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 1443149 = 541181) (by norm_num)
theorem B7996757 : Blo 638302 7996757 := bbase (se 12 (by rfl) ⟨2928, by rfl⟩ : syracuseStep 7996757 = 5857) (by norm_num)
theorem B722281 : Blo 638302 722281 := bbase (se 2 (by rfl) ⟨270855, by rfl⟩ : syracuseStep 722281 = 541711) (by norm_num)
theorem B722317 : Blo 638302 722317 := bbase (se 3 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 722317 = 270869) (by norm_num)
theorem B1443221 : Blo 638302 1443221 := bbase (se 6 (by rfl) ⟨33825, by rfl⟩ : syracuseStep 1443221 = 67651) (by norm_num)
theorem B1213861 : Blo 638302 1213861 := bbase (se 4 (by rfl) ⟨113799, by rfl⟩ : syracuseStep 1213861 = 227599) (by norm_num)
theorem B722353 : Blo 638302 722353 := bbase (se 2 (by rfl) ⟨270882, by rfl⟩ : syracuseStep 722353 = 541765) (by norm_num)
theorem B1082821 : Blo 638302 1082821 := bbase (se 4 (by rfl) ⟨101514, by rfl⟩ : syracuseStep 1082821 = 203029) (by norm_num)
theorem B722389 : Blo 638302 722389 := bbase (se 7 (by rfl) ⟨8465, by rfl⟩ : syracuseStep 722389 = 16931) (by norm_num)
theorem B8455637 : Blo 638302 8455637 := bbase (se 7 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 8455637 = 198179) (by norm_num)
theorem B1443293 : Blo 638302 1443293 := bbase (se 3 (by rfl) ⟨270617, by rfl⟩ : syracuseStep 1443293 = 541235) (by norm_num)
theorem B722425 : Blo 638302 722425 := bbase (se 2 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 722425 = 541819) (by norm_num)
theorem B1082909 : Blo 638302 1082909 := bbase (se 3 (by rfl) ⟨203045, by rfl⟩ : syracuseStep 1082909 = 406091) (by norm_num)
theorem B722461 : Blo 638302 722461 := bbase (se 3 (by rfl) ⟨135461, by rfl⟩ : syracuseStep 722461 = 270923) (by norm_num)
theorem B1443365 : Blo 638302 1443365 := bbase (se 4 (by rfl) ⟨135315, by rfl⟩ : syracuseStep 1443365 = 270631) (by norm_num)
theorem B722497 : Blo 638302 722497 := bbase (se 2 (by rfl) ⟨270936, by rfl⟩ : syracuseStep 722497 = 541873) (by norm_num)
theorem B1214021 : Blo 638302 1214021 := bbase (se 4 (by rfl) ⟨113814, by rfl⟩ : syracuseStep 1214021 = 227629) (by norm_num)
theorem B3245669 : Blo 638302 3245669 := bbase (se 4 (by rfl) ⟨304281, by rfl⟩ : syracuseStep 3245669 = 608563) (by norm_num)
theorem B722533 : Blo 638302 722533 := bbase (se 4 (by rfl) ⟨67737, by rfl⟩ : syracuseStep 722533 = 135475) (by norm_num)
theorem B1443437 : Blo 638302 1443437 := bbase (se 3 (by rfl) ⟨270644, by rfl⟩ : syracuseStep 1443437 = 541289) (by norm_num)
theorem B722569 : Blo 638302 722569 := bbase (se 2 (by rfl) ⟨270963, by rfl⟩ : syracuseStep 722569 = 541927) (by norm_num)
theorem B1312405 : Blo 638302 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2164373 : Blo 638302 2164373 := bbase (se 6 (by rfl) ⟨50727, by rfl⟩ : syracuseStep 2164373 = 101455) (by norm_num)
theorem B1083037 : Blo 638302 1083037 := bbase (se 3 (by rfl) ⟨203069, by rfl⟩ : syracuseStep 1083037 = 406139) (by norm_num)
theorem B1443509 : Blo 638302 1443509 := bbase (se 5 (by rfl) ⟨67664, by rfl⟩ : syracuseStep 1443509 = 135329) (by norm_num)
theorem B1640125 : Blo 638302 1640125 := bbase (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) (by norm_num)
theorem B1214165 : Blo 638302 1214165 := bbase (se 7 (by rfl) ⟨14228, by rfl⟩ : syracuseStep 1214165 = 28457) (by norm_num)
theorem B1083125 : Blo 638302 1083125 := bbase (se 5 (by rfl) ⟨50771, by rfl⟩ : syracuseStep 1083125 = 101543) (by norm_num)
theorem B1443581 : Blo 638302 1443581 := bbase (se 3 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 1443581 = 541343) (by norm_num)
theorem B2590517 : Blo 638302 2590517 := bbase (se 5 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 2590517 = 242861) (by norm_num)
theorem B1443653 : Blo 638302 1443653 := bbase (se 4 (by rfl) ⟨135342, by rfl⟩ : syracuseStep 1443653 = 270685) (by norm_num)
theorem B952141 : Blo 638302 952141 := bbase (se 3 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 952141 = 357053) (by norm_num)
theorem B1083253 : Blo 638302 1083253 := bbase (se 5 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 1083253 = 101555) (by norm_num)
theorem B1443725 : Blo 638302 1443725 := bbase (se 3 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 1443725 = 541397) (by norm_num)
theorem B1083341 : Blo 638302 1083341 := bbase (se 3 (by rfl) ⟨203126, by rfl⟩ : syracuseStep 1083341 = 406253) (by norm_num)
theorem B1443797 : Blo 638302 1443797 := bbase (se 7 (by rfl) ⟨16919, by rfl⟩ : syracuseStep 1443797 = 33839) (by norm_num)
theorem B1214453 : Blo 638302 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B1476605 : Blo 638302 1476605 := bbase (se 3 (by rfl) ⟨276863, by rfl⟩ : syracuseStep 1476605 = 553727) (by norm_num)
theorem B1443869 : Blo 638302 1443869 := bbase (se 3 (by rfl) ⟨270725, by rfl⟩ : syracuseStep 1443869 = 541451) (by norm_num)
theorem B2164805 : Blo 638302 2164805 := bbase (se 4 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 2164805 = 405901) (by norm_num)
theorem B1083469 : Blo 638302 1083469 := bbase (se 3 (by rfl) ⟨203150, by rfl⟩ : syracuseStep 1083469 = 406301) (by norm_num)
theorem B1443941 : Blo 638302 1443941 := bbase (se 4 (by rfl) ⟨135369, by rfl⟩ : syracuseStep 1443941 = 270739) (by norm_num)
theorem B6228085 : Blo 638302 6228085 := bbase (se 5 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 6228085 = 583883) (by norm_num)
theorem B3082373 : Blo 638302 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B1214605 : Blo 638302 1214605 := bbase (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) (by norm_num)
theorem B1083557 : Blo 638302 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B1444013 : Blo 638302 1444013 := bbase (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) (by norm_num)
theorem B1444085 : Blo 638302 1444085 := bbase (se 5 (by rfl) ⟨67691, by rfl⟩ : syracuseStep 1444085 = 135383) (by norm_num)
theorem B1083685 : Blo 638302 1083685 := bbase (se 4 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 1083685 = 203191) (by norm_num)
theorem B1640749 : Blo 638302 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B1444157 : Blo 638302 1444157 := bbase (se 3 (by rfl) ⟨270779, by rfl⟩ : syracuseStep 1444157 = 541559) (by norm_num)
theorem B2427205 : Blo 638302 2427205 := bbase (se 4 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 2427205 = 455101) (by norm_num)
theorem B1083773 : Blo 638302 1083773 := bbase (se 3 (by rfl) ⟨203207, by rfl⟩ : syracuseStep 1083773 = 406415) (by norm_num)
theorem B1444229 : Blo 638302 1444229 := bbase (se 4 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 1444229 = 270793) (by norm_num)
theorem B1214909 : Blo 638302 1214909 := bbase (se 3 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 1214909 = 455591) (by norm_num)
theorem B1444301 : Blo 638302 1444301 := bbase (se 3 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 1444301 = 541613) (by norm_num)
theorem B2165237 : Blo 638302 2165237 := bbase (se 5 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 2165237 = 202991) (by norm_num)
theorem B1444373 : Blo 638302 1444373 := bbase (se 6 (by rfl) ⟨33852, by rfl⟩ : syracuseStep 1444373 = 67705) (by norm_num)
theorem B1444445 : Blo 638302 1444445 := bbase (se 3 (by rfl) ⟨270833, by rfl⟩ : syracuseStep 1444445 = 541667) (by norm_num)
theorem B821873 : Blo 638302 821873 := bbase (se 2 (by rfl) ⟨308202, by rfl⟩ : syracuseStep 821873 = 616405) (by norm_num)
theorem B2427509 : Blo 638302 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B1444517 : Blo 638302 1444517 := bbase (se 4 (by rfl) ⟨135423, by rfl⟩ : syracuseStep 1444517 = 270847) (by norm_num)
theorem B1444589 : Blo 638302 1444589 := bbase (se 3 (by rfl) ⟨270860, by rfl⟩ : syracuseStep 1444589 = 541721) (by norm_num)
theorem B1542925 : Blo 638302 1542925 := bbase (se 3 (by rfl) ⟨289298, by rfl⟩ : syracuseStep 1542925 = 578597) (by norm_num)
theorem B822037 : Blo 638302 822037 := bbase (se 6 (by rfl) ⟨19266, by rfl⟩ : syracuseStep 822037 = 38533) (by norm_num)
theorem B658217 : Blo 638302 658217 := bbase (se 2 (by rfl) ⟨246831, by rfl⟩ : syracuseStep 658217 = 493663) (by norm_num)
theorem B1444661 : Blo 638302 1444661 := bbase (se 5 (by rfl) ⟨67718, by rfl⟩ : syracuseStep 1444661 = 135437) (by norm_num)
theorem B3246965 : Blo 638302 3246965 := bbase (se 5 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 3246965 = 304403) (by norm_num)
theorem B1444733 : Blo 638302 1444733 := bbase (se 3 (by rfl) ⟨270887, by rfl⟩ : syracuseStep 1444733 = 541775) (by norm_num)
theorem B2165669 : Blo 638302 2165669 := bbase (se 4 (by rfl) ⟨203031, by rfl⟩ : syracuseStep 2165669 = 406063) (by norm_num)
theorem B1444805 : Blo 638302 1444805 := bbase (se 4 (by rfl) ⟨135450, by rfl⟩ : syracuseStep 1444805 = 270901) (by norm_num)
theorem B1543117 : Blo 638302 1543117 := bbase (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) (by norm_num)
theorem B1543157 : Blo 638302 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B1444877 : Blo 638302 1444877 := bbase (se 3 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 1444877 = 541829) (by norm_num)
theorem B1444949 : Blo 638302 1444949 := bbase (se 8 (by rfl) ⟨8466, by rfl⟩ : syracuseStep 1444949 = 16933) (by norm_num)
theorem B1445021 : Blo 638302 1445021 := bbase (se 3 (by rfl) ⟨270941, by rfl⟩ : syracuseStep 1445021 = 541883) (by norm_num)
theorem B1215661 : Blo 638302 1215661 := bbase (se 3 (by rfl) ⟨227936, by rfl⟩ : syracuseStep 1215661 = 455873) (by norm_num)
theorem B1445093 : Blo 638302 1445093 := bbase (se 4 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 1445093 = 270955) (by norm_num)
theorem B1445165 : Blo 638302 1445165 := bbase (se 3 (by rfl) ⟨270968, by rfl⟩ : syracuseStep 1445165 = 541937) (by norm_num)
theorem B1215805 : Blo 638302 1215805 := bbase (se 3 (by rfl) ⟨227963, by rfl⟩ : syracuseStep 1215805 = 455927) (by norm_num)
theorem B2166101 : Blo 638302 2166101 := bbase (se 11 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 2166101 = 3173) (by norm_num)
theorem B5475701 : Blo 638302 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B7769557 : Blo 638302 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B1641941 : Blo 638302 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B1215965 : Blo 638302 1215965 := bbase (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) (by norm_num)
theorem B4918805 : Blo 638302 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B1216109 : Blo 638302 1216109 := bbase (se 3 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 1216109 = 456041) (by norm_num)
theorem B2166533 : Blo 638302 2166533 := bbase (se 4 (by rfl) ⟨203112, by rfl⟩ : syracuseStep 2166533 = 406225) (by norm_num)
theorem B1216397 : Blo 638302 1216397 := bbase (se 3 (by rfl) ⟨228074, by rfl⟩ : syracuseStep 1216397 = 456149) (by norm_num)
theorem B1216549 : Blo 638302 1216549 := bbase (se 4 (by rfl) ⟨114051, by rfl⟩ : syracuseStep 1216549 = 228103) (by norm_num)
theorem B1478741 : Blo 638302 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B3084389 : Blo 638302 3084389 := bbase (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) (by norm_num)
theorem B3248261 : Blo 638302 3248261 := bbase (se 4 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 3248261 = 609049) (by norm_num)
theorem B2166965 : Blo 638302 2166965 := bbase (se 5 (by rfl) ⟨101576, by rfl⟩ : syracuseStep 2166965 = 203153) (by norm_num)
theorem B3084581 : Blo 638302 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B5902645 : Blo 638302 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B1216853 : Blo 638302 1216853 := bbase (se 10 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 1216853 = 3565) (by norm_num)
theorem B2167397 : Blo 638302 2167397 := bbase (se 4 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 2167397 = 406387) (by norm_num)
theorem B2429621 : Blo 638302 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B2429909 : Blo 638302 2429909 := bbase (se 7 (by rfl) ⟨28475, by rfl⟩ : syracuseStep 2429909 = 56951) (by norm_num)
theorem B693317 : Blo 638302 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B1217605 : Blo 638302 1217605 := bbase (se 4 (by rfl) ⟨114150, by rfl⟩ : syracuseStep 1217605 = 228301) (by norm_num)
theorem B1217749 : Blo 638302 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B922853 : Blo 638302 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B3642677 : Blo 638302 3642677 := bbase (se 5 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 3642677 = 341501) (by norm_num)
theorem B1217909 : Blo 638302 1217909 := bbase (se 5 (by rfl) ⟨57089, by rfl⟩ : syracuseStep 1217909 = 114179) (by norm_num)
theorem B3249557 : Blo 638302 3249557 := bbase (se 6 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 3249557 = 152323) (by norm_num)
theorem B1480117 : Blo 638302 1480117 := bbase (se 5 (by rfl) ⟨69380, by rfl⟩ : syracuseStep 1480117 = 138761) (by norm_num)
theorem B1218053 : Blo 638302 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B3282565 : Blo 638302 3282565 := bbase (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) (by norm_num)
theorem B1152797 : Blo 638302 1152797 := bbase (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) (by norm_num)
theorem B1218341 : Blo 638302 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B4626325 : Blo 638302 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B1218493 : Blo 638302 1218493 := bbase (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) (by norm_num)
theorem B694261 : Blo 638302 694261 := bbase (se 5 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 694261 = 65087) (by norm_num)
theorem B2922581 : Blo 638302 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B2431093 : Blo 638302 2431093 := bbase (se 5 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 2431093 = 227915) (by norm_num)
theorem B1218797 : Blo 638302 1218797 := bbase (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) (by norm_num)
theorem B5478677 : Blo 638302 5478677 := bbase (se 6 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 5478677 = 256813) (by norm_num)
theorem B2431397 : Blo 638302 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B1055285 : Blo 638302 1055285 := bbase (se 5 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 1055285 = 98933) (by norm_num)
theorem B3250853 : Blo 638302 3250853 := bbase (se 4 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 3250853 = 609535) (by norm_num)
theorem B1022645 : Blo 638302 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B1153757 : Blo 638302 1153757 := bbase (se 3 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 1153757 = 432659) (by norm_num)
theorem B4856597 : Blo 638302 4856597 := bbase (se 6 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 4856597 = 227653) (by norm_num)
theorem B4102933 : Blo 638302 4102933 := bbase (se 6 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 4102933 = 192325) (by norm_num)
theorem B1481509 : Blo 638302 1481509 := bbase (se 4 (by rfl) ⟨138891, by rfl⟩ : syracuseStep 1481509 = 277783) (by norm_num)
theorem B2923381 : Blo 638302 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B957461 : Blo 638302 957461 := bbase (se 6 (by rfl) ⟨22440, by rfl⟩ : syracuseStep 957461 = 44881) (by norm_num)
theorem B957485 : Blo 638302 957485 := bbase (se 3 (by rfl) ⟨179528, by rfl⟩ : syracuseStep 957485 = 359057) (by norm_num)
theorem B957509 : Blo 638302 957509 := bbase (se 4 (by rfl) ⟨89766, by rfl⟩ : syracuseStep 957509 = 179533) (by norm_num)
theorem B957533 : Blo 638302 957533 := bbase (se 3 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 957533 = 359075) (by norm_num)
theorem B957557 : Blo 638302 957557 := bbase (se 5 (by rfl) ⟨44885, by rfl⟩ : syracuseStep 957557 = 89771) (by norm_num)
theorem B1023101 : Blo 638302 1023101 := bbase (se 3 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 1023101 = 383663) (by norm_num)
theorem B957581 : Blo 638302 957581 := bbase (se 3 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 957581 = 359093) (by norm_num)
theorem B957605 : Blo 638302 957605 := bbase (se 4 (by rfl) ⟨89775, by rfl⟩ : syracuseStep 957605 = 179551) (by norm_num)
theorem B957629 : Blo 638302 957629 := bbase (se 3 (by rfl) ⟨179555, by rfl⟩ : syracuseStep 957629 = 359111) (by norm_num)
theorem B957653 : Blo 638302 957653 := bbase (se 7 (by rfl) ⟨11222, by rfl⟩ : syracuseStep 957653 = 22445) (by norm_num)
theorem B957677 : Blo 638302 957677 := bbase (se 3 (by rfl) ⟨179564, by rfl⟩ : syracuseStep 957677 = 359129) (by norm_num)
theorem B957701 : Blo 638302 957701 := bbase (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) (by norm_num)
theorem B1187093 : Blo 638302 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B957725 : Blo 638302 957725 := bbase (se 3 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 957725 = 359147) (by norm_num)
theorem B957749 : Blo 638302 957749 := bbase (se 5 (by rfl) ⟨44894, by rfl⟩ : syracuseStep 957749 = 89789) (by norm_num)
theorem B957773 : Blo 638302 957773 := bbase (se 3 (by rfl) ⟨179582, by rfl⟩ : syracuseStep 957773 = 359165) (by norm_num)
theorem B7806293 : Blo 638302 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B957797 : Blo 638302 957797 := bbase (se 4 (by rfl) ⟨89793, by rfl⟩ : syracuseStep 957797 = 179587) (by norm_num)
theorem B957821 : Blo 638302 957821 := bbase (se 3 (by rfl) ⟨179591, by rfl⟩ : syracuseStep 957821 = 359183) (by norm_num)
theorem B957845 : Blo 638302 957845 := bbase (se 6 (by rfl) ⟨22449, by rfl⟩ : syracuseStep 957845 = 44899) (by norm_num)
theorem B957869 : Blo 638302 957869 := bbase (se 3 (by rfl) ⟨179600, by rfl⟩ : syracuseStep 957869 = 359201) (by norm_num)
theorem B957893 : Blo 638302 957893 := bbase (se 4 (by rfl) ⟨89802, by rfl⟩ : syracuseStep 957893 = 179605) (by norm_num)
theorem B957917 : Blo 638302 957917 := bbase (se 3 (by rfl) ⟨179609, by rfl⟩ : syracuseStep 957917 = 359219) (by norm_num)
theorem B1646045 : Blo 638302 1646045 := bbase (se 3 (by rfl) ⟨308633, by rfl⟩ : syracuseStep 1646045 = 617267) (by norm_num)
theorem B957941 : Blo 638302 957941 := bbase (se 5 (by rfl) ⟨44903, by rfl⟩ : syracuseStep 957941 = 89807) (by norm_num)
theorem B1383925 : Blo 638302 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B957965 : Blo 638302 957965 := bbase (se 3 (by rfl) ⟨179618, by rfl⟩ : syracuseStep 957965 = 359237) (by norm_num)
theorem B4562453 : Blo 638302 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B957989 : Blo 638302 957989 := bbase (se 4 (by rfl) ⟨89811, by rfl⟩ : syracuseStep 957989 = 179623) (by norm_num)
theorem B958013 : Blo 638302 958013 := bbase (se 3 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 958013 = 359255) (by norm_num)
theorem B958037 : Blo 638302 958037 := bbase (se 8 (by rfl) ⟨5613, by rfl⟩ : syracuseStep 958037 = 11227) (by norm_num)
theorem B958061 : Blo 638302 958061 := bbase (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) (by norm_num)
theorem B728689 : Blo 638302 728689 := bbase (se 2 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 728689 = 546517) (by norm_num)
theorem B958085 : Blo 638302 958085 := bbase (se 4 (by rfl) ⟨89820, by rfl⟩ : syracuseStep 958085 = 179641) (by norm_num)
theorem B958109 : Blo 638302 958109 := bbase (se 3 (by rfl) ⟨179645, by rfl⟩ : syracuseStep 958109 = 359291) (by norm_num)
theorem B958133 : Blo 638302 958133 := bbase (se 5 (by rfl) ⟨44912, by rfl⟩ : syracuseStep 958133 = 89825) (by norm_num)
theorem B958157 : Blo 638302 958157 := bbase (se 3 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 958157 = 359309) (by norm_num)
theorem B958181 : Blo 638302 958181 := bbase (se 4 (by rfl) ⟨89829, by rfl⟩ : syracuseStep 958181 = 179659) (by norm_num)
theorem B958205 : Blo 638302 958205 := bbase (se 3 (by rfl) ⟨179663, by rfl⟩ : syracuseStep 958205 = 359327) (by norm_num)
theorem B1646333 : Blo 638302 1646333 := bbase (se 3 (by rfl) ⟨308687, by rfl⟩ : syracuseStep 1646333 = 617375) (by norm_num)
theorem B958229 : Blo 638302 958229 := bbase (se 6 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 958229 = 44917) (by norm_num)
theorem B2629397 : Blo 638302 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B958253 : Blo 638302 958253 := bbase (se 3 (by rfl) ⟨179672, by rfl⟩ : syracuseStep 958253 = 359345) (by norm_num)
theorem B958277 : Blo 638302 958277 := bbase (se 4 (by rfl) ⟨89838, by rfl⟩ : syracuseStep 958277 = 179677) (by norm_num)
theorem B958301 : Blo 638302 958301 := bbase (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) (by norm_num)
theorem B958325 : Blo 638302 958325 := bbase (se 5 (by rfl) ⟨44921, by rfl⟩ : syracuseStep 958325 = 89843) (by norm_num)
theorem B958349 : Blo 638302 958349 := bbase (se 3 (by rfl) ⟨179690, by rfl⟩ : syracuseStep 958349 = 359381) (by norm_num)
theorem B958373 : Blo 638302 958373 := bbase (se 4 (by rfl) ⟨89847, by rfl⟩ : syracuseStep 958373 = 179695) (by norm_num)
theorem B1154989 : Blo 638302 1154989 := bbase (se 3 (by rfl) ⟨216560, by rfl⟩ : syracuseStep 1154989 = 433121) (by norm_num)
theorem B958397 : Blo 638302 958397 := bbase (se 3 (by rfl) ⟨179699, by rfl⟩ : syracuseStep 958397 = 359399) (by norm_num)
theorem B958421 : Blo 638302 958421 := bbase (se 7 (by rfl) ⟨11231, by rfl⟩ : syracuseStep 958421 = 22463) (by norm_num)
theorem B958445 : Blo 638302 958445 := bbase (se 3 (by rfl) ⟨179708, by rfl⟩ : syracuseStep 958445 = 359417) (by norm_num)
theorem B958469 : Blo 638302 958469 := bbase (se 4 (by rfl) ⟨89856, by rfl⟩ : syracuseStep 958469 = 179713) (by norm_num)
theorem B7282709 : Blo 638302 7282709 := bbase (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) (by norm_num)
theorem B958493 : Blo 638302 958493 := bbase (se 3 (by rfl) ⟨179717, by rfl⟩ : syracuseStep 958493 = 359435) (by norm_num)
theorem B3285029 : Blo 638302 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B958517 : Blo 638302 958517 := bbase (se 5 (by rfl) ⟨44930, by rfl⟩ : syracuseStep 958517 = 89861) (by norm_num)
theorem B958541 : Blo 638302 958541 := bbase (se 3 (by rfl) ⟨179726, by rfl⟩ : syracuseStep 958541 = 359453) (by norm_num)
theorem B1024093 : Blo 638302 1024093 := bbase (se 3 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 1024093 = 384035) (by norm_num)
theorem B958565 : Blo 638302 958565 := bbase (se 4 (by rfl) ⟨89865, by rfl⟩ : syracuseStep 958565 = 179731) (by norm_num)
theorem B958589 : Blo 638302 958589 := bbase (se 3 (by rfl) ⟨179735, by rfl⟩ : syracuseStep 958589 = 359471) (by norm_num)
theorem B958613 : Blo 638302 958613 := bbase (se 6 (by rfl) ⟨22467, by rfl⟩ : syracuseStep 958613 = 44935) (by norm_num)
theorem B958637 : Blo 638302 958637 := bbase (se 3 (by rfl) ⟨179744, by rfl⟩ : syracuseStep 958637 = 359489) (by norm_num)
theorem B958661 : Blo 638302 958661 := bbase (se 4 (by rfl) ⟨89874, by rfl⟩ : syracuseStep 958661 = 179749) (by norm_num)
theorem B4923605 : Blo 638302 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B958685 : Blo 638302 958685 := bbase (se 3 (by rfl) ⟨179753, by rfl⟩ : syracuseStep 958685 = 359507) (by norm_num)
theorem B2728181 : Blo 638302 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B958709 : Blo 638302 958709 := bbase (se 5 (by rfl) ⟨44939, by rfl⟩ : syracuseStep 958709 = 89879) (by norm_num)
theorem B958733 : Blo 638302 958733 := bbase (se 3 (by rfl) ⟨179762, by rfl⟩ : syracuseStep 958733 = 359525) (by norm_num)
theorem B958757 : Blo 638302 958757 := bbase (se 4 (by rfl) ⟨89883, by rfl⟩ : syracuseStep 958757 = 179767) (by norm_num)
theorem B958781 : Blo 638302 958781 := bbase (se 3 (by rfl) ⟨179771, by rfl⟩ : syracuseStep 958781 = 359543) (by norm_num)
theorem B958805 : Blo 638302 958805 := bbase (se 10 (by rfl) ⟨1404, by rfl⟩ : syracuseStep 958805 = 2809) (by norm_num)
theorem B958829 : Blo 638302 958829 := bbase (se 3 (by rfl) ⟨179780, by rfl⟩ : syracuseStep 958829 = 359561) (by norm_num)
theorem B958853 : Blo 638302 958853 := bbase (se 4 (by rfl) ⟨89892, by rfl⟩ : syracuseStep 958853 = 179785) (by norm_num)
theorem B958877 : Blo 638302 958877 := bbase (se 3 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 958877 = 359579) (by norm_num)
theorem B958901 : Blo 638302 958901 := bbase (se 5 (by rfl) ⟨44948, by rfl⟩ : syracuseStep 958901 = 89897) (by norm_num)
theorem B1647029 : Blo 638302 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B958925 : Blo 638302 958925 := bbase (se 3 (by rfl) ⟨179798, by rfl⟩ : syracuseStep 958925 = 359597) (by norm_num)
theorem B958949 : Blo 638302 958949 := bbase (se 4 (by rfl) ⟨89901, by rfl⟩ : syracuseStep 958949 = 179803) (by norm_num)
theorem B2433509 : Blo 638302 2433509 := bbase (se 4 (by rfl) ⟨228141, by rfl⟩ : syracuseStep 2433509 = 456283) (by norm_num)
theorem B958973 : Blo 638302 958973 := bbase (se 3 (by rfl) ⟨179807, by rfl⟩ : syracuseStep 958973 = 359615) (by norm_num)
theorem B958997 : Blo 638302 958997 := bbase (se 6 (by rfl) ⟨22476, by rfl⟩ : syracuseStep 958997 = 44953) (by norm_num)
theorem B959021 : Blo 638302 959021 := bbase (se 3 (by rfl) ⟨179816, by rfl⟩ : syracuseStep 959021 = 359633) (by norm_num)
theorem B959045 : Blo 638302 959045 := bbase (se 4 (by rfl) ⟨89910, by rfl⟩ : syracuseStep 959045 = 179821) (by norm_num)
theorem B959069 : Blo 638302 959069 := bbase (se 3 (by rfl) ⟨179825, by rfl⟩ : syracuseStep 959069 = 359651) (by norm_num)
theorem B959093 : Blo 638302 959093 := bbase (se 5 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 959093 = 89915) (by norm_num)
theorem B959117 : Blo 638302 959117 := bbase (se 3 (by rfl) ⟨179834, by rfl⟩ : syracuseStep 959117 = 359669) (by norm_num)
theorem B959141 : Blo 638302 959141 := bbase (se 4 (by rfl) ⟨89919, by rfl⟩ : syracuseStep 959141 = 179839) (by norm_num)
theorem B959165 : Blo 638302 959165 := bbase (se 3 (by rfl) ⟨179843, by rfl⟩ : syracuseStep 959165 = 359687) (by norm_num)
theorem B959189 : Blo 638302 959189 := bbase (se 7 (by rfl) ⟨11240, by rfl⟩ : syracuseStep 959189 = 22481) (by norm_num)
theorem B1024741 : Blo 638302 1024741 := bbase (se 4 (by rfl) ⟨96069, by rfl⟩ : syracuseStep 1024741 = 192139) (by norm_num)
theorem B959213 : Blo 638302 959213 := bbase (se 3 (by rfl) ⟨179852, by rfl⟩ : syracuseStep 959213 = 359705) (by norm_num)
theorem B959237 : Blo 638302 959237 := bbase (se 4 (by rfl) ⟨89928, by rfl⟩ : syracuseStep 959237 = 179857) (by norm_num)
theorem B2433797 : Blo 638302 2433797 := bbase (se 4 (by rfl) ⟨228168, by rfl⟩ : syracuseStep 2433797 = 456337) (by norm_num)
theorem B959261 : Blo 638302 959261 := bbase (se 3 (by rfl) ⟨179861, by rfl⟩ : syracuseStep 959261 = 359723) (by norm_num)
theorem B959285 : Blo 638302 959285 := bbase (se 5 (by rfl) ⟨44966, by rfl⟩ : syracuseStep 959285 = 89933) (by norm_num)
theorem B959309 : Blo 638302 959309 := bbase (se 3 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 959309 = 359741) (by norm_num)
theorem B959333 : Blo 638302 959333 := bbase (se 4 (by rfl) ⟨89937, by rfl⟩ : syracuseStep 959333 = 179875) (by norm_num)
theorem B959357 : Blo 638302 959357 := bbase (se 3 (by rfl) ⟨179879, by rfl⟩ : syracuseStep 959357 = 359759) (by norm_num)
theorem B959381 : Blo 638302 959381 := bbase (se 6 (by rfl) ⟨22485, by rfl⟩ : syracuseStep 959381 = 44971) (by norm_num)
theorem B959405 : Blo 638302 959405 := bbase (se 3 (by rfl) ⟨179888, by rfl⟩ : syracuseStep 959405 = 359777) (by norm_num)
theorem B2302901 : Blo 638302 2302901 := bbase (se 5 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 2302901 = 215897) (by norm_num)
theorem B959429 : Blo 638302 959429 := bbase (se 4 (by rfl) ⟨89946, by rfl⟩ : syracuseStep 959429 = 179893) (by norm_num)
theorem B959453 : Blo 638302 959453 := bbase (se 3 (by rfl) ⟨179897, by rfl⟩ : syracuseStep 959453 = 359795) (by norm_num)
theorem B1942501 : Blo 638302 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B959477 : Blo 638302 959477 := bbase (se 5 (by rfl) ⟨44975, by rfl⟩ : syracuseStep 959477 = 89951) (by norm_num)
theorem B959501 : Blo 638302 959501 := bbase (se 3 (by rfl) ⟨179906, by rfl⟩ : syracuseStep 959501 = 359813) (by norm_num)
theorem B959525 : Blo 638302 959525 := bbase (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) (by norm_num)
theorem B959549 : Blo 638302 959549 := bbase (se 3 (by rfl) ⟨179915, by rfl⟩ : syracuseStep 959549 = 359831) (by norm_num)
theorem B959573 : Blo 638302 959573 := bbase (se 8 (by rfl) ⟨5622, by rfl⟩ : syracuseStep 959573 = 11245) (by norm_num)
theorem B959597 : Blo 638302 959597 := bbase (se 3 (by rfl) ⟨179924, by rfl⟩ : syracuseStep 959597 = 359849) (by norm_num)
theorem B959621 : Blo 638302 959621 := bbase (se 4 (by rfl) ⟨89964, by rfl⟩ : syracuseStep 959621 = 179929) (by norm_num)
theorem B959645 : Blo 638302 959645 := bbase (se 3 (by rfl) ⟨179933, by rfl⟩ : syracuseStep 959645 = 359867) (by norm_num)
theorem B959669 : Blo 638302 959669 := bbase (se 5 (by rfl) ⟨44984, by rfl⟩ : syracuseStep 959669 = 89969) (by norm_num)
theorem B959693 : Blo 638302 959693 := bbase (se 3 (by rfl) ⟨179942, by rfl⟩ : syracuseStep 959693 = 359885) (by norm_num)
theorem B959717 : Blo 638302 959717 := bbase (se 4 (by rfl) ⟨89973, by rfl⟩ : syracuseStep 959717 = 179947) (by norm_num)
theorem B3122405 : Blo 638302 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B959741 : Blo 638302 959741 := bbase (se 3 (by rfl) ⟨179951, by rfl⟩ : syracuseStep 959741 = 359903) (by norm_num)
theorem B959765 : Blo 638302 959765 := bbase (se 6 (by rfl) ⟨22494, by rfl⟩ : syracuseStep 959765 = 44989) (by norm_num)
theorem B1156373 : Blo 638302 1156373 := bbase (se 6 (by rfl) ⟨27102, by rfl⟩ : syracuseStep 1156373 = 54205) (by norm_num)
theorem B959789 : Blo 638302 959789 := bbase (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) (by norm_num)
theorem B959813 : Blo 638302 959813 := bbase (se 4 (by rfl) ⟨89982, by rfl⟩ : syracuseStep 959813 = 179965) (by norm_num)
theorem B959837 : Blo 638302 959837 := bbase (se 3 (by rfl) ⟨179969, by rfl⟩ : syracuseStep 959837 = 359939) (by norm_num)
theorem B1156445 : Blo 638302 1156445 := bbase (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) (by norm_num)
theorem B959861 : Blo 638302 959861 := bbase (se 5 (by rfl) ⟨44993, by rfl⟩ : syracuseStep 959861 = 89987) (by norm_num)
theorem B959885 : Blo 638302 959885 := bbase (se 3 (by rfl) ⟨179978, by rfl⟩ : syracuseStep 959885 = 359957) (by norm_num)
theorem B959909 : Blo 638302 959909 := bbase (se 4 (by rfl) ⟨89991, by rfl⟩ : syracuseStep 959909 = 179983) (by norm_num)
theorem B959933 : Blo 638302 959933 := bbase (se 3 (by rfl) ⟨179987, by rfl⟩ : syracuseStep 959933 = 359975) (by norm_num)
theorem B959957 : Blo 638302 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B959981 : Blo 638302 959981 := bbase (se 3 (by rfl) ⟨179996, by rfl⟩ : syracuseStep 959981 = 359993) (by norm_num)
theorem B1156589 : Blo 638302 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B2303477 : Blo 638302 2303477 := bbase (se 5 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 2303477 = 215951) (by norm_num)
theorem B960005 : Blo 638302 960005 := bbase (se 4 (by rfl) ⟨90000, by rfl⟩ : syracuseStep 960005 = 180001) (by norm_num)
theorem B960029 : Blo 638302 960029 := bbase (se 3 (by rfl) ⟨180005, by rfl⟩ : syracuseStep 960029 = 360011) (by norm_num)
theorem B960053 : Blo 638302 960053 := bbase (se 5 (by rfl) ⟨45002, by rfl⟩ : syracuseStep 960053 = 90005) (by norm_num)
theorem B960077 : Blo 638302 960077 := bbase (se 3 (by rfl) ⟨180014, by rfl⟩ : syracuseStep 960077 = 360029) (by norm_num)
theorem B960101 : Blo 638302 960101 := bbase (se 4 (by rfl) ⟨90009, by rfl⟩ : syracuseStep 960101 = 180019) (by norm_num)
theorem B1975909 : Blo 638302 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B960125 : Blo 638302 960125 := bbase (se 3 (by rfl) ⟨180023, by rfl⟩ : syracuseStep 960125 = 360047) (by norm_num)
theorem B1025669 : Blo 638302 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B960149 : Blo 638302 960149 := bbase (se 6 (by rfl) ⟨22503, by rfl⟩ : syracuseStep 960149 = 45007) (by norm_num)
theorem B960173 : Blo 638302 960173 := bbase (se 3 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 960173 = 360065) (by norm_num)
theorem B960197 : Blo 638302 960197 := bbase (se 4 (by rfl) ⟨90018, by rfl⟩ : syracuseStep 960197 = 180037) (by norm_num)
theorem B960221 : Blo 638302 960221 := bbase (se 3 (by rfl) ⟨180041, by rfl⟩ : syracuseStep 960221 = 360083) (by norm_num)
theorem B960245 : Blo 638302 960245 := bbase (se 5 (by rfl) ⟨45011, by rfl⟩ : syracuseStep 960245 = 90023) (by norm_num)
theorem B960269 : Blo 638302 960269 := bbase (se 3 (by rfl) ⟨180050, by rfl⟩ : syracuseStep 960269 = 360101) (by norm_num)
theorem B960293 : Blo 638302 960293 := bbase (se 4 (by rfl) ⟨90027, by rfl⟩ : syracuseStep 960293 = 180055) (by norm_num)
theorem B960317 : Blo 638302 960317 := bbase (se 3 (by rfl) ⟨180059, by rfl⟩ : syracuseStep 960317 = 360119) (by norm_num)
theorem B960341 : Blo 638302 960341 := bbase (se 9 (by rfl) ⟨2813, by rfl⟩ : syracuseStep 960341 = 5627) (by norm_num)
theorem B960365 : Blo 638302 960365 := bbase (se 3 (by rfl) ⟨180068, by rfl⟩ : syracuseStep 960365 = 360137) (by norm_num)
theorem B960389 : Blo 638302 960389 := bbase (se 4 (by rfl) ⟨90036, by rfl⟩ : syracuseStep 960389 = 180073) (by norm_num)
theorem B10921877 : Blo 638302 10921877 := bbase (se 6 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 10921877 = 511963) (by norm_num)
theorem B960413 : Blo 638302 960413 := bbase (se 3 (by rfl) ⟨180077, by rfl⟩ : syracuseStep 960413 = 360155) (by norm_num)
theorem B2434981 : Blo 638302 2434981 := bbase (se 4 (by rfl) ⟨228279, by rfl⟩ : syracuseStep 2434981 = 456559) (by norm_num)
theorem B960437 : Blo 638302 960437 := bbase (se 5 (by rfl) ⟨45020, by rfl⟩ : syracuseStep 960437 = 90041) (by norm_num)
theorem B960461 : Blo 638302 960461 := bbase (se 3 (by rfl) ⟨180086, by rfl⟩ : syracuseStep 960461 = 360173) (by norm_num)
theorem B960485 : Blo 638302 960485 := bbase (se 4 (by rfl) ⟨90045, by rfl⟩ : syracuseStep 960485 = 180091) (by norm_num)
theorem B960509 : Blo 638302 960509 := bbase (se 3 (by rfl) ⟨180095, by rfl⟩ : syracuseStep 960509 = 360191) (by norm_num)
theorem B960533 : Blo 638302 960533 := bbase (se 6 (by rfl) ⟨22512, by rfl⟩ : syracuseStep 960533 = 45025) (by norm_num)
theorem B1615909 : Blo 638302 1615909 := bbase (se 4 (by rfl) ⟨151491, by rfl⟩ : syracuseStep 1615909 = 302983) (by norm_num)
theorem B960557 : Blo 638302 960557 := bbase (se 3 (by rfl) ⟨180104, by rfl⟩ : syracuseStep 960557 = 360209) (by norm_num)
theorem B960581 : Blo 638302 960581 := bbase (se 4 (by rfl) ⟨90054, by rfl⟩ : syracuseStep 960581 = 180109) (by norm_num)
theorem B1026125 : Blo 638302 1026125 := bbase (se 3 (by rfl) ⟨192398, by rfl⟩ : syracuseStep 1026125 = 384797) (by norm_num)
theorem B960605 : Blo 638302 960605 := bbase (se 3 (by rfl) ⟨180113, by rfl⟩ : syracuseStep 960605 = 360227) (by norm_num)
theorem B960629 : Blo 638302 960629 := bbase (se 5 (by rfl) ⟨45029, by rfl⟩ : syracuseStep 960629 = 90059) (by norm_num)
theorem B960653 : Blo 638302 960653 := bbase (se 3 (by rfl) ⟨180122, by rfl⟩ : syracuseStep 960653 = 360245) (by norm_num)
theorem B1616021 : Blo 638302 1616021 := bbase (se 6 (by rfl) ⟨37875, by rfl⟩ : syracuseStep 1616021 = 75751) (by norm_num)
theorem B960677 : Blo 638302 960677 := bbase (se 4 (by rfl) ⟨90063, by rfl⟩ : syracuseStep 960677 = 180127) (by norm_num)
theorem B960701 : Blo 638302 960701 := bbase (se 3 (by rfl) ⟨180131, by rfl⟩ : syracuseStep 960701 = 360263) (by norm_num)
theorem B1943765 : Blo 638302 1943765 := bbase (se 7 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 1943765 = 45557) (by norm_num)
theorem B960725 : Blo 638302 960725 := bbase (se 7 (by rfl) ⟨11258, by rfl⟩ : syracuseStep 960725 = 22517) (by norm_num)
theorem B2435285 : Blo 638302 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B960749 : Blo 638302 960749 := bbase (se 3 (by rfl) ⟨180140, by rfl⟩ : syracuseStep 960749 = 360281) (by norm_num)
theorem B1943813 : Blo 638302 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B960773 : Blo 638302 960773 := bbase (se 4 (by rfl) ⟨90072, by rfl⟩ : syracuseStep 960773 = 180145) (by norm_num)
theorem B960797 : Blo 638302 960797 := bbase (se 3 (by rfl) ⟨180149, by rfl⟩ : syracuseStep 960797 = 360299) (by norm_num)
theorem B960821 : Blo 638302 960821 := bbase (se 5 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 960821 = 90077) (by norm_num)
theorem B960845 : Blo 638302 960845 := bbase (se 3 (by rfl) ⟨180158, by rfl⟩ : syracuseStep 960845 = 360317) (by norm_num)
theorem B1616213 : Blo 638302 1616213 := bbase (se 10 (by rfl) ⟨2367, by rfl⟩ : syracuseStep 1616213 = 4735) (by norm_num)
theorem B960869 : Blo 638302 960869 := bbase (se 4 (by rfl) ⟨90081, by rfl⟩ : syracuseStep 960869 = 180163) (by norm_num)
theorem B3451253 : Blo 638302 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B960893 : Blo 638302 960893 := bbase (se 3 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 960893 = 360335) (by norm_num)
theorem B960917 : Blo 638302 960917 := bbase (se 6 (by rfl) ⟨22521, by rfl⟩ : syracuseStep 960917 = 45043) (by norm_num)
theorem B731549 : Blo 638302 731549 := bbase (se 3 (by rfl) ⟨137165, by rfl⟩ : syracuseStep 731549 = 274331) (by norm_num)
theorem B960941 : Blo 638302 960941 := bbase (se 3 (by rfl) ⟨180176, by rfl⟩ : syracuseStep 960941 = 360353) (by norm_num)
theorem B960965 : Blo 638302 960965 := bbase (se 4 (by rfl) ⟨90090, by rfl⟩ : syracuseStep 960965 = 180181) (by norm_num)
theorem B960989 : Blo 638302 960989 := bbase (se 3 (by rfl) ⟨180185, by rfl⟩ : syracuseStep 960989 = 360371) (by norm_num)
theorem B961013 : Blo 638302 961013 := bbase (se 5 (by rfl) ⟨45047, by rfl⟩ : syracuseStep 961013 = 90095) (by norm_num)
theorem B961037 : Blo 638302 961037 := bbase (se 3 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 961037 = 360389) (by norm_num)
theorem B961061 : Blo 638302 961061 := bbase (se 4 (by rfl) ⟨90099, by rfl⟩ : syracuseStep 961061 = 180199) (by norm_num)
theorem B1878565 : Blo 638302 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B961085 : Blo 638302 961085 := bbase (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) (by norm_num)
theorem B961109 : Blo 638302 961109 := bbase (se 8 (by rfl) ⟨5631, by rfl⟩ : syracuseStep 961109 = 11263) (by norm_num)
theorem B961133 : Blo 638302 961133 := bbase (se 3 (by rfl) ⟨180212, by rfl⟩ : syracuseStep 961133 = 360425) (by norm_num)
theorem B6564469 : Blo 638302 6564469 := bbase (se 5 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 6564469 = 615419) (by norm_num)
theorem B961157 : Blo 638302 961157 := bbase (se 4 (by rfl) ⟨90108, by rfl⟩ : syracuseStep 961157 = 180217) (by norm_num)
theorem B961181 : Blo 638302 961181 := bbase (se 3 (by rfl) ⟨180221, by rfl⟩ : syracuseStep 961181 = 360443) (by norm_num)
theorem B1616557 : Blo 638302 1616557 := bbase (se 3 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 1616557 = 606209) (by norm_num)
theorem B961205 : Blo 638302 961205 := bbase (se 5 (by rfl) ⟨45056, by rfl⟩ : syracuseStep 961205 = 90113) (by norm_num)
theorem B961229 : Blo 638302 961229 := bbase (se 3 (by rfl) ⟨180230, by rfl⟩ : syracuseStep 961229 = 360461) (by norm_num)
theorem B961253 : Blo 638302 961253 := bbase (se 4 (by rfl) ⟨90117, by rfl⟩ : syracuseStep 961253 = 180235) (by norm_num)
theorem B961277 : Blo 638302 961277 := bbase (se 3 (by rfl) ⟨180239, by rfl⟩ : syracuseStep 961277 = 360479) (by norm_num)
theorem B2501381 : Blo 638302 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B961301 : Blo 638302 961301 := bbase (se 6 (by rfl) ⟨22530, by rfl⟩ : syracuseStep 961301 = 45061) (by norm_num)
theorem B1616669 : Blo 638302 1616669 := bbase (se 3 (by rfl) ⟨303125, by rfl⟩ : syracuseStep 1616669 = 606251) (by norm_num)
theorem B961325 : Blo 638302 961325 := bbase (se 3 (by rfl) ⟨180248, by rfl⟩ : syracuseStep 961325 = 360497) (by norm_num)
theorem B961349 : Blo 638302 961349 := bbase (se 4 (by rfl) ⟨90126, by rfl⟩ : syracuseStep 961349 = 180253) (by norm_num)
theorem B961373 : Blo 638302 961373 := bbase (se 3 (by rfl) ⟨180257, by rfl⟩ : syracuseStep 961373 = 360515) (by norm_num)
theorem B961397 : Blo 638302 961397 := bbase (se 5 (by rfl) ⟨45065, by rfl⟩ : syracuseStep 961397 = 90131) (by norm_num)
theorem B961421 : Blo 638302 961421 := bbase (se 3 (by rfl) ⟨180266, by rfl⟩ : syracuseStep 961421 = 360533) (by norm_num)
theorem B961445 : Blo 638302 961445 := bbase (se 4 (by rfl) ⟨90135, by rfl⟩ : syracuseStep 961445 = 180271) (by norm_num)
theorem B961469 : Blo 638302 961469 := bbase (se 3 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 961469 = 360551) (by norm_num)
theorem B961493 : Blo 638302 961493 := bbase (se 7 (by rfl) ⟨11267, by rfl⟩ : syracuseStep 961493 = 22535) (by norm_num)
theorem B1616861 : Blo 638302 1616861 := bbase (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) (by norm_num)
theorem B961517 : Blo 638302 961517 := bbase (se 3 (by rfl) ⟨180284, by rfl⟩ : syracuseStep 961517 = 360569) (by norm_num)
theorem B961541 : Blo 638302 961541 := bbase (se 4 (by rfl) ⟨90144, by rfl⟩ : syracuseStep 961541 = 180289) (by norm_num)
theorem B961565 : Blo 638302 961565 := bbase (se 3 (by rfl) ⟨180293, by rfl⟩ : syracuseStep 961565 = 360587) (by norm_num)
theorem B961589 : Blo 638302 961589 := bbase (se 5 (by rfl) ⟨45074, by rfl⟩ : syracuseStep 961589 = 90149) (by norm_num)
theorem B961613 : Blo 638302 961613 := bbase (se 3 (by rfl) ⟨180302, by rfl⟩ : syracuseStep 961613 = 360605) (by norm_num)
theorem B961637 : Blo 638302 961637 := bbase (se 4 (by rfl) ⟨90153, by rfl⟩ : syracuseStep 961637 = 180307) (by norm_num)
theorem B961661 : Blo 638302 961661 := bbase (se 3 (by rfl) ⟨180311, by rfl⟩ : syracuseStep 961661 = 360623) (by norm_num)
theorem B732305 : Blo 638302 732305 := bbase (se 2 (by rfl) ⟨274614, by rfl⟩ : syracuseStep 732305 = 549229) (by norm_num)
theorem B961685 : Blo 638302 961685 := bbase (se 6 (by rfl) ⟨22539, by rfl⟩ : syracuseStep 961685 = 45079) (by norm_num)
theorem B961709 : Blo 638302 961709 := bbase (se 3 (by rfl) ⟨180320, by rfl⟩ : syracuseStep 961709 = 360641) (by norm_num)
theorem B961733 : Blo 638302 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B961757 : Blo 638302 961757 := bbase (se 3 (by rfl) ⟨180329, by rfl⟩ : syracuseStep 961757 = 360659) (by norm_num)
theorem B961781 : Blo 638302 961781 := bbase (se 5 (by rfl) ⟨45083, by rfl⟩ : syracuseStep 961781 = 90167) (by norm_num)
theorem B961805 : Blo 638302 961805 := bbase (se 3 (by rfl) ⟨180338, by rfl⟩ : syracuseStep 961805 = 360677) (by norm_num)
theorem B961829 : Blo 638302 961829 := bbase (se 4 (by rfl) ⟨90171, by rfl⟩ : syracuseStep 961829 = 180343) (by norm_num)
theorem B1617205 : Blo 638302 1617205 := bbase (se 5 (by rfl) ⟨75806, by rfl⟩ : syracuseStep 1617205 = 151613) (by norm_num)
theorem B961853 : Blo 638302 961853 := bbase (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) (by norm_num)
theorem B961877 : Blo 638302 961877 := bbase (se 11 (by rfl) ⟨704, by rfl⟩ : syracuseStep 961877 = 1409) (by norm_num)
theorem B961901 : Blo 638302 961901 := bbase (se 3 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 961901 = 360713) (by norm_num)
theorem B961925 : Blo 638302 961925 := bbase (se 4 (by rfl) ⟨90180, by rfl⟩ : syracuseStep 961925 = 180361) (by norm_num)
theorem B961949 : Blo 638302 961949 := bbase (se 3 (by rfl) ⟨180365, by rfl⟩ : syracuseStep 961949 = 360731) (by norm_num)
theorem B1617317 : Blo 638302 1617317 := bbase (se 4 (by rfl) ⟨151623, by rfl⟩ : syracuseStep 1617317 = 303247) (by norm_num)
theorem B961973 : Blo 638302 961973 := bbase (se 5 (by rfl) ⟨45092, by rfl⟩ : syracuseStep 961973 = 90185) (by norm_num)
theorem B961997 : Blo 638302 961997 := bbase (se 3 (by rfl) ⟨180374, by rfl⟩ : syracuseStep 961997 = 360749) (by norm_num)
theorem B1027541 : Blo 638302 1027541 := bbase (se 7 (by rfl) ⟨12041, by rfl⟩ : syracuseStep 1027541 = 24083) (by norm_num)
theorem B863717 : Blo 638302 863717 := bbase (se 4 (by rfl) ⟨80973, by rfl⟩ : syracuseStep 863717 = 161947) (by norm_num)
theorem B962021 : Blo 638302 962021 := bbase (se 4 (by rfl) ⟨90189, by rfl⟩ : syracuseStep 962021 = 180379) (by norm_num)
theorem B962045 : Blo 638302 962045 := bbase (se 3 (by rfl) ⟨180383, by rfl⟩ : syracuseStep 962045 = 360767) (by norm_num)
theorem B962069 : Blo 638302 962069 := bbase (se 6 (by rfl) ⟨22548, by rfl⟩ : syracuseStep 962069 = 45097) (by norm_num)
theorem B962093 : Blo 638302 962093 := bbase (se 3 (by rfl) ⟨180392, by rfl⟩ : syracuseStep 962093 = 360785) (by norm_num)
theorem B962117 : Blo 638302 962117 := bbase (se 4 (by rfl) ⟨90198, by rfl⟩ : syracuseStep 962117 = 180397) (by norm_num)
theorem B962141 : Blo 638302 962141 := bbase (se 3 (by rfl) ⟨180401, by rfl⟩ : syracuseStep 962141 = 360803) (by norm_num)
theorem B1617509 : Blo 638302 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B962165 : Blo 638302 962165 := bbase (se 5 (by rfl) ⟨45101, by rfl⟩ : syracuseStep 962165 = 90203) (by norm_num)
theorem B962189 : Blo 638302 962189 := bbase (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) (by norm_num)
theorem B962213 : Blo 638302 962213 := bbase (se 4 (by rfl) ⟨90207, by rfl⟩ : syracuseStep 962213 = 180415) (by norm_num)
theorem B1027765 : Blo 638302 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B962237 : Blo 638302 962237 := bbase (se 3 (by rfl) ⟨180419, by rfl⟩ : syracuseStep 962237 = 360839) (by norm_num)
theorem B962261 : Blo 638302 962261 := bbase (se 7 (by rfl) ⟨11276, by rfl⟩ : syracuseStep 962261 = 22553) (by norm_num)
theorem B1388261 : Blo 638302 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B962285 : Blo 638302 962285 := bbase (se 3 (by rfl) ⟨180428, by rfl⟩ : syracuseStep 962285 = 360857) (by norm_num)
theorem B962309 : Blo 638302 962309 := bbase (se 4 (by rfl) ⟨90216, by rfl⟩ : syracuseStep 962309 = 180433) (by norm_num)
theorem B962333 : Blo 638302 962333 := bbase (se 3 (by rfl) ⟨180437, by rfl⟩ : syracuseStep 962333 = 360875) (by norm_num)
theorem B962357 : Blo 638302 962357 := bbase (se 5 (by rfl) ⟨45110, by rfl⟩ : syracuseStep 962357 = 90221) (by norm_num)
theorem B962381 : Blo 638302 962381 := bbase (se 3 (by rfl) ⟨180446, by rfl⟩ : syracuseStep 962381 = 360893) (by norm_num)
theorem B962405 : Blo 638302 962405 := bbase (se 4 (by rfl) ⟨90225, by rfl⟩ : syracuseStep 962405 = 180451) (by norm_num)
theorem B962429 : Blo 638302 962429 := bbase (se 3 (by rfl) ⟨180455, by rfl⟩ : syracuseStep 962429 = 360911) (by norm_num)
theorem B962453 : Blo 638302 962453 := bbase (se 6 (by rfl) ⟨22557, by rfl⟩ : syracuseStep 962453 = 45115) (by norm_num)
theorem B962477 : Blo 638302 962477 := bbase (se 3 (by rfl) ⟨180464, by rfl⟩ : syracuseStep 962477 = 360929) (by norm_num)
theorem B1617853 : Blo 638302 1617853 := bbase (se 3 (by rfl) ⟨303347, by rfl⟩ : syracuseStep 1617853 = 606695) (by norm_num)
theorem B962501 : Blo 638302 962501 := bbase (se 4 (by rfl) ⟨90234, by rfl⟩ : syracuseStep 962501 = 180469) (by norm_num)
theorem B962525 : Blo 638302 962525 := bbase (se 3 (by rfl) ⟨180473, by rfl⟩ : syracuseStep 962525 = 360947) (by norm_num)
theorem B962549 : Blo 638302 962549 := bbase (se 5 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 962549 = 90239) (by norm_num)
theorem B962573 : Blo 638302 962573 := bbase (se 3 (by rfl) ⟨180482, by rfl⟩ : syracuseStep 962573 = 360965) (by norm_num)
theorem B962597 : Blo 638302 962597 := bbase (se 4 (by rfl) ⟨90243, by rfl⟩ : syracuseStep 962597 = 180487) (by norm_num)
theorem B1617965 : Blo 638302 1617965 := bbase (se 3 (by rfl) ⟨303368, by rfl⟩ : syracuseStep 1617965 = 606737) (by norm_num)
theorem B962621 : Blo 638302 962621 := bbase (se 3 (by rfl) ⟨180491, by rfl⟩ : syracuseStep 962621 = 360983) (by norm_num)
theorem B962645 : Blo 638302 962645 := bbase (se 8 (by rfl) ⟨5640, by rfl⟩ : syracuseStep 962645 = 11281) (by norm_num)
theorem B962669 : Blo 638302 962669 := bbase (se 3 (by rfl) ⟨180500, by rfl⟩ : syracuseStep 962669 = 361001) (by norm_num)
theorem B962693 : Blo 638302 962693 := bbase (se 4 (by rfl) ⟨90252, by rfl⟩ : syracuseStep 962693 = 180505) (by norm_num)
theorem B1978501 : Blo 638302 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B962717 : Blo 638302 962717 := bbase (se 3 (by rfl) ⟨180509, by rfl⟩ : syracuseStep 962717 = 361019) (by norm_num)
theorem B962741 : Blo 638302 962741 := bbase (se 5 (by rfl) ⟨45128, by rfl⟩ : syracuseStep 962741 = 90257) (by norm_num)
theorem B962765 : Blo 638302 962765 := bbase (se 3 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 962765 = 361037) (by norm_num)
theorem B962789 : Blo 638302 962789 := bbase (se 4 (by rfl) ⟨90261, by rfl⟩ : syracuseStep 962789 = 180523) (by norm_num)
theorem B1618157 : Blo 638302 1618157 := bbase (se 3 (by rfl) ⟨303404, by rfl⟩ : syracuseStep 1618157 = 606809) (by norm_num)
theorem B962813 : Blo 638302 962813 := bbase (se 3 (by rfl) ⟨180527, by rfl⟩ : syracuseStep 962813 = 361055) (by norm_num)
theorem B962837 : Blo 638302 962837 := bbase (se 6 (by rfl) ⟨22566, by rfl⟩ : syracuseStep 962837 = 45133) (by norm_num)
theorem B2437397 : Blo 638302 2437397 := bbase (se 6 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 2437397 = 114253) (by norm_num)
theorem B962861 : Blo 638302 962861 := bbase (se 3 (by rfl) ⟨180536, by rfl⟩ : syracuseStep 962861 = 361073) (by norm_num)
theorem B962885 : Blo 638302 962885 := bbase (se 4 (by rfl) ⟨90270, by rfl⟩ : syracuseStep 962885 = 180541) (by norm_num)
theorem B962909 : Blo 638302 962909 := bbase (se 3 (by rfl) ⟨180545, by rfl⟩ : syracuseStep 962909 = 361091) (by norm_num)
theorem B962933 : Blo 638302 962933 := bbase (se 5 (by rfl) ⟨45137, by rfl⟩ : syracuseStep 962933 = 90275) (by norm_num)
theorem B962957 : Blo 638302 962957 := bbase (se 3 (by rfl) ⟨180554, by rfl⟩ : syracuseStep 962957 = 361109) (by norm_num)
theorem B2732453 : Blo 638302 2732453 := bbase (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) (by norm_num)
theorem B962981 : Blo 638302 962981 := bbase (se 4 (by rfl) ⟨90279, by rfl⟩ : syracuseStep 962981 = 180559) (by norm_num)
theorem B2929061 : Blo 638302 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B963005 : Blo 638302 963005 := bbase (se 3 (by rfl) ⟨180563, by rfl⟩ : syracuseStep 963005 = 361127) (by norm_num)
theorem B963029 : Blo 638302 963029 := bbase (se 7 (by rfl) ⟨11285, by rfl⟩ : syracuseStep 963029 = 22571) (by norm_num)
theorem B963053 : Blo 638302 963053 := bbase (se 3 (by rfl) ⟨180572, by rfl⟩ : syracuseStep 963053 = 361145) (by norm_num)
theorem B963077 : Blo 638302 963077 := bbase (se 4 (by rfl) ⟨90288, by rfl⟩ : syracuseStep 963077 = 180577) (by norm_num)
theorem B963101 : Blo 638302 963101 := bbase (se 3 (by rfl) ⟨180581, by rfl⟩ : syracuseStep 963101 = 361163) (by norm_num)
theorem B2437685 : Blo 638302 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B963125 : Blo 638302 963125 := bbase (se 5 (by rfl) ⟨45146, by rfl⟩ : syracuseStep 963125 = 90293) (by norm_num)
theorem B1618501 : Blo 638302 1618501 := bbase (se 4 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 1618501 = 303469) (by norm_num)
theorem B963149 : Blo 638302 963149 := bbase (se 3 (by rfl) ⟨180590, by rfl⟩ : syracuseStep 963149 = 361181) (by norm_num)
theorem B963173 : Blo 638302 963173 := bbase (se 4 (by rfl) ⟨90297, by rfl⟩ : syracuseStep 963173 = 180595) (by norm_num)
theorem B963197 : Blo 638302 963197 := bbase (se 3 (by rfl) ⟨180599, by rfl⟩ : syracuseStep 963197 = 361199) (by norm_num)
theorem B963221 : Blo 638302 963221 := bbase (se 6 (by rfl) ⟨22575, by rfl⟩ : syracuseStep 963221 = 45151) (by norm_num)
theorem B963245 : Blo 638302 963245 := bbase (se 3 (by rfl) ⟨180608, by rfl⟩ : syracuseStep 963245 = 361217) (by norm_num)
theorem B1618613 : Blo 638302 1618613 := bbase (se 5 (by rfl) ⟨75872, by rfl⟩ : syracuseStep 1618613 = 151745) (by norm_num)
theorem B963269 : Blo 638302 963269 := bbase (se 4 (by rfl) ⟨90306, by rfl⟩ : syracuseStep 963269 = 180613) (by norm_num)
theorem B963293 : Blo 638302 963293 := bbase (se 3 (by rfl) ⟨180617, by rfl⟩ : syracuseStep 963293 = 361235) (by norm_num)
theorem B963317 : Blo 638302 963317 := bbase (se 5 (by rfl) ⟨45155, by rfl⟩ : syracuseStep 963317 = 90311) (by norm_num)
theorem B963341 : Blo 638302 963341 := bbase (se 3 (by rfl) ⟨180626, by rfl⟩ : syracuseStep 963341 = 361253) (by norm_num)
theorem B963365 : Blo 638302 963365 := bbase (se 4 (by rfl) ⟨90315, by rfl⟩ : syracuseStep 963365 = 180631) (by norm_num)
theorem B963389 : Blo 638302 963389 := bbase (se 3 (by rfl) ⟨180635, by rfl⟩ : syracuseStep 963389 = 361271) (by norm_num)
theorem B6566741 : Blo 638302 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B963413 : Blo 638302 963413 := bbase (se 9 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 963413 = 5645) (by norm_num)
theorem B865117 : Blo 638302 865117 := bbase (se 3 (by rfl) ⟨162209, by rfl⟩ : syracuseStep 865117 = 324419) (by norm_num)
theorem B963437 : Blo 638302 963437 := bbase (se 3 (by rfl) ⟨180644, by rfl⟩ : syracuseStep 963437 = 361289) (by norm_num)
theorem B1618805 : Blo 638302 1618805 := bbase (se 5 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 1618805 = 151763) (by norm_num)
theorem B1094573 : Blo 638302 1094573 := bbase (se 3 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 1094573 = 410465) (by norm_num)
theorem B4109237 : Blo 638302 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B1782773 : Blo 638302 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B2765957 : Blo 638302 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B3650741 : Blo 638302 3650741 := bbase (se 5 (by rfl) ⟨171128, by rfl⟩ : syracuseStep 3650741 = 342257) (by norm_num)
theorem B2602181 : Blo 638302 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B1619149 : Blo 638302 1619149 := bbase (se 3 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 1619149 = 607181) (by norm_num)
theorem B1619261 : Blo 638302 1619261 := bbase (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) (by norm_num)
theorem B865733 : Blo 638302 865733 := bbase (se 4 (by rfl) ⟨81162, by rfl⟩ : syracuseStep 865733 = 162325) (by norm_num)
theorem B767441 : Blo 638302 767441 := bbase (se 2 (by rfl) ⟨287790, by rfl⟩ : syracuseStep 767441 = 575581) (by norm_num)
theorem B2471381 : Blo 638302 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B1619453 : Blo 638302 1619453 := bbase (se 3 (by rfl) ⟨303647, by rfl⟩ : syracuseStep 1619453 = 607295) (by norm_num)
theorem B1947365 : Blo 638302 1947365 := bbase (se 4 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 1947365 = 365131) (by norm_num)
theorem B1947461 : Blo 638302 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B1619797 : Blo 638302 1619797 := bbase (se 9 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 1619797 = 9491) (by norm_num)
theorem B2045893 : Blo 638302 2045893 := bbase (se 4 (by rfl) ⟨191802, by rfl⟩ : syracuseStep 2045893 = 383605) (by norm_num)
theorem B1619909 : Blo 638302 1619909 := bbase (se 4 (by rfl) ⟨151866, by rfl⟩ : syracuseStep 1619909 = 303733) (by norm_num)
theorem B768133 : Blo 638302 768133 := bbase (se 4 (by rfl) ⟨72012, by rfl⟩ : syracuseStep 768133 = 144025) (by norm_num)
theorem B1620101 : Blo 638302 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B768137 : Blo 638302 768137 := bbase (se 2 (by rfl) ⟨288051, by rfl⟩ : syracuseStep 768137 = 576103) (by norm_num)
theorem B2734229 : Blo 638302 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B2308277 : Blo 638302 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B866485 : Blo 638302 866485 := bbase (se 5 (by rfl) ⟨40616, by rfl⟩ : syracuseStep 866485 = 81233) (by norm_num)
theorem B866533 : Blo 638302 866533 := bbase (se 4 (by rfl) ⟨81237, by rfl⟩ : syracuseStep 866533 = 162475) (by norm_num)
theorem B3651925 : Blo 638302 3651925 := bbase (se 10 (by rfl) ⟨5349, by rfl⟩ : syracuseStep 3651925 = 10699) (by norm_num)
theorem B4864373 : Blo 638302 4864373 := bbase (se 5 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 4864373 = 456035) (by norm_num)
theorem B2734469 : Blo 638302 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B1620445 : Blo 638302 1620445 := bbase (se 3 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 1620445 = 607667) (by norm_num)
theorem B1620557 : Blo 638302 1620557 := bbase (se 3 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 1620557 = 607709) (by norm_num)
theorem B768637 : Blo 638302 768637 := bbase (se 3 (by rfl) ⟨144119, by rfl⟩ : syracuseStep 768637 = 288239) (by norm_num)
theorem B2046725 : Blo 638302 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B1620749 : Blo 638302 1620749 := bbase (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) (by norm_num)
theorem B1457021 : Blo 638302 1457021 := bbase (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) (by norm_num)
theorem B1096597 : Blo 638302 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B769021 : Blo 638302 769021 := bbase (se 3 (by rfl) ⟨144191, by rfl⟩ : syracuseStep 769021 = 288383) (by norm_num)
theorem B1621093 : Blo 638302 1621093 := bbase (se 4 (by rfl) ⟨151977, by rfl⟩ : syracuseStep 1621093 = 303955) (by norm_num)
theorem B2309285 : Blo 638302 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B1621205 : Blo 638302 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B4668661 : Blo 638302 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B11124053 : Blo 638302 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B1621397 : Blo 638302 1621397 := bbase (se 6 (by rfl) ⟨38001, by rfl⟩ : syracuseStep 1621397 = 76003) (by norm_num)
theorem B1457605 : Blo 638302 1457605 := bbase (se 4 (by rfl) ⟨136650, by rfl⟩ : syracuseStep 1457605 = 273301) (by norm_num)
theorem B1097309 : Blo 638302 1097309 := bbase (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) (by norm_num)
theorem B1621741 : Blo 638302 1621741 := bbase (se 3 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 1621741 = 608153) (by norm_num)
theorem B2244341 : Blo 638302 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B1818389 : Blo 638302 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B1621853 : Blo 638302 1621853 := bbase (se 3 (by rfl) ⟨304097, by rfl⟩ : syracuseStep 1621853 = 608195) (by norm_num)
theorem B769925 : Blo 638302 769925 := bbase (se 4 (by rfl) ⟨72180, by rfl⟩ : syracuseStep 769925 = 144361) (by norm_num)
theorem B1622045 : Blo 638302 1622045 := bbase (se 3 (by rfl) ⟨304133, by rfl⟩ : syracuseStep 1622045 = 608267) (by norm_num)
theorem B770185 : Blo 638302 770185 := bbase (se 2 (by rfl) ⟨288819, by rfl⟩ : syracuseStep 770185 = 577639) (by norm_num)
theorem B3653909 : Blo 638302 3653909 := bbase (se 6 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 3653909 = 171277) (by norm_num)
theorem B770377 : Blo 638302 770377 := bbase (se 2 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 770377 = 577783) (by norm_num)
theorem B770401 : Blo 638302 770401 := bbase (se 2 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 770401 = 577801) (by norm_num)
theorem B770405 : Blo 638302 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B3457397 : Blo 638302 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B1622389 : Blo 638302 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B1819061 : Blo 638302 1819061 := bbase (se 5 (by rfl) ⟨85268, by rfl⟩ : syracuseStep 1819061 = 170537) (by norm_num)
theorem B1622501 : Blo 638302 1622501 := bbase (se 4 (by rfl) ⟨152109, by rfl⟩ : syracuseStep 1622501 = 304219) (by norm_num)
theorem B2048597 : Blo 638302 2048597 := bbase (se 8 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 2048597 = 24007) (by norm_num)
theorem B2736757 : Blo 638302 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B1622693 : Blo 638302 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B770905 : Blo 638302 770905 := bbase (se 2 (by rfl) ⟨289089, by rfl⟩ : syracuseStep 770905 = 578179) (by norm_num)
theorem B1819493 : Blo 638302 1819493 := bbase (se 4 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 1819493 = 341155) (by norm_num)
theorem B771001 : Blo 638302 771001 := bbase (se 2 (by rfl) ⟨289125, by rfl⟩ : syracuseStep 771001 = 578251) (by norm_num)
theorem B1557469 : Blo 638302 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B1623037 : Blo 638302 1623037 := bbase (se 3 (by rfl) ⟨304319, by rfl⟩ : syracuseStep 1623037 = 608639) (by norm_num)
theorem B1623149 : Blo 638302 1623149 := bbase (se 3 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 1623149 = 608681) (by norm_num)
theorem B1623341 : Blo 638302 1623341 := bbase (se 3 (by rfl) ⟨304376, by rfl⟩ : syracuseStep 1623341 = 608753) (by norm_num)
theorem B1459613 : Blo 638302 1459613 := bbase (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) (by norm_num)
theorem B1820245 : Blo 638302 1820245 := bbase (se 8 (by rfl) ⟨10665, by rfl⟩ : syracuseStep 1820245 = 21331) (by norm_num)
theorem B1623685 : Blo 638302 1623685 := bbase (se 4 (by rfl) ⟨152220, by rfl⟩ : syracuseStep 1623685 = 304441) (by norm_num)
theorem B1296037 : Blo 638302 1296037 := bbase (se 4 (by rfl) ⟨121503, by rfl⟩ : syracuseStep 1296037 = 243007) (by norm_num)
theorem B1623797 : Blo 638302 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B1623989 : Blo 638302 1623989 := bbase (se 5 (by rfl) ⟨76124, by rfl⟩ : syracuseStep 1623989 = 152249) (by norm_num)
theorem B2738245 : Blo 638302 2738245 := bbase (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) (by norm_num)
theorem B2738261 : Blo 638302 2738261 := bbase (se 8 (by rfl) ⟨16044, by rfl⟩ : syracuseStep 2738261 = 32089) (by norm_num)
theorem B1231085 : Blo 638302 1231085 := bbase (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) (by norm_num)
theorem B6310133 : Blo 638302 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B1624333 : Blo 638302 1624333 := bbase (se 3 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 1624333 = 609125) (by norm_num)
theorem B1624445 : Blo 638302 1624445 := bbase (se 3 (by rfl) ⟨304583, by rfl⟩ : syracuseStep 1624445 = 609167) (by norm_num)
theorem B3656117 : Blo 638302 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B5556757 : Blo 638302 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B1624637 : Blo 638302 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B1297093 : Blo 638302 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B7785173 : Blo 638302 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B1297205 : Blo 638302 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B1624981 : Blo 638302 1624981 := bbase (se 6 (by rfl) ⟨38085, by rfl⟩ : syracuseStep 1624981 = 76171) (by norm_num)
theorem B1625093 : Blo 638302 1625093 := bbase (se 4 (by rfl) ⟨152352, by rfl⟩ : syracuseStep 1625093 = 304705) (by norm_num)
theorem B1461365 : Blo 638302 1461365 := bbase (se 5 (by rfl) ⟨68501, by rfl⟩ : syracuseStep 1461365 = 137003) (by norm_num)
theorem B1625285 : Blo 638302 1625285 := bbase (se 4 (by rfl) ⟨152370, by rfl⟩ : syracuseStep 1625285 = 304741) (by norm_num)
theorem B1297613 : Blo 638302 1297613 := bbase (se 3 (by rfl) ⟨243302, by rfl⟩ : syracuseStep 1297613 = 486605) (by norm_num)
theorem B2051365 : Blo 638302 2051365 := bbase (se 4 (by rfl) ⟨192315, by rfl⟩ : syracuseStep 2051365 = 384631) (by norm_num)
theorem B1625629 : Blo 638302 1625629 := bbase (se 3 (by rfl) ⟨304805, by rfl⟩ : syracuseStep 1625629 = 609611) (by norm_num)
theorem B1363493 : Blo 638302 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B1625741 : Blo 638302 1625741 := bbase (se 3 (by rfl) ⟨304826, by rfl⟩ : syracuseStep 1625741 = 609653) (by norm_num)
theorem B1232533 : Blo 638302 1232533 := bbase (se 6 (by rfl) ⟨28887, by rfl⟩ : syracuseStep 1232533 = 57775) (by norm_num)
theorem B3231413 : Blo 638302 3231413 := bbase (se 5 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 3231413 = 302945) (by norm_num)
theorem B970613 : Blo 638302 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B2740517 : Blo 638302 2740517 := bbase (se 4 (by rfl) ⟨256923, by rfl⟩ : syracuseStep 2740517 = 513847) (by norm_num)
theorem B1823093 : Blo 638302 1823093 := bbase (se 5 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 1823093 = 170915) (by norm_num)
theorem B1364381 : Blo 638302 1364381 := bbase (se 3 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 1364381 = 511643) (by norm_num)
theorem B1364501 : Blo 638302 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B1233749 : Blo 638302 1233749 := bbase (se 9 (by rfl) ⟨3614, by rfl⟩ : syracuseStep 1233749 = 7229) (by norm_num)
theorem B3232709 : Blo 638302 3232709 := bbase (se 4 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 3232709 = 606133) (by norm_num)
theorem B807889 : Blo 638302 807889 := bbase (se 2 (by rfl) ⟨302958, by rfl⟩ : syracuseStep 807889 = 605917) (by norm_num)
theorem B807985 : Blo 638302 807985 := bbase (se 2 (by rfl) ⟨302994, by rfl⟩ : syracuseStep 807985 = 605989) (by norm_num)
theorem B1365133 : Blo 638302 1365133 := bbase (se 3 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 1365133 = 511925) (by norm_num)
theorem B808157 : Blo 638302 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B808213 : Blo 638302 808213 := bbase (se 6 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 808213 = 37885) (by norm_num)
theorem B808309 : Blo 638302 808309 := bbase (se 5 (by rfl) ⟨37889, by rfl⟩ : syracuseStep 808309 = 75779) (by norm_num)
theorem B1725877 : Blo 638302 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B1824277 : Blo 638302 1824277 := bbase (se 6 (by rfl) ⟨42756, by rfl⟩ : syracuseStep 1824277 = 85513) (by norm_num)
theorem B808481 : Blo 638302 808481 := bbase (se 2 (by rfl) ⟨303180, by rfl⟩ : syracuseStep 808481 = 606361) (by norm_num)
theorem B808537 : Blo 638302 808537 := bbase (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) (by norm_num)
theorem B972461 : Blo 638302 972461 := bbase (se 3 (by rfl) ⟨182336, by rfl⟩ : syracuseStep 972461 = 364673) (by norm_num)
theorem B1824437 : Blo 638302 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B808633 : Blo 638302 808633 := bbase (se 2 (by rfl) ⟨303237, by rfl⟩ : syracuseStep 808633 = 606475) (by norm_num)
theorem B808805 : Blo 638302 808805 := bbase (se 4 (by rfl) ⟨75825, by rfl⟩ : syracuseStep 808805 = 151651) (by norm_num)
theorem B1464173 : Blo 638302 1464173 := bbase (se 3 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 1464173 = 549065) (by norm_num)
theorem B2250629 : Blo 638302 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B972685 : Blo 638302 972685 := bbase (se 3 (by rfl) ⟨182378, by rfl⟩ : syracuseStep 972685 = 364757) (by norm_num)
theorem B808861 : Blo 638302 808861 := bbase (se 3 (by rfl) ⟨151661, by rfl⟩ : syracuseStep 808861 = 303323) (by norm_num)
theorem B1824677 : Blo 638302 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B4872149 : Blo 638302 4872149 := bbase (se 7 (by rfl) ⟨57095, by rfl⟩ : syracuseStep 4872149 = 114191) (by norm_num)
theorem B808957 : Blo 638302 808957 := bbase (se 3 (by rfl) ⟨151679, by rfl⟩ : syracuseStep 808957 = 303359) (by norm_num)
theorem B1366021 : Blo 638302 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B1824869 : Blo 638302 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B2054261 : Blo 638302 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B1366141 : Blo 638302 1366141 := bbase (se 3 (by rfl) ⟨256151, by rfl⟩ : syracuseStep 1366141 = 512303) (by norm_num)
theorem B809129 : Blo 638302 809129 := bbase (se 2 (by rfl) ⟨303423, by rfl⟩ : syracuseStep 809129 = 606847) (by norm_num)
theorem B3234005 : Blo 638302 3234005 := bbase (se 7 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 3234005 = 75797) (by norm_num)
theorem B809185 : Blo 638302 809185 := bbase (se 2 (by rfl) ⟨303444, by rfl⟩ : syracuseStep 809185 = 606889) (by norm_num)
theorem B809281 : Blo 638302 809281 := bbase (se 2 (by rfl) ⟨303480, by rfl⟩ : syracuseStep 809281 = 606961) (by norm_num)
theorem B973141 : Blo 638302 973141 := bbase (se 10 (by rfl) ⟨1425, by rfl⟩ : syracuseStep 973141 = 2851) (by norm_num)
theorem B1366397 : Blo 638302 1366397 := bbase (se 3 (by rfl) ⟨256199, by rfl⟩ : syracuseStep 1366397 = 512399) (by norm_num)
theorem B809453 : Blo 638302 809453 := bbase (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) (by norm_num)
theorem B809509 : Blo 638302 809509 := bbase (se 4 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 809509 = 151783) (by norm_num)
theorem B809605 : Blo 638302 809605 := bbase (se 4 (by rfl) ⟨75900, by rfl⟩ : syracuseStep 809605 = 151801) (by norm_num)
theorem B809777 : Blo 638302 809777 := bbase (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) (by norm_num)
theorem B809833 : Blo 638302 809833 := bbase (se 2 (by rfl) ⟨303687, by rfl⟩ : syracuseStep 809833 = 607375) (by norm_num)
theorem B1727381 : Blo 638302 1727381 := bbase (se 6 (by rfl) ⟨40485, by rfl⟩ : syracuseStep 1727381 = 80971) (by norm_num)
theorem B5823413 : Blo 638302 5823413 := bbase (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) (by norm_num)
theorem B809929 : Blo 638302 809929 := bbase (se 2 (by rfl) ⟨303723, by rfl⟩ : syracuseStep 809929 = 607447) (by norm_num)
theorem B973829 : Blo 638302 973829 := bbase (se 4 (by rfl) ⟨91296, by rfl⟩ : syracuseStep 973829 = 182593) (by norm_num)
theorem B1235981 : Blo 638302 1235981 := bbase (se 3 (by rfl) ⟨231746, by rfl⟩ : syracuseStep 1235981 = 463493) (by norm_num)
theorem B1825861 : Blo 638302 1825861 := bbase (se 4 (by rfl) ⟨171174, by rfl⟩ : syracuseStep 1825861 = 342349) (by norm_num)
theorem B810101 : Blo 638302 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B810157 : Blo 638302 810157 := bbase (se 3 (by rfl) ⟨151904, by rfl⟩ : syracuseStep 810157 = 303809) (by norm_num)
theorem B5823701 : Blo 638302 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B1367285 : Blo 638302 1367285 := bbase (se 5 (by rfl) ⟨64091, by rfl⟩ : syracuseStep 1367285 = 128183) (by norm_num)
theorem B810253 : Blo 638302 810253 := bbase (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) (by norm_num)
theorem B1564085 : Blo 638302 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B810425 : Blo 638302 810425 := bbase (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) (by norm_num)
theorem B1367525 : Blo 638302 1367525 := bbase (se 4 (by rfl) ⟨128205, by rfl⟩ : syracuseStep 1367525 = 256411) (by norm_num)
theorem B3235301 : Blo 638302 3235301 := bbase (se 4 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 3235301 = 606619) (by norm_num)
theorem B810481 : Blo 638302 810481 := bbase (se 2 (by rfl) ⟨303930, by rfl⟩ : syracuseStep 810481 = 607861) (by norm_num)
theorem B810577 : Blo 638302 810577 := bbase (se 2 (by rfl) ⟨303966, by rfl⟩ : syracuseStep 810577 = 607933) (by norm_num)
theorem B909029 : Blo 638302 909029 := bbase (se 4 (by rfl) ⟨85221, by rfl⟩ : syracuseStep 909029 = 170443) (by norm_num)
theorem B810749 : Blo 638302 810749 := bbase (se 3 (by rfl) ⟨152015, by rfl⟩ : syracuseStep 810749 = 304031) (by norm_num)
theorem B810805 : Blo 638302 810805 := bbase (se 5 (by rfl) ⟨38006, by rfl⟩ : syracuseStep 810805 = 76013) (by norm_num)
theorem B810901 : Blo 638302 810901 := bbase (se 6 (by rfl) ⟨19005, by rfl⟩ : syracuseStep 810901 = 38011) (by norm_num)
theorem B2154437 : Blo 638302 2154437 := bbase (se 4 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 2154437 = 403957) (by norm_num)
theorem B1368029 : Blo 638302 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B1368037 : Blo 638302 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B811073 : Blo 638302 811073 := bbase (se 2 (by rfl) ⟨304152, by rfl⟩ : syracuseStep 811073 = 608305) (by norm_num)
theorem B647281 : Blo 638302 647281 := bbase (se 2 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 647281 = 485461) (by norm_num)
theorem B811129 : Blo 638302 811129 := bbase (se 2 (by rfl) ⟨304173, by rfl⟩ : syracuseStep 811129 = 608347) (by norm_num)
theorem B1826965 : Blo 638302 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B811225 : Blo 638302 811225 := bbase (se 2 (by rfl) ⟨304209, by rfl⟩ : syracuseStep 811225 = 608419) (by norm_num)
theorem B2154869 : Blo 638302 2154869 := bbase (se 5 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 2154869 = 202019) (by norm_num)
theorem B811397 : Blo 638302 811397 := bbase (se 4 (by rfl) ⟨76068, by rfl⟩ : syracuseStep 811397 = 152137) (by norm_num)
theorem B811453 : Blo 638302 811453 := bbase (se 3 (by rfl) ⟨152147, by rfl⟩ : syracuseStep 811453 = 304295) (by norm_num)
theorem B811549 : Blo 638302 811549 := bbase (se 3 (by rfl) ⟨152165, by rfl⟩ : syracuseStep 811549 = 304331) (by norm_num)
theorem B1401517 : Blo 638302 1401517 := bbase (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) (by norm_num)
theorem B811721 : Blo 638302 811721 := bbase (se 2 (by rfl) ⟨304395, by rfl⟩ : syracuseStep 811721 = 608791) (by norm_num)
theorem B3236597 : Blo 638302 3236597 := bbase (se 5 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 3236597 = 303431) (by norm_num)
theorem B811777 : Blo 638302 811777 := bbase (se 2 (by rfl) ⟨304416, by rfl⟩ : syracuseStep 811777 = 608833) (by norm_num)
theorem B2155301 : Blo 638302 2155301 := bbase (se 4 (by rfl) ⟨202059, by rfl⟩ : syracuseStep 2155301 = 404119) (by norm_num)
theorem B811873 : Blo 638302 811873 := bbase (se 2 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 811873 = 608905) (by norm_num)
theorem B812045 : Blo 638302 812045 := bbase (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) (by norm_num)
theorem B812101 : Blo 638302 812101 := bbase (se 4 (by rfl) ⟨76134, by rfl⟩ : syracuseStep 812101 = 152269) (by norm_num)
theorem B1369165 : Blo 638302 1369165 := bbase (se 3 (by rfl) ⟨256718, by rfl⟩ : syracuseStep 1369165 = 513437) (by norm_num)
theorem B910453 : Blo 638302 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B812197 : Blo 638302 812197 := bbase (se 4 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 812197 = 152287) (by norm_num)
theorem B2057413 : Blo 638302 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B2155733 : Blo 638302 2155733 := bbase (se 7 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 2155733 = 50525) (by norm_num)
theorem B779549 : Blo 638302 779549 := bbase (se 3 (by rfl) ⟨146165, by rfl⟩ : syracuseStep 779549 = 292331) (by norm_num)
theorem B812369 : Blo 638302 812369 := bbase (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) (by norm_num)
theorem B976261 : Blo 638302 976261 := bbase (se 4 (by rfl) ⟨91524, by rfl⟩ : syracuseStep 976261 = 183049) (by norm_num)
theorem B812425 : Blo 638302 812425 := bbase (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) (by norm_num)
theorem B5203349 : Blo 638302 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B2778533 : Blo 638302 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B1369541 : Blo 638302 1369541 := bbase (se 4 (by rfl) ⟨128394, by rfl⟩ : syracuseStep 1369541 = 256789) (by norm_num)
theorem B812521 : Blo 638302 812521 := bbase (se 2 (by rfl) ⟨304695, by rfl⟩ : syracuseStep 812521 = 609391) (by norm_num)
theorem B1664509 : Blo 638302 1664509 := bbase (se 3 (by rfl) ⟨312095, by rfl⟩ : syracuseStep 1664509 = 624191) (by norm_num)
theorem B1402429 : Blo 638302 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1828469 : Blo 638302 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B2156165 : Blo 638302 2156165 := bbase (se 4 (by rfl) ⟨202140, by rfl⟩ : syracuseStep 2156165 = 404281) (by norm_num)
theorem B812693 : Blo 638302 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B911045 : Blo 638302 911045 := bbase (se 4 (by rfl) ⟨85410, by rfl⟩ : syracuseStep 911045 = 170821) (by norm_num)
theorem B812749 : Blo 638302 812749 := bbase (se 3 (by rfl) ⟨152390, by rfl⟩ : syracuseStep 812749 = 304781) (by norm_num)
theorem B911125 : Blo 638302 911125 := bbase (se 6 (by rfl) ⟨21354, by rfl⟩ : syracuseStep 911125 = 42709) (by norm_num)
theorem B812845 : Blo 638302 812845 := bbase (se 3 (by rfl) ⟨152408, by rfl⟩ : syracuseStep 812845 = 304817) (by norm_num)
theorem B911245 : Blo 638302 911245 := bbase (se 3 (by rfl) ⟨170858, by rfl⟩ : syracuseStep 911245 = 341717) (by norm_num)
theorem B681917 : Blo 638302 681917 := bbase (se 3 (by rfl) ⟨127859, by rfl⟩ : syracuseStep 681917 = 255719) (by norm_num)
theorem B911341 : Blo 638302 911341 := bbase (se 3 (by rfl) ⟨170876, by rfl⟩ : syracuseStep 911341 = 341753) (by norm_num)
theorem B681977 : Blo 638302 681977 := bbase (se 2 (by rfl) ⟨255741, by rfl⟩ : syracuseStep 681977 = 511483) (by norm_num)
theorem B3237893 : Blo 638302 3237893 := bbase (se 4 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 3237893 = 607105) (by norm_num)
theorem B2156597 : Blo 638302 2156597 := bbase (se 5 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 2156597 = 202181) (by norm_num)
theorem B682105 : Blo 638302 682105 := bbase (se 2 (by rfl) ⟨255789, by rfl⟩ : syracuseStep 682105 = 511579) (by norm_num)
theorem B4811093 : Blo 638302 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B911837 : Blo 638302 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B2157029 : Blo 638302 2157029 := bbase (se 4 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 2157029 = 404443) (by norm_num)
theorem B682549 : Blo 638302 682549 := bbase (se 5 (by rfl) ⟨31994, by rfl⟩ : syracuseStep 682549 = 63989) (by norm_num)
theorem B1436237 : Blo 638302 1436237 := bbase (se 3 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 1436237 = 538589) (by norm_num)
theorem B3467861 : Blo 638302 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B1436309 : Blo 638302 1436309 := bbase (se 6 (by rfl) ⟨33663, by rfl⟩ : syracuseStep 1436309 = 67327) (by norm_num)
theorem B1534621 : Blo 638302 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B682669 : Blo 638302 682669 := bbase (se 3 (by rfl) ⟨128000, by rfl⟩ : syracuseStep 682669 = 256001) (by norm_num)
theorem B1436381 : Blo 638302 1436381 := bbase (se 3 (by rfl) ⟨269321, by rfl⟩ : syracuseStep 1436381 = 538643) (by norm_num)
theorem B1436453 : Blo 638302 1436453 := bbase (se 4 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 1436453 = 269335) (by norm_num)
theorem B1436525 : Blo 638302 1436525 := bbase (se 3 (by rfl) ⟨269348, by rfl⟩ : syracuseStep 1436525 = 538697) (by norm_num)
theorem B2157461 : Blo 638302 2157461 := bbase (se 6 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 2157461 = 101131) (by norm_num)
theorem B682921 : Blo 638302 682921 := bbase (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) (by norm_num)
theorem B682925 : Blo 638302 682925 := bbase (se 3 (by rfl) ⟨128048, by rfl⟩ : syracuseStep 682925 = 256097) (by norm_num)
theorem B1436597 : Blo 638302 1436597 := bbase (se 5 (by rfl) ⟨67340, by rfl⟩ : syracuseStep 1436597 = 134681) (by norm_num)
theorem B1436669 : Blo 638302 1436669 := bbase (se 3 (by rfl) ⟨269375, by rfl⟩ : syracuseStep 1436669 = 538751) (by norm_num)
theorem B912389 : Blo 638302 912389 := bbase (se 4 (by rfl) ⟨85536, by rfl⟩ : syracuseStep 912389 = 171073) (by norm_num)
theorem B650273 : Blo 638302 650273 := bbase (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) (by norm_num)
theorem B1371181 : Blo 638302 1371181 := bbase (se 3 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 1371181 = 514193) (by norm_num)
theorem B1436741 : Blo 638302 1436741 := bbase (se 4 (by rfl) ⟨134694, by rfl⟩ : syracuseStep 1436741 = 269389) (by norm_num)
theorem B1436813 : Blo 638302 1436813 := bbase (se 3 (by rfl) ⟨269402, by rfl⟩ : syracuseStep 1436813 = 538805) (by norm_num)
theorem B4091093 : Blo 638302 4091093 := bbase (se 7 (by rfl) ⟨47942, by rfl⟩ : syracuseStep 4091093 = 95885) (by norm_num)
theorem B1436885 : Blo 638302 1436885 := bbase (se 7 (by rfl) ⟨16838, by rfl⟩ : syracuseStep 1436885 = 33677) (by norm_num)
theorem B3075317 : Blo 638302 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B1535237 : Blo 638302 1535237 := bbase (se 4 (by rfl) ⟨143928, by rfl⟩ : syracuseStep 1535237 = 287857) (by norm_num)
theorem B3239189 : Blo 638302 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B1436957 : Blo 638302 1436957 := bbase (se 3 (by rfl) ⟨269429, by rfl⟩ : syracuseStep 1436957 = 538859) (by norm_num)
theorem B2157893 : Blo 638302 2157893 := bbase (se 4 (by rfl) ⟨202302, by rfl⟩ : syracuseStep 2157893 = 404605) (by norm_num)
theorem B748873 : Blo 638302 748873 := bbase (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) (by norm_num)
theorem B1437029 : Blo 638302 1437029 := bbase (se 4 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 1437029 = 269443) (by norm_num)
theorem B1437101 : Blo 638302 1437101 := bbase (se 3 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 1437101 = 538913) (by norm_num)
theorem B1535429 : Blo 638302 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B683489 : Blo 638302 683489 := bbase (se 2 (by rfl) ⟨256308, by rfl⟩ : syracuseStep 683489 = 512617) (by norm_num)
theorem B1437173 : Blo 638302 1437173 := bbase (se 5 (by rfl) ⟨67367, by rfl⟩ : syracuseStep 1437173 = 134735) (by norm_num)
theorem B1535525 : Blo 638302 1535525 := bbase (se 4 (by rfl) ⟨143955, by rfl⟩ : syracuseStep 1535525 = 287911) (by norm_num)
theorem B1437245 : Blo 638302 1437245 := bbase (se 3 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 1437245 = 538967) (by norm_num)
theorem B1437317 : Blo 638302 1437317 := bbase (se 4 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 1437317 = 269497) (by norm_num)
theorem B683677 : Blo 638302 683677 := bbase (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) (by norm_num)
theorem B1437389 : Blo 638302 1437389 := bbase (se 3 (by rfl) ⟨269510, by rfl⟩ : syracuseStep 1437389 = 539021) (by norm_num)
theorem B1732309 : Blo 638302 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B2158325 : Blo 638302 2158325 := bbase (se 5 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 2158325 = 202343) (by norm_num)
theorem B913141 : Blo 638302 913141 := bbase (se 5 (by rfl) ⟨42803, by rfl⟩ : syracuseStep 913141 = 85607) (by norm_num)
theorem B1437461 : Blo 638302 1437461 := bbase (se 6 (by rfl) ⟨33690, by rfl⟩ : syracuseStep 1437461 = 67381) (by norm_num)
theorem B1437533 : Blo 638302 1437533 := bbase (se 3 (by rfl) ⟨269537, by rfl⟩ : syracuseStep 1437533 = 539075) (by norm_num)
theorem B1437605 : Blo 638302 1437605 := bbase (se 4 (by rfl) ⟨134775, by rfl⟩ : syracuseStep 1437605 = 269551) (by norm_num)
theorem B1077205 : Blo 638302 1077205 := bbase (se 7 (by rfl) ⟨12623, by rfl⟩ : syracuseStep 1077205 = 25247) (by norm_num)
theorem B1437677 : Blo 638302 1437677 := bbase (se 3 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 1437677 = 539129) (by norm_num)
theorem B6582293 : Blo 638302 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B1077293 : Blo 638302 1077293 := bbase (se 3 (by rfl) ⟨201992, by rfl⟩ : syracuseStep 1077293 = 403985) (by norm_num)
theorem B1437749 : Blo 638302 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B1437821 : Blo 638302 1437821 := bbase (se 3 (by rfl) ⟨269591, by rfl⟩ : syracuseStep 1437821 = 539183) (by norm_num)
theorem B2158757 : Blo 638302 2158757 := bbase (se 4 (by rfl) ⟨202383, by rfl⟩ : syracuseStep 2158757 = 404767) (by norm_num)
theorem B1077421 : Blo 638302 1077421 := bbase (se 3 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 1077421 = 404033) (by norm_num)
theorem B1437893 : Blo 638302 1437893 := bbase (se 4 (by rfl) ⟨134802, by rfl⟩ : syracuseStep 1437893 = 269605) (by norm_num)
theorem B1077509 : Blo 638302 1077509 := bbase (se 4 (by rfl) ⟨101016, by rfl⟩ : syracuseStep 1077509 = 202033) (by norm_num)
theorem B1437965 : Blo 638302 1437965 := bbase (se 3 (by rfl) ⟨269618, by rfl⟩ : syracuseStep 1437965 = 539237) (by norm_num)
theorem B1438037 : Blo 638302 1438037 := bbase (se 10 (by rfl) ⟨2106, by rfl⟩ : syracuseStep 1438037 = 4213) (by norm_num)
theorem B1077637 : Blo 638302 1077637 := bbase (se 4 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 1077637 = 202057) (by norm_num)
theorem B1438109 : Blo 638302 1438109 := bbase (se 3 (by rfl) ⟨269645, by rfl⟩ : syracuseStep 1438109 = 539291) (by norm_num)
theorem B684497 : Blo 638302 684497 := bbase (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) (by norm_num)
theorem B1077725 : Blo 638302 1077725 := bbase (se 3 (by rfl) ⟨202073, by rfl⟩ : syracuseStep 1077725 = 404147) (by norm_num)
theorem B1438181 : Blo 638302 1438181 := bbase (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) (by norm_num)
theorem B913933 : Blo 638302 913933 := bbase (se 3 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 913933 = 342725) (by norm_num)
theorem B3240485 : Blo 638302 3240485 := bbase (se 4 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 3240485 = 607591) (by norm_num)
theorem B1438253 : Blo 638302 1438253 := bbase (se 3 (by rfl) ⟨269672, by rfl⟩ : syracuseStep 1438253 = 539345) (by norm_num)
theorem B2159189 : Blo 638302 2159189 := bbase (se 8 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 2159189 = 25303) (by norm_num)
theorem B1077853 : Blo 638302 1077853 := bbase (se 3 (by rfl) ⟨202097, by rfl⟩ : syracuseStep 1077853 = 404195) (by norm_num)
theorem B1438325 : Blo 638302 1438325 := bbase (se 5 (by rfl) ⟨67421, by rfl⟩ : syracuseStep 1438325 = 134843) (by norm_num)
theorem B1077941 : Blo 638302 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B1438397 : Blo 638302 1438397 := bbase (se 3 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 1438397 = 539399) (by norm_num)
theorem B1438469 : Blo 638302 1438469 := bbase (se 4 (by rfl) ⟨134856, by rfl⟩ : syracuseStep 1438469 = 269713) (by norm_num)
theorem B1078069 : Blo 638302 1078069 := bbase (se 5 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 1078069 = 101069) (by norm_num)
theorem B1438541 : Blo 638302 1438541 := bbase (se 3 (by rfl) ⟨269726, by rfl⟩ : syracuseStep 1438541 = 539453) (by norm_num)
theorem B914269 : Blo 638302 914269 := bbase (se 3 (by rfl) ⟨171425, by rfl⟩ : syracuseStep 914269 = 342851) (by norm_num)
theorem B1078157 : Blo 638302 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B684941 : Blo 638302 684941 := bbase (se 3 (by rfl) ⟨128426, by rfl⟩ : syracuseStep 684941 = 256853) (by norm_num)
theorem B1438613 : Blo 638302 1438613 := bbase (se 6 (by rfl) ⟨33717, by rfl⟩ : syracuseStep 1438613 = 67435) (by norm_num)
theorem B1438685 : Blo 638302 1438685 := bbase (se 3 (by rfl) ⟨269753, by rfl⟩ : syracuseStep 1438685 = 539507) (by norm_num)
theorem B3109877 : Blo 638302 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2159621 : Blo 638302 2159621 := bbase (se 4 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 2159621 = 404929) (by norm_num)
theorem B1078285 : Blo 638302 1078285 := bbase (se 3 (by rfl) ⟨202178, by rfl⟩ : syracuseStep 1078285 = 404357) (by norm_num)
theorem B1438757 : Blo 638302 1438757 := bbase (se 4 (by rfl) ⟨134883, by rfl⟩ : syracuseStep 1438757 = 269767) (by norm_num)
theorem B914485 : Blo 638302 914485 := bbase (se 5 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 914485 = 85733) (by norm_num)
theorem B6157397 : Blo 638302 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1078373 : Blo 638302 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B1438829 : Blo 638302 1438829 := bbase (se 3 (by rfl) ⟨269780, by rfl⟩ : syracuseStep 1438829 = 539561) (by norm_num)
theorem B685189 : Blo 638302 685189 := bbase (se 4 (by rfl) ⟨64236, by rfl⟩ : syracuseStep 685189 = 128473) (by norm_num)
theorem B1438901 : Blo 638302 1438901 := bbase (se 5 (by rfl) ⟨67448, by rfl⟩ : syracuseStep 1438901 = 134897) (by norm_num)
theorem B17528021 : Blo 638302 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B1733845 : Blo 638302 1733845 := bbase (se 7 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 1733845 = 40637) (by norm_num)
theorem B1078501 : Blo 638302 1078501 := bbase (se 4 (by rfl) ⟨101109, by rfl⟩ : syracuseStep 1078501 = 202219) (by norm_num)
theorem B1438973 : Blo 638302 1438973 := bbase (se 3 (by rfl) ⟨269807, by rfl⟩ : syracuseStep 1438973 = 539615) (by norm_num)
theorem B718105 : Blo 638302 718105 := bbase (se 2 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 718105 = 538579) (by norm_num)
theorem B718141 : Blo 638302 718141 := bbase (se 3 (by rfl) ⟨134651, by rfl⟩ : syracuseStep 718141 = 269303) (by norm_num)
theorem B1078589 : Blo 638302 1078589 := bbase (se 3 (by rfl) ⟨202235, by rfl⟩ : syracuseStep 1078589 = 404471) (by norm_num)
theorem B1439045 : Blo 638302 1439045 := bbase (se 4 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 1439045 = 269821) (by norm_num)
theorem B12285269 : Blo 638302 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B718177 : Blo 638302 718177 := bbase (se 2 (by rfl) ⟨269316, by rfl⟩ : syracuseStep 718177 = 538633) (by norm_num)
theorem B718213 : Blo 638302 718213 := bbase (se 4 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 718213 = 134665) (by norm_num)
theorem B1439117 : Blo 638302 1439117 := bbase (se 3 (by rfl) ⟨269834, by rfl⟩ : syracuseStep 1439117 = 539669) (by norm_num)
theorem B718249 : Blo 638302 718249 := bbase (se 2 (by rfl) ⟨269343, by rfl⟩ : syracuseStep 718249 = 538687) (by norm_num)
theorem B2160053 : Blo 638302 2160053 := bbase (se 5 (by rfl) ⟨101252, by rfl⟩ : syracuseStep 2160053 = 202505) (by norm_num)
theorem B1078717 : Blo 638302 1078717 := bbase (se 3 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 1078717 = 404519) (by norm_num)
theorem B718285 : Blo 638302 718285 := bbase (se 3 (by rfl) ⟨134678, by rfl⟩ : syracuseStep 718285 = 269357) (by norm_num)
theorem B1439189 : Blo 638302 1439189 := bbase (se 7 (by rfl) ⟨16865, by rfl⟩ : syracuseStep 1439189 = 33731) (by norm_num)
theorem B718321 : Blo 638302 718321 := bbase (se 2 (by rfl) ⟨269370, by rfl⟩ : syracuseStep 718321 = 538741) (by norm_num)
theorem B718357 : Blo 638302 718357 := bbase (se 6 (by rfl) ⟨16836, by rfl⟩ : syracuseStep 718357 = 33673) (by norm_num)
theorem B1078805 : Blo 638302 1078805 := bbase (se 6 (by rfl) ⟨25284, by rfl⟩ : syracuseStep 1078805 = 50569) (by norm_num)
theorem B1439261 : Blo 638302 1439261 := bbase (se 3 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 1439261 = 539723) (by norm_num)
theorem B685621 : Blo 638302 685621 := bbase (se 5 (by rfl) ⟨32138, by rfl⟩ : syracuseStep 685621 = 64277) (by norm_num)
theorem B718393 : Blo 638302 718393 := bbase (se 2 (by rfl) ⟨269397, by rfl⟩ : syracuseStep 718393 = 538795) (by norm_num)
theorem B718429 : Blo 638302 718429 := bbase (se 3 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 718429 = 269411) (by norm_num)
theorem B1439333 : Blo 638302 1439333 := bbase (se 4 (by rfl) ⟨134937, by rfl⟩ : syracuseStep 1439333 = 269875) (by norm_num)
theorem B685693 : Blo 638302 685693 := bbase (se 3 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 685693 = 257135) (by norm_num)
theorem B718465 : Blo 638302 718465 := bbase (se 2 (by rfl) ⟨269424, by rfl⟩ : syracuseStep 718465 = 538849) (by norm_num)
theorem B1078933 : Blo 638302 1078933 := bbase (se 6 (by rfl) ⟨25287, by rfl⟩ : syracuseStep 1078933 = 50575) (by norm_num)
theorem B718501 : Blo 638302 718501 := bbase (se 4 (by rfl) ⟨67359, by rfl⟩ : syracuseStep 718501 = 134719) (by norm_num)
theorem B1439405 : Blo 638302 1439405 := bbase (se 3 (by rfl) ⟨269888, by rfl⟩ : syracuseStep 1439405 = 539777) (by norm_num)
theorem B718537 : Blo 638302 718537 := bbase (se 2 (by rfl) ⟨269451, by rfl⟩ : syracuseStep 718537 = 538903) (by norm_num)
theorem B718573 : Blo 638302 718573 := bbase (se 3 (by rfl) ⟨134732, by rfl⟩ : syracuseStep 718573 = 269465) (by norm_num)
theorem B1079021 : Blo 638302 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B1439477 : Blo 638302 1439477 := bbase (se 5 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 1439477 = 134951) (by norm_num)
theorem B718609 : Blo 638302 718609 := bbase (se 2 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 718609 = 538957) (by norm_num)
theorem B718645 : Blo 638302 718645 := bbase (se 5 (by rfl) ⟨33686, by rfl⟩ : syracuseStep 718645 = 67373) (by norm_num)
theorem B3241781 : Blo 638302 3241781 := bbase (se 5 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 3241781 = 303917) (by norm_num)
theorem B1439549 : Blo 638302 1439549 := bbase (se 3 (by rfl) ⟨269915, by rfl⟩ : syracuseStep 1439549 = 539831) (by norm_num)
theorem B718681 : Blo 638302 718681 := bbase (se 2 (by rfl) ⟨269505, by rfl⟩ : syracuseStep 718681 = 539011) (by norm_num)
theorem B2160485 : Blo 638302 2160485 := bbase (se 4 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 2160485 = 405091) (by norm_num)
theorem B1079149 : Blo 638302 1079149 := bbase (se 3 (by rfl) ⟨202340, by rfl⟩ : syracuseStep 1079149 = 404681) (by norm_num)
theorem B718717 : Blo 638302 718717 := bbase (se 3 (by rfl) ⟨134759, by rfl⟩ : syracuseStep 718717 = 269519) (by norm_num)
theorem B1439621 : Blo 638302 1439621 := bbase (se 4 (by rfl) ⟨134964, by rfl⟩ : syracuseStep 1439621 = 269929) (by norm_num)
theorem B718753 : Blo 638302 718753 := bbase (se 2 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 718753 = 539065) (by norm_num)
theorem B1537957 : Blo 638302 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B718789 : Blo 638302 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B1079237 : Blo 638302 1079237 := bbase (se 4 (by rfl) ⟨101178, by rfl⟩ : syracuseStep 1079237 = 202357) (by norm_num)
theorem B1439693 : Blo 638302 1439693 := bbase (se 3 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 1439693 = 539885) (by norm_num)
theorem B718825 : Blo 638302 718825 := bbase (se 2 (by rfl) ⟨269559, by rfl⟩ : syracuseStep 718825 = 539119) (by norm_num)
theorem B718861 : Blo 638302 718861 := bbase (se 3 (by rfl) ⟨134786, by rfl⟩ : syracuseStep 718861 = 269573) (by norm_num)
theorem B1439765 : Blo 638302 1439765 := bbase (se 6 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 1439765 = 67489) (by norm_num)
theorem B718897 : Blo 638302 718897 := bbase (se 2 (by rfl) ⟨269586, by rfl⟩ : syracuseStep 718897 = 539173) (by norm_num)
theorem B1079365 : Blo 638302 1079365 := bbase (se 4 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 1079365 = 202381) (by norm_num)
theorem B718933 : Blo 638302 718933 := bbase (se 8 (by rfl) ⟨4212, by rfl⟩ : syracuseStep 718933 = 8425) (by norm_num)
theorem B1439837 : Blo 638302 1439837 := bbase (se 3 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 1439837 = 539939) (by norm_num)
theorem B718969 : Blo 638302 718969 := bbase (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) (by norm_num)
theorem B719005 : Blo 638302 719005 := bbase (se 3 (by rfl) ⟨134813, by rfl⟩ : syracuseStep 719005 = 269627) (by norm_num)
theorem B1079453 : Blo 638302 1079453 := bbase (se 3 (by rfl) ⟨202397, by rfl⟩ : syracuseStep 1079453 = 404795) (by norm_num)
theorem B1439909 : Blo 638302 1439909 := bbase (se 4 (by rfl) ⟨134991, by rfl⟩ : syracuseStep 1439909 = 269983) (by norm_num)
theorem B719041 : Blo 638302 719041 := bbase (se 2 (by rfl) ⟨269640, by rfl⟩ : syracuseStep 719041 = 539281) (by norm_num)
theorem B719077 : Blo 638302 719077 := bbase (se 4 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 719077 = 134827) (by norm_num)
theorem B1439981 : Blo 638302 1439981 := bbase (se 3 (by rfl) ⟨269996, by rfl⟩ : syracuseStep 1439981 = 539993) (by norm_num)
theorem B1538293 : Blo 638302 1538293 := bbase (se 5 (by rfl) ⟨72107, by rfl⟩ : syracuseStep 1538293 = 144215) (by norm_num)
theorem B719113 : Blo 638302 719113 := bbase (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) (by norm_num)
theorem B2160917 : Blo 638302 2160917 := bbase (se 6 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 2160917 = 101293) (by norm_num)
theorem B1079581 : Blo 638302 1079581 := bbase (se 3 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 1079581 = 404843) (by norm_num)
theorem B719149 : Blo 638302 719149 := bbase (se 3 (by rfl) ⟨134840, by rfl⟩ : syracuseStep 719149 = 269681) (by norm_num)
theorem B1440053 : Blo 638302 1440053 := bbase (se 5 (by rfl) ⟨67502, by rfl⟩ : syracuseStep 1440053 = 135005) (by norm_num)
theorem B719185 : Blo 638302 719185 := bbase (se 2 (by rfl) ⟨269694, by rfl⟩ : syracuseStep 719185 = 539389) (by norm_num)
theorem B719221 : Blo 638302 719221 := bbase (se 5 (by rfl) ⟨33713, by rfl⟩ : syracuseStep 719221 = 67427) (by norm_num)
theorem B1079669 : Blo 638302 1079669 := bbase (se 5 (by rfl) ⟨50609, by rfl⟩ : syracuseStep 1079669 = 101219) (by norm_num)
theorem B1440125 : Blo 638302 1440125 := bbase (se 3 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 1440125 = 540047) (by norm_num)
theorem B719257 : Blo 638302 719257 := bbase (se 2 (by rfl) ⟨269721, by rfl⟩ : syracuseStep 719257 = 539443) (by norm_num)
theorem B719293 : Blo 638302 719293 := bbase (se 3 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 719293 = 269735) (by norm_num)
theorem B1440197 : Blo 638302 1440197 := bbase (se 4 (by rfl) ⟨135018, by rfl⟩ : syracuseStep 1440197 = 270037) (by norm_num)
theorem B719329 : Blo 638302 719329 := bbase (se 2 (by rfl) ⟨269748, by rfl⟩ : syracuseStep 719329 = 539497) (by norm_num)
theorem B1079797 : Blo 638302 1079797 := bbase (se 5 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 1079797 = 101231) (by norm_num)
theorem B719365 : Blo 638302 719365 := bbase (se 4 (by rfl) ⟨67440, by rfl⟩ : syracuseStep 719365 = 134881) (by norm_num)
theorem B1440269 : Blo 638302 1440269 := bbase (se 3 (by rfl) ⟨270050, by rfl⟩ : syracuseStep 1440269 = 540101) (by norm_num)
theorem B719401 : Blo 638302 719401 := bbase (se 2 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 719401 = 539551) (by norm_num)
theorem B719437 : Blo 638302 719437 := bbase (se 3 (by rfl) ⟨134894, by rfl⟩ : syracuseStep 719437 = 269789) (by norm_num)
theorem B1079885 : Blo 638302 1079885 := bbase (se 3 (by rfl) ⟨202478, by rfl⟩ : syracuseStep 1079885 = 404957) (by norm_num)
theorem B1440341 : Blo 638302 1440341 := bbase (se 8 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 1440341 = 16879) (by norm_num)
theorem B1735253 : Blo 638302 1735253 := bbase (se 8 (by rfl) ⟨10167, by rfl⟩ : syracuseStep 1735253 = 20335) (by norm_num)
theorem B719473 : Blo 638302 719473 := bbase (se 2 (by rfl) ⟨269802, by rfl⟩ : syracuseStep 719473 = 539605) (by norm_num)
theorem B719509 : Blo 638302 719509 := bbase (se 6 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 719509 = 33727) (by norm_num)
theorem B1440413 : Blo 638302 1440413 := bbase (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) (by norm_num)
theorem B719545 : Blo 638302 719545 := bbase (se 2 (by rfl) ⟨269829, by rfl⟩ : syracuseStep 719545 = 539659) (by norm_num)
theorem B2161349 : Blo 638302 2161349 := bbase (se 4 (by rfl) ⟨202626, by rfl⟩ : syracuseStep 2161349 = 405253) (by norm_num)
theorem B1080013 : Blo 638302 1080013 := bbase (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) (by norm_num)
theorem B719581 : Blo 638302 719581 := bbase (se 3 (by rfl) ⟨134921, by rfl⟩ : syracuseStep 719581 = 269843) (by norm_num)
theorem B1440485 : Blo 638302 1440485 := bbase (se 4 (by rfl) ⟨135045, by rfl⟩ : syracuseStep 1440485 = 270091) (by norm_num)
theorem B719617 : Blo 638302 719617 := bbase (se 2 (by rfl) ⟨269856, by rfl⟩ : syracuseStep 719617 = 539713) (by norm_num)
theorem B1735445 : Blo 638302 1735445 := bbase (se 6 (by rfl) ⟨40674, by rfl⟩ : syracuseStep 1735445 = 81349) (by norm_num)
theorem B719653 : Blo 638302 719653 := bbase (se 4 (by rfl) ⟨67467, by rfl⟩ : syracuseStep 719653 = 134935) (by norm_num)
theorem B1080101 : Blo 638302 1080101 := bbase (se 4 (by rfl) ⟨101259, by rfl⟩ : syracuseStep 1080101 = 202519) (by norm_num)
theorem B1440557 : Blo 638302 1440557 := bbase (se 3 (by rfl) ⟨270104, by rfl⟩ : syracuseStep 1440557 = 540209) (by norm_num)
theorem B2423621 : Blo 638302 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B719689 : Blo 638302 719689 := bbase (se 2 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 719689 = 539767) (by norm_num)
theorem B1538909 : Blo 638302 1538909 := bbase (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) (by norm_num)
theorem B719725 : Blo 638302 719725 := bbase (se 3 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 719725 = 269897) (by norm_num)
theorem B1440629 : Blo 638302 1440629 := bbase (se 5 (by rfl) ⟨67529, by rfl⟩ : syracuseStep 1440629 = 135059) (by norm_num)
theorem B719761 : Blo 638302 719761 := bbase (se 2 (by rfl) ⟨269910, by rfl⟩ : syracuseStep 719761 = 539821) (by norm_num)
theorem B1080229 : Blo 638302 1080229 := bbase (se 4 (by rfl) ⟨101271, by rfl⟩ : syracuseStep 1080229 = 202543) (by norm_num)
theorem B719797 : Blo 638302 719797 := bbase (se 5 (by rfl) ⟨33740, by rfl⟩ : syracuseStep 719797 = 67481) (by norm_num)
theorem B1440701 : Blo 638302 1440701 := bbase (se 3 (by rfl) ⟨270131, by rfl⟩ : syracuseStep 1440701 = 540263) (by norm_num)
theorem B719833 : Blo 638302 719833 := bbase (se 2 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 719833 = 539875) (by norm_num)
theorem B719869 : Blo 638302 719869 := bbase (se 3 (by rfl) ⟨134975, by rfl⟩ : syracuseStep 719869 = 269951) (by norm_num)
theorem B1080317 : Blo 638302 1080317 := bbase (se 3 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 1080317 = 405119) (by norm_num)
theorem B1440773 : Blo 638302 1440773 := bbase (se 4 (by rfl) ⟨135072, by rfl⟩ : syracuseStep 1440773 = 270145) (by norm_num)
theorem B719905 : Blo 638302 719905 := bbase (se 2 (by rfl) ⟨269964, by rfl⟩ : syracuseStep 719905 = 539929) (by norm_num)
theorem B719941 : Blo 638302 719941 := bbase (se 4 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 719941 = 134989) (by norm_num)
theorem B3243077 : Blo 638302 3243077 := bbase (se 4 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 3243077 = 608077) (by norm_num)
theorem B1440845 : Blo 638302 1440845 := bbase (se 3 (by rfl) ⟨270158, by rfl⟩ : syracuseStep 1440845 = 540317) (by norm_num)
theorem B719977 : Blo 638302 719977 := bbase (se 2 (by rfl) ⟨269991, by rfl⟩ : syracuseStep 719977 = 539983) (by norm_num)
theorem B2161781 : Blo 638302 2161781 := bbase (se 5 (by rfl) ⟨101333, by rfl⟩ : syracuseStep 2161781 = 202667) (by norm_num)
theorem B1080445 : Blo 638302 1080445 := bbase (se 3 (by rfl) ⟨202583, by rfl⟩ : syracuseStep 1080445 = 405167) (by norm_num)
theorem B720013 : Blo 638302 720013 := bbase (se 3 (by rfl) ⟨135002, by rfl⟩ : syracuseStep 720013 = 270005) (by norm_num)
theorem B1440917 : Blo 638302 1440917 := bbase (se 6 (by rfl) ⟨33771, by rfl⟩ : syracuseStep 1440917 = 67543) (by norm_num)
theorem B720049 : Blo 638302 720049 := bbase (se 2 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 720049 = 540037) (by norm_num)
theorem B4848821 : Blo 638302 4848821 := bbase (se 5 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 4848821 = 454577) (by norm_num)
theorem B720085 : Blo 638302 720085 := bbase (se 7 (by rfl) ⟨8438, by rfl⟩ : syracuseStep 720085 = 16877) (by norm_num)
theorem B1080533 : Blo 638302 1080533 := bbase (se 7 (by rfl) ⟨12662, by rfl⟩ : syracuseStep 1080533 = 25325) (by norm_num)
theorem B1440989 : Blo 638302 1440989 := bbase (se 3 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 1440989 = 540371) (by norm_num)
theorem B720121 : Blo 638302 720121 := bbase (se 2 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 720121 = 540091) (by norm_num)
theorem B1539341 : Blo 638302 1539341 := bbase (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) (by norm_num)
theorem B720157 : Blo 638302 720157 := bbase (se 3 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 720157 = 270059) (by norm_num)
theorem B1441061 : Blo 638302 1441061 := bbase (se 4 (by rfl) ⟨135099, by rfl⟩ : syracuseStep 1441061 = 270199) (by norm_num)
theorem B4914485 : Blo 638302 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B720193 : Blo 638302 720193 := bbase (se 2 (by rfl) ⟨270072, by rfl⟩ : syracuseStep 720193 = 540145) (by norm_num)
theorem B1080661 : Blo 638302 1080661 := bbase (se 11 (by rfl) ⟨791, by rfl⟩ : syracuseStep 1080661 = 1583) (by norm_num)
theorem B720229 : Blo 638302 720229 := bbase (se 4 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 720229 = 135043) (by norm_num)
theorem B1441133 : Blo 638302 1441133 := bbase (se 3 (by rfl) ⟨270212, by rfl⟩ : syracuseStep 1441133 = 540425) (by norm_num)
theorem B720265 : Blo 638302 720265 := bbase (se 2 (by rfl) ⟨270099, by rfl⟩ : syracuseStep 720265 = 540199) (by norm_num)
theorem B720301 : Blo 638302 720301 := bbase (se 3 (by rfl) ⟨135056, by rfl⟩ : syracuseStep 720301 = 270113) (by norm_num)
theorem B1080749 : Blo 638302 1080749 := bbase (se 3 (by rfl) ⟨202640, by rfl⟩ : syracuseStep 1080749 = 405281) (by norm_num)
theorem B1441205 : Blo 638302 1441205 := bbase (se 5 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 1441205 = 135113) (by norm_num)
theorem B1736117 : Blo 638302 1736117 := bbase (se 5 (by rfl) ⟨81380, by rfl⟩ : syracuseStep 1736117 = 162761) (by norm_num)
theorem B720337 : Blo 638302 720337 := bbase (se 2 (by rfl) ⟨270126, by rfl⟩ : syracuseStep 720337 = 540253) (by norm_num)
theorem B8224213 : Blo 638302 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B720373 : Blo 638302 720373 := bbase (se 5 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 720373 = 67535) (by norm_num)
theorem B1441277 : Blo 638302 1441277 := bbase (se 3 (by rfl) ⟨270239, by rfl⟩ : syracuseStep 1441277 = 540479) (by norm_num)
theorem B1211917 : Blo 638302 1211917 := bbase (se 3 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 1211917 = 454469) (by norm_num)
theorem B720409 : Blo 638302 720409 := bbase (se 2 (by rfl) ⟨270153, by rfl⟩ : syracuseStep 720409 = 540307) (by norm_num)
theorem B2162213 : Blo 638302 2162213 := bbase (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) (by norm_num)
theorem B1080877 : Blo 638302 1080877 := bbase (se 3 (by rfl) ⟨202664, by rfl⟩ : syracuseStep 1080877 = 405329) (by norm_num)
theorem B720445 : Blo 638302 720445 := bbase (se 3 (by rfl) ⟨135083, by rfl⟩ : syracuseStep 720445 = 270167) (by norm_num)
theorem B1441349 : Blo 638302 1441349 := bbase (se 4 (by rfl) ⟨135126, by rfl⟩ : syracuseStep 1441349 = 270253) (by norm_num)
theorem B720481 : Blo 638302 720481 := bbase (se 2 (by rfl) ⟨270180, by rfl⟩ : syracuseStep 720481 = 540361) (by norm_num)
theorem B720517 : Blo 638302 720517 := bbase (se 4 (by rfl) ⟨67548, by rfl⟩ : syracuseStep 720517 = 135097) (by norm_num)
theorem B1080965 : Blo 638302 1080965 := bbase (se 4 (by rfl) ⟨101340, by rfl⟩ : syracuseStep 1080965 = 202681) (by norm_num)
theorem B1441421 : Blo 638302 1441421 := bbase (se 3 (by rfl) ⟨270266, by rfl⟩ : syracuseStep 1441421 = 540533) (by norm_num)
theorem B720553 : Blo 638302 720553 := bbase (se 2 (by rfl) ⟨270207, by rfl⟩ : syracuseStep 720553 = 540415) (by norm_num)
theorem B1212077 : Blo 638302 1212077 := bbase (se 3 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 1212077 = 454529) (by norm_num)
theorem B720589 : Blo 638302 720589 := bbase (se 3 (by rfl) ⟨135110, by rfl⟩ : syracuseStep 720589 = 270221) (by norm_num)
theorem B1441493 : Blo 638302 1441493 := bbase (se 7 (by rfl) ⟨16892, by rfl⟩ : syracuseStep 1441493 = 33785) (by norm_num)
theorem B720625 : Blo 638302 720625 := bbase (se 2 (by rfl) ⟨270234, by rfl⟩ : syracuseStep 720625 = 540469) (by norm_num)
theorem B1081093 : Blo 638302 1081093 := bbase (se 4 (by rfl) ⟨101352, by rfl⟩ : syracuseStep 1081093 = 202705) (by norm_num)
theorem B720661 : Blo 638302 720661 := bbase (se 6 (by rfl) ⟨16890, by rfl⟩ : syracuseStep 720661 = 33781) (by norm_num)
theorem B1441565 : Blo 638302 1441565 := bbase (se 3 (by rfl) ⟨270293, by rfl⟩ : syracuseStep 1441565 = 540587) (by norm_num)
theorem B720697 : Blo 638302 720697 := bbase (se 2 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 720697 = 540523) (by norm_num)
theorem B1212221 : Blo 638302 1212221 := bbase (se 3 (by rfl) ⟨227291, by rfl⟩ : syracuseStep 1212221 = 454583) (by norm_num)
theorem B720733 : Blo 638302 720733 := bbase (se 3 (by rfl) ⟨135137, by rfl⟩ : syracuseStep 720733 = 270275) (by norm_num)
theorem B1081181 : Blo 638302 1081181 := bbase (se 3 (by rfl) ⟨202721, by rfl⟩ : syracuseStep 1081181 = 405443) (by norm_num)
theorem B1441637 : Blo 638302 1441637 := bbase (se 4 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 1441637 = 270307) (by norm_num)
theorem B1539965 : Blo 638302 1539965 := bbase (se 3 (by rfl) ⟨288743, by rfl⟩ : syracuseStep 1539965 = 577487) (by norm_num)
theorem B720769 : Blo 638302 720769 := bbase (se 2 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 720769 = 540577) (by norm_num)
theorem B720805 : Blo 638302 720805 := bbase (se 4 (by rfl) ⟨67575, by rfl⟩ : syracuseStep 720805 = 135151) (by norm_num)
theorem B1441709 : Blo 638302 1441709 := bbase (se 3 (by rfl) ⟨270320, by rfl⟩ : syracuseStep 1441709 = 540641) (by norm_num)
theorem B720841 : Blo 638302 720841 := bbase (se 2 (by rfl) ⟨270315, by rfl⟩ : syracuseStep 720841 = 540631) (by norm_num)
theorem B2162645 : Blo 638302 2162645 := bbase (se 7 (by rfl) ⟨25343, by rfl⟩ : syracuseStep 2162645 = 50687) (by norm_num)
theorem B1081309 : Blo 638302 1081309 := bbase (se 3 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 1081309 = 405491) (by norm_num)
theorem B720877 : Blo 638302 720877 := bbase (se 3 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 720877 = 270329) (by norm_num)
theorem B1441781 : Blo 638302 1441781 := bbase (se 5 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 1441781 = 135167) (by norm_num)
theorem B1081363 : Blo 638302 1081363 := bstep (se 1 (by rfl) ⟨811022, by rfl⟩ : syracuseStep 1081363 = 1622045) B1622045
theorem B720931 : Blo 638302 720931 := bstep (se 1 (by rfl) ⟨540698, by rfl⟩ : syracuseStep 720931 = 1081397) B1081397
theorem B1081505 : Blo 638302 1081505 := bstep (se 2 (by rfl) ⟨405564, by rfl⟩ : syracuseStep 1081505 = 811129) B811129
theorem B2162861 : Blo 638302 2162861 := bstep (se 3 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 2162861 = 811073) B811073
theorem B721075 : Blo 638302 721075 := bstep (se 1 (by rfl) ⟨540806, by rfl⟩ : syracuseStep 721075 = 1081613) B1081613
theorem B2162915 : Blo 638302 2162915 := bstep (se 1 (by rfl) ⟨1622186, by rfl⟩ : syracuseStep 2162915 = 3244373) B3244373
theorem B1442033 : Blo 638302 1442033 := bstep (se 2 (by rfl) ⟨540762, by rfl⟩ : syracuseStep 1442033 = 1081525) B1081525
theorem B1442051 : Blo 638302 1442051 := bstep (se 1 (by rfl) ⟨1081538, by rfl⟩ : syracuseStep 1442051 = 2163077) B2163077
theorem B1081633 : Blo 638302 1081633 := bstep (se 2 (by rfl) ⟨405612, by rfl⟩ : syracuseStep 1081633 = 811225) B811225
theorem B1212707 : Blo 638302 1212707 := bstep (se 1 (by rfl) ⟨909530, by rfl⟩ : syracuseStep 1212707 = 1819061) B1819061
theorem B1081667 : Blo 638302 1081667 := bstep (se 1 (by rfl) ⟨811250, by rfl⟩ : syracuseStep 1081667 = 1622501) B1622501
theorem B721219 : Blo 638302 721219 := bstep (se 1 (by rfl) ⟨540914, by rfl⟩ : syracuseStep 721219 = 1081829) B1081829
theorem B1081795 : Blo 638302 1081795 := bstep (se 1 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 1081795 = 1622693) B1622693
theorem B721363 : Blo 638302 721363 := bstep (se 1 (by rfl) ⟨541022, by rfl⟩ : syracuseStep 721363 = 1082045) B1082045
theorem B2163185 : Blo 638302 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B1442321 : Blo 638302 1442321 := bstep (se 2 (by rfl) ⟨540870, by rfl⟩ : syracuseStep 1442321 = 1081741) B1081741
theorem B1442339 : Blo 638302 1442339 := bstep (se 1 (by rfl) ⟨1081754, by rfl⟩ : syracuseStep 1442339 = 2163509) B2163509
theorem B1212995 : Blo 638302 1212995 := bstep (se 1 (by rfl) ⟨909746, by rfl⟩ : syracuseStep 1212995 = 1819493) B1819493
theorem B1081937 : Blo 638302 1081937 := bstep (se 2 (by rfl) ⟨405726, by rfl⟩ : syracuseStep 1081937 = 811453) B811453
theorem B721507 : Blo 638302 721507 := bstep (se 1 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 721507 = 1082261) B1082261
theorem B1082065 : Blo 638302 1082065 := bstep (se 2 (by rfl) ⟨405774, by rfl⟩ : syracuseStep 1082065 = 811549) B811549
theorem B721651 : Blo 638302 721651 := bstep (se 1 (by rfl) ⟨541238, by rfl⟩ : syracuseStep 721651 = 1082477) B1082477
theorem B1082099 : Blo 638302 1082099 := bstep (se 1 (by rfl) ⟨811574, by rfl⟩ : syracuseStep 1082099 = 1623149) B1623149
theorem B8225549 : Blo 638302 8225549 := bstep (se 3 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 8225549 = 3084581) B3084581
theorem B1442609 : Blo 638302 1442609 := bstep (se 2 (by rfl) ⟨540978, by rfl⟩ : syracuseStep 1442609 = 1081957) B1081957
theorem B1442627 : Blo 638302 1442627 := bstep (se 1 (by rfl) ⟨1081970, by rfl⟩ : syracuseStep 1442627 = 2163941) B2163941
theorem B1082227 : Blo 638302 1082227 := bstep (se 1 (by rfl) ⟨811670, by rfl⟩ : syracuseStep 1082227 = 1623341) B1623341
theorem B721795 : Blo 638302 721795 := bstep (se 1 (by rfl) ⟨541346, by rfl⟩ : syracuseStep 721795 = 1082693) B1082693
theorem B1868689 : Blo 638302 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B1082369 : Blo 638302 1082369 := bstep (se 2 (by rfl) ⟨405888, by rfl⟩ : syracuseStep 1082369 = 811777) B811777
theorem B2163725 : Blo 638302 2163725 := bstep (se 3 (by rfl) ⟨405698, by rfl⟩ : syracuseStep 2163725 = 811397) B811397
theorem B721939 : Blo 638302 721939 := bstep (se 1 (by rfl) ⟨541454, by rfl⟩ : syracuseStep 721939 = 1082909) B1082909
theorem B2163779 : Blo 638302 2163779 := bstep (se 1 (by rfl) ⟨1622834, by rfl⟩ : syracuseStep 2163779 = 3245669) B3245669
theorem B1442897 : Blo 638302 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B1442915 : Blo 638302 1442915 := bstep (se 1 (by rfl) ⟨1082186, by rfl⟩ : syracuseStep 1442915 = 2164373) B2164373
theorem B1082497 : Blo 638302 1082497 := bstep (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) B811873
theorem B4392077 : Blo 638302 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B1082531 : Blo 638302 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B722083 : Blo 638302 722083 := bstep (se 1 (by rfl) ⟨541562, by rfl⟩ : syracuseStep 722083 = 1083125) B1083125
theorem B1082659 : Blo 638302 1082659 := bstep (se 1 (by rfl) ⟨811994, by rfl⟩ : syracuseStep 1082659 = 1623989) B1623989
theorem B2590001 : Blo 638302 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B722227 : Blo 638302 722227 := bstep (se 1 (by rfl) ⟨541670, by rfl⟩ : syracuseStep 722227 = 1083341) B1083341
theorem B2164049 : Blo 638302 2164049 := bstep (se 2 (by rfl) ⟨811518, by rfl⟩ : syracuseStep 2164049 = 1623037) B1623037
theorem B984403 : Blo 638302 984403 := bstep (se 1 (by rfl) ⟨738302, by rfl⟩ : syracuseStep 984403 = 1476605) B1476605
theorem B1443185 : Blo 638302 1443185 := bstep (se 2 (by rfl) ⟨541194, by rfl⟩ : syracuseStep 1443185 = 1082389) B1082389
theorem B1443203 : Blo 638302 1443203 := bstep (se 1 (by rfl) ⟨1082402, by rfl⟩ : syracuseStep 1443203 = 2164805) B2164805
theorem B1082801 : Blo 638302 1082801 := bstep (se 2 (by rfl) ⟨406050, by rfl⟩ : syracuseStep 1082801 = 812101) B812101
theorem B722371 : Blo 638302 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B1213937 : Blo 638302 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B1082929 : Blo 638302 1082929 := bstep (se 2 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 1082929 = 812197) B812197
theorem B1082963 : Blo 638302 1082963 := bstep (se 1 (by rfl) ⟨812222, by rfl⟩ : syracuseStep 1082963 = 1624445) B1624445
theorem B722515 : Blo 638302 722515 := bstep (se 1 (by rfl) ⟨541886, by rfl⟩ : syracuseStep 722515 = 1083773) B1083773
theorem B1443473 : Blo 638302 1443473 := bstep (se 2 (by rfl) ⟨541302, by rfl⟩ : syracuseStep 1443473 = 1082605) B1082605
theorem B1443491 : Blo 638302 1443491 := bstep (se 1 (by rfl) ⟨1082618, by rfl⟩ : syracuseStep 1443491 = 2165237) B2165237
theorem B1083091 : Blo 638302 1083091 := bstep (se 1 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 1083091 = 1624637) B1624637
theorem B1083233 : Blo 638302 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B2164589 : Blo 638302 2164589 := bstep (se 3 (by rfl) ⟨405860, by rfl⟩ : syracuseStep 2164589 = 811721) B811721
theorem B2164643 : Blo 638302 2164643 := bstep (se 1 (by rfl) ⟨1623482, by rfl⟩ : syracuseStep 2164643 = 3246965) B3246965
theorem B1443761 : Blo 638302 1443761 := bstep (se 2 (by rfl) ⟨541410, by rfl⟩ : syracuseStep 1443761 = 1082821) B1082821
theorem B1443779 : Blo 638302 1443779 := bstep (se 1 (by rfl) ⟨1082834, by rfl⟩ : syracuseStep 1443779 = 2165669) B2165669
theorem B1083361 : Blo 638302 1083361 := bstep (se 2 (by rfl) ⟨406260, by rfl⟩ : syracuseStep 1083361 = 812521) B812521
theorem B1083395 : Blo 638302 1083395 := bstep (se 1 (by rfl) ⟨812546, by rfl⟩ : syracuseStep 1083395 = 1625093) B1625093
theorem B1869905 : Blo 638302 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B2426993 : Blo 638302 2426993 := bstep (se 2 (by rfl) ⟨910122, by rfl⟩ : syracuseStep 2426993 = 1820245) B1820245
theorem B1083523 : Blo 638302 1083523 := bstep (se 1 (by rfl) ⟨812642, by rfl⟩ : syracuseStep 1083523 = 1625285) B1625285
theorem B2164913 : Blo 638302 2164913 := bstep (se 2 (by rfl) ⟨811842, by rfl⟩ : syracuseStep 2164913 = 1623685) B1623685
theorem B1444049 : Blo 638302 1444049 := bstep (se 2 (by rfl) ⟨541518, by rfl⟩ : syracuseStep 1444049 = 1083037) B1083037
theorem B1444067 : Blo 638302 1444067 := bstep (se 1 (by rfl) ⟨1083050, by rfl⟩ : syracuseStep 1444067 = 2166101) B2166101
theorem B1083665 : Blo 638302 1083665 := bstep (se 2 (by rfl) ⟨406374, by rfl⟩ : syracuseStep 1083665 = 812749) B812749
theorem B3279203 : Blo 638302 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B1214833 : Blo 638302 1214833 := bstep (se 2 (by rfl) ⟨455562, by rfl⟩ : syracuseStep 1214833 = 911125) B911125
theorem B1083793 : Blo 638302 1083793 := bstep (se 2 (by rfl) ⟨406422, by rfl⟩ : syracuseStep 1083793 = 812845) B812845
theorem B1083827 : Blo 638302 1083827 := bstep (se 1 (by rfl) ⟨812870, by rfl⟩ : syracuseStep 1083827 = 1625741) B1625741
theorem B2918861 : Blo 638302 2918861 := bstep (se 3 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 2918861 = 1094573) B1094573
theorem B1444337 : Blo 638302 1444337 := bstep (se 2 (by rfl) ⟨541626, by rfl⟩ : syracuseStep 1444337 = 1083253) B1083253
theorem B1444355 : Blo 638302 1444355 := bstep (se 1 (by rfl) ⟨1083266, by rfl⟩ : syracuseStep 1444355 = 2166533) B2166533
theorem B1214993 : Blo 638302 1214993 := bstep (se 2 (by rfl) ⟨455622, by rfl⟩ : syracuseStep 1214993 = 911245) B911245
theorem B3246641 : Blo 638302 3246641 := bstep (se 2 (by rfl) ⟨1217490, by rfl⟩ : syracuseStep 3246641 = 2434981) B2434981
theorem B2165453 : Blo 638302 2165453 := bstep (se 3 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 2165453 = 812045) B812045
theorem B2165507 : Blo 638302 2165507 := bstep (se 1 (by rfl) ⟨1624130, by rfl⟩ : syracuseStep 2165507 = 3248261) B3248261
theorem B1444625 : Blo 638302 1444625 := bstep (se 2 (by rfl) ⟨541734, by rfl⟩ : syracuseStep 1444625 = 1083469) B1083469
theorem B1444643 : Blo 638302 1444643 := bstep (se 1 (by rfl) ⟨1083482, by rfl⟩ : syracuseStep 1444643 = 2166965) B2166965
theorem B1215395 : Blo 638302 1215395 := bstep (se 1 (by rfl) ⟨911546, by rfl⟩ : syracuseStep 1215395 = 1823093) B1823093
theorem B3640261 : Blo 638302 3640261 := bstep (se 4 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 3640261 = 682549) B682549
theorem B2165777 : Blo 638302 2165777 := bstep (se 2 (by rfl) ⟨812166, by rfl⟩ : syracuseStep 2165777 = 1624333) B1624333
theorem B1444913 : Blo 638302 1444913 := bstep (se 2 (by rfl) ⟨541842, by rfl⟩ : syracuseStep 1444913 = 1083685) B1083685
theorem B1444931 : Blo 638302 1444931 := bstep (se 1 (by rfl) ⟨1083698, by rfl⟩ : syracuseStep 1444931 = 2167397) B2167397
theorem B2460941 : Blo 638302 2460941 := bstep (se 3 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 2460941 = 922853) B922853
theorem B7409009 : Blo 638302 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B8752625 : Blo 638302 8752625 := bstep (se 2 (by rfl) ⟨3282234, by rfl⟩ : syracuseStep 8752625 = 6564469) B6564469
theorem B2428451 : Blo 638302 2428451 := bstep (se 1 (by rfl) ⟨1821338, by rfl⟩ : syracuseStep 2428451 = 3642677) B3642677
theorem B2166317 : Blo 638302 2166317 := bstep (se 3 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 2166317 = 812369) B812369
theorem B85298741 : Blo 638302 85298741 := bstep (se 5 (by rfl) ⟨3998378, by rfl⟩ : syracuseStep 85298741 = 7996757) B7996757
theorem B2166371 : Blo 638302 2166371 := bstep (se 1 (by rfl) ⟨1624778, by rfl⟩ : syracuseStep 2166371 = 3249557) B3249557
theorem B1216291 : Blo 638302 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B2166641 : Blo 638302 2166641 := bstep (se 2 (by rfl) ⟨812490, by rfl⟩ : syracuseStep 2166641 = 1624981) B1624981
theorem B22548365 : Blo 638302 22548365 := bstep (se 3 (by rfl) ⟨4227818, by rfl⟩ : syracuseStep 22548365 = 8455637) B8455637
theorem B1216451 : Blo 638302 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B3248099 : Blo 638302 3248099 := bstep (se 1 (by rfl) ⟨2436074, by rfl⟩ : syracuseStep 3248099 = 4872149) B4872149
theorem B7901381 : Blo 638302 7901381 := bstep (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) B1481509
theorem B2167181 : Blo 638302 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B2167235 : Blo 638302 2167235 := bstep (se 1 (by rfl) ⟨1625426, by rfl⟩ : syracuseStep 2167235 = 3250853) B3250853
theorem B2429453 : Blo 638302 2429453 := bstep (se 3 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 2429453 = 911045) B911045
theorem B1151587 : Blo 638302 1151587 := bstep (se 1 (by rfl) ⟨863690, by rfl⟩ : syracuseStep 1151587 = 1727381) B1727381
theorem B10359409 : Blo 638302 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B823987 : Blo 638302 823987 := bstep (se 1 (by rfl) ⟨617990, by rfl⟩ : syracuseStep 823987 = 1235981) B1235981
theorem B2167505 : Blo 638302 2167505 := bstep (se 2 (by rfl) ⟨812814, by rfl⟩ : syracuseStep 2167505 = 1625629) B1625629
theorem B3248909 : Blo 638302 3248909 := bstep (se 3 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 3248909 = 1218341) B1218341
theorem B1643377 : Blo 638302 1643377 := bstep (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) B1232533
theorem B3642245 : Blo 638302 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1217521 : Blo 638302 1217521 := bstep (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) B913141
theorem B4101445 : Blo 638302 4101445 := bstep (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) B769021
theorem B4855139 : Blo 638302 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B3282403 : Blo 638302 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B7870193 : Blo 638302 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B3282893 : Blo 638302 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B1218577 : Blo 638302 1218577 := bstep (se 2 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 1218577 = 913933) B913933
theorem B1218979 : Blo 638302 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B1153489 : Blo 638302 1153489 := bstep (se 2 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 1153489 = 865117) B865117
theorem B1219025 : Blo 638302 1219025 := bstep (se 2 (by rfl) ⟨457134, by rfl⟩ : syracuseStep 1219025 = 914269) B914269
theorem B2431565 : Blo 638302 2431565 := bstep (se 3 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 2431565 = 911837) B911837
theorem B7281251 : Blo 638302 7281251 := bstep (se 1 (by rfl) ⟨5460938, by rfl⟩ : syracuseStep 7281251 = 10921877) B10921877
theorem B1219313 : Blo 638302 1219313 := bstep (se 2 (by rfl) ⟨457242, by rfl⟩ : syracuseStep 1219313 = 914485) B914485
theorem B957473 : Blo 638302 957473 := bstep (se 2 (by rfl) ⟨359052, by rfl⟩ : syracuseStep 957473 = 718105) B718105
theorem B957491 : Blo 638302 957491 := bstep (se 1 (by rfl) ⟨718118, by rfl⟩ : syracuseStep 957491 = 1436237) B1436237
theorem B957521 : Blo 638302 957521 := bstep (se 2 (by rfl) ⟨359070, by rfl⟩ : syracuseStep 957521 = 718141) B718141
theorem B957539 : Blo 638302 957539 := bstep (se 1 (by rfl) ⟨718154, by rfl⟩ : syracuseStep 957539 = 1436309) B1436309
theorem B957569 : Blo 638302 957569 := bstep (se 2 (by rfl) ⟨359088, by rfl⟩ : syracuseStep 957569 = 718177) B718177
theorem B2727053 : Blo 638302 2727053 := bstep (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) B1022645
theorem B957587 : Blo 638302 957587 := bstep (se 1 (by rfl) ⟨718190, by rfl⟩ : syracuseStep 957587 = 1436381) B1436381
theorem B957617 : Blo 638302 957617 := bstep (se 2 (by rfl) ⟨359106, by rfl⟩ : syracuseStep 957617 = 718213) B718213
theorem B957635 : Blo 638302 957635 := bstep (se 1 (by rfl) ⟨718226, by rfl⟩ : syracuseStep 957635 = 1436453) B1436453
theorem B957665 : Blo 638302 957665 := bstep (se 2 (by rfl) ⟨359124, by rfl⟩ : syracuseStep 957665 = 718249) B718249
theorem B2301169 : Blo 638302 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B1973489 : Blo 638302 1973489 := bstep (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) B1480117
theorem B957683 : Blo 638302 957683 := bstep (se 1 (by rfl) ⟨718262, by rfl⟩ : syracuseStep 957683 = 1436525) B1436525
theorem B957713 : Blo 638302 957713 := bstep (se 2 (by rfl) ⟨359142, by rfl⟩ : syracuseStep 957713 = 718285) B718285
theorem B957731 : Blo 638302 957731 := bstep (se 1 (by rfl) ⟨718298, by rfl⟩ : syracuseStep 957731 = 1436597) B1436597
theorem B957761 : Blo 638302 957761 := bstep (se 2 (by rfl) ⟨359160, by rfl⟩ : syracuseStep 957761 = 718321) B718321
theorem B957779 : Blo 638302 957779 := bstep (se 1 (by rfl) ⟨718334, by rfl⟩ : syracuseStep 957779 = 1436669) B1436669
theorem B957809 : Blo 638302 957809 := bstep (se 2 (by rfl) ⟨359178, by rfl⟩ : syracuseStep 957809 = 718357) B718357
theorem B2432369 : Blo 638302 2432369 := bstep (se 2 (by rfl) ⟨912138, by rfl⟩ : syracuseStep 2432369 = 1824277) B1824277
theorem B957827 : Blo 638302 957827 := bstep (se 1 (by rfl) ⟨718370, by rfl⟩ : syracuseStep 957827 = 1436741) B1436741
theorem B4627853 : Blo 638302 4627853 := bstep (se 3 (by rfl) ⟨867722, by rfl⟩ : syracuseStep 4627853 = 1735445) B1735445
theorem B957857 : Blo 638302 957857 := bstep (se 2 (by rfl) ⟨359196, by rfl⟩ : syracuseStep 957857 = 718393) B718393
theorem B957875 : Blo 638302 957875 := bstep (se 1 (by rfl) ⟨718406, by rfl⟩ : syracuseStep 957875 = 1436813) B1436813
theorem B957905 : Blo 638302 957905 := bstep (se 2 (by rfl) ⟨359214, by rfl⟩ : syracuseStep 957905 = 718429) B718429
theorem B2727395 : Blo 638302 2727395 := bstep (se 1 (by rfl) ⟨2045546, by rfl⟩ : syracuseStep 2727395 = 4091093) B4091093
theorem B957923 : Blo 638302 957923 := bstep (se 1 (by rfl) ⟨718442, by rfl⟩ : syracuseStep 957923 = 1436885) B1436885
theorem B957953 : Blo 638302 957953 := bstep (se 2 (by rfl) ⟨359232, by rfl⟩ : syracuseStep 957953 = 718465) B718465
theorem B1023491 : Blo 638302 1023491 := bstep (se 1 (by rfl) ⟨767618, by rfl⟩ : syracuseStep 1023491 = 1535237) B1535237
theorem B957971 : Blo 638302 957971 := bstep (se 1 (by rfl) ⟨718478, by rfl⟩ : syracuseStep 957971 = 1436957) B1436957
theorem B958001 : Blo 638302 958001 := bstep (se 2 (by rfl) ⟨359250, by rfl⟩ : syracuseStep 958001 = 718501) B718501
theorem B958019 : Blo 638302 958019 := bstep (se 1 (by rfl) ⟨718514, by rfl⟩ : syracuseStep 958019 = 1437029) B1437029
theorem B958049 : Blo 638302 958049 := bstep (se 2 (by rfl) ⟨359268, by rfl⟩ : syracuseStep 958049 = 718537) B718537
theorem B958067 : Blo 638302 958067 := bstep (se 1 (by rfl) ⟨718550, by rfl⟩ : syracuseStep 958067 = 1437101) B1437101
theorem B1023619 : Blo 638302 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B958097 : Blo 638302 958097 := bstep (se 2 (by rfl) ⟨359286, by rfl⟩ : syracuseStep 958097 = 718573) B718573
theorem B958115 : Blo 638302 958115 := bstep (se 1 (by rfl) ⟨718586, by rfl⟩ : syracuseStep 958115 = 1437173) B1437173
theorem B958145 : Blo 638302 958145 := bstep (se 2 (by rfl) ⟨359304, by rfl⟩ : syracuseStep 958145 = 718609) B718609
theorem B1023683 : Blo 638302 1023683 := bstep (se 1 (by rfl) ⟨767762, by rfl⟩ : syracuseStep 1023683 = 1535525) B1535525
theorem B958163 : Blo 638302 958163 := bstep (se 1 (by rfl) ⟨718622, by rfl⟩ : syracuseStep 958163 = 1437245) B1437245
theorem B958193 : Blo 638302 958193 := bstep (se 2 (by rfl) ⟨359322, by rfl⟩ : syracuseStep 958193 = 718645) B718645
theorem B958211 : Blo 638302 958211 := bstep (se 1 (by rfl) ⟨718658, by rfl⟩ : syracuseStep 958211 = 1437317) B1437317
theorem B958241 : Blo 638302 958241 := bstep (se 2 (by rfl) ⟨359340, by rfl⟩ : syracuseStep 958241 = 718681) B718681
theorem B958259 : Blo 638302 958259 := bstep (se 1 (by rfl) ⟨718694, by rfl⟩ : syracuseStep 958259 = 1437389) B1437389
theorem B958289 : Blo 638302 958289 := bstep (se 2 (by rfl) ⟨359358, by rfl⟩ : syracuseStep 958289 = 718717) B718717
theorem B958307 : Blo 638302 958307 := bstep (se 1 (by rfl) ⟨718730, by rfl⟩ : syracuseStep 958307 = 1437461) B1437461
theorem B6168433 : Blo 638302 6168433 := bstep (se 2 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 6168433 = 4626325) B4626325
theorem B958337 : Blo 638302 958337 := bstep (se 2 (by rfl) ⟨359376, by rfl⟩ : syracuseStep 958337 = 718753) B718753
theorem B958355 : Blo 638302 958355 := bstep (se 1 (by rfl) ⟨718766, by rfl⟩ : syracuseStep 958355 = 1437533) B1437533
theorem B2727857 : Blo 638302 2727857 := bstep (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) B2045893
theorem B958385 : Blo 638302 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B958403 : Blo 638302 958403 := bstep (se 1 (by rfl) ⟨718802, by rfl⟩ : syracuseStep 958403 = 1437605) B1437605
theorem B958433 : Blo 638302 958433 := bstep (se 2 (by rfl) ⟨359412, by rfl⟩ : syracuseStep 958433 = 718825) B718825
theorem B958451 : Blo 638302 958451 := bstep (se 1 (by rfl) ⟨718838, by rfl⟩ : syracuseStep 958451 = 1437677) B1437677
theorem B2433037 : Blo 638302 2433037 := bstep (se 3 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 2433037 = 912389) B912389
theorem B958481 : Blo 638302 958481 := bstep (se 2 (by rfl) ⟨359430, by rfl⟩ : syracuseStep 958481 = 718861) B718861
theorem B958499 : Blo 638302 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B958529 : Blo 638302 958529 := bstep (se 2 (by rfl) ⟨359448, by rfl⟩ : syracuseStep 958529 = 718897) B718897
theorem B958547 : Blo 638302 958547 := bstep (se 1 (by rfl) ⟨718910, by rfl⟩ : syracuseStep 958547 = 1437821) B1437821
theorem B958577 : Blo 638302 958577 := bstep (se 2 (by rfl) ⟨359466, by rfl⟩ : syracuseStep 958577 = 718933) B718933
theorem B958595 : Blo 638302 958595 := bstep (se 1 (by rfl) ⟨718946, by rfl⟩ : syracuseStep 958595 = 1437893) B1437893
theorem B958625 : Blo 638302 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B1024177 : Blo 638302 1024177 := bstep (se 2 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 1024177 = 768133) B768133
theorem B958643 : Blo 638302 958643 := bstep (se 1 (by rfl) ⟨718982, by rfl⟩ : syracuseStep 958643 = 1437965) B1437965
theorem B958673 : Blo 638302 958673 := bstep (se 2 (by rfl) ⟨359502, by rfl⟩ : syracuseStep 958673 = 719005) B719005
theorem B958691 : Blo 638302 958691 := bstep (se 1 (by rfl) ⟨719018, by rfl⟩ : syracuseStep 958691 = 1438037) B1438037
theorem B1155313 : Blo 638302 1155313 := bstep (se 2 (by rfl) ⟨433242, by rfl⟩ : syracuseStep 1155313 = 866485) B866485
theorem B958721 : Blo 638302 958721 := bstep (se 2 (by rfl) ⟨359520, by rfl⟩ : syracuseStep 958721 = 719041) B719041
theorem B958739 : Blo 638302 958739 := bstep (se 1 (by rfl) ⟨719054, by rfl⟩ : syracuseStep 958739 = 1438109) B1438109
theorem B958769 : Blo 638302 958769 := bstep (se 2 (by rfl) ⟨359538, by rfl⟩ : syracuseStep 958769 = 719077) B719077
theorem B1155377 : Blo 638302 1155377 := bstep (se 2 (by rfl) ⟨433266, by rfl⟩ : syracuseStep 1155377 = 866533) B866533
theorem B958787 : Blo 638302 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B958817 : Blo 638302 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B958835 : Blo 638302 958835 := bstep (se 1 (by rfl) ⟨719126, by rfl⟩ : syracuseStep 958835 = 1438253) B1438253
theorem B958865 : Blo 638302 958865 := bstep (se 2 (by rfl) ⟨359574, by rfl⟩ : syracuseStep 958865 = 719149) B719149
theorem B958883 : Blo 638302 958883 := bstep (se 1 (by rfl) ⟨719162, by rfl⟩ : syracuseStep 958883 = 1438325) B1438325
theorem B958913 : Blo 638302 958913 := bstep (se 2 (by rfl) ⟨359592, by rfl⟩ : syracuseStep 958913 = 719185) B719185
theorem B958931 : Blo 638302 958931 := bstep (se 1 (by rfl) ⟨719198, by rfl⟩ : syracuseStep 958931 = 1438397) B1438397
theorem B958961 : Blo 638302 958961 := bstep (se 2 (by rfl) ⟨359610, by rfl⟩ : syracuseStep 958961 = 719221) B719221
theorem B958979 : Blo 638302 958979 := bstep (se 1 (by rfl) ⟨719234, by rfl⟩ : syracuseStep 958979 = 1438469) B1438469
theorem B959009 : Blo 638302 959009 := bstep (se 2 (by rfl) ⟨359628, by rfl⟩ : syracuseStep 959009 = 719257) B719257
theorem B959027 : Blo 638302 959027 := bstep (se 1 (by rfl) ⟨719270, by rfl⟩ : syracuseStep 959027 = 1438541) B1438541
theorem B959057 : Blo 638302 959057 := bstep (se 2 (by rfl) ⟨359646, by rfl⟩ : syracuseStep 959057 = 719293) B719293
theorem B959075 : Blo 638302 959075 := bstep (se 1 (by rfl) ⟨719306, by rfl⟩ : syracuseStep 959075 = 1438613) B1438613
theorem B959105 : Blo 638302 959105 := bstep (se 2 (by rfl) ⟨359664, by rfl⟩ : syracuseStep 959105 = 719329) B719329
theorem B3646093 : Blo 638302 3646093 := bstep (se 3 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 3646093 = 1367285) B1367285
theorem B959123 : Blo 638302 959123 := bstep (se 1 (by rfl) ⟨719342, by rfl⟩ : syracuseStep 959123 = 1438685) B1438685
theorem B2073251 : Blo 638302 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B1188515 : Blo 638302 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B959153 : Blo 638302 959153 := bstep (se 2 (by rfl) ⟨359682, by rfl⟩ : syracuseStep 959153 = 719365) B719365
theorem B959171 : Blo 638302 959171 := bstep (se 1 (by rfl) ⟨719378, by rfl⟩ : syracuseStep 959171 = 1438757) B1438757
theorem B959201 : Blo 638302 959201 := bstep (se 2 (by rfl) ⟨359700, by rfl⟩ : syracuseStep 959201 = 719401) B719401
theorem B4104931 : Blo 638302 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B959219 : Blo 638302 959219 := bstep (se 1 (by rfl) ⟨719414, by rfl⟩ : syracuseStep 959219 = 1438829) B1438829
theorem B959249 : Blo 638302 959249 := bstep (se 2 (by rfl) ⟨359718, by rfl⟩ : syracuseStep 959249 = 719437) B719437
theorem B959267 : Blo 638302 959267 := bstep (se 1 (by rfl) ⟨719450, by rfl⟩ : syracuseStep 959267 = 1438901) B1438901
theorem B2433827 : Blo 638302 2433827 := bstep (se 1 (by rfl) ⟨1825370, by rfl⟩ : syracuseStep 2433827 = 3650741) B3650741
theorem B959297 : Blo 638302 959297 := bstep (se 2 (by rfl) ⟨359736, by rfl⟩ : syracuseStep 959297 = 719473) B719473
theorem B1024849 : Blo 638302 1024849 := bstep (se 2 (by rfl) ⟨384318, by rfl⟩ : syracuseStep 1024849 = 768637) B768637
theorem B959315 : Blo 638302 959315 := bstep (se 1 (by rfl) ⟨719486, by rfl⟩ : syracuseStep 959315 = 1438973) B1438973
theorem B959345 : Blo 638302 959345 := bstep (se 2 (by rfl) ⟨359754, by rfl⟩ : syracuseStep 959345 = 719509) B719509
theorem B959363 : Blo 638302 959363 := bstep (se 1 (by rfl) ⟨719522, by rfl⟩ : syracuseStep 959363 = 1439045) B1439045
theorem B959393 : Blo 638302 959393 := bstep (se 2 (by rfl) ⟨359772, by rfl⟩ : syracuseStep 959393 = 719545) B719545
theorem B959411 : Blo 638302 959411 := bstep (se 1 (by rfl) ⟨719558, by rfl⟩ : syracuseStep 959411 = 1439117) B1439117
theorem B959441 : Blo 638302 959441 := bstep (se 2 (by rfl) ⟨359790, by rfl⟩ : syracuseStep 959441 = 719581) B719581
theorem B959459 : Blo 638302 959459 := bstep (se 1 (by rfl) ⟨719594, by rfl⟩ : syracuseStep 959459 = 1439189) B1439189
theorem B1647587 : Blo 638302 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B959489 : Blo 638302 959489 := bstep (se 2 (by rfl) ⟨359808, by rfl⟩ : syracuseStep 959489 = 719617) B719617
theorem B959507 : Blo 638302 959507 := bstep (se 1 (by rfl) ⟨719630, by rfl⟩ : syracuseStep 959507 = 1439261) B1439261
theorem B959537 : Blo 638302 959537 := bstep (se 2 (by rfl) ⟨359826, by rfl⟩ : syracuseStep 959537 = 719653) B719653
theorem B959555 : Blo 638302 959555 := bstep (se 1 (by rfl) ⟨719666, by rfl⟩ : syracuseStep 959555 = 1439333) B1439333
theorem B959585 : Blo 638302 959585 := bstep (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) B719689
theorem B959603 : Blo 638302 959603 := bstep (se 1 (by rfl) ⟨719702, by rfl⟩ : syracuseStep 959603 = 1439405) B1439405
theorem B959633 : Blo 638302 959633 := bstep (se 2 (by rfl) ⟨359862, by rfl⟩ : syracuseStep 959633 = 719725) B719725
theorem B959651 : Blo 638302 959651 := bstep (se 1 (by rfl) ⟨719738, by rfl⟩ : syracuseStep 959651 = 1439477) B1439477
theorem B959681 : Blo 638302 959681 := bstep (se 2 (by rfl) ⟨359880, by rfl⟩ : syracuseStep 959681 = 719761) B719761
theorem B959699 : Blo 638302 959699 := bstep (se 1 (by rfl) ⟨719774, by rfl⟩ : syracuseStep 959699 = 1439549) B1439549
theorem B959729 : Blo 638302 959729 := bstep (se 2 (by rfl) ⟨359898, by rfl⟩ : syracuseStep 959729 = 719797) B719797
theorem B959747 : Blo 638302 959747 := bstep (se 1 (by rfl) ⟨719810, by rfl⟩ : syracuseStep 959747 = 1439621) B1439621
theorem B2303245 : Blo 638302 2303245 := bstep (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) B863717
theorem B959777 : Blo 638302 959777 := bstep (se 2 (by rfl) ⟨359916, by rfl⟩ : syracuseStep 959777 = 719833) B719833
theorem B959795 : Blo 638302 959795 := bstep (se 1 (by rfl) ⟨719846, by rfl⟩ : syracuseStep 959795 = 1439693) B1439693
theorem B959825 : Blo 638302 959825 := bstep (se 2 (by rfl) ⟨359934, by rfl⟩ : syracuseStep 959825 = 719869) B719869
theorem B959843 : Blo 638302 959843 := bstep (se 1 (by rfl) ⟨719882, by rfl⟩ : syracuseStep 959843 = 1439765) B1439765
theorem B959873 : Blo 638302 959873 := bstep (se 2 (by rfl) ⟨359952, by rfl⟩ : syracuseStep 959873 = 719905) B719905
theorem B12166541 : Blo 638302 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B959891 : Blo 638302 959891 := bstep (se 1 (by rfl) ⟨719918, by rfl⟩ : syracuseStep 959891 = 1439837) B1439837
theorem B959921 : Blo 638302 959921 := bstep (se 2 (by rfl) ⟨359970, by rfl⟩ : syracuseStep 959921 = 719941) B719941
theorem B2434481 : Blo 638302 2434481 := bstep (se 2 (by rfl) ⟨912930, by rfl⟩ : syracuseStep 2434481 = 1825861) B1825861
theorem B959939 : Blo 638302 959939 := bstep (se 1 (by rfl) ⟨719954, by rfl⟩ : syracuseStep 959939 = 1439909) B1439909
theorem B959969 : Blo 638302 959969 := bstep (se 2 (by rfl) ⟨359988, by rfl⟩ : syracuseStep 959969 = 719977) B719977
theorem B959987 : Blo 638302 959987 := bstep (se 1 (by rfl) ⟨719990, by rfl⟩ : syracuseStep 959987 = 1439981) B1439981
theorem B960017 : Blo 638302 960017 := bstep (se 2 (by rfl) ⟨360006, by rfl⟩ : syracuseStep 960017 = 720013) B720013
theorem B960035 : Blo 638302 960035 := bstep (se 1 (by rfl) ⟨720026, by rfl⟩ : syracuseStep 960035 = 1440053) B1440053
theorem B960065 : Blo 638302 960065 := bstep (se 2 (by rfl) ⟨360024, by rfl⟩ : syracuseStep 960065 = 720049) B720049
theorem B960083 : Blo 638302 960083 := bstep (se 1 (by rfl) ⟨720062, by rfl⟩ : syracuseStep 960083 = 1440125) B1440125
theorem B960113 : Blo 638302 960113 := bstep (se 2 (by rfl) ⟨360042, by rfl⟩ : syracuseStep 960113 = 720085) B720085
theorem B960131 : Blo 638302 960131 := bstep (se 1 (by rfl) ⟨720098, by rfl⟩ : syracuseStep 960131 = 1440197) B1440197
theorem B960161 : Blo 638302 960161 := bstep (se 2 (by rfl) ⟨360060, by rfl⟩ : syracuseStep 960161 = 720121) B720121
theorem B960179 : Blo 638302 960179 := bstep (se 1 (by rfl) ⟨720134, by rfl⟩ : syracuseStep 960179 = 1440269) B1440269
theorem B960209 : Blo 638302 960209 := bstep (se 2 (by rfl) ⟨360078, by rfl⟩ : syracuseStep 960209 = 720157) B720157
theorem B960227 : Blo 638302 960227 := bstep (se 1 (by rfl) ⟨720170, by rfl⟩ : syracuseStep 960227 = 1440341) B1440341
theorem B1156835 : Blo 638302 1156835 := bstep (se 1 (by rfl) ⟨867626, by rfl⟩ : syracuseStep 1156835 = 1735253) B1735253
theorem B960257 : Blo 638302 960257 := bstep (se 2 (by rfl) ⟨360096, by rfl⟩ : syracuseStep 960257 = 720193) B720193
theorem B960275 : Blo 638302 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B960305 : Blo 638302 960305 := bstep (se 2 (by rfl) ⟨360114, by rfl⟩ : syracuseStep 960305 = 720229) B720229
theorem B960323 : Blo 638302 960323 := bstep (se 1 (by rfl) ⟨720242, by rfl⟩ : syracuseStep 960323 = 1440485) B1440485
theorem B960353 : Blo 638302 960353 := bstep (se 2 (by rfl) ⟨360132, by rfl⟩ : syracuseStep 960353 = 720265) B720265
theorem B960371 : Blo 638302 960371 := bstep (se 1 (by rfl) ⟨720278, by rfl⟩ : syracuseStep 960371 = 1440557) B1440557
theorem B1615747 : Blo 638302 1615747 := bstep (se 1 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 1615747 = 2423621) B2423621
theorem B960401 : Blo 638302 960401 := bstep (se 2 (by rfl) ⟨360150, by rfl⟩ : syracuseStep 960401 = 720301) B720301
theorem B1025939 : Blo 638302 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B960419 : Blo 638302 960419 := bstep (se 1 (by rfl) ⟨720314, by rfl⟩ : syracuseStep 960419 = 1440629) B1440629
theorem B1943473 : Blo 638302 1943473 := bstep (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) B1457605
theorem B960449 : Blo 638302 960449 := bstep (se 2 (by rfl) ⟨360168, by rfl⟩ : syracuseStep 960449 = 720337) B720337
theorem B960467 : Blo 638302 960467 := bstep (se 1 (by rfl) ⟨720350, by rfl⟩ : syracuseStep 960467 = 1440701) B1440701
theorem B1845233 : Blo 638302 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B960497 : Blo 638302 960497 := bstep (se 2 (by rfl) ⟨360186, by rfl⟩ : syracuseStep 960497 = 720373) B720373
theorem B960515 : Blo 638302 960515 := bstep (se 1 (by rfl) ⟨720386, by rfl⟩ : syracuseStep 960515 = 1440773) B1440773
theorem B1615889 : Blo 638302 1615889 := bstep (se 2 (by rfl) ⟨605958, by rfl⟩ : syracuseStep 1615889 = 1211917) B1211917
theorem B960545 : Blo 638302 960545 := bstep (se 2 (by rfl) ⟨360204, by rfl⟩ : syracuseStep 960545 = 720409) B720409
theorem B960563 : Blo 638302 960563 := bstep (se 1 (by rfl) ⟨720422, by rfl⟩ : syracuseStep 960563 = 1440845) B1440845
theorem B960593 : Blo 638302 960593 := bstep (se 2 (by rfl) ⟨360222, by rfl⟩ : syracuseStep 960593 = 720445) B720445
theorem B960611 : Blo 638302 960611 := bstep (se 1 (by rfl) ⟨720458, by rfl⟩ : syracuseStep 960611 = 1440917) B1440917
theorem B960641 : Blo 638302 960641 := bstep (se 2 (by rfl) ⟨360240, by rfl⟩ : syracuseStep 960641 = 720481) B720481
theorem B960659 : Blo 638302 960659 := bstep (se 1 (by rfl) ⟨720494, by rfl⟩ : syracuseStep 960659 = 1440989) B1440989
theorem B960689 : Blo 638302 960689 := bstep (se 2 (by rfl) ⟨360258, by rfl⟩ : syracuseStep 960689 = 720517) B720517
theorem B1026227 : Blo 638302 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B960707 : Blo 638302 960707 := bstep (se 1 (by rfl) ⟨720530, by rfl⟩ : syracuseStep 960707 = 1441061) B1441061
theorem B960737 : Blo 638302 960737 := bstep (se 2 (by rfl) ⟨360276, by rfl⟩ : syracuseStep 960737 = 720553) B720553
theorem B7416035 : Blo 638302 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B960755 : Blo 638302 960755 := bstep (se 1 (by rfl) ⟨720566, by rfl⟩ : syracuseStep 960755 = 1441133) B1441133
theorem B960785 : Blo 638302 960785 := bstep (se 2 (by rfl) ⟨360294, by rfl⟩ : syracuseStep 960785 = 720589) B720589
theorem B960803 : Blo 638302 960803 := bstep (se 1 (by rfl) ⟨720602, by rfl⟩ : syracuseStep 960803 = 1441205) B1441205
theorem B1157411 : Blo 638302 1157411 := bstep (se 1 (by rfl) ⟨868058, by rfl⟩ : syracuseStep 1157411 = 1736117) B1736117
theorem B960833 : Blo 638302 960833 := bstep (se 2 (by rfl) ⟨360312, by rfl⟩ : syracuseStep 960833 = 720625) B720625
theorem B960851 : Blo 638302 960851 := bstep (se 1 (by rfl) ⟨720638, by rfl⟩ : syracuseStep 960851 = 1441277) B1441277
theorem B960881 : Blo 638302 960881 := bstep (se 2 (by rfl) ⟨360330, by rfl⟩ : syracuseStep 960881 = 720661) B720661
theorem B960899 : Blo 638302 960899 := bstep (se 1 (by rfl) ⟨720674, by rfl⟩ : syracuseStep 960899 = 1441349) B1441349
theorem B731539 : Blo 638302 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B960929 : Blo 638302 960929 := bstep (se 2 (by rfl) ⟨360348, by rfl⟩ : syracuseStep 960929 = 720697) B720697
theorem B960947 : Blo 638302 960947 := bstep (se 1 (by rfl) ⟨720710, by rfl⟩ : syracuseStep 960947 = 1441421) B1441421
theorem B960977 : Blo 638302 960977 := bstep (se 2 (by rfl) ⟨360366, by rfl⟩ : syracuseStep 960977 = 720733) B720733
theorem B960995 : Blo 638302 960995 := bstep (se 1 (by rfl) ⟨720746, by rfl⟩ : syracuseStep 960995 = 1441493) B1441493
theorem B961025 : Blo 638302 961025 := bstep (se 2 (by rfl) ⟨360384, by rfl⟩ : syracuseStep 961025 = 720769) B720769
theorem B961043 : Blo 638302 961043 := bstep (se 1 (by rfl) ⟨720782, by rfl⟩ : syracuseStep 961043 = 1441565) B1441565
theorem B961073 : Blo 638302 961073 := bstep (se 2 (by rfl) ⟨360402, by rfl⟩ : syracuseStep 961073 = 720805) B720805
theorem B961091 : Blo 638302 961091 := bstep (se 1 (by rfl) ⟨720818, by rfl⟩ : syracuseStep 961091 = 1441637) B1441637
theorem B4860485 : Blo 638302 4860485 := bstep (se 4 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 4860485 = 911341) B911341
theorem B3648077 : Blo 638302 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B1026643 : Blo 638302 1026643 := bstep (se 1 (by rfl) ⟨769982, by rfl⟩ : syracuseStep 1026643 = 1539965) B1539965
theorem B961121 : Blo 638302 961121 := bstep (se 2 (by rfl) ⟨360420, by rfl⟩ : syracuseStep 961121 = 720841) B720841
theorem B961139 : Blo 638302 961139 := bstep (se 1 (by rfl) ⟨720854, by rfl⟩ : syracuseStep 961139 = 1441709) B1441709
theorem B961169 : Blo 638302 961169 := bstep (se 2 (by rfl) ⟨360438, by rfl⟩ : syracuseStep 961169 = 720877) B720877
theorem B961187 : Blo 638302 961187 := bstep (se 1 (by rfl) ⟨720890, by rfl⟩ : syracuseStep 961187 = 1441781) B1441781
theorem B961217 : Blo 638302 961217 := bstep (se 2 (by rfl) ⟨360456, by rfl⟩ : syracuseStep 961217 = 720913) B720913
theorem B961235 : Blo 638302 961235 := bstep (se 1 (by rfl) ⟨720926, by rfl⟩ : syracuseStep 961235 = 1441853) B1441853
theorem B961265 : Blo 638302 961265 := bstep (se 2 (by rfl) ⟨360474, by rfl⟩ : syracuseStep 961265 = 720949) B720949
theorem B961283 : Blo 638302 961283 := bstep (se 1 (by rfl) ⟨720962, by rfl⟩ : syracuseStep 961283 = 1441925) B1441925
theorem B961313 : Blo 638302 961313 := bstep (se 2 (by rfl) ⟨360492, by rfl⟩ : syracuseStep 961313 = 720985) B720985
theorem B961331 : Blo 638302 961331 := bstep (se 1 (by rfl) ⟨720998, by rfl⟩ : syracuseStep 961331 = 1441997) B1441997
theorem B961361 : Blo 638302 961361 := bstep (se 2 (by rfl) ⟨360510, by rfl⟩ : syracuseStep 961361 = 721021) B721021
theorem B1026913 : Blo 638302 1026913 := bstep (se 2 (by rfl) ⟨385092, by rfl⟩ : syracuseStep 1026913 = 770185) B770185
theorem B961379 : Blo 638302 961379 := bstep (se 1 (by rfl) ⟨721034, by rfl⟩ : syracuseStep 961379 = 1442069) B1442069
theorem B2435939 : Blo 638302 2435939 := bstep (se 1 (by rfl) ⟨1826954, by rfl⟩ : syracuseStep 2435939 = 3653909) B3653909
theorem B2435953 : Blo 638302 2435953 := bstep (se 2 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 2435953 = 1826965) B1826965
theorem B961409 : Blo 638302 961409 := bstep (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) B721057
theorem B961427 : Blo 638302 961427 := bstep (se 1 (by rfl) ⟨721070, by rfl⟩ : syracuseStep 961427 = 1442141) B1442141
theorem B2304931 : Blo 638302 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B961457 : Blo 638302 961457 := bstep (se 2 (by rfl) ⟨360546, by rfl⟩ : syracuseStep 961457 = 721093) B721093
theorem B961475 : Blo 638302 961475 := bstep (se 1 (by rfl) ⟨721106, by rfl⟩ : syracuseStep 961475 = 1442213) B1442213
theorem B961505 : Blo 638302 961505 := bstep (se 2 (by rfl) ⟨360564, by rfl⟩ : syracuseStep 961505 = 721129) B721129
theorem B1616881 : Blo 638302 1616881 := bstep (se 2 (by rfl) ⟨606330, by rfl⟩ : syracuseStep 1616881 = 1212661) B1212661
theorem B961523 : Blo 638302 961523 := bstep (se 1 (by rfl) ⟨721142, by rfl⟩ : syracuseStep 961523 = 1442285) B1442285
theorem B961553 : Blo 638302 961553 := bstep (se 2 (by rfl) ⟨360582, by rfl⟩ : syracuseStep 961553 = 721165) B721165
theorem B961571 : Blo 638302 961571 := bstep (se 1 (by rfl) ⟨721178, by rfl⟩ : syracuseStep 961571 = 1442357) B1442357
theorem B961601 : Blo 638302 961601 := bstep (se 2 (by rfl) ⟨360600, by rfl⟩ : syracuseStep 961601 = 721201) B721201
theorem B961619 : Blo 638302 961619 := bstep (se 1 (by rfl) ⟨721214, by rfl⟩ : syracuseStep 961619 = 1442429) B1442429
theorem B1027169 : Blo 638302 1027169 := bstep (se 2 (by rfl) ⟨385188, by rfl⟩ : syracuseStep 1027169 = 770377) B770377
theorem B961649 : Blo 638302 961649 := bstep (se 2 (by rfl) ⟨360618, by rfl⟩ : syracuseStep 961649 = 721237) B721237
theorem B961667 : Blo 638302 961667 := bstep (se 1 (by rfl) ⟨721250, by rfl⟩ : syracuseStep 961667 = 1442501) B1442501
theorem B961697 : Blo 638302 961697 := bstep (se 2 (by rfl) ⟨360636, by rfl⟩ : syracuseStep 961697 = 721273) B721273
theorem B961715 : Blo 638302 961715 := bstep (se 1 (by rfl) ⟨721286, by rfl⟩ : syracuseStep 961715 = 1442573) B1442573
theorem B961745 : Blo 638302 961745 := bstep (se 2 (by rfl) ⟨360654, by rfl⟩ : syracuseStep 961745 = 721309) B721309
theorem B961763 : Blo 638302 961763 := bstep (se 1 (by rfl) ⟨721322, by rfl⟩ : syracuseStep 961763 = 1442645) B1442645
theorem B961793 : Blo 638302 961793 := bstep (se 2 (by rfl) ⟨360672, by rfl⟩ : syracuseStep 961793 = 721345) B721345
theorem B1617155 : Blo 638302 1617155 := bstep (se 1 (by rfl) ⟨1212866, by rfl⟩ : syracuseStep 1617155 = 2425733) B2425733
theorem B3452165 : Blo 638302 3452165 := bstep (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) B647281
theorem B961811 : Blo 638302 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B961841 : Blo 638302 961841 := bstep (se 2 (by rfl) ⟨360690, by rfl⟩ : syracuseStep 961841 = 721381) B721381
theorem B961859 : Blo 638302 961859 := bstep (se 1 (by rfl) ⟨721394, by rfl⟩ : syracuseStep 961859 = 1442789) B1442789
theorem B961889 : Blo 638302 961889 := bstep (se 2 (by rfl) ⟨360708, by rfl⟩ : syracuseStep 961889 = 721417) B721417
theorem B961907 : Blo 638302 961907 := bstep (se 1 (by rfl) ⟨721430, by rfl⟩ : syracuseStep 961907 = 1442861) B1442861
theorem B961937 : Blo 638302 961937 := bstep (se 2 (by rfl) ⟨360726, by rfl⟩ : syracuseStep 961937 = 721453) B721453
theorem B2731427 : Blo 638302 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B961955 : Blo 638302 961955 := bstep (se 1 (by rfl) ⟨721466, by rfl⟩ : syracuseStep 961955 = 1442933) B1442933
theorem B961985 : Blo 638302 961985 := bstep (se 2 (by rfl) ⟨360744, by rfl⟩ : syracuseStep 961985 = 721489) B721489
theorem B1617347 : Blo 638302 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B962003 : Blo 638302 962003 := bstep (se 1 (by rfl) ⟨721502, by rfl⟩ : syracuseStep 962003 = 1443005) B1443005
theorem B3649009 : Blo 638302 3649009 := bstep (se 2 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 3649009 = 2736757) B2736757
theorem B962033 : Blo 638302 962033 := bstep (se 2 (by rfl) ⟨360762, by rfl⟩ : syracuseStep 962033 = 721525) B721525
theorem B962051 : Blo 638302 962051 := bstep (se 1 (by rfl) ⟨721538, by rfl⟩ : syracuseStep 962051 = 1443077) B1443077
theorem B962081 : Blo 638302 962081 := bstep (se 2 (by rfl) ⟨360780, by rfl⟩ : syracuseStep 962081 = 721561) B721561
theorem B3452465 : Blo 638302 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B962099 : Blo 638302 962099 := bstep (se 1 (by rfl) ⟨721574, by rfl⟩ : syracuseStep 962099 = 1443149) B1443149
theorem B15773237 : Blo 638302 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B962129 : Blo 638302 962129 := bstep (se 2 (by rfl) ⟨360798, by rfl⟩ : syracuseStep 962129 = 721597) B721597
theorem B962147 : Blo 638302 962147 := bstep (se 1 (by rfl) ⟨721610, by rfl⟩ : syracuseStep 962147 = 1443221) B1443221
theorem B962177 : Blo 638302 962177 := bstep (se 2 (by rfl) ⟨360816, by rfl⟩ : syracuseStep 962177 = 721633) B721633
theorem B962195 : Blo 638302 962195 := bstep (se 1 (by rfl) ⟨721646, by rfl⟩ : syracuseStep 962195 = 1443293) B1443293
theorem B962225 : Blo 638302 962225 := bstep (se 2 (by rfl) ⟨360834, by rfl⟩ : syracuseStep 962225 = 721669) B721669
theorem B962243 : Blo 638302 962243 := bstep (se 1 (by rfl) ⟨721682, by rfl⟩ : syracuseStep 962243 = 1443365) B1443365
theorem B962273 : Blo 638302 962273 := bstep (se 2 (by rfl) ⟨360852, by rfl⟩ : syracuseStep 962273 = 721705) B721705
theorem B962291 : Blo 638302 962291 := bstep (se 1 (by rfl) ⟨721718, by rfl⟩ : syracuseStep 962291 = 1443437) B1443437
theorem B962321 : Blo 638302 962321 := bstep (se 2 (by rfl) ⟨360870, by rfl⟩ : syracuseStep 962321 = 721741) B721741
theorem B1027873 : Blo 638302 1027873 := bstep (se 2 (by rfl) ⟨385452, by rfl⟩ : syracuseStep 1027873 = 770905) B770905
theorem B962339 : Blo 638302 962339 := bstep (se 1 (by rfl) ⟨721754, by rfl⟩ : syracuseStep 962339 = 1443509) B1443509
theorem B962369 : Blo 638302 962369 := bstep (se 2 (by rfl) ⟨360888, by rfl⟩ : syracuseStep 962369 = 721777) B721777
theorem B962387 : Blo 638302 962387 := bstep (se 1 (by rfl) ⟨721790, by rfl⟩ : syracuseStep 962387 = 1443581) B1443581
theorem B962417 : Blo 638302 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B962435 : Blo 638302 962435 := bstep (se 1 (by rfl) ⟨721826, by rfl⟩ : syracuseStep 962435 = 1443653) B1443653
theorem B962465 : Blo 638302 962465 := bstep (se 2 (by rfl) ⟨360924, by rfl⟩ : syracuseStep 962465 = 721849) B721849
theorem B962483 : Blo 638302 962483 := bstep (se 1 (by rfl) ⟨721862, by rfl⟩ : syracuseStep 962483 = 1443725) B1443725
theorem B2076625 : Blo 638302 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B962513 : Blo 638302 962513 := bstep (se 2 (by rfl) ⟨360942, by rfl⟩ : syracuseStep 962513 = 721885) B721885
theorem B962531 : Blo 638302 962531 := bstep (se 1 (by rfl) ⟨721898, by rfl⟩ : syracuseStep 962531 = 1443797) B1443797
theorem B962561 : Blo 638302 962561 := bstep (se 2 (by rfl) ⟨360960, by rfl⟩ : syracuseStep 962561 = 721921) B721921
theorem B962579 : Blo 638302 962579 := bstep (se 1 (by rfl) ⟨721934, by rfl⟩ : syracuseStep 962579 = 1443869) B1443869
theorem B962609 : Blo 638302 962609 := bstep (se 2 (by rfl) ⟨360978, by rfl⟩ : syracuseStep 962609 = 721957) B721957
theorem B29503541 : Blo 638302 29503541 := bstep (se 5 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 29503541 = 2765957) B2765957
theorem B962627 : Blo 638302 962627 := bstep (se 1 (by rfl) ⟨721970, by rfl⟩ : syracuseStep 962627 = 1443941) B1443941
theorem B962657 : Blo 638302 962657 := bstep (se 2 (by rfl) ⟨360996, by rfl⟩ : syracuseStep 962657 = 721993) B721993
theorem B962675 : Blo 638302 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B962705 : Blo 638302 962705 := bstep (se 2 (by rfl) ⟨361014, by rfl⟩ : syracuseStep 962705 = 722029) B722029
theorem B4206755 : Blo 638302 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B962723 : Blo 638302 962723 := bstep (se 1 (by rfl) ⟨722042, by rfl⟩ : syracuseStep 962723 = 1444085) B1444085
theorem B962753 : Blo 638302 962753 := bstep (se 2 (by rfl) ⟨361032, by rfl⟩ : syracuseStep 962753 = 722065) B722065
theorem B962771 : Blo 638302 962771 := bstep (se 1 (by rfl) ⟨722078, by rfl⟩ : syracuseStep 962771 = 1444157) B1444157
theorem B962801 : Blo 638302 962801 := bstep (se 2 (by rfl) ⟨361050, by rfl⟩ : syracuseStep 962801 = 722101) B722101
theorem B962819 : Blo 638302 962819 := bstep (se 1 (by rfl) ⟨722114, by rfl⟩ : syracuseStep 962819 = 1444229) B1444229
theorem B962849 : Blo 638302 962849 := bstep (se 2 (by rfl) ⟨361068, by rfl⟩ : syracuseStep 962849 = 722137) B722137
theorem B2437411 : Blo 638302 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B962867 : Blo 638302 962867 := bstep (se 1 (by rfl) ⟨722150, by rfl⟩ : syracuseStep 962867 = 1444301) B1444301
theorem B962897 : Blo 638302 962897 := bstep (se 2 (by rfl) ⟨361086, by rfl⟩ : syracuseStep 962897 = 722173) B722173
theorem B962915 : Blo 638302 962915 := bstep (se 1 (by rfl) ⟨722186, by rfl⟩ : syracuseStep 962915 = 1444373) B1444373
theorem B1618289 : Blo 638302 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B962945 : Blo 638302 962945 := bstep (se 2 (by rfl) ⟨361104, by rfl⟩ : syracuseStep 962945 = 722209) B722209
theorem B962963 : Blo 638302 962963 := bstep (se 1 (by rfl) ⟨722222, by rfl⟩ : syracuseStep 962963 = 1444445) B1444445
theorem B1618339 : Blo 638302 1618339 := bstep (se 1 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 1618339 = 2427509) B2427509
theorem B962993 : Blo 638302 962993 := bstep (se 2 (by rfl) ⟨361122, by rfl⟩ : syracuseStep 962993 = 722245) B722245
theorem B963011 : Blo 638302 963011 := bstep (se 1 (by rfl) ⟨722258, by rfl⟩ : syracuseStep 963011 = 1444517) B1444517
theorem B5190085 : Blo 638302 5190085 := bstep (se 4 (by rfl) ⟨486570, by rfl⟩ : syracuseStep 5190085 = 973141) B973141
theorem B963041 : Blo 638302 963041 := bstep (se 2 (by rfl) ⟨361140, by rfl⟩ : syracuseStep 963041 = 722281) B722281
theorem B963059 : Blo 638302 963059 := bstep (se 1 (by rfl) ⟨722294, by rfl⟩ : syracuseStep 963059 = 1444589) B1444589
theorem B4108805 : Blo 638302 4108805 := bstep (se 4 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 4108805 = 770401) B770401
theorem B963089 : Blo 638302 963089 := bstep (se 2 (by rfl) ⟨361158, by rfl⟩ : syracuseStep 963089 = 722317) B722317
theorem B864803 : Blo 638302 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B963107 : Blo 638302 963107 := bstep (se 1 (by rfl) ⟨722330, by rfl⟩ : syracuseStep 963107 = 1444661) B1444661
theorem B1618481 : Blo 638302 1618481 := bstep (se 2 (by rfl) ⟨606930, by rfl⟩ : syracuseStep 1618481 = 1213861) B1213861
theorem B963137 : Blo 638302 963137 := bstep (se 2 (by rfl) ⟨361176, by rfl⟩ : syracuseStep 963137 = 722353) B722353
theorem B963155 : Blo 638302 963155 := bstep (se 1 (by rfl) ⟨722366, by rfl⟩ : syracuseStep 963155 = 1444733) B1444733
theorem B963185 : Blo 638302 963185 := bstep (se 2 (by rfl) ⟨361194, by rfl⟩ : syracuseStep 963185 = 722389) B722389
theorem B963203 : Blo 638302 963203 := bstep (se 1 (by rfl) ⟨722402, by rfl⟩ : syracuseStep 963203 = 1444805) B1444805
theorem B963233 : Blo 638302 963233 := bstep (se 2 (by rfl) ⟨361212, by rfl⟩ : syracuseStep 963233 = 722425) B722425
theorem B1028771 : Blo 638302 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B963251 : Blo 638302 963251 := bstep (se 1 (by rfl) ⟨722438, by rfl⟩ : syracuseStep 963251 = 1444877) B1444877
theorem B963281 : Blo 638302 963281 := bstep (se 2 (by rfl) ⟨361230, by rfl⟩ : syracuseStep 963281 = 722461) B722461
theorem B963299 : Blo 638302 963299 := bstep (se 1 (by rfl) ⟨722474, by rfl⟩ : syracuseStep 963299 = 1444949) B1444949
theorem B963329 : Blo 638302 963329 := bstep (se 2 (by rfl) ⟨361248, by rfl⟩ : syracuseStep 963329 = 722497) B722497
theorem B963347 : Blo 638302 963347 := bstep (se 1 (by rfl) ⟨722510, by rfl⟩ : syracuseStep 963347 = 1445021) B1445021
theorem B2634545 : Blo 638302 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B963377 : Blo 638302 963377 := bstep (se 2 (by rfl) ⟨361266, by rfl⟩ : syracuseStep 963377 = 722533) B722533
theorem B865075 : Blo 638302 865075 := bstep (se 1 (by rfl) ⟨648806, by rfl⟩ : syracuseStep 865075 = 1297613) B1297613
theorem B963395 : Blo 638302 963395 := bstep (se 1 (by rfl) ⟨722546, by rfl⟩ : syracuseStep 963395 = 1445093) B1445093
theorem B963425 : Blo 638302 963425 := bstep (se 2 (by rfl) ⟨361284, by rfl⟩ : syracuseStep 963425 = 722569) B722569
theorem B963443 : Blo 638302 963443 := bstep (se 1 (by rfl) ⟨722582, by rfl⟩ : syracuseStep 963443 = 1445165) B1445165
theorem B3289997 : Blo 638302 3289997 := bstep (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) B1233749
theorem B3650467 : Blo 638302 3650467 := bstep (se 1 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 3650467 = 5475701) B5475701
theorem B1094627 : Blo 638302 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B3650993 : Blo 638302 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B8304113 : Blo 638302 8304113 := bstep (se 2 (by rfl) ⟨3114042, by rfl⟩ : syracuseStep 8304113 = 6228085) B6228085
theorem B1848845 : Blo 638302 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B1619473 : Blo 638302 1619473 := bstep (se 2 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 1619473 = 1214605) B1214605
theorem B27997973 : Blo 638302 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1619747 : Blo 638302 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B1619939 : Blo 638302 1619939 := bstep (se 1 (by rfl) ⟨1214954, by rfl⟩ : syracuseStep 1619939 = 2429909) B2429909
theorem B2504753 : Blo 638302 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B2078797 : Blo 638302 2078797 := bstep (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) B779549
theorem B2046161 : Blo 638302 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B1096049 : Blo 638302 1096049 := bstep (se 2 (by rfl) ⟨411018, by rfl⟩ : syracuseStep 1096049 = 822037) B822037
theorem B2046509 : Blo 638302 2046509 := bstep (se 3 (by rfl) ⟨383720, by rfl⟩ : syracuseStep 2046509 = 767441) B767441
theorem B1948387 : Blo 638302 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B3652451 : Blo 638302 3652451 := bstep (se 1 (by rfl) ⟨2739338, by rfl⟩ : syracuseStep 3652451 = 5478677) B5478677
theorem B1620881 : Blo 638302 1620881 := bstep (se 2 (by rfl) ⟨607830, by rfl⟩ : syracuseStep 1620881 = 1215661) B1215661
theorem B1620931 : Blo 638302 1620931 := bstep (se 1 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 1620931 = 2431397) B2431397
theorem B2735117 : Blo 638302 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B703523 : Blo 638302 703523 := bstep (se 1 (by rfl) ⟨527642, by rfl⟩ : syracuseStep 703523 = 1055285) B1055285
theorem B2735153 : Blo 638302 2735153 := bstep (se 2 (by rfl) ⟨1025682, by rfl⟩ : syracuseStep 2735153 = 2051365) B2051365
theorem B1621073 : Blo 638302 1621073 := bstep (se 2 (by rfl) ⟨607902, by rfl⟩ : syracuseStep 1621073 = 1215805) B1215805
theorem B998497 : Blo 638302 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B769171 : Blo 638302 769171 := bstep (se 1 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 769171 = 1153757) B1153757
theorem B3882275 : Blo 638302 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B638307 : Blo 638302 638307 := bstep (se 1 (by rfl) ⟨478730, by rfl⟩ : syracuseStep 638307 = 957461) B957461
theorem B638323 : Blo 638302 638323 := bstep (se 1 (by rfl) ⟨478742, by rfl⟩ : syracuseStep 638323 = 957485) B957485
theorem B638339 : Blo 638302 638339 := bstep (se 1 (by rfl) ⟨478754, by rfl⟩ : syracuseStep 638339 = 957509) B957509
theorem B638355 : Blo 638302 638355 := bstep (se 1 (by rfl) ⟨478766, by rfl⟩ : syracuseStep 638355 = 957533) B957533
theorem B638371 : Blo 638302 638371 := bstep (se 1 (by rfl) ⟨478778, by rfl⟩ : syracuseStep 638371 = 957557) B957557
theorem B638387 : Blo 638302 638387 := bstep (se 1 (by rfl) ⟨478790, by rfl⟩ : syracuseStep 638387 = 957581) B957581
theorem B638403 : Blo 638302 638403 := bstep (se 1 (by rfl) ⟨478802, by rfl⟩ : syracuseStep 638403 = 957605) B957605
theorem B5848517 : Blo 638302 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B638419 : Blo 638302 638419 := bstep (se 1 (by rfl) ⟨478814, by rfl⟩ : syracuseStep 638419 = 957629) B957629
theorem B3882467 : Blo 638302 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B638435 : Blo 638302 638435 := bstep (se 1 (by rfl) ⟨478826, by rfl⟩ : syracuseStep 638435 = 957653) B957653
theorem B638451 : Blo 638302 638451 := bstep (se 1 (by rfl) ⟨478838, by rfl⟩ : syracuseStep 638451 = 957677) B957677
theorem B638467 : Blo 638302 638467 := bstep (se 1 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 638467 = 957701) B957701
theorem B5193229 : Blo 638302 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B638483 : Blo 638302 638483 := bstep (se 1 (by rfl) ⟨478862, by rfl⟩ : syracuseStep 638483 = 957725) B957725
theorem B638499 : Blo 638302 638499 := bstep (se 1 (by rfl) ⟨478874, by rfl⟩ : syracuseStep 638499 = 957749) B957749
theorem B638515 : Blo 638302 638515 := bstep (se 1 (by rfl) ⟨478886, by rfl⟩ : syracuseStep 638515 = 957773) B957773
theorem B638531 : Blo 638302 638531 := bstep (se 1 (by rfl) ⟨478898, by rfl⟩ : syracuseStep 638531 = 957797) B957797
theorem B638547 : Blo 638302 638547 := bstep (se 1 (by rfl) ⟨478910, by rfl⟩ : syracuseStep 638547 = 957821) B957821
theorem B638563 : Blo 638302 638563 := bstep (se 1 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 638563 = 957845) B957845
theorem B638579 : Blo 638302 638579 := bstep (se 1 (by rfl) ⟨478934, by rfl⟩ : syracuseStep 638579 = 957869) B957869
theorem B638595 : Blo 638302 638595 := bstep (se 1 (by rfl) ⟨478946, by rfl⟩ : syracuseStep 638595 = 957893) B957893
theorem B4112005 : Blo 638302 4112005 := bstep (se 4 (by rfl) ⟨385500, by rfl⟩ : syracuseStep 4112005 = 771001) B771001
theorem B638611 : Blo 638302 638611 := bstep (se 1 (by rfl) ⟨478958, by rfl⟩ : syracuseStep 638611 = 957917) B957917
theorem B1097363 : Blo 638302 1097363 := bstep (se 1 (by rfl) ⟨823022, by rfl⟩ : syracuseStep 1097363 = 1646045) B1646045
theorem B638627 : Blo 638302 638627 := bstep (se 1 (by rfl) ⟨478970, by rfl⟩ : syracuseStep 638627 = 957941) B957941
theorem B638643 : Blo 638302 638643 := bstep (se 1 (by rfl) ⟨478982, by rfl⟩ : syracuseStep 638643 = 957965) B957965
theorem B638659 : Blo 638302 638659 := bstep (se 1 (by rfl) ⟨478994, by rfl⟩ : syracuseStep 638659 = 957989) B957989
theorem B638675 : Blo 638302 638675 := bstep (se 1 (by rfl) ⟨479006, by rfl⟩ : syracuseStep 638675 = 958013) B958013
theorem B638691 : Blo 638302 638691 := bstep (se 1 (by rfl) ⟨479018, by rfl⟩ : syracuseStep 638691 = 958037) B958037
theorem B638707 : Blo 638302 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B638723 : Blo 638302 638723 := bstep (se 1 (by rfl) ⟨479042, by rfl⟩ : syracuseStep 638723 = 958085) B958085
theorem B638739 : Blo 638302 638739 := bstep (se 1 (by rfl) ⟨479054, by rfl⟩ : syracuseStep 638739 = 958109) B958109
theorem B638755 : Blo 638302 638755 := bstep (se 1 (by rfl) ⟨479066, by rfl⟩ : syracuseStep 638755 = 958133) B958133
theorem B638771 : Blo 638302 638771 := bstep (se 1 (by rfl) ⟨479078, by rfl⟩ : syracuseStep 638771 = 958157) B958157
theorem B638787 : Blo 638302 638787 := bstep (se 1 (by rfl) ⟨479090, by rfl⟩ : syracuseStep 638787 = 958181) B958181
theorem B1818445 : Blo 638302 1818445 := bstep (se 3 (by rfl) ⟨340958, by rfl⟩ : syracuseStep 1818445 = 681917) B681917
theorem B638803 : Blo 638302 638803 := bstep (se 1 (by rfl) ⟨479102, by rfl⟩ : syracuseStep 638803 = 958205) B958205
theorem B1097555 : Blo 638302 1097555 := bstep (se 1 (by rfl) ⟨823166, by rfl⟩ : syracuseStep 1097555 = 1646333) B1646333
theorem B638819 : Blo 638302 638819 := bstep (se 1 (by rfl) ⟨479114, by rfl⟩ : syracuseStep 638819 = 958229) B958229
theorem B1752931 : Blo 638302 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B638835 : Blo 638302 638835 := bstep (se 1 (by rfl) ⟨479126, by rfl⟩ : syracuseStep 638835 = 958253) B958253
theorem B638851 : Blo 638302 638851 := bstep (se 1 (by rfl) ⟨479138, by rfl⟩ : syracuseStep 638851 = 958277) B958277
theorem B638867 : Blo 638302 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B638883 : Blo 638302 638883 := bstep (se 1 (by rfl) ⟨479162, by rfl⟩ : syracuseStep 638883 = 958325) B958325
theorem B638899 : Blo 638302 638899 := bstep (se 1 (by rfl) ⟨479174, by rfl⟩ : syracuseStep 638899 = 958349) B958349
theorem B638915 : Blo 638302 638915 := bstep (se 1 (by rfl) ⟨479186, by rfl⟩ : syracuseStep 638915 = 958373) B958373
theorem B638931 : Blo 638302 638931 := bstep (se 1 (by rfl) ⟨479198, by rfl⟩ : syracuseStep 638931 = 958397) B958397
theorem B638947 : Blo 638302 638947 := bstep (se 1 (by rfl) ⟨479210, by rfl⟩ : syracuseStep 638947 = 958421) B958421
theorem B1818605 : Blo 638302 1818605 := bstep (se 3 (by rfl) ⟨340988, by rfl⟩ : syracuseStep 1818605 = 681977) B681977
theorem B638963 : Blo 638302 638963 := bstep (se 1 (by rfl) ⟨479222, by rfl⟩ : syracuseStep 638963 = 958445) B958445
theorem B638979 : Blo 638302 638979 := bstep (se 1 (by rfl) ⟨479234, by rfl⟩ : syracuseStep 638979 = 958469) B958469
theorem B638995 : Blo 638302 638995 := bstep (se 1 (by rfl) ⟨479246, by rfl⟩ : syracuseStep 638995 = 958493) B958493
theorem B639011 : Blo 638302 639011 := bstep (se 1 (by rfl) ⟨479258, by rfl⟩ : syracuseStep 639011 = 958517) B958517
theorem B1622065 : Blo 638302 1622065 := bstep (se 2 (by rfl) ⟨608274, by rfl⟩ : syracuseStep 1622065 = 1216549) B1216549
theorem B639027 : Blo 638302 639027 := bstep (se 1 (by rfl) ⟨479270, by rfl⟩ : syracuseStep 639027 = 958541) B958541
theorem B639043 : Blo 638302 639043 := bstep (se 1 (by rfl) ⟨479282, by rfl⟩ : syracuseStep 639043 = 958565) B958565
theorem B639059 : Blo 638302 639059 := bstep (se 1 (by rfl) ⟨479294, by rfl⟩ : syracuseStep 639059 = 958589) B958589
theorem B639075 : Blo 638302 639075 := bstep (se 1 (by rfl) ⟨479306, by rfl⟩ : syracuseStep 639075 = 958613) B958613
theorem B639091 : Blo 638302 639091 := bstep (se 1 (by rfl) ⟨479318, by rfl⟩ : syracuseStep 639091 = 958637) B958637
theorem B639107 : Blo 638302 639107 := bstep (se 1 (by rfl) ⟨479330, by rfl⟩ : syracuseStep 639107 = 958661) B958661
theorem B639123 : Blo 638302 639123 := bstep (se 1 (by rfl) ⟨479342, by rfl⟩ : syracuseStep 639123 = 958685) B958685
theorem B1818787 : Blo 638302 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B639139 : Blo 638302 639139 := bstep (se 1 (by rfl) ⟨479354, by rfl⟩ : syracuseStep 639139 = 958709) B958709
theorem B2638001 : Blo 638302 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B639155 : Blo 638302 639155 := bstep (se 1 (by rfl) ⟨479366, by rfl⟩ : syracuseStep 639155 = 958733) B958733
theorem B639171 : Blo 638302 639171 := bstep (se 1 (by rfl) ⟨479378, by rfl⟩ : syracuseStep 639171 = 958757) B958757
theorem B639187 : Blo 638302 639187 := bstep (se 1 (by rfl) ⟨479390, by rfl⟩ : syracuseStep 639187 = 958781) B958781
theorem B639203 : Blo 638302 639203 := bstep (se 1 (by rfl) ⟨479402, by rfl⟩ : syracuseStep 639203 = 958805) B958805
theorem B639219 : Blo 638302 639219 := bstep (se 1 (by rfl) ⟨479414, by rfl⟩ : syracuseStep 639219 = 958829) B958829
theorem B639235 : Blo 638302 639235 := bstep (se 1 (by rfl) ⟨479426, by rfl⟩ : syracuseStep 639235 = 958853) B958853
theorem B4866317 : Blo 638302 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B639251 : Blo 638302 639251 := bstep (se 1 (by rfl) ⟨479438, by rfl⟩ : syracuseStep 639251 = 958877) B958877
theorem B639267 : Blo 638302 639267 := bstep (se 1 (by rfl) ⟨479450, by rfl⟩ : syracuseStep 639267 = 958901) B958901
theorem B639283 : Blo 638302 639283 := bstep (se 1 (by rfl) ⟨479462, by rfl⟩ : syracuseStep 639283 = 958925) B958925
theorem B639299 : Blo 638302 639299 := bstep (se 1 (by rfl) ⟨479474, by rfl⟩ : syracuseStep 639299 = 958949) B958949
theorem B1622339 : Blo 638302 1622339 := bstep (se 1 (by rfl) ⟨1216754, by rfl⟩ : syracuseStep 1622339 = 2433509) B2433509
theorem B639315 : Blo 638302 639315 := bstep (se 1 (by rfl) ⟨479486, by rfl⟩ : syracuseStep 639315 = 958973) B958973
theorem B639331 : Blo 638302 639331 := bstep (se 1 (by rfl) ⟨479498, by rfl⟩ : syracuseStep 639331 = 958997) B958997
theorem B2048365 : Blo 638302 2048365 := bstep (se 3 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 2048365 = 768137) B768137
theorem B639347 : Blo 638302 639347 := bstep (se 1 (by rfl) ⟨479510, by rfl⟩ : syracuseStep 639347 = 959021) B959021
theorem B639363 : Blo 638302 639363 := bstep (se 1 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 639363 = 959045) B959045
theorem B639379 : Blo 638302 639379 := bstep (se 1 (by rfl) ⟨479534, by rfl⟩ : syracuseStep 639379 = 959069) B959069
theorem B639395 : Blo 638302 639395 := bstep (se 1 (by rfl) ⟨479546, by rfl⟩ : syracuseStep 639395 = 959093) B959093
theorem B639411 : Blo 638302 639411 := bstep (se 1 (by rfl) ⟨479558, by rfl⟩ : syracuseStep 639411 = 959117) B959117
theorem B639427 : Blo 638302 639427 := bstep (se 1 (by rfl) ⟨479570, by rfl⟩ : syracuseStep 639427 = 959141) B959141
theorem B639443 : Blo 638302 639443 := bstep (se 1 (by rfl) ⟨479582, by rfl⟩ : syracuseStep 639443 = 959165) B959165
theorem B639459 : Blo 638302 639459 := bstep (se 1 (by rfl) ⟨479594, by rfl⟩ : syracuseStep 639459 = 959189) B959189
theorem B639475 : Blo 638302 639475 := bstep (se 1 (by rfl) ⟨479606, by rfl⟩ : syracuseStep 639475 = 959213) B959213
theorem B639491 : Blo 638302 639491 := bstep (se 1 (by rfl) ⟨479618, by rfl⟩ : syracuseStep 639491 = 959237) B959237
theorem B1622531 : Blo 638302 1622531 := bstep (se 1 (by rfl) ⟨1216898, by rfl⟩ : syracuseStep 1622531 = 2433797) B2433797
theorem B639507 : Blo 638302 639507 := bstep (se 1 (by rfl) ⟨479630, by rfl⟩ : syracuseStep 639507 = 959261) B959261
theorem B639523 : Blo 638302 639523 := bstep (se 1 (by rfl) ⟨479642, by rfl⟩ : syracuseStep 639523 = 959285) B959285
theorem B639539 : Blo 638302 639539 := bstep (se 1 (by rfl) ⟨479654, by rfl⟩ : syracuseStep 639539 = 959309) B959309
theorem B639555 : Blo 638302 639555 := bstep (se 1 (by rfl) ⟨479666, by rfl⟩ : syracuseStep 639555 = 959333) B959333
theorem B639571 : Blo 638302 639571 := bstep (se 1 (by rfl) ⟨479678, by rfl⟩ : syracuseStep 639571 = 959357) B959357
theorem B639587 : Blo 638302 639587 := bstep (se 1 (by rfl) ⟨479690, by rfl⟩ : syracuseStep 639587 = 959381) B959381
theorem B639603 : Blo 638302 639603 := bstep (se 1 (by rfl) ⟨479702, by rfl⟩ : syracuseStep 639603 = 959405) B959405
theorem B639619 : Blo 638302 639619 := bstep (se 1 (by rfl) ⟨479714, by rfl⟩ : syracuseStep 639619 = 959429) B959429
theorem B639635 : Blo 638302 639635 := bstep (se 1 (by rfl) ⟨479726, by rfl⟩ : syracuseStep 639635 = 959453) B959453
theorem B639651 : Blo 638302 639651 := bstep (se 1 (by rfl) ⟨479738, by rfl⟩ : syracuseStep 639651 = 959477) B959477
theorem B639667 : Blo 638302 639667 := bstep (se 1 (by rfl) ⟨479750, by rfl⟩ : syracuseStep 639667 = 959501) B959501
theorem B639683 : Blo 638302 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B3654341 : Blo 638302 3654341 := bstep (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) B685189
theorem B639699 : Blo 638302 639699 := bstep (se 1 (by rfl) ⟨479774, by rfl⟩ : syracuseStep 639699 = 959549) B959549
theorem B639715 : Blo 638302 639715 := bstep (se 1 (by rfl) ⟨479786, by rfl⟩ : syracuseStep 639715 = 959573) B959573
theorem B639731 : Blo 638302 639731 := bstep (se 1 (by rfl) ⟨479798, by rfl⟩ : syracuseStep 639731 = 959597) B959597
theorem B639747 : Blo 638302 639747 := bstep (se 1 (by rfl) ⟨479810, by rfl⟩ : syracuseStep 639747 = 959621) B959621
theorem B639763 : Blo 638302 639763 := bstep (se 1 (by rfl) ⟨479822, by rfl⟩ : syracuseStep 639763 = 959645) B959645
theorem B639779 : Blo 638302 639779 := bstep (se 1 (by rfl) ⟨479834, by rfl⟩ : syracuseStep 639779 = 959669) B959669
theorem B639795 : Blo 638302 639795 := bstep (se 1 (by rfl) ⟨479846, by rfl⟩ : syracuseStep 639795 = 959693) B959693
theorem B639811 : Blo 638302 639811 := bstep (se 1 (by rfl) ⟨479858, by rfl⟩ : syracuseStep 639811 = 959717) B959717
theorem B2081603 : Blo 638302 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B639827 : Blo 638302 639827 := bstep (se 1 (by rfl) ⟨479870, by rfl⟩ : syracuseStep 639827 = 959741) B959741
theorem B639843 : Blo 638302 639843 := bstep (se 1 (by rfl) ⟨479882, by rfl⟩ : syracuseStep 639843 = 959765) B959765
theorem B770915 : Blo 638302 770915 := bstep (se 1 (by rfl) ⟨578186, by rfl⟩ : syracuseStep 770915 = 1156373) B1156373
theorem B639859 : Blo 638302 639859 := bstep (se 1 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 639859 = 959789) B959789
theorem B639875 : Blo 638302 639875 := bstep (se 1 (by rfl) ⟨479906, by rfl⟩ : syracuseStep 639875 = 959813) B959813
theorem B639891 : Blo 638302 639891 := bstep (se 1 (by rfl) ⟨479918, by rfl⟩ : syracuseStep 639891 = 959837) B959837
theorem B770963 : Blo 638302 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B639907 : Blo 638302 639907 := bstep (se 1 (by rfl) ⟨479930, by rfl⟩ : syracuseStep 639907 = 959861) B959861
theorem B639923 : Blo 638302 639923 := bstep (se 1 (by rfl) ⟨479942, by rfl⟩ : syracuseStep 639923 = 959885) B959885
theorem B639939 : Blo 638302 639939 := bstep (se 1 (by rfl) ⟨479954, by rfl⟩ : syracuseStep 639939 = 959909) B959909
theorem B1852355 : Blo 638302 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B639955 : Blo 638302 639955 := bstep (se 1 (by rfl) ⟨479966, by rfl⟩ : syracuseStep 639955 = 959933) B959933
theorem B639971 : Blo 638302 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B639987 : Blo 638302 639987 := bstep (se 1 (by rfl) ⟨479990, by rfl⟩ : syracuseStep 639987 = 959981) B959981
theorem B771059 : Blo 638302 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B640003 : Blo 638302 640003 := bstep (se 1 (by rfl) ⟨480002, by rfl⟩ : syracuseStep 640003 = 960005) B960005
theorem B640019 : Blo 638302 640019 := bstep (se 1 (by rfl) ⟨480014, by rfl⟩ : syracuseStep 640019 = 960029) B960029
theorem B640035 : Blo 638302 640035 := bstep (se 1 (by rfl) ⟨480026, by rfl⟩ : syracuseStep 640035 = 960053) B960053
theorem B640051 : Blo 638302 640051 := bstep (se 1 (by rfl) ⟨480038, by rfl⟩ : syracuseStep 640051 = 960077) B960077
theorem B640067 : Blo 638302 640067 := bstep (se 1 (by rfl) ⟨480050, by rfl⟩ : syracuseStep 640067 = 960101) B960101
theorem B1950797 : Blo 638302 1950797 := bstep (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) B731549
theorem B640083 : Blo 638302 640083 := bstep (se 1 (by rfl) ⟨480062, by rfl⟩ : syracuseStep 640083 = 960125) B960125
theorem B640099 : Blo 638302 640099 := bstep (se 1 (by rfl) ⟨480074, by rfl⟩ : syracuseStep 640099 = 960149) B960149
theorem B640115 : Blo 638302 640115 := bstep (se 1 (by rfl) ⟨480086, by rfl⟩ : syracuseStep 640115 = 960173) B960173
theorem B640131 : Blo 638302 640131 := bstep (se 1 (by rfl) ⟨480098, by rfl⟩ : syracuseStep 640131 = 960197) B960197
theorem B640147 : Blo 638302 640147 := bstep (se 1 (by rfl) ⟨480110, by rfl⟩ : syracuseStep 640147 = 960221) B960221
theorem B640163 : Blo 638302 640163 := bstep (se 1 (by rfl) ⟨480122, by rfl⟩ : syracuseStep 640163 = 960245) B960245
theorem B640179 : Blo 638302 640179 := bstep (se 1 (by rfl) ⟨480134, by rfl⟩ : syracuseStep 640179 = 960269) B960269
theorem B640195 : Blo 638302 640195 := bstep (se 1 (by rfl) ⟨480146, by rfl⟩ : syracuseStep 640195 = 960293) B960293
theorem B640211 : Blo 638302 640211 := bstep (se 1 (by rfl) ⟨480158, by rfl⟩ : syracuseStep 640211 = 960317) B960317
theorem B640227 : Blo 638302 640227 := bstep (se 1 (by rfl) ⟨480170, by rfl⟩ : syracuseStep 640227 = 960341) B960341
theorem B640243 : Blo 638302 640243 := bstep (se 1 (by rfl) ⟨480182, by rfl⟩ : syracuseStep 640243 = 960365) B960365
theorem B640259 : Blo 638302 640259 := bstep (se 1 (by rfl) ⟨480194, by rfl⟩ : syracuseStep 640259 = 960389) B960389
theorem B640275 : Blo 638302 640275 := bstep (se 1 (by rfl) ⟨480206, by rfl⟩ : syracuseStep 640275 = 960413) B960413
theorem B640291 : Blo 638302 640291 := bstep (se 1 (by rfl) ⟨480218, by rfl⟩ : syracuseStep 640291 = 960437) B960437
theorem B640307 : Blo 638302 640307 := bstep (se 1 (by rfl) ⟨480230, by rfl⟩ : syracuseStep 640307 = 960461) B960461
theorem B640323 : Blo 638302 640323 := bstep (se 1 (by rfl) ⟨480242, by rfl⟩ : syracuseStep 640323 = 960485) B960485
theorem B640339 : Blo 638302 640339 := bstep (se 1 (by rfl) ⟨480254, by rfl⟩ : syracuseStep 640339 = 960509) B960509
theorem B640355 : Blo 638302 640355 := bstep (se 1 (by rfl) ⟨480266, by rfl⟩ : syracuseStep 640355 = 960533) B960533
theorem B640371 : Blo 638302 640371 := bstep (se 1 (by rfl) ⟨480278, by rfl⟩ : syracuseStep 640371 = 960557) B960557
theorem B640387 : Blo 638302 640387 := bstep (se 1 (by rfl) ⟨480290, by rfl⟩ : syracuseStep 640387 = 960581) B960581
theorem B640403 : Blo 638302 640403 := bstep (se 1 (by rfl) ⟨480302, by rfl⟩ : syracuseStep 640403 = 960605) B960605
theorem B640419 : Blo 638302 640419 := bstep (se 1 (by rfl) ⟨480314, by rfl⟩ : syracuseStep 640419 = 960629) B960629
theorem B1623473 : Blo 638302 1623473 := bstep (se 2 (by rfl) ⟨608802, by rfl⟩ : syracuseStep 1623473 = 1217605) B1217605
theorem B640435 : Blo 638302 640435 := bstep (se 1 (by rfl) ⟨480326, by rfl⟩ : syracuseStep 640435 = 960653) B960653
theorem B640451 : Blo 638302 640451 := bstep (se 1 (by rfl) ⟨480338, by rfl⟩ : syracuseStep 640451 = 960677) B960677
theorem B640467 : Blo 638302 640467 := bstep (se 1 (by rfl) ⟨480350, by rfl⟩ : syracuseStep 640467 = 960701) B960701
theorem B1295843 : Blo 638302 1295843 := bstep (se 1 (by rfl) ⟨971882, by rfl⟩ : syracuseStep 1295843 = 1943765) B1943765
theorem B640483 : Blo 638302 640483 := bstep (se 1 (by rfl) ⟨480362, by rfl⟩ : syracuseStep 640483 = 960725) B960725
theorem B1623523 : Blo 638302 1623523 := bstep (se 1 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 1623523 = 2435285) B2435285
theorem B640499 : Blo 638302 640499 := bstep (se 1 (by rfl) ⟨480374, by rfl⟩ : syracuseStep 640499 = 960749) B960749
theorem B1295875 : Blo 638302 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B640515 : Blo 638302 640515 := bstep (se 1 (by rfl) ⟨480386, by rfl⟩ : syracuseStep 640515 = 960773) B960773
theorem B1820177 : Blo 638302 1820177 := bstep (se 2 (by rfl) ⟨682566, by rfl⟩ : syracuseStep 1820177 = 1365133) B1365133
theorem B640531 : Blo 638302 640531 := bstep (se 1 (by rfl) ⟨480398, by rfl⟩ : syracuseStep 640531 = 960797) B960797
theorem B640547 : Blo 638302 640547 := bstep (se 1 (by rfl) ⟨480410, by rfl⟩ : syracuseStep 640547 = 960821) B960821
theorem B640563 : Blo 638302 640563 := bstep (se 1 (by rfl) ⟨480422, by rfl⟩ : syracuseStep 640563 = 960845) B960845
theorem B640579 : Blo 638302 640579 := bstep (se 1 (by rfl) ⟨480434, by rfl⟩ : syracuseStep 640579 = 960869) B960869
theorem B640595 : Blo 638302 640595 := bstep (se 1 (by rfl) ⟨480446, by rfl⟩ : syracuseStep 640595 = 960893) B960893
theorem B640611 : Blo 638302 640611 := bstep (se 1 (by rfl) ⟨480458, by rfl⟩ : syracuseStep 640611 = 960917) B960917
theorem B2311793 : Blo 638302 2311793 := bstep (se 2 (by rfl) ⟨866922, by rfl⟩ : syracuseStep 2311793 = 1733845) B1733845
theorem B1623665 : Blo 638302 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B640627 : Blo 638302 640627 := bstep (se 1 (by rfl) ⟨480470, by rfl⟩ : syracuseStep 640627 = 960941) B960941
theorem B640643 : Blo 638302 640643 := bstep (se 1 (by rfl) ⟨480482, by rfl⟩ : syracuseStep 640643 = 960965) B960965
theorem B640659 : Blo 638302 640659 := bstep (se 1 (by rfl) ⟨480494, by rfl⟩ : syracuseStep 640659 = 960989) B960989
theorem B640675 : Blo 638302 640675 := bstep (se 1 (by rfl) ⟨480506, by rfl⟩ : syracuseStep 640675 = 961013) B961013
theorem B640691 : Blo 638302 640691 := bstep (se 1 (by rfl) ⟨480518, by rfl⟩ : syracuseStep 640691 = 961037) B961037
theorem B640707 : Blo 638302 640707 := bstep (se 1 (by rfl) ⟨480530, by rfl⟩ : syracuseStep 640707 = 961061) B961061
theorem B640723 : Blo 638302 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B640739 : Blo 638302 640739 := bstep (se 1 (by rfl) ⟨480554, by rfl⟩ : syracuseStep 640739 = 961109) B961109
theorem B2311907 : Blo 638302 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B640755 : Blo 638302 640755 := bstep (se 1 (by rfl) ⟨480566, by rfl⟩ : syracuseStep 640755 = 961133) B961133
theorem B640771 : Blo 638302 640771 := bstep (se 1 (by rfl) ⟨480578, by rfl⟩ : syracuseStep 640771 = 961157) B961157
theorem B640787 : Blo 638302 640787 := bstep (se 1 (by rfl) ⟨480590, by rfl⟩ : syracuseStep 640787 = 961181) B961181
theorem B640803 : Blo 638302 640803 := bstep (se 1 (by rfl) ⟨480602, by rfl⟩ : syracuseStep 640803 = 961205) B961205
theorem B640819 : Blo 638302 640819 := bstep (se 1 (by rfl) ⟨480614, by rfl⟩ : syracuseStep 640819 = 961229) B961229
theorem B640835 : Blo 638302 640835 := bstep (se 1 (by rfl) ⟨480626, by rfl⟩ : syracuseStep 640835 = 961253) B961253
theorem B640851 : Blo 638302 640851 := bstep (se 1 (by rfl) ⟨480638, by rfl⟩ : syracuseStep 640851 = 961277) B961277
theorem B640867 : Blo 638302 640867 := bstep (se 1 (by rfl) ⟨480650, by rfl⟩ : syracuseStep 640867 = 961301) B961301
theorem B640883 : Blo 638302 640883 := bstep (se 1 (by rfl) ⟨480662, by rfl⟩ : syracuseStep 640883 = 961325) B961325
theorem B640899 : Blo 638302 640899 := bstep (se 1 (by rfl) ⟨480674, by rfl⟩ : syracuseStep 640899 = 961349) B961349
theorem B20760461 : Blo 638302 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B640915 : Blo 638302 640915 := bstep (se 1 (by rfl) ⟨480686, by rfl⟩ : syracuseStep 640915 = 961373) B961373
theorem B640931 : Blo 638302 640931 := bstep (se 1 (by rfl) ⟨480698, by rfl⟩ : syracuseStep 640931 = 961397) B961397
theorem B640947 : Blo 638302 640947 := bstep (se 1 (by rfl) ⟨480710, by rfl⟩ : syracuseStep 640947 = 961421) B961421
theorem B640963 : Blo 638302 640963 := bstep (se 1 (by rfl) ⟨480722, by rfl⟩ : syracuseStep 640963 = 961445) B961445
theorem B640979 : Blo 638302 640979 := bstep (se 1 (by rfl) ⟨480734, by rfl⟩ : syracuseStep 640979 = 961469) B961469
theorem B640995 : Blo 638302 640995 := bstep (se 1 (by rfl) ⟨480746, by rfl⟩ : syracuseStep 640995 = 961493) B961493
theorem B641011 : Blo 638302 641011 := bstep (se 1 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 641011 = 961517) B961517
theorem B641027 : Blo 638302 641027 := bstep (se 1 (by rfl) ⟨480770, by rfl⟩ : syracuseStep 641027 = 961541) B961541
theorem B6670349 : Blo 638302 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B641043 : Blo 638302 641043 := bstep (se 1 (by rfl) ⟨480782, by rfl⟩ : syracuseStep 641043 = 961565) B961565
theorem B641059 : Blo 638302 641059 := bstep (se 1 (by rfl) ⟨480794, by rfl⟩ : syracuseStep 641059 = 961589) B961589
theorem B641075 : Blo 638302 641075 := bstep (se 1 (by rfl) ⟨480806, by rfl⟩ : syracuseStep 641075 = 961613) B961613
theorem B641091 : Blo 638302 641091 := bstep (se 1 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 641091 = 961637) B961637
theorem B641107 : Blo 638302 641107 := bstep (se 1 (by rfl) ⟨480830, by rfl⟩ : syracuseStep 641107 = 961661) B961661
theorem B641123 : Blo 638302 641123 := bstep (se 1 (by rfl) ⟨480842, by rfl⟩ : syracuseStep 641123 = 961685) B961685
theorem B1755245 : Blo 638302 1755245 := bstep (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) B658217
theorem B641139 : Blo 638302 641139 := bstep (se 1 (by rfl) ⟨480854, by rfl⟩ : syracuseStep 641139 = 961709) B961709
theorem B641155 : Blo 638302 641155 := bstep (se 1 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 641155 = 961733) B961733
theorem B641171 : Blo 638302 641171 := bstep (se 1 (by rfl) ⟨480878, by rfl⟩ : syracuseStep 641171 = 961757) B961757
theorem B2050211 : Blo 638302 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B641187 : Blo 638302 641187 := bstep (se 1 (by rfl) ⟨480890, by rfl⟩ : syracuseStep 641187 = 961781) B961781
theorem B4376753 : Blo 638302 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B641203 : Blo 638302 641203 := bstep (se 1 (by rfl) ⟨480902, by rfl⟩ : syracuseStep 641203 = 961805) B961805
theorem B641219 : Blo 638302 641219 := bstep (se 1 (by rfl) ⟨480914, by rfl⟩ : syracuseStep 641219 = 961829) B961829
theorem B641235 : Blo 638302 641235 := bstep (se 1 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 641235 = 961853) B961853
theorem B641251 : Blo 638302 641251 := bstep (se 1 (by rfl) ⟨480938, by rfl⟩ : syracuseStep 641251 = 961877) B961877
theorem B641267 : Blo 638302 641267 := bstep (se 1 (by rfl) ⟨480950, by rfl⟩ : syracuseStep 641267 = 961901) B961901
theorem B641283 : Blo 638302 641283 := bstep (se 1 (by rfl) ⟨480962, by rfl⟩ : syracuseStep 641283 = 961925) B961925
theorem B641299 : Blo 638302 641299 := bstep (se 1 (by rfl) ⟨480974, by rfl⟩ : syracuseStep 641299 = 961949) B961949
theorem B641315 : Blo 638302 641315 := bstep (se 1 (by rfl) ⟨480986, by rfl⟩ : syracuseStep 641315 = 961973) B961973
theorem B641331 : Blo 638302 641331 := bstep (se 1 (by rfl) ⟨480998, by rfl⟩ : syracuseStep 641331 = 961997) B961997
theorem B641347 : Blo 638302 641347 := bstep (se 1 (by rfl) ⟨481010, by rfl⟩ : syracuseStep 641347 = 962021) B962021
theorem B641363 : Blo 638302 641363 := bstep (se 1 (by rfl) ⟨481022, by rfl⟩ : syracuseStep 641363 = 962045) B962045
theorem B641379 : Blo 638302 641379 := bstep (se 1 (by rfl) ⟨481034, by rfl⟩ : syracuseStep 641379 = 962069) B962069
theorem B641395 : Blo 638302 641395 := bstep (se 1 (by rfl) ⟨481046, by rfl⟩ : syracuseStep 641395 = 962093) B962093
theorem B641411 : Blo 638302 641411 := bstep (se 1 (by rfl) ⟨481058, by rfl⟩ : syracuseStep 641411 = 962117) B962117
theorem B641427 : Blo 638302 641427 := bstep (se 1 (by rfl) ⟨481070, by rfl⟩ : syracuseStep 641427 = 962141) B962141
theorem B641443 : Blo 638302 641443 := bstep (se 1 (by rfl) ⟨481082, by rfl⟩ : syracuseStep 641443 = 962165) B962165
theorem B641459 : Blo 638302 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B641475 : Blo 638302 641475 := bstep (se 1 (by rfl) ⟨481106, by rfl⟩ : syracuseStep 641475 = 962213) B962213
theorem B1821133 : Blo 638302 1821133 := bstep (se 3 (by rfl) ⟨341462, by rfl⟩ : syracuseStep 1821133 = 682925) B682925
theorem B641491 : Blo 638302 641491 := bstep (se 1 (by rfl) ⟨481118, by rfl⟩ : syracuseStep 641491 = 962237) B962237
theorem B641507 : Blo 638302 641507 := bstep (se 1 (by rfl) ⟨481130, by rfl⟩ : syracuseStep 641507 = 962261) B962261
theorem B641523 : Blo 638302 641523 := bstep (se 1 (by rfl) ⟨481142, by rfl⟩ : syracuseStep 641523 = 962285) B962285
theorem B641539 : Blo 638302 641539 := bstep (se 1 (by rfl) ⟨481154, by rfl⟩ : syracuseStep 641539 = 962309) B962309
theorem B1296913 : Blo 638302 1296913 := bstep (se 2 (by rfl) ⟨486342, by rfl⟩ : syracuseStep 1296913 = 972685) B972685
theorem B641555 : Blo 638302 641555 := bstep (se 1 (by rfl) ⟨481166, by rfl⟩ : syracuseStep 641555 = 962333) B962333
theorem B641571 : Blo 638302 641571 := bstep (se 1 (by rfl) ⟨481178, by rfl⟩ : syracuseStep 641571 = 962357) B962357
theorem B2050609 : Blo 638302 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B641587 : Blo 638302 641587 := bstep (se 1 (by rfl) ⟨481190, by rfl⟩ : syracuseStep 641587 = 962381) B962381
theorem B641603 : Blo 638302 641603 := bstep (se 1 (by rfl) ⟨481202, by rfl⟩ : syracuseStep 641603 = 962405) B962405
theorem B1624657 : Blo 638302 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B641619 : Blo 638302 641619 := bstep (se 1 (by rfl) ⟨481214, by rfl⟩ : syracuseStep 641619 = 962429) B962429
theorem B641635 : Blo 638302 641635 := bstep (se 1 (by rfl) ⟨481226, by rfl⟩ : syracuseStep 641635 = 962453) B962453
theorem B641651 : Blo 638302 641651 := bstep (se 1 (by rfl) ⟨481238, by rfl⟩ : syracuseStep 641651 = 962477) B962477
theorem B641667 : Blo 638302 641667 := bstep (se 1 (by rfl) ⟨481250, by rfl⟩ : syracuseStep 641667 = 962501) B962501
theorem B641683 : Blo 638302 641683 := bstep (se 1 (by rfl) ⟨481262, by rfl⟩ : syracuseStep 641683 = 962525) B962525
theorem B641699 : Blo 638302 641699 := bstep (se 1 (by rfl) ⟨481274, by rfl⟩ : syracuseStep 641699 = 962549) B962549
theorem B1821361 : Blo 638302 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B641715 : Blo 638302 641715 := bstep (se 1 (by rfl) ⟨481286, by rfl⟩ : syracuseStep 641715 = 962573) B962573
theorem B641731 : Blo 638302 641731 := bstep (se 1 (by rfl) ⟨481298, by rfl⟩ : syracuseStep 641731 = 962597) B962597
theorem B641747 : Blo 638302 641747 := bstep (se 1 (by rfl) ⟨481310, by rfl⟩ : syracuseStep 641747 = 962621) B962621
theorem B641763 : Blo 638302 641763 := bstep (se 1 (by rfl) ⟨481322, by rfl⟩ : syracuseStep 641763 = 962645) B962645
theorem B641779 : Blo 638302 641779 := bstep (se 1 (by rfl) ⟨481334, by rfl⟩ : syracuseStep 641779 = 962669) B962669
theorem B641795 : Blo 638302 641795 := bstep (se 1 (by rfl) ⟨481346, by rfl⟩ : syracuseStep 641795 = 962693) B962693
theorem B641811 : Blo 638302 641811 := bstep (se 1 (by rfl) ⟨481358, by rfl⟩ : syracuseStep 641811 = 962717) B962717
theorem B641827 : Blo 638302 641827 := bstep (se 1 (by rfl) ⟨481370, by rfl⟩ : syracuseStep 641827 = 962741) B962741
theorem B641843 : Blo 638302 641843 := bstep (se 1 (by rfl) ⟨481382, by rfl⟩ : syracuseStep 641843 = 962765) B962765
theorem B641859 : Blo 638302 641859 := bstep (se 1 (by rfl) ⟨481394, by rfl⟩ : syracuseStep 641859 = 962789) B962789
theorem B1821521 : Blo 638302 1821521 := bstep (se 2 (by rfl) ⟨683070, by rfl⟩ : syracuseStep 1821521 = 1366141) B1366141
theorem B641875 : Blo 638302 641875 := bstep (se 1 (by rfl) ⟨481406, by rfl⟩ : syracuseStep 641875 = 962813) B962813
theorem B641891 : Blo 638302 641891 := bstep (se 1 (by rfl) ⟨481418, by rfl⟩ : syracuseStep 641891 = 962837) B962837
theorem B1624931 : Blo 638302 1624931 := bstep (se 1 (by rfl) ⟨1218698, by rfl⟩ : syracuseStep 1624931 = 2437397) B2437397
theorem B641907 : Blo 638302 641907 := bstep (se 1 (by rfl) ⟨481430, by rfl⟩ : syracuseStep 641907 = 962861) B962861
theorem B641923 : Blo 638302 641923 := bstep (se 1 (by rfl) ⟨481442, by rfl⟩ : syracuseStep 641923 = 962885) B962885
theorem B641939 : Blo 638302 641939 := bstep (se 1 (by rfl) ⟨481454, by rfl⟩ : syracuseStep 641939 = 962909) B962909
theorem B641955 : Blo 638302 641955 := bstep (se 1 (by rfl) ⟨481466, by rfl⟩ : syracuseStep 641955 = 962933) B962933
theorem B641971 : Blo 638302 641971 := bstep (se 1 (by rfl) ⟨481478, by rfl⟩ : syracuseStep 641971 = 962957) B962957
theorem B1821635 : Blo 638302 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B641987 : Blo 638302 641987 := bstep (se 1 (by rfl) ⟨481490, by rfl⟩ : syracuseStep 641987 = 962981) B962981
theorem B1952707 : Blo 638302 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B642003 : Blo 638302 642003 := bstep (se 1 (by rfl) ⟨481502, by rfl⟩ : syracuseStep 642003 = 963005) B963005
theorem B642019 : Blo 638302 642019 := bstep (se 1 (by rfl) ⟨481514, by rfl⟩ : syracuseStep 642019 = 963029) B963029
theorem B2051057 : Blo 638302 2051057 := bstep (se 2 (by rfl) ⟨769146, by rfl⟩ : syracuseStep 2051057 = 1538293) B1538293
theorem B642035 : Blo 638302 642035 := bstep (se 1 (by rfl) ⟨481526, by rfl⟩ : syracuseStep 642035 = 963053) B963053
theorem B642051 : Blo 638302 642051 := bstep (se 1 (by rfl) ⟨481538, by rfl⟩ : syracuseStep 642051 = 963077) B963077
theorem B642067 : Blo 638302 642067 := bstep (se 1 (by rfl) ⟨481550, by rfl⟩ : syracuseStep 642067 = 963101) B963101
theorem B1625123 : Blo 638302 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B642083 : Blo 638302 642083 := bstep (se 1 (by rfl) ⟨481562, by rfl⟩ : syracuseStep 642083 = 963125) B963125
theorem B1952813 : Blo 638302 1952813 := bstep (se 3 (by rfl) ⟨366152, by rfl⟩ : syracuseStep 1952813 = 732305) B732305
theorem B642099 : Blo 638302 642099 := bstep (se 1 (by rfl) ⟨481574, by rfl⟩ : syracuseStep 642099 = 963149) B963149
theorem B642115 : Blo 638302 642115 := bstep (se 1 (by rfl) ⟨481586, by rfl⟩ : syracuseStep 642115 = 963173) B963173
theorem B642131 : Blo 638302 642131 := bstep (se 1 (by rfl) ⟨481598, by rfl⟩ : syracuseStep 642131 = 963197) B963197
theorem B642147 : Blo 638302 642147 := bstep (se 1 (by rfl) ⟨481610, by rfl⟩ : syracuseStep 642147 = 963221) B963221
theorem B4869233 : Blo 638302 4869233 := bstep (se 2 (by rfl) ⟨1825962, by rfl⟩ : syracuseStep 4869233 = 3651925) B3651925
theorem B642163 : Blo 638302 642163 := bstep (se 1 (by rfl) ⟨481622, by rfl⟩ : syracuseStep 642163 = 963245) B963245
theorem B642179 : Blo 638302 642179 := bstep (se 1 (by rfl) ⟨481634, by rfl⟩ : syracuseStep 642179 = 963269) B963269
theorem B642195 : Blo 638302 642195 := bstep (se 1 (by rfl) ⟨481646, by rfl⟩ : syracuseStep 642195 = 963293) B963293
theorem B642211 : Blo 638302 642211 := bstep (se 1 (by rfl) ⟨481658, by rfl⟩ : syracuseStep 642211 = 963317) B963317
theorem B642227 : Blo 638302 642227 := bstep (se 1 (by rfl) ⟨481670, by rfl⟩ : syracuseStep 642227 = 963341) B963341
theorem B642243 : Blo 638302 642243 := bstep (se 1 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 642243 = 963365) B963365
theorem B642259 : Blo 638302 642259 := bstep (se 1 (by rfl) ⟨481694, by rfl⟩ : syracuseStep 642259 = 963389) B963389
theorem B4377827 : Blo 638302 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B642275 : Blo 638302 642275 := bstep (se 1 (by rfl) ⟨481706, by rfl⟩ : syracuseStep 642275 = 963413) B963413
theorem B642291 : Blo 638302 642291 := bstep (se 1 (by rfl) ⟨481718, by rfl⟩ : syracuseStep 642291 = 963437) B963437
theorem B2739491 : Blo 638302 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B3165581 : Blo 638302 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B11685347 : Blo 638302 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B1298243 : Blo 638302 1298243 := bstep (se 1 (by rfl) ⟨973682, by rfl⟩ : syracuseStep 1298243 = 1947365) B1947365
theorem B1822637 : Blo 638302 1822637 := bstep (se 3 (by rfl) ⟨341744, by rfl⟩ : syracuseStep 1822637 = 683489) B683489
theorem B1822819 : Blo 638302 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B1822979 : Blo 638302 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B1364483 : Blo 638302 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B971347 : Blo 638302 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B10965617 : Blo 638302 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B3232547 : Blo 638302 3232547 := bstep (se 1 (by rfl) ⟨2424410, by rfl⟩ : syracuseStep 3232547 = 4848821) B4848821
theorem B971585 : Blo 638302 971585 := bstep (se 2 (by rfl) ⟨364344, by rfl⟩ : syracuseStep 971585 = 728689) B728689
theorem B2053133 : Blo 638302 2053133 := bstep (se 3 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 2053133 = 769925) B769925
theorem B808051 : Blo 638302 808051 := bstep (se 1 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 808051 = 1212077) B1212077
theorem B1496227 : Blo 638302 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B808147 : Blo 638302 808147 := bstep (se 1 (by rfl) ⟨606110, by rfl⟩ : syracuseStep 808147 = 1212221) B1212221
theorem B1824049 : Blo 638302 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B2184653 : Blo 638302 2184653 := bstep (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) B819245
theorem B3233357 : Blo 638302 3233357 := bstep (se 3 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 3233357 = 1212509) B1212509
theorem B3757745 : Blo 638302 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B808643 : Blo 638302 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B1365731 : Blo 638302 1365731 := bstep (se 1 (by rfl) ⟨1024298, by rfl⟩ : syracuseStep 1365731 = 2048597) B2048597
theorem B5461829 : Blo 638302 5461829 := bstep (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) B1024093
theorem B2054413 : Blo 638302 2054413 := bstep (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) B770405
theorem B973075 : Blo 638302 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B1366321 : Blo 638302 1366321 := bstep (se 2 (by rfl) ⟨512370, by rfl⟩ : syracuseStep 1366321 = 1024741) B1024741
theorem B809347 : Blo 638302 809347 := bstep (se 1 (by rfl) ⟨607010, by rfl⟩ : syracuseStep 809347 = 1214021) B1214021
theorem B809443 : Blo 638302 809443 := bstep (se 1 (by rfl) ⟨607082, by rfl⟩ : syracuseStep 809443 = 1214165) B1214165
theorem B1727011 : Blo 638302 1727011 := bstep (se 1 (by rfl) ⟨1295258, by rfl⟩ : syracuseStep 1727011 = 2590517) B2590517
theorem B1825325 : Blo 638302 1825325 := bstep (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) B684497
theorem B1825507 : Blo 638302 1825507 := bstep (se 1 (by rfl) ⟨1369130, by rfl⟩ : syracuseStep 1825507 = 2738261) B2738261
theorem B2054915 : Blo 638302 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B1825553 : Blo 638302 1825553 := bstep (se 2 (by rfl) ⟨684582, by rfl⟩ : syracuseStep 1825553 = 1369165) B1369165
theorem B2743217 : Blo 638302 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B809939 : Blo 638302 809939 := bstep (se 1 (by rfl) ⟨607454, by rfl⟩ : syracuseStep 809939 = 1214909) B1214909
theorem B1301681 : Blo 638302 1301681 := bstep (se 2 (by rfl) ⟨488130, by rfl⟩ : syracuseStep 1301681 = 976261) B976261
theorem B2219345 : Blo 638302 2219345 := bstep (se 2 (by rfl) ⟨832254, by rfl⟩ : syracuseStep 2219345 = 1664509) B1664509
theorem B974243 : Blo 638302 974243 := bstep (se 1 (by rfl) ⟨730682, by rfl⟩ : syracuseStep 974243 = 1461365) B1461365
theorem B1728049 : Blo 638302 1728049 := bstep (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) B1296037
theorem B2186833 : Blo 638302 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B810643 : Blo 638302 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B908995 : Blo 638302 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B810739 : Blo 638302 810739 := bstep (se 1 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 810739 = 1216109) B1216109
theorem B1269521 : Blo 638302 1269521 := bstep (se 2 (by rfl) ⟨476070, by rfl⟩ : syracuseStep 1269521 = 952141) B952141
theorem B2154275 : Blo 638302 2154275 := bstep (se 1 (by rfl) ⟨1615706, by rfl⟩ : syracuseStep 2154275 = 3231413) B3231413
theorem B647075 : Blo 638302 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B2154545 : Blo 638302 2154545 := bstep (se 2 (by rfl) ⟨807954, by rfl⟩ : syracuseStep 2154545 = 1615909) B1615909
theorem B2056259 : Blo 638302 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B909473 : Blo 638302 909473 := bstep (se 2 (by rfl) ⟨341052, by rfl⟩ : syracuseStep 909473 = 682105) B682105
theorem B1827011 : Blo 638302 1827011 := bstep (se 1 (by rfl) ⟨1370258, by rfl⟩ : syracuseStep 1827011 = 2740517) B2740517
theorem B811235 : Blo 638302 811235 := bstep (se 1 (by rfl) ⟨608426, by rfl⟩ : syracuseStep 811235 = 1216853) B1216853
theorem B909587 : Blo 638302 909587 := bstep (se 1 (by rfl) ⟨682190, by rfl⟩ : syracuseStep 909587 = 1364381) B1364381
theorem B909667 : Blo 638302 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B2187665 : Blo 638302 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B3236273 : Blo 638302 3236273 := bstep (se 2 (by rfl) ⟨1213602, by rfl⟩ : syracuseStep 3236273 = 2427205) B2427205
theorem B2155085 : Blo 638302 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B2155139 : Blo 638302 2155139 := bstep (se 1 (by rfl) ⟨1616354, by rfl⟩ : syracuseStep 2155139 = 3232709) B3232709
theorem B2155409 : Blo 638302 2155409 := bstep (se 2 (by rfl) ⟨808278, by rfl⟩ : syracuseStep 2155409 = 1616557) B1616557
theorem B910225 : Blo 638302 910225 := bstep (se 2 (by rfl) ⟨341334, by rfl⟩ : syracuseStep 910225 = 682669) B682669
theorem B811939 : Blo 638302 811939 := bstep (se 1 (by rfl) ⟨608954, by rfl⟩ : syracuseStep 811939 = 1217909) B1217909
theorem B1729457 : Blo 638302 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B812035 : Blo 638302 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B2057233 : Blo 638302 2057233 := bstep (se 2 (by rfl) ⟨771462, by rfl⟩ : syracuseStep 2057233 = 1542925) B1542925
theorem B648307 : Blo 638302 648307 := bstep (se 1 (by rfl) ⟨486230, by rfl⟩ : syracuseStep 648307 = 972461) B972461
theorem B976115 : Blo 638302 976115 := bstep (se 1 (by rfl) ⟨732086, by rfl⟩ : syracuseStep 976115 = 1464173) B1464173
theorem B1500419 : Blo 638302 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B2057489 : Blo 638302 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B1828241 : Blo 638302 1828241 := bstep (se 2 (by rfl) ⟨685590, by rfl⟩ : syracuseStep 1828241 = 1371181) B1371181
theorem B1369507 : Blo 638302 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B2155949 : Blo 638302 2155949 := bstep (se 3 (by rfl) ⟨404240, by rfl⟩ : syracuseStep 2155949 = 808481) B808481
theorem B2156003 : Blo 638302 2156003 := bstep (se 1 (by rfl) ⟨1617002, by rfl⟩ : syracuseStep 2156003 = 3234005) B3234005
theorem B812531 : Blo 638302 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B910931 : Blo 638302 910931 := bstep (se 1 (by rfl) ⟨683198, by rfl⟩ : syracuseStep 910931 = 1366397) B1366397
theorem B2156273 : Blo 638302 2156273 := bstep (se 2 (by rfl) ⟨808602, by rfl⟩ : syracuseStep 2156273 = 1617205) B1617205
theorem B3237731 : Blo 638302 3237731 := bstep (se 1 (by rfl) ⟨2428298, by rfl⟩ : syracuseStep 3237731 = 4856597) B4856597
theorem B15591365 : Blo 638302 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B649219 : Blo 638302 649219 := bstep (se 1 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 649219 = 973829) B973829
theorem B9234485 : Blo 638302 9234485 := bstep (se 5 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 9234485 = 865733) B865733
theorem B3074125 : Blo 638302 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B682067 : Blo 638302 682067 := bstep (se 1 (by rfl) ⟨511550, by rfl⟩ : syracuseStep 682067 = 1023101) B1023101
theorem B911569 : Blo 638302 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B5204195 : Blo 638302 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B1370353 : Blo 638302 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B2156813 : Blo 638302 2156813 := bstep (se 3 (by rfl) ⟨404402, by rfl⟩ : syracuseStep 2156813 = 808805) B808805
theorem B1042723 : Blo 638302 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B2156867 : Blo 638302 2156867 := bstep (se 1 (by rfl) ⟨1617650, by rfl⟩ : syracuseStep 2156867 = 3235301) B3235301
theorem B911683 : Blo 638302 911683 := bstep (se 1 (by rfl) ⟨683762, by rfl⟩ : syracuseStep 911683 = 1367525) B1367525
theorem B2157137 : Blo 638302 2157137 := bstep (se 2 (by rfl) ⟨808926, by rfl⟩ : syracuseStep 2157137 = 1617853) B1617853
theorem B1436273 : Blo 638302 1436273 := bstep (se 2 (by rfl) ⟨538602, by rfl⟩ : syracuseStep 1436273 = 1077205) B1077205
theorem B1436291 : Blo 638302 1436291 := bstep (se 1 (by rfl) ⟨1077218, by rfl⟩ : syracuseStep 1436291 = 2154437) B2154437
theorem B3238541 : Blo 638302 3238541 := bstep (se 3 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 3238541 = 1214453) B1214453
theorem B2190019 : Blo 638302 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B1436561 : Blo 638302 1436561 := bstep (se 2 (by rfl) ⟨538710, by rfl⟩ : syracuseStep 1436561 = 1077421) B1077421
theorem B1436579 : Blo 638302 1436579 := bstep (se 1 (by rfl) ⟨1077434, by rfl⟩ : syracuseStep 1436579 = 2154869) B2154869
theorem B2157677 : Blo 638302 2157677 := bstep (se 3 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 2157677 = 809129) B809129
theorem B2157731 : Blo 638302 2157731 := bstep (se 1 (by rfl) ⟨1618298, by rfl⟩ : syracuseStep 2157731 = 3236597) B3236597
theorem B1436849 : Blo 638302 1436849 := bstep (se 2 (by rfl) ⟨538818, by rfl⟩ : syracuseStep 1436849 = 1077637) B1077637
theorem B1436867 : Blo 638302 1436867 := bstep (se 1 (by rfl) ⟨1077650, by rfl⟩ : syracuseStep 1436867 = 2155301) B2155301
theorem B1535267 : Blo 638302 1535267 := bstep (se 1 (by rfl) ⟨1151450, by rfl⟩ : syracuseStep 1535267 = 2302901) B2302901
theorem B2158001 : Blo 638302 2158001 := bstep (se 2 (by rfl) ⟨809250, by rfl⟩ : syracuseStep 2158001 = 1618501) B1618501
theorem B1437137 : Blo 638302 1437137 := bstep (se 2 (by rfl) ⟨538926, by rfl⟩ : syracuseStep 1437137 = 1077853) B1077853
theorem B1437155 : Blo 638302 1437155 := bstep (se 1 (by rfl) ⟨1077866, by rfl⟩ : syracuseStep 1437155 = 2155733) B2155733
theorem B3468899 : Blo 638302 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B913027 : Blo 638302 913027 := bstep (se 1 (by rfl) ⟨684770, by rfl⟩ : syracuseStep 913027 = 1369541) B1369541
theorem B9203341 : Blo 638302 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B1535651 : Blo 638302 1535651 := bstep (se 1 (by rfl) ⟨1151738, by rfl⟩ : syracuseStep 1535651 = 2303477) B2303477
theorem B1437425 : Blo 638302 1437425 := bstep (se 2 (by rfl) ⟨539034, by rfl⟩ : syracuseStep 1437425 = 1078069) B1078069
theorem B1437443 : Blo 638302 1437443 := bstep (se 1 (by rfl) ⟨1078082, by rfl⟩ : syracuseStep 1437443 = 2156165) B2156165
theorem B1077185 : Blo 638302 1077185 := bstep (se 2 (by rfl) ⟨403944, by rfl⟩ : syracuseStep 1077185 = 807889) B807889
theorem B2158541 : Blo 638302 2158541 := bstep (se 3 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 2158541 = 809453) B809453
theorem B2158595 : Blo 638302 2158595 := bstep (se 1 (by rfl) ⟨1618946, by rfl⟩ : syracuseStep 2158595 = 3237893) B3237893
theorem B1437713 : Blo 638302 1437713 := bstep (se 2 (by rfl) ⟨539142, by rfl⟩ : syracuseStep 1437713 = 1078285) B1078285
theorem B1437731 : Blo 638302 1437731 := bstep (se 1 (by rfl) ⟨1078298, by rfl⟩ : syracuseStep 1437731 = 2156597) B2156597
theorem B684083 : Blo 638302 684083 := bstep (se 1 (by rfl) ⟨513062, by rfl⟩ : syracuseStep 684083 = 1026125) B1026125
theorem B1077313 : Blo 638302 1077313 := bstep (se 2 (by rfl) ⟨403992, by rfl⟩ : syracuseStep 1077313 = 807985) B807985
theorem B1077347 : Blo 638302 1077347 := bstep (se 1 (by rfl) ⟨808010, by rfl⟩ : syracuseStep 1077347 = 1616021) B1616021
theorem B1077475 : Blo 638302 1077475 := bstep (se 1 (by rfl) ⟨808106, by rfl⟩ : syracuseStep 1077475 = 1616213) B1616213
theorem B3207395 : Blo 638302 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B2158865 : Blo 638302 2158865 := bstep (se 2 (by rfl) ⟨809574, by rfl⟩ : syracuseStep 2158865 = 1619149) B1619149
theorem B2191661 : Blo 638302 2191661 := bstep (se 3 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 2191661 = 821873) B821873
theorem B1438001 : Blo 638302 1438001 := bstep (se 2 (by rfl) ⟨539250, by rfl⟩ : syracuseStep 1438001 = 1078501) B1078501
theorem B1438019 : Blo 638302 1438019 := bstep (se 1 (by rfl) ⟨1078514, by rfl⟩ : syracuseStep 1438019 = 2157029) B2157029
theorem B1077617 : Blo 638302 1077617 := bstep (se 2 (by rfl) ⟨404106, by rfl⟩ : syracuseStep 1077617 = 808213) B808213
theorem B1077745 : Blo 638302 1077745 := bstep (se 2 (by rfl) ⟨404154, by rfl⟩ : syracuseStep 1077745 = 808309) B808309
theorem B1077779 : Blo 638302 1077779 := bstep (se 1 (by rfl) ⟨808334, by rfl⟩ : syracuseStep 1077779 = 1616669) B1616669
theorem B1438289 : Blo 638302 1438289 := bstep (se 2 (by rfl) ⟨539358, by rfl⟩ : syracuseStep 1438289 = 1078717) B1078717
theorem B1438307 : Blo 638302 1438307 := bstep (se 1 (by rfl) ⟨1078730, by rfl⟩ : syracuseStep 1438307 = 2157461) B2157461
theorem B1077907 : Blo 638302 1077907 := bstep (se 1 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 1077907 = 1616861) B1616861
theorem B914161 : Blo 638302 914161 := bstep (se 2 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 914161 = 685621) B685621
theorem B1078049 : Blo 638302 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B2159405 : Blo 638302 2159405 := bstep (se 3 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 2159405 = 809777) B809777
theorem B914257 : Blo 638302 914257 := bstep (se 2 (by rfl) ⟨342846, by rfl⟩ : syracuseStep 914257 = 685693) B685693
theorem B2159459 : Blo 638302 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B1438577 : Blo 638302 1438577 := bstep (se 2 (by rfl) ⟨539466, by rfl⟩ : syracuseStep 1438577 = 1078933) B1078933
theorem B1438595 : Blo 638302 1438595 := bstep (se 1 (by rfl) ⟨1078946, by rfl⟩ : syracuseStep 1438595 = 2157893) B2157893
theorem B1078177 : Blo 638302 1078177 := bstep (se 2 (by rfl) ⟨404316, by rfl⟩ : syracuseStep 1078177 = 808633) B808633
theorem B1078211 : Blo 638302 1078211 := bstep (se 1 (by rfl) ⟨808658, by rfl⟩ : syracuseStep 1078211 = 1617317) B1617317
theorem B685027 : Blo 638302 685027 := bstep (se 1 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 685027 = 1027541) B1027541
theorem B1078339 : Blo 638302 1078339 := bstep (se 1 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 1078339 = 1617509) B1617509
theorem B2159729 : Blo 638302 2159729 := bstep (se 2 (by rfl) ⟨809898, by rfl⟩ : syracuseStep 2159729 = 1619797) B1619797
theorem B1438865 : Blo 638302 1438865 := bstep (se 2 (by rfl) ⟨539574, by rfl⟩ : syracuseStep 1438865 = 1079149) B1079149
theorem B1438883 : Blo 638302 1438883 := bstep (se 1 (by rfl) ⟨1079162, by rfl⟩ : syracuseStep 1438883 = 2158325) B2158325
theorem B1078481 : Blo 638302 1078481 := bstep (se 2 (by rfl) ⟨404430, by rfl⟩ : syracuseStep 1078481 = 808861) B808861
theorem B1078609 : Blo 638302 1078609 := bstep (se 2 (by rfl) ⟨404478, by rfl⟩ : syracuseStep 1078609 = 808957) B808957
theorem B4388195 : Blo 638302 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B718195 : Blo 638302 718195 := bstep (se 1 (by rfl) ⟨538646, by rfl⟩ : syracuseStep 718195 = 1077293) B1077293
theorem B1078643 : Blo 638302 1078643 := bstep (se 1 (by rfl) ⟨808982, by rfl⟩ : syracuseStep 1078643 = 1617965) B1617965
theorem B1734061 : Blo 638302 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B1439153 : Blo 638302 1439153 := bstep (se 2 (by rfl) ⟨539682, by rfl⟩ : syracuseStep 1439153 = 1079365) B1079365
theorem B1439171 : Blo 638302 1439171 := bstep (se 1 (by rfl) ⟨1079378, by rfl⟩ : syracuseStep 1439171 = 2158757) B2158757
theorem B3241457 : Blo 638302 3241457 := bstep (se 2 (by rfl) ⟨1215546, by rfl⟩ : syracuseStep 3241457 = 2431093) B2431093
theorem B1078771 : Blo 638302 1078771 := bstep (se 1 (by rfl) ⟨809078, by rfl⟩ : syracuseStep 1078771 = 1618157) B1618157
theorem B718339 : Blo 638302 718339 := bstep (se 1 (by rfl) ⟨538754, by rfl⟩ : syracuseStep 718339 = 1077509) B1077509
theorem B1078913 : Blo 638302 1078913 := bstep (se 2 (by rfl) ⟨404592, by rfl⟩ : syracuseStep 1078913 = 809185) B809185
theorem B2160269 : Blo 638302 2160269 := bstep (se 3 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 2160269 = 810101) B810101
theorem B718483 : Blo 638302 718483 := bstep (se 1 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 718483 = 1077725) B1077725
theorem B2160323 : Blo 638302 2160323 := bstep (se 1 (by rfl) ⟨1620242, by rfl⟩ : syracuseStep 2160323 = 3240485) B3240485
theorem B1439441 : Blo 638302 1439441 := bstep (se 2 (by rfl) ⟨539790, by rfl⟩ : syracuseStep 1439441 = 1079581) B1079581
theorem B1439459 : Blo 638302 1439459 := bstep (se 1 (by rfl) ⟨1079594, by rfl⟩ : syracuseStep 1439459 = 2159189) B2159189
theorem B1079041 : Blo 638302 1079041 := bstep (se 2 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 1079041 = 809281) B809281
theorem B718627 : Blo 638302 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B1079075 : Blo 638302 1079075 := bstep (se 1 (by rfl) ⟨809306, by rfl⟩ : syracuseStep 1079075 = 1618613) B1618613
theorem B1079203 : Blo 638302 1079203 := bstep (se 1 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 1079203 = 1618805) B1618805
theorem B718771 : Blo 638302 718771 := bstep (se 1 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 718771 = 1078157) B1078157
theorem B2160593 : Blo 638302 2160593 := bstep (se 2 (by rfl) ⟨810222, by rfl⟩ : syracuseStep 2160593 = 1620445) B1620445
theorem B1439729 : Blo 638302 1439729 := bstep (se 2 (by rfl) ⟨539898, by rfl⟩ : syracuseStep 1439729 = 1079797) B1079797
theorem B1439747 : Blo 638302 1439747 := bstep (se 1 (by rfl) ⟨1079810, by rfl⟩ : syracuseStep 1439747 = 2159621) B2159621
theorem B1079345 : Blo 638302 1079345 := bstep (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) B809509
theorem B718915 : Blo 638302 718915 := bstep (se 1 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 718915 = 1078373) B1078373
theorem B1734787 : Blo 638302 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B1079473 : Blo 638302 1079473 := bstep (se 2 (by rfl) ⟨404802, by rfl⟩ : syracuseStep 1079473 = 809605) B809605
theorem B719059 : Blo 638302 719059 := bstep (se 1 (by rfl) ⟨539294, by rfl⟩ : syracuseStep 719059 = 1078589) B1078589
theorem B1079507 : Blo 638302 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B8190179 : Blo 638302 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B1440017 : Blo 638302 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B1440035 : Blo 638302 1440035 := bstep (se 1 (by rfl) ⟨1080026, by rfl⟩ : syracuseStep 1440035 = 2160053) B2160053
theorem B1079635 : Blo 638302 1079635 := bstep (se 1 (by rfl) ⟨809726, by rfl⟩ : syracuseStep 1079635 = 1619453) B1619453
theorem B719203 : Blo 638302 719203 := bstep (se 1 (by rfl) ⟨539402, by rfl⟩ : syracuseStep 719203 = 1078805) B1078805
theorem B5470577 : Blo 638302 5470577 := bstep (se 2 (by rfl) ⟨2051466, by rfl⟩ : syracuseStep 5470577 = 4102933) B4102933
theorem B9238981 : Blo 638302 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B1079777 : Blo 638302 1079777 := bstep (se 2 (by rfl) ⟨404916, by rfl⟩ : syracuseStep 1079777 = 809833) B809833
theorem B2161133 : Blo 638302 2161133 := bstep (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) B810425
theorem B719347 : Blo 638302 719347 := bstep (se 1 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 719347 = 1079021) B1079021
theorem B2161187 : Blo 638302 2161187 := bstep (se 1 (by rfl) ⟨1620890, by rfl⟩ : syracuseStep 2161187 = 3241781) B3241781
theorem B1440305 : Blo 638302 1440305 := bstep (se 2 (by rfl) ⟨540114, by rfl⟩ : syracuseStep 1440305 = 1080229) B1080229
theorem B1440323 : Blo 638302 1440323 := bstep (se 1 (by rfl) ⟨1080242, by rfl⟩ : syracuseStep 1440323 = 2160485) B2160485
theorem B1079905 : Blo 638302 1079905 := bstep (se 2 (by rfl) ⟨404964, by rfl⟩ : syracuseStep 1079905 = 809929) B809929
theorem B719491 : Blo 638302 719491 := bstep (se 1 (by rfl) ⟨539618, by rfl⟩ : syracuseStep 719491 = 1079237) B1079237
theorem B1079939 : Blo 638302 1079939 := bstep (se 1 (by rfl) ⟨809954, by rfl⟩ : syracuseStep 1079939 = 1619909) B1619909
theorem B1080067 : Blo 638302 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B719635 : Blo 638302 719635 := bstep (se 1 (by rfl) ⟨539726, by rfl⟩ : syracuseStep 719635 = 1079453) B1079453
theorem B1538851 : Blo 638302 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B2161457 : Blo 638302 2161457 := bstep (se 2 (by rfl) ⟨810546, by rfl⟩ : syracuseStep 2161457 = 1621093) B1621093
theorem B7306037 : Blo 638302 7306037 := bstep (se 5 (by rfl) ⟨342470, by rfl⟩ : syracuseStep 7306037 = 684941) B684941
theorem B1440593 : Blo 638302 1440593 := bstep (se 2 (by rfl) ⟨540222, by rfl⟩ : syracuseStep 1440593 = 1080445) B1080445
theorem B1440611 : Blo 638302 1440611 := bstep (se 1 (by rfl) ⟨1080458, by rfl⟩ : syracuseStep 1440611 = 2160917) B2160917
theorem B1080209 : Blo 638302 1080209 := bstep (se 2 (by rfl) ⟨405078, by rfl⟩ : syracuseStep 1080209 = 810157) B810157
theorem B719779 : Blo 638302 719779 := bstep (se 1 (by rfl) ⟨539834, by rfl⟩ : syracuseStep 719779 = 1079669) B1079669
theorem B3242915 : Blo 638302 3242915 := bstep (se 1 (by rfl) ⟨2432186, by rfl⟩ : syracuseStep 3242915 = 4864373) B4864373
theorem B6224881 : Blo 638302 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B1080337 : Blo 638302 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B719923 : Blo 638302 719923 := bstep (se 1 (by rfl) ⟨539942, by rfl⟩ : syracuseStep 719923 = 1079885) B1079885
theorem B1080371 : Blo 638302 1080371 := bstep (se 1 (by rfl) ⟨810278, by rfl⟩ : syracuseStep 1080371 = 1620557) B1620557
theorem B1440881 : Blo 638302 1440881 := bstep (se 2 (by rfl) ⟨540330, by rfl⟩ : syracuseStep 1440881 = 1080661) B1080661
theorem B1440899 : Blo 638302 1440899 := bstep (se 1 (by rfl) ⟨1080674, by rfl⟩ : syracuseStep 1440899 = 2161349) B2161349
theorem B1080499 : Blo 638302 1080499 := bstep (se 1 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 1080499 = 1620749) B1620749
theorem B720067 : Blo 638302 720067 := bstep (se 1 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 720067 = 1080101) B1080101
theorem B2424077 : Blo 638302 2424077 := bstep (se 3 (by rfl) ⟨454514, by rfl⟩ : syracuseStep 2424077 = 909029) B909029
theorem B3702029 : Blo 638302 3702029 := bstep (se 3 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 3702029 = 1388261) B1388261
theorem B1080641 : Blo 638302 1080641 := bstep (se 2 (by rfl) ⟨405240, by rfl⟩ : syracuseStep 1080641 = 810481) B810481
theorem B2161997 : Blo 638302 2161997 := bstep (se 3 (by rfl) ⟨405374, by rfl⟩ : syracuseStep 2161997 = 810749) B810749
theorem B720211 : Blo 638302 720211 := bstep (se 1 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 720211 = 1080317) B1080317
theorem B2162051 : Blo 638302 2162051 := bstep (se 1 (by rfl) ⟨1621538, by rfl⟩ : syracuseStep 2162051 = 3243077) B3243077
theorem B1441169 : Blo 638302 1441169 := bstep (se 2 (by rfl) ⟨540438, by rfl⟩ : syracuseStep 1441169 = 1080877) B1080877
theorem B1441187 : Blo 638302 1441187 := bstep (se 1 (by rfl) ⟨1080890, by rfl⟩ : syracuseStep 1441187 = 2161781) B2161781
theorem B1080769 : Blo 638302 1080769 := bstep (se 2 (by rfl) ⟨405288, by rfl⟩ : syracuseStep 1080769 = 810577) B810577
theorem B1539523 : Blo 638302 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B720355 : Blo 638302 720355 := bstep (se 1 (by rfl) ⟨540266, by rfl⟩ : syracuseStep 720355 = 1080533) B1080533
theorem B1080803 : Blo 638302 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B3276323 : Blo 638302 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B1080931 : Blo 638302 1080931 := bstep (se 1 (by rfl) ⟨810698, by rfl⟩ : syracuseStep 1080931 = 1621397) B1621397
theorem B720499 : Blo 638302 720499 := bstep (se 1 (by rfl) ⟨540374, by rfl⟩ : syracuseStep 720499 = 1080749) B1080749
theorem B2162321 : Blo 638302 2162321 := bstep (se 2 (by rfl) ⟨810870, by rfl⟩ : syracuseStep 2162321 = 1621741) B1621741
theorem B1441457 : Blo 638302 1441457 := bstep (se 2 (by rfl) ⟨540546, by rfl⟩ : syracuseStep 1441457 = 1081093) B1081093
theorem B1441475 : Blo 638302 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B3243725 : Blo 638302 3243725 := bstep (se 3 (by rfl) ⟨608198, by rfl⟩ : syracuseStep 3243725 = 1216397) B1216397
theorem B1081073 : Blo 638302 1081073 := bstep (se 2 (by rfl) ⟨405402, by rfl⟩ : syracuseStep 1081073 = 810805) B810805
theorem B720643 : Blo 638302 720643 := bstep (se 1 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 720643 = 1080965) B1080965
theorem B1212259 : Blo 638302 1212259 := bstep (se 1 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 1212259 = 1818389) B1818389
theorem B1081201 : Blo 638302 1081201 := bstep (se 2 (by rfl) ⟨405450, by rfl⟩ : syracuseStep 1081201 = 810901) B810901
theorem B1539985 : Blo 638302 1539985 := bstep (se 2 (by rfl) ⟨577494, by rfl⟩ : syracuseStep 1539985 = 1154989) B1154989
theorem B720787 : Blo 638302 720787 := bstep (se 1 (by rfl) ⟨540590, by rfl⟩ : syracuseStep 720787 = 1081181) B1081181
theorem B1081235 : Blo 638302 1081235 := bstep (se 1 (by rfl) ⟨810926, by rfl⟩ : syracuseStep 1081235 = 1621853) B1621853
theorem B3702725 : Blo 638302 3702725 := bstep (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) B694261
theorem B1441745 : Blo 638302 1441745 := bstep (se 2 (by rfl) ⟨540654, by rfl⟩ : syracuseStep 1441745 = 1081309) B1081309
theorem B1441763 : Blo 638302 1441763 := bstep (se 1 (by rfl) ⟨1081322, by rfl⟩ : syracuseStep 1441763 = 2162645) B2162645
theorem B3244049 : Blo 638302 3244049 := bstep (se 2 (by rfl) ⟨1216518, by rfl⟩ : syracuseStep 3244049 = 2433037) B2433037
theorem B1441817 : Blo 638302 1441817 := bstep (se 2 (by rfl) ⟨540681, by rfl⟩ : syracuseStep 1441817 = 1081363) B1081363
theorem B2162753 : Blo 638302 2162753 := bstep (se 2 (by rfl) ⟨811032, by rfl⟩ : syracuseStep 2162753 = 1622065) B1622065
theorem B721003 : Blo 638302 721003 := bstep (se 1 (by rfl) ⟨540752, by rfl⟩ : syracuseStep 721003 = 1081505) B1081505
theorem B1441907 : Blo 638302 1441907 := bstep (se 1 (by rfl) ⟨1081430, by rfl⟩ : syracuseStep 1441907 = 2162861) B2162861
theorem B78676109 : Blo 638302 78676109 := bstep (se 3 (by rfl) ⟨14751770, by rfl⟩ : syracuseStep 78676109 = 29503541) B29503541
theorem B1441943 : Blo 638302 1441943 := bstep (se 1 (by rfl) ⟨1081457, by rfl⟩ : syracuseStep 1441943 = 2162915) B2162915
theorem B3244211 : Blo 638302 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B1081559 : Blo 638302 1081559 := bstep (se 1 (by rfl) ⟨811169, by rfl⟩ : syracuseStep 1081559 = 1622339) B1622339
theorem B721111 : Blo 638302 721111 := bstep (se 1 (by rfl) ⟨540833, by rfl⟩ : syracuseStep 721111 = 1081667) B1081667
theorem B2425049 : Blo 638302 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B1442123 : Blo 638302 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B1081687 : Blo 638302 1081687 := bstep (se 1 (by rfl) ⟨811265, by rfl⟩ : syracuseStep 1081687 = 1622531) B1622531
theorem B1442177 : Blo 638302 1442177 := bstep (se 2 (by rfl) ⟨540816, by rfl⟩ : syracuseStep 1442177 = 1081633) B1081633
theorem B721291 : Blo 638302 721291 := bstep (se 1 (by rfl) ⟨540968, by rfl⟩ : syracuseStep 721291 = 1081937) B1081937
theorem B2425261 : Blo 638302 2425261 := bstep (se 3 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 2425261 = 909473) B909473
theorem B1212889 : Blo 638302 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B721399 : Blo 638302 721399 := bstep (se 1 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 721399 = 1082099) B1082099
theorem B1442393 : Blo 638302 1442393 := bstep (se 2 (by rfl) ⟨540897, by rfl⟩ : syracuseStep 1442393 = 1081795) B1081795
theorem B8553053 : Blo 638302 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B2163293 : Blo 638302 2163293 := bstep (se 3 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 2163293 = 811235) B811235
theorem B721579 : Blo 638302 721579 := bstep (se 1 (by rfl) ⟨541184, by rfl⟩ : syracuseStep 721579 = 1082369) B1082369
theorem B1442483 : Blo 638302 1442483 := bstep (se 1 (by rfl) ⟨1081862, by rfl⟩ : syracuseStep 1442483 = 2163725) B2163725
theorem B1442519 : Blo 638302 1442519 := bstep (se 1 (by rfl) ⟨1081889, by rfl⟩ : syracuseStep 1442519 = 2163779) B2163779
theorem B2425565 : Blo 638302 2425565 := bstep (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) B909587
theorem B721687 : Blo 638302 721687 := bstep (se 1 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 721687 = 1082531) B1082531
theorem B3081005 : Blo 638302 3081005 := bstep (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) B1155377
theorem B1442699 : Blo 638302 1442699 := bstep (se 1 (by rfl) ⟨1082024, by rfl⟩ : syracuseStep 1442699 = 2164049) B2164049
theorem B1442753 : Blo 638302 1442753 := bstep (se 2 (by rfl) ⟨541032, by rfl⟩ : syracuseStep 1442753 = 1082065) B1082065
theorem B1082315 : Blo 638302 1082315 := bstep (se 1 (by rfl) ⟨811736, by rfl⟩ : syracuseStep 1082315 = 1623473) B1623473
theorem B721867 : Blo 638302 721867 := bstep (se 1 (by rfl) ⟨541400, by rfl⟩ : syracuseStep 721867 = 1082801) B1082801
theorem B5473241 : Blo 638302 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B1213451 : Blo 638302 1213451 := bstep (se 1 (by rfl) ⟨910088, by rfl⟩ : syracuseStep 1213451 = 1820177) B1820177
theorem B721975 : Blo 638302 721975 := bstep (se 1 (by rfl) ⟨541481, by rfl⟩ : syracuseStep 721975 = 1082963) B1082963
theorem B1541195 : Blo 638302 1541195 := bstep (se 1 (by rfl) ⟨1155896, by rfl⟩ : syracuseStep 1541195 = 2311793) B2311793
theorem B1082443 : Blo 638302 1082443 := bstep (se 1 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 1082443 = 1623665) B1623665
theorem B1442969 : Blo 638302 1442969 := bstep (se 2 (by rfl) ⟨541113, by rfl⟩ : syracuseStep 1442969 = 1082227) B1082227
theorem B1213633 : Blo 638302 1213633 := bstep (se 2 (by rfl) ⟨455112, by rfl⟩ : syracuseStep 1213633 = 910225) B910225
theorem B1082585 : Blo 638302 1082585 := bstep (se 2 (by rfl) ⟨405969, by rfl⟩ : syracuseStep 1082585 = 811939) B811939
theorem B722155 : Blo 638302 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B1443059 : Blo 638302 1443059 := bstep (se 1 (by rfl) ⟨1082294, by rfl⟩ : syracuseStep 1443059 = 2164589) B2164589
theorem B6161669 : Blo 638302 6161669 := bstep (se 4 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 6161669 = 1155313) B1155313
theorem B1443095 : Blo 638302 1443095 := bstep (se 1 (by rfl) ⟨1082321, by rfl⟩ : syracuseStep 1443095 = 2164643) B2164643
theorem B722263 : Blo 638302 722263 := bstep (se 1 (by rfl) ⟨541697, by rfl⟩ : syracuseStep 722263 = 1083395) B1083395
theorem B1082713 : Blo 638302 1082713 := bstep (se 2 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 1082713 = 812035) B812035
theorem B3638621 : Blo 638302 3638621 := bstep (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) B1364483
theorem B1246603 : Blo 638302 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B2917835 : Blo 638302 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B1443275 : Blo 638302 1443275 := bstep (se 1 (by rfl) ⟨1082456, by rfl⟩ : syracuseStep 1443275 = 2164913) B2164913
theorem B1443329 : Blo 638302 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B722443 : Blo 638302 722443 := bstep (se 1 (by rfl) ⟨541832, by rfl⟩ : syracuseStep 722443 = 1083665) B1083665
theorem B722551 : Blo 638302 722551 := bstep (se 1 (by rfl) ⟨541913, by rfl⟩ : syracuseStep 722551 = 1083827) B1083827
theorem B2164427 : Blo 638302 2164427 := bstep (se 1 (by rfl) ⟨1623320, by rfl⟩ : syracuseStep 2164427 = 3246641) B3246641
theorem B1443545 : Blo 638302 1443545 := bstep (se 2 (by rfl) ⟨541329, by rfl⟩ : syracuseStep 1443545 = 1082659) B1082659
theorem B1312537 : Blo 638302 1312537 := bstep (se 2 (by rfl) ⟨492201, by rfl⟩ : syracuseStep 1312537 = 984403) B984403
theorem B1443635 : Blo 638302 1443635 := bstep (se 1 (by rfl) ⟨1082726, by rfl⟩ : syracuseStep 1443635 = 2165453) B2165453
theorem B1443671 : Blo 638302 1443671 := bstep (se 1 (by rfl) ⟨1082753, by rfl⟩ : syracuseStep 1443671 = 2165507) B2165507
theorem B1214347 : Blo 638302 1214347 := bstep (se 1 (by rfl) ⟨910760, by rfl⟩ : syracuseStep 1214347 = 1821521) B1821521
theorem B1083287 : Blo 638302 1083287 := bstep (se 1 (by rfl) ⟨812465, by rfl⟩ : syracuseStep 1083287 = 1624931) B1624931
theorem B1214423 : Blo 638302 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B2164697 : Blo 638302 2164697 := bstep (se 2 (by rfl) ⟨811761, by rfl⟩ : syracuseStep 2164697 = 1623523) B1623523
theorem B1443851 : Blo 638302 1443851 := bstep (se 1 (by rfl) ⟨1082888, by rfl⟩ : syracuseStep 1443851 = 2165777) B2165777
theorem B1083415 : Blo 638302 1083415 := bstep (se 1 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 1083415 = 1625123) B1625123
theorem B1443905 : Blo 638302 1443905 := bstep (se 2 (by rfl) ⟨541464, by rfl⟩ : syracuseStep 1443905 = 1082929) B1082929
theorem B3246155 : Blo 638302 3246155 := bstep (se 1 (by rfl) ⟨2434616, by rfl⟩ : syracuseStep 3246155 = 4869233) B4869233
theorem B1640627 : Blo 638302 1640627 := bstep (se 1 (by rfl) ⟨1230470, by rfl⟩ : syracuseStep 1640627 = 2460941) B2460941
theorem B1444121 : Blo 638302 1444121 := bstep (se 2 (by rfl) ⟨541545, by rfl⟩ : syracuseStep 1444121 = 1083091) B1083091
theorem B5835083 : Blo 638302 5835083 := bstep (se 1 (by rfl) ⟨4376312, by rfl⟩ : syracuseStep 5835083 = 8752625) B8752625
theorem B1444211 : Blo 638302 1444211 := bstep (se 1 (by rfl) ⟨1083158, by rfl⟩ : syracuseStep 1444211 = 2166317) B2166317
theorem B1444247 : Blo 638302 1444247 := bstep (se 1 (by rfl) ⟨1083185, by rfl⟩ : syracuseStep 1444247 = 2166371) B2166371
theorem B2591297 : Blo 638302 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B1444427 : Blo 638302 1444427 := bstep (se 1 (by rfl) ⟨1083320, by rfl⟩ : syracuseStep 1444427 = 2166641) B2166641
theorem B4393565 : Blo 638302 4393565 := bstep (se 3 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 4393565 = 1647587) B1647587
theorem B1215091 : Blo 638302 1215091 := bstep (se 1 (by rfl) ⟨911318, by rfl⟩ : syracuseStep 1215091 = 1822637) B1822637
theorem B1444481 : Blo 638302 1444481 := bstep (se 2 (by rfl) ⟨541680, by rfl⟩ : syracuseStep 1444481 = 1083361) B1083361
theorem B2165399 : Blo 638302 2165399 := bstep (se 1 (by rfl) ⟨1624049, by rfl⟩ : syracuseStep 2165399 = 3248099) B3248099
theorem B4098833 : Blo 638302 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B1215319 : Blo 638302 1215319 := bstep (se 1 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 1215319 = 1822979) B1822979
theorem B1444697 : Blo 638302 1444697 := bstep (se 2 (by rfl) ⟨541761, by rfl⟩ : syracuseStep 1444697 = 1083523) B1083523
theorem B1444787 : Blo 638302 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B1215425 : Blo 638302 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B1444823 : Blo 638302 1444823 := bstep (se 1 (by rfl) ⟨1083617, by rfl⟩ : syracuseStep 1444823 = 2167235) B2167235
theorem B7310411 : Blo 638302 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B1215577 : Blo 638302 1215577 := bstep (se 2 (by rfl) ⟨455841, by rfl⟩ : syracuseStep 1215577 = 911683) B911683
theorem B1445003 : Blo 638302 1445003 := bstep (se 1 (by rfl) ⟨1083752, by rfl⟩ : syracuseStep 1445003 = 2167505) B2167505
theorem B2165939 : Blo 638302 2165939 := bstep (se 1 (by rfl) ⟨1624454, by rfl⟩ : syracuseStep 2165939 = 3248909) B3248909
theorem B1445057 : Blo 638302 1445057 := bstep (se 2 (by rfl) ⟨541896, by rfl⟩ : syracuseStep 1445057 = 1083793) B1083793
theorem B2428163 : Blo 638302 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B2428177 : Blo 638302 2428177 := bstep (se 2 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 2428177 = 1821133) B1821133
theorem B2166209 : Blo 638302 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B2428481 : Blo 638302 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B2920025 : Blo 638302 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B11701853 : Blo 638302 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B3247937 : Blo 638302 3247937 := bstep (se 2 (by rfl) ⟨1217976, by rfl⟩ : syracuseStep 3247937 = 2435953) B2435953
theorem B5246795 : Blo 638302 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B3641219 : Blo 638302 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B4853681 : Blo 638302 4853681 := bstep (se 2 (by rfl) ⟨1820130, by rfl⟩ : syracuseStep 4853681 = 3640261) B3640261
theorem B2166749 : Blo 638302 2166749 := bstep (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) B812531
theorem B2429149 : Blo 638302 2429149 := bstep (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) B910931
theorem B1216883 : Blo 638302 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B4854167 : Blo 638302 4854167 := bstep (se 1 (by rfl) ⟨3640625, by rfl⟩ : syracuseStep 4854167 = 7281251) B7281251
theorem B1217035 : Blo 638302 1217035 := bstep (se 1 (by rfl) ⟨912776, by rfl⟩ : syracuseStep 1217035 = 1825553) B1825553
theorem B6165085 : Blo 638302 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B9966341 : Blo 638302 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B1217369 : Blo 638302 1217369 := bstep (se 2 (by rfl) ⟨456513, by rfl⟩ : syracuseStep 1217369 = 913027) B913027
theorem B1479563 : Blo 638302 1479563 := bstep (se 1 (by rfl) ⟨1109672, by rfl⟩ : syracuseStep 1479563 = 2219345) B2219345
theorem B3085235 : Blo 638302 3085235 := bstep (se 1 (by rfl) ⟨2313926, by rfl⟩ : syracuseStep 3085235 = 4627853) B4627853
theorem B1218007 : Blo 638302 1218007 := bstep (se 1 (by rfl) ⟨913505, by rfl⟩ : syracuseStep 1218007 = 1827011) B1827011
theorem B2430425 : Blo 638302 2430425 := bstep (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) B1822819
theorem B3249881 : Blo 638302 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B1382167 : Blo 638302 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B6920113 : Blo 638302 6920113 := bstep (se 2 (by rfl) ⟨2595042, by rfl⟩ : syracuseStep 6920113 = 5190085) B5190085
theorem B1152971 : Blo 638302 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B1218827 : Blo 638302 1218827 := bstep (se 1 (by rfl) ⟨914120, by rfl⟩ : syracuseStep 1218827 = 1828241) B1828241
theorem B2922797 : Blo 638302 2922797 := bstep (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) B1096049
theorem B1218881 : Blo 638302 1218881 := bstep (se 2 (by rfl) ⟨457080, by rfl⟩ : syracuseStep 1218881 = 914161) B914161
theorem B1153433 : Blo 638302 1153433 := bstep (se 2 (by rfl) ⟨432537, by rfl⟩ : syracuseStep 1153433 = 865075) B865075
theorem B10394243 : Blo 638302 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B2432051 : Blo 638302 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B2432065 : Blo 638302 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B957515 : Blo 638302 957515 := bstep (se 1 (by rfl) ⟨718136, by rfl⟩ : syracuseStep 957515 = 1436273) B1436273
theorem B957527 : Blo 638302 957527 := bstep (se 1 (by rfl) ⟨718145, by rfl⟩ : syracuseStep 957527 = 1436291) B1436291
theorem B957593 : Blo 638302 957593 := bstep (se 2 (by rfl) ⟨359097, by rfl⟩ : syracuseStep 957593 = 718195) B718195
theorem B957707 : Blo 638302 957707 := bstep (se 1 (by rfl) ⟨718280, by rfl⟩ : syracuseStep 957707 = 1436561) B1436561
theorem B957719 : Blo 638302 957719 := bstep (se 1 (by rfl) ⟨718289, by rfl⟩ : syracuseStep 957719 = 1436579) B1436579
theorem B3251501 : Blo 638302 3251501 := bstep (se 3 (by rfl) ⟨609656, by rfl⟩ : syracuseStep 3251501 = 1219313) B1219313
theorem B957785 : Blo 638302 957785 := bstep (se 2 (by rfl) ⟨359169, by rfl⟩ : syracuseStep 957785 = 718339) B718339
theorem B957899 : Blo 638302 957899 := bstep (se 1 (by rfl) ⟨718424, by rfl⟩ : syracuseStep 957899 = 1436849) B1436849
theorem B957911 : Blo 638302 957911 := bstep (se 1 (by rfl) ⟨718433, by rfl⟩ : syracuseStep 957911 = 1436867) B1436867
theorem B2301443 : Blo 638302 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B1023511 : Blo 638302 1023511 := bstep (se 1 (by rfl) ⟨767633, by rfl⟩ : syracuseStep 1023511 = 1535267) B1535267
theorem B957977 : Blo 638302 957977 := bstep (se 2 (by rfl) ⟨359241, by rfl⟩ : syracuseStep 957977 = 718483) B718483
theorem B958091 : Blo 638302 958091 := bstep (se 1 (by rfl) ⟨718568, by rfl⟩ : syracuseStep 958091 = 1437137) B1437137
theorem B958103 : Blo 638302 958103 := bstep (se 1 (by rfl) ⟨718577, by rfl⟩ : syracuseStep 958103 = 1437155) B1437155
theorem B2301643 : Blo 638302 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B958169 : Blo 638302 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B1023767 : Blo 638302 1023767 := bstep (se 1 (by rfl) ⟨767825, by rfl⟩ : syracuseStep 1023767 = 1535651) B1535651
theorem B958283 : Blo 638302 958283 := bstep (se 1 (by rfl) ⟨718712, by rfl⟩ : syracuseStep 958283 = 1437425) B1437425
theorem B958295 : Blo 638302 958295 := bstep (se 1 (by rfl) ⟨718721, by rfl⟩ : syracuseStep 958295 = 1437443) B1437443
theorem B958361 : Blo 638302 958361 := bstep (se 2 (by rfl) ⟨359385, by rfl⟩ : syracuseStep 958361 = 718771) B718771
theorem B958475 : Blo 638302 958475 := bstep (se 1 (by rfl) ⟨718856, by rfl⟩ : syracuseStep 958475 = 1437713) B1437713
theorem B958487 : Blo 638302 958487 := bstep (se 1 (by rfl) ⟨718865, by rfl⟩ : syracuseStep 958487 = 1437731) B1437731
theorem B958553 : Blo 638302 958553 := bstep (se 2 (by rfl) ⟨359457, by rfl⟩ : syracuseStep 958553 = 718915) B718915
theorem B1876061 : Blo 638302 1876061 := bstep (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) B703523
theorem B958667 : Blo 638302 958667 := bstep (se 1 (by rfl) ⟨719000, by rfl⟩ : syracuseStep 958667 = 1438001) B1438001
theorem B958679 : Blo 638302 958679 := bstep (se 1 (by rfl) ⟨719009, by rfl⟩ : syracuseStep 958679 = 1438019) B1438019
theorem B958745 : Blo 638302 958745 := bstep (se 2 (by rfl) ⟨359529, by rfl⟩ : syracuseStep 958745 = 719059) B719059
theorem B958859 : Blo 638302 958859 := bstep (se 1 (by rfl) ⟨719144, by rfl⟩ : syracuseStep 958859 = 1438289) B1438289
theorem B958871 : Blo 638302 958871 := bstep (se 1 (by rfl) ⟨719153, by rfl⟩ : syracuseStep 958871 = 1438307) B1438307
theorem B958937 : Blo 638302 958937 := bstep (se 2 (by rfl) ⟨359601, by rfl⟩ : syracuseStep 958937 = 719203) B719203
theorem B959051 : Blo 638302 959051 := bstep (se 1 (by rfl) ⟨719288, by rfl⟩ : syracuseStep 959051 = 1438577) B1438577
theorem B959063 : Blo 638302 959063 := bstep (se 1 (by rfl) ⟨719297, by rfl⟩ : syracuseStep 959063 = 1438595) B1438595
theorem B11674205 : Blo 638302 11674205 := bstep (se 3 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 11674205 = 4377827) B4377827
theorem B729751 : Blo 638302 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B959129 : Blo 638302 959129 := bstep (se 2 (by rfl) ⟨359673, by rfl⟩ : syracuseStep 959129 = 719347) B719347
theorem B9872077 : Blo 638302 9872077 := bstep (se 3 (by rfl) ⟨1851014, by rfl⟩ : syracuseStep 9872077 = 3702029) B3702029
theorem B2302681 : Blo 638302 2302681 := bstep (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) B1727011
theorem B959243 : Blo 638302 959243 := bstep (se 1 (by rfl) ⟨719432, by rfl⟩ : syracuseStep 959243 = 1438865) B1438865
theorem B959255 : Blo 638302 959255 := bstep (se 1 (by rfl) ⟨719441, by rfl⟩ : syracuseStep 959255 = 1438883) B1438883
theorem B959321 : Blo 638302 959321 := bstep (se 2 (by rfl) ⟨359745, by rfl⟩ : syracuseStep 959321 = 719491) B719491
theorem B11707253 : Blo 638302 11707253 := bstep (se 5 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 11707253 = 1097555) B1097555
theorem B959435 : Blo 638302 959435 := bstep (se 1 (by rfl) ⟨719576, by rfl⟩ : syracuseStep 959435 = 1439153) B1439153
theorem B2433995 : Blo 638302 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B959447 : Blo 638302 959447 := bstep (se 1 (by rfl) ⟨719585, by rfl⟩ : syracuseStep 959447 = 1439171) B1439171
theorem B2597849 : Blo 638302 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B2434009 : Blo 638302 2434009 := bstep (se 2 (by rfl) ⟨912753, by rfl⟩ : syracuseStep 2434009 = 1825507) B1825507
theorem B959513 : Blo 638302 959513 := bstep (se 2 (by rfl) ⟨359817, by rfl⟩ : syracuseStep 959513 = 719635) B719635
theorem B959627 : Blo 638302 959627 := bstep (se 1 (by rfl) ⟨719720, by rfl⟩ : syracuseStep 959627 = 1439441) B1439441
theorem B959639 : Blo 638302 959639 := bstep (se 1 (by rfl) ⟨719729, by rfl⟩ : syracuseStep 959639 = 1439459) B1439459
theorem B959705 : Blo 638302 959705 := bstep (se 2 (by rfl) ⟨359889, by rfl⟩ : syracuseStep 959705 = 719779) B719779
theorem B8299841 : Blo 638302 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B959819 : Blo 638302 959819 := bstep (se 1 (by rfl) ⟨719864, by rfl⟩ : syracuseStep 959819 = 1439729) B1439729
theorem B959831 : Blo 638302 959831 := bstep (se 1 (by rfl) ⟨719873, by rfl⟩ : syracuseStep 959831 = 1439747) B1439747
theorem B959897 : Blo 638302 959897 := bstep (se 2 (by rfl) ⟨359961, by rfl⟩ : syracuseStep 959897 = 719923) B719923
theorem B5481989 : Blo 638302 5481989 := bstep (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) B1027873
theorem B960011 : Blo 638302 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B960023 : Blo 638302 960023 := bstep (se 1 (by rfl) ⟨720017, by rfl⟩ : syracuseStep 960023 = 1440035) B1440035
theorem B1025561 : Blo 638302 1025561 := bstep (se 2 (by rfl) ⟨384585, by rfl⟩ : syracuseStep 1025561 = 769171) B769171
theorem B3647051 : Blo 638302 3647051 := bstep (se 1 (by rfl) ⟨2735288, by rfl⟩ : syracuseStep 3647051 = 5470577) B5470577
theorem B960089 : Blo 638302 960089 := bstep (se 2 (by rfl) ⟨360033, by rfl⟩ : syracuseStep 960089 = 720067) B720067
theorem B960203 : Blo 638302 960203 := bstep (se 1 (by rfl) ⟨720152, by rfl⟩ : syracuseStep 960203 = 1440305) B1440305
theorem B960215 : Blo 638302 960215 := bstep (se 1 (by rfl) ⟨720161, by rfl⟩ : syracuseStep 960215 = 1440323) B1440323
theorem B960281 : Blo 638302 960281 := bstep (se 2 (by rfl) ⟨360105, by rfl⟩ : syracuseStep 960281 = 720211) B720211
theorem B2729821 : Blo 638302 2729821 := bstep (se 3 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 2729821 = 1023683) B1023683
theorem B9348965 : Blo 638302 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B960395 : Blo 638302 960395 := bstep (se 1 (by rfl) ⟨720296, by rfl⟩ : syracuseStep 960395 = 1440593) B1440593
theorem B960407 : Blo 638302 960407 := bstep (se 1 (by rfl) ⟨720305, by rfl⟩ : syracuseStep 960407 = 1440611) B1440611
theorem B2434967 : Blo 638302 2434967 := bstep (se 1 (by rfl) ⟨1826225, by rfl⟩ : syracuseStep 2434967 = 3652451) B3652451
theorem B960473 : Blo 638302 960473 := bstep (se 2 (by rfl) ⟨360177, by rfl⟩ : syracuseStep 960473 = 720355) B720355
theorem B6924305 : Blo 638302 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B2304065 : Blo 638302 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B960587 : Blo 638302 960587 := bstep (se 1 (by rfl) ⟨720440, by rfl⟩ : syracuseStep 960587 = 1440881) B1440881
theorem B960599 : Blo 638302 960599 := bstep (se 1 (by rfl) ⟨720449, by rfl⟩ : syracuseStep 960599 = 1440899) B1440899
theorem B960665 : Blo 638302 960665 := bstep (se 2 (by rfl) ⟨360249, by rfl⟩ : syracuseStep 960665 = 720499) B720499
theorem B5482673 : Blo 638302 5482673 := bstep (se 2 (by rfl) ⟨2056002, by rfl⟩ : syracuseStep 5482673 = 4112005) B4112005
theorem B1616051 : Blo 638302 1616051 := bstep (se 1 (by rfl) ⟨1212038, by rfl⟩ : syracuseStep 1616051 = 2424077) B2424077
theorem B960779 : Blo 638302 960779 := bstep (se 1 (by rfl) ⟨720584, by rfl⟩ : syracuseStep 960779 = 1441169) B1441169
theorem B960791 : Blo 638302 960791 := bstep (se 1 (by rfl) ⟨720593, by rfl⟩ : syracuseStep 960791 = 1441187) B1441187
theorem B960857 : Blo 638302 960857 := bstep (se 2 (by rfl) ⟨360321, by rfl⟩ : syracuseStep 960857 = 720643) B720643
theorem B731575 : Blo 638302 731575 := bstep (se 1 (by rfl) ⟨548681, by rfl⟩ : syracuseStep 731575 = 1097363) B1097363
theorem B960971 : Blo 638302 960971 := bstep (se 1 (by rfl) ⟨720728, by rfl⟩ : syracuseStep 960971 = 1441457) B1441457
theorem B960983 : Blo 638302 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B1616345 : Blo 638302 1616345 := bstep (se 2 (by rfl) ⟨606129, by rfl⟩ : syracuseStep 1616345 = 1212259) B1212259
theorem B961049 : Blo 638302 961049 := bstep (se 2 (by rfl) ⟨360393, by rfl⟩ : syracuseStep 961049 = 720787) B720787
theorem B2468483 : Blo 638302 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B961163 : Blo 638302 961163 := bstep (se 1 (by rfl) ⟨720872, by rfl⟩ : syracuseStep 961163 = 1441745) B1441745
theorem B961175 : Blo 638302 961175 := bstep (se 1 (by rfl) ⟨720881, by rfl⟩ : syracuseStep 961175 = 1441763) B1441763
theorem B961241 : Blo 638302 961241 := bstep (se 2 (by rfl) ⟨360465, by rfl⟩ : syracuseStep 961241 = 720931) B720931
theorem B961355 : Blo 638302 961355 := bstep (se 1 (by rfl) ⟨721016, by rfl⟩ : syracuseStep 961355 = 1442033) B1442033
theorem B961367 : Blo 638302 961367 := bstep (se 1 (by rfl) ⟨721025, by rfl⟩ : syracuseStep 961367 = 1442051) B1442051
theorem B961433 : Blo 638302 961433 := bstep (se 2 (by rfl) ⟨360537, by rfl⟩ : syracuseStep 961433 = 721075) B721075
theorem B961547 : Blo 638302 961547 := bstep (se 1 (by rfl) ⟨721160, by rfl⟩ : syracuseStep 961547 = 1442321) B1442321
theorem B961559 : Blo 638302 961559 := bstep (se 1 (by rfl) ⟨721169, by rfl⟩ : syracuseStep 961559 = 1442339) B1442339
theorem B961625 : Blo 638302 961625 := bstep (se 2 (by rfl) ⟨360609, by rfl⟩ : syracuseStep 961625 = 721219) B721219
theorem B2436227 : Blo 638302 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B2731153 : Blo 638302 2731153 := bstep (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) B2048365
theorem B5483699 : Blo 638302 5483699 := bstep (se 1 (by rfl) ⟨4112774, by rfl⟩ : syracuseStep 5483699 = 8225549) B8225549
theorem B961739 : Blo 638302 961739 := bstep (se 1 (by rfl) ⟨721304, by rfl⟩ : syracuseStep 961739 = 1442609) B1442609
theorem B1387735 : Blo 638302 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B961751 : Blo 638302 961751 := bstep (se 1 (by rfl) ⟨721313, by rfl⟩ : syracuseStep 961751 = 1442627) B1442627
theorem B961817 : Blo 638302 961817 := bstep (se 2 (by rfl) ⟨360681, by rfl⟩ : syracuseStep 961817 = 721363) B721363
theorem B961931 : Blo 638302 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B961943 : Blo 638302 961943 := bstep (se 1 (by rfl) ⟨721457, by rfl⟩ : syracuseStep 961943 = 1442915) B1442915
theorem B962009 : Blo 638302 962009 := bstep (se 2 (by rfl) ⟨360753, by rfl⟩ : syracuseStep 962009 = 721507) B721507
theorem B4861457 : Blo 638302 4861457 := bstep (se 2 (by rfl) ⟨1823046, by rfl⟩ : syracuseStep 4861457 = 3646093) B3646093
theorem B962123 : Blo 638302 962123 := bstep (se 1 (by rfl) ⟨721592, by rfl⟩ : syracuseStep 962123 = 1443185) B1443185
theorem B962135 : Blo 638302 962135 := bstep (se 1 (by rfl) ⟨721601, by rfl⟩ : syracuseStep 962135 = 1443203) B1443203
theorem B962201 : Blo 638302 962201 := bstep (se 2 (by rfl) ⟨360825, by rfl⟩ : syracuseStep 962201 = 721651) B721651
theorem B962315 : Blo 638302 962315 := bstep (se 1 (by rfl) ⟨721736, by rfl⟩ : syracuseStep 962315 = 1443473) B1443473
theorem B962327 : Blo 638302 962327 := bstep (se 1 (by rfl) ⟨721745, by rfl⟩ : syracuseStep 962327 = 1443491) B1443491
theorem B962393 : Blo 638302 962393 := bstep (se 2 (by rfl) ⟨360897, by rfl⟩ : syracuseStep 962393 = 721795) B721795
theorem B13840307 : Blo 638302 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B962507 : Blo 638302 962507 := bstep (se 1 (by rfl) ⟨721880, by rfl⟩ : syracuseStep 962507 = 1443761) B1443761
theorem B962519 : Blo 638302 962519 := bstep (se 1 (by rfl) ⟨721889, by rfl⟩ : syracuseStep 962519 = 1443779) B1443779
theorem B962585 : Blo 638302 962585 := bstep (se 2 (by rfl) ⟨360969, by rfl⟩ : syracuseStep 962585 = 721939) B721939
theorem B10956869 : Blo 638302 10956869 := bstep (se 4 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 10956869 = 2054413) B2054413
theorem B1617995 : Blo 638302 1617995 := bstep (se 1 (by rfl) ⟨1213496, by rfl⟩ : syracuseStep 1617995 = 2426993) B2426993
theorem B2306141 : Blo 638302 2306141 := bstep (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) B864803
theorem B962699 : Blo 638302 962699 := bstep (se 1 (by rfl) ⟨722024, by rfl⟩ : syracuseStep 962699 = 1444049) B1444049
theorem B962711 : Blo 638302 962711 := bstep (se 1 (by rfl) ⟨722033, by rfl⟩ : syracuseStep 962711 = 1444067) B1444067
theorem B962777 : Blo 638302 962777 := bstep (se 2 (by rfl) ⟨361041, by rfl⟩ : syracuseStep 962777 = 722083) B722083
theorem B1945907 : Blo 638302 1945907 := bstep (se 1 (by rfl) ⟨1459430, by rfl⟩ : syracuseStep 1945907 = 2918861) B2918861
theorem B962891 : Blo 638302 962891 := bstep (se 1 (by rfl) ⟨722168, by rfl⟩ : syracuseStep 962891 = 1444337) B1444337
theorem B962903 : Blo 638302 962903 := bstep (se 1 (by rfl) ⟨722177, by rfl⟩ : syracuseStep 962903 = 1444355) B1444355
theorem B962969 : Blo 638302 962969 := bstep (se 2 (by rfl) ⟨361113, by rfl⟩ : syracuseStep 962969 = 722227) B722227
theorem B963083 : Blo 638302 963083 := bstep (se 1 (by rfl) ⟨722312, by rfl⟩ : syracuseStep 963083 = 1444625) B1444625
theorem B963095 : Blo 638302 963095 := bstep (se 1 (by rfl) ⟨722321, by rfl⟩ : syracuseStep 963095 = 1444643) B1444643
theorem B963161 : Blo 638302 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B963275 : Blo 638302 963275 := bstep (se 1 (by rfl) ⟨722456, by rfl⟩ : syracuseStep 963275 = 1444913) B1444913
theorem B963287 : Blo 638302 963287 := bstep (se 1 (by rfl) ⟨722465, by rfl⟩ : syracuseStep 963287 = 1444931) B1444931
theorem B963353 : Blo 638302 963353 := bstep (se 2 (by rfl) ⟨361257, by rfl⟩ : syracuseStep 963353 = 722515) B722515
theorem B2110387 : Blo 638302 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B1618967 : Blo 638302 1618967 := bstep (se 1 (by rfl) ⟨1214225, by rfl⟩ : syracuseStep 1618967 = 2428451) B2428451
theorem B56865827 : Blo 638302 56865827 := bstep (se 1 (by rfl) ⟨42649370, by rfl⟩ : syracuseStep 56865827 = 85298741) B85298741
theorem B21050549 : Blo 638302 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B865495 : Blo 638302 865495 := bstep (se 1 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 865495 = 1298243) B1298243
theorem B865625 : Blo 638302 865625 := bstep (se 2 (by rfl) ⟨324609, by rfl⟩ : syracuseStep 865625 = 649219) B649219
theorem B1619635 : Blo 638302 1619635 := bstep (se 1 (by rfl) ⟨1214726, by rfl⟩ : syracuseStep 1619635 = 2429453) B2429453
theorem B11712205 : Blo 638302 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B1619777 : Blo 638302 1619777 := bstep (se 2 (by rfl) ⟨607416, by rfl⟩ : syracuseStep 1619777 = 1214833) B1214833
theorem B2734145 : Blo 638302 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B2505163 : Blo 638302 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B2603609 : Blo 638302 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B3455581 : Blo 638302 3455581 := bstep (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) B1295843
theorem B1621043 : Blo 638302 1621043 := bstep (se 1 (by rfl) ⟨1215782, by rfl⟩ : syracuseStep 1621043 = 2431565) B2431565
theorem B4865345 : Blo 638302 4865345 := bstep (se 2 (by rfl) ⟨1824504, by rfl⟩ : syracuseStep 4865345 = 3649009) B3649009
theorem B638315 : Blo 638302 638315 := bstep (se 1 (by rfl) ⟨478736, by rfl⟩ : syracuseStep 638315 = 957473) B957473
theorem B638327 : Blo 638302 638327 := bstep (se 1 (by rfl) ⟨478745, by rfl⟩ : syracuseStep 638327 = 957491) B957491
theorem B638347 : Blo 638302 638347 := bstep (se 1 (by rfl) ⟨478760, by rfl⟩ : syracuseStep 638347 = 957521) B957521
theorem B638359 : Blo 638302 638359 := bstep (se 1 (by rfl) ⟨478769, by rfl⟩ : syracuseStep 638359 = 957539) B957539
theorem B638379 : Blo 638302 638379 := bstep (se 1 (by rfl) ⟨478784, by rfl⟩ : syracuseStep 638379 = 957569) B957569
theorem B1818035 : Blo 638302 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B638391 : Blo 638302 638391 := bstep (se 1 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 638391 = 957587) B957587
theorem B638411 : Blo 638302 638411 := bstep (se 1 (by rfl) ⟨478808, by rfl⟩ : syracuseStep 638411 = 957617) B957617
theorem B638423 : Blo 638302 638423 := bstep (se 1 (by rfl) ⟨478817, by rfl⟩ : syracuseStep 638423 = 957635) B957635
theorem B638443 : Blo 638302 638443 := bstep (se 1 (by rfl) ⟨478832, by rfl⟩ : syracuseStep 638443 = 957665) B957665
theorem B638455 : Blo 638302 638455 := bstep (se 1 (by rfl) ⟨478841, by rfl⟩ : syracuseStep 638455 = 957683) B957683
theorem B638475 : Blo 638302 638475 := bstep (se 1 (by rfl) ⟨478856, by rfl⟩ : syracuseStep 638475 = 957713) B957713
theorem B12271121 : Blo 638302 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B638487 : Blo 638302 638487 := bstep (se 1 (by rfl) ⟨478865, by rfl⟩ : syracuseStep 638487 = 957731) B957731
theorem B638507 : Blo 638302 638507 := bstep (se 1 (by rfl) ⟨478880, by rfl⟩ : syracuseStep 638507 = 957761) B957761
theorem B638519 : Blo 638302 638519 := bstep (se 1 (by rfl) ⟨478889, by rfl⟩ : syracuseStep 638519 = 957779) B957779
theorem B638539 : Blo 638302 638539 := bstep (se 1 (by rfl) ⟨478904, by rfl⟩ : syracuseStep 638539 = 957809) B957809
theorem B1621579 : Blo 638302 1621579 := bstep (se 1 (by rfl) ⟨1216184, by rfl⟩ : syracuseStep 1621579 = 2432369) B2432369
theorem B638551 : Blo 638302 638551 := bstep (se 1 (by rfl) ⟨478913, by rfl⟩ : syracuseStep 638551 = 957827) B957827
theorem B638571 : Blo 638302 638571 := bstep (se 1 (by rfl) ⟨478928, by rfl⟩ : syracuseStep 638571 = 957857) B957857
theorem B638583 : Blo 638302 638583 := bstep (se 1 (by rfl) ⟨478937, by rfl⟩ : syracuseStep 638583 = 957875) B957875
theorem B638603 : Blo 638302 638603 := bstep (se 1 (by rfl) ⟨478952, by rfl⟩ : syracuseStep 638603 = 957905) B957905
theorem B1818263 : Blo 638302 1818263 := bstep (se 1 (by rfl) ⟨1363697, by rfl⟩ : syracuseStep 1818263 = 2727395) B2727395
theorem B638615 : Blo 638302 638615 := bstep (se 1 (by rfl) ⟨478961, by rfl⟩ : syracuseStep 638615 = 957923) B957923
theorem B638635 : Blo 638302 638635 := bstep (se 1 (by rfl) ⟨478976, by rfl⟩ : syracuseStep 638635 = 957953) B957953
theorem B638647 : Blo 638302 638647 := bstep (se 1 (by rfl) ⟨478985, by rfl⟩ : syracuseStep 638647 = 957971) B957971
theorem B638667 : Blo 638302 638667 := bstep (se 1 (by rfl) ⟨479000, by rfl⟩ : syracuseStep 638667 = 958001) B958001
theorem B638679 : Blo 638302 638679 := bstep (se 1 (by rfl) ⟨479009, by rfl⟩ : syracuseStep 638679 = 958019) B958019
theorem B1621721 : Blo 638302 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B638699 : Blo 638302 638699 := bstep (se 1 (by rfl) ⟨479024, by rfl⟩ : syracuseStep 638699 = 958049) B958049
theorem B638711 : Blo 638302 638711 := bstep (se 1 (by rfl) ⟨479033, by rfl⟩ : syracuseStep 638711 = 958067) B958067
theorem B638731 : Blo 638302 638731 := bstep (se 1 (by rfl) ⟨479048, by rfl⟩ : syracuseStep 638731 = 958097) B958097
theorem B638743 : Blo 638302 638743 := bstep (se 1 (by rfl) ⟨479057, by rfl⟩ : syracuseStep 638743 = 958115) B958115
theorem B638763 : Blo 638302 638763 := bstep (se 1 (by rfl) ⟨479072, by rfl⟩ : syracuseStep 638763 = 958145) B958145
theorem B638775 : Blo 638302 638775 := bstep (se 1 (by rfl) ⟨479081, by rfl⟩ : syracuseStep 638775 = 958163) B958163
theorem B638795 : Blo 638302 638795 := bstep (se 1 (by rfl) ⟨479096, by rfl⟩ : syracuseStep 638795 = 958193) B958193
theorem B638807 : Blo 638302 638807 := bstep (se 1 (by rfl) ⟨479105, by rfl⟩ : syracuseStep 638807 = 958211) B958211
theorem B638827 : Blo 638302 638827 := bstep (se 1 (by rfl) ⟨479120, by rfl⟩ : syracuseStep 638827 = 958241) B958241
theorem B638839 : Blo 638302 638839 := bstep (se 1 (by rfl) ⟨479129, by rfl⟩ : syracuseStep 638839 = 958259) B958259
theorem B638859 : Blo 638302 638859 := bstep (se 1 (by rfl) ⟨479144, by rfl⟩ : syracuseStep 638859 = 958289) B958289
theorem B638871 : Blo 638302 638871 := bstep (se 1 (by rfl) ⟨479153, by rfl⟩ : syracuseStep 638871 = 958307) B958307
theorem B638891 : Blo 638302 638891 := bstep (se 1 (by rfl) ⟨479168, by rfl⟩ : syracuseStep 638891 = 958337) B958337
theorem B638903 : Blo 638302 638903 := bstep (se 1 (by rfl) ⟨479177, by rfl⟩ : syracuseStep 638903 = 958355) B958355
theorem B2768833 : Blo 638302 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B1818571 : Blo 638302 1818571 := bstep (se 1 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 1818571 = 2727857) B2727857
theorem B638923 : Blo 638302 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B638935 : Blo 638302 638935 := bstep (se 1 (by rfl) ⟨479201, by rfl⟩ : syracuseStep 638935 = 958403) B958403
theorem B638955 : Blo 638302 638955 := bstep (se 1 (by rfl) ⟨479216, by rfl⟩ : syracuseStep 638955 = 958433) B958433
theorem B638967 : Blo 638302 638967 := bstep (se 1 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 638967 = 958451) B958451
theorem B638987 : Blo 638302 638987 := bstep (se 1 (by rfl) ⟨479240, by rfl⟩ : syracuseStep 638987 = 958481) B958481
theorem B638999 : Blo 638302 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B639019 : Blo 638302 639019 := bstep (se 1 (by rfl) ⟨479264, by rfl⟩ : syracuseStep 639019 = 958529) B958529
theorem B639031 : Blo 638302 639031 := bstep (se 1 (by rfl) ⟨479273, by rfl⟩ : syracuseStep 639031 = 958547) B958547
theorem B639051 : Blo 638302 639051 := bstep (se 1 (by rfl) ⟨479288, by rfl⟩ : syracuseStep 639051 = 958577) B958577
theorem B639063 : Blo 638302 639063 := bstep (se 1 (by rfl) ⟨479297, by rfl⟩ : syracuseStep 639063 = 958595) B958595
theorem B639083 : Blo 638302 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B639095 : Blo 638302 639095 := bstep (se 1 (by rfl) ⟨479321, by rfl⟩ : syracuseStep 639095 = 958643) B958643
theorem B639115 : Blo 638302 639115 := bstep (se 1 (by rfl) ⟨479336, by rfl⟩ : syracuseStep 639115 = 958673) B958673
theorem B639127 : Blo 638302 639127 := bstep (se 1 (by rfl) ⟨479345, by rfl⟩ : syracuseStep 639127 = 958691) B958691
theorem B639147 : Blo 638302 639147 := bstep (se 1 (by rfl) ⟨479360, by rfl⟩ : syracuseStep 639147 = 958721) B958721
theorem B639159 : Blo 638302 639159 := bstep (se 1 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 639159 = 958739) B958739
theorem B639179 : Blo 638302 639179 := bstep (se 1 (by rfl) ⟨479384, by rfl⟩ : syracuseStep 639179 = 958769) B958769
theorem B639191 : Blo 638302 639191 := bstep (se 1 (by rfl) ⟨479393, by rfl⟩ : syracuseStep 639191 = 958787) B958787
theorem B1818845 : Blo 638302 1818845 := bstep (se 3 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 1818845 = 682067) B682067
theorem B639211 : Blo 638302 639211 := bstep (se 1 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 639211 = 958817) B958817
theorem B639223 : Blo 638302 639223 := bstep (se 1 (by rfl) ⟨479417, by rfl⟩ : syracuseStep 639223 = 958835) B958835
theorem B639243 : Blo 638302 639243 := bstep (se 1 (by rfl) ⟨479432, by rfl⟩ : syracuseStep 639243 = 958865) B958865
theorem B1458443 : Blo 638302 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B639255 : Blo 638302 639255 := bstep (se 1 (by rfl) ⟨479441, by rfl⟩ : syracuseStep 639255 = 958883) B958883
theorem B639275 : Blo 638302 639275 := bstep (se 1 (by rfl) ⟨479456, by rfl⟩ : syracuseStep 639275 = 958913) B958913
theorem B639287 : Blo 638302 639287 := bstep (se 1 (by rfl) ⟨479465, by rfl⟩ : syracuseStep 639287 = 958931) B958931
theorem B639307 : Blo 638302 639307 := bstep (se 1 (by rfl) ⟨479480, by rfl⟩ : syracuseStep 639307 = 958961) B958961
theorem B639319 : Blo 638302 639319 := bstep (se 1 (by rfl) ⟨479489, by rfl⟩ : syracuseStep 639319 = 958979) B958979
theorem B639339 : Blo 638302 639339 := bstep (se 1 (by rfl) ⟨479504, by rfl⟩ : syracuseStep 639339 = 959009) B959009
theorem B639351 : Blo 638302 639351 := bstep (se 1 (by rfl) ⟨479513, by rfl⟩ : syracuseStep 639351 = 959027) B959027
theorem B639371 : Blo 638302 639371 := bstep (se 1 (by rfl) ⟨479528, by rfl⟩ : syracuseStep 639371 = 959057) B959057
theorem B639383 : Blo 638302 639383 := bstep (se 1 (by rfl) ⟨479537, by rfl⟩ : syracuseStep 639383 = 959075) B959075
theorem B639403 : Blo 638302 639403 := bstep (se 1 (by rfl) ⟨479552, by rfl⟩ : syracuseStep 639403 = 959105) B959105
theorem B639415 : Blo 638302 639415 := bstep (se 1 (by rfl) ⟨479561, by rfl⟩ : syracuseStep 639415 = 959123) B959123
theorem B639435 : Blo 638302 639435 := bstep (se 1 (by rfl) ⟨479576, by rfl⟩ : syracuseStep 639435 = 959153) B959153
theorem B639447 : Blo 638302 639447 := bstep (se 1 (by rfl) ⟨479585, by rfl⟩ : syracuseStep 639447 = 959171) B959171
theorem B2736605 : Blo 638302 2736605 := bstep (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) B1026227
theorem B639467 : Blo 638302 639467 := bstep (se 1 (by rfl) ⟨479600, by rfl⟩ : syracuseStep 639467 = 959201) B959201
theorem B639479 : Blo 638302 639479 := bstep (se 1 (by rfl) ⟨479609, by rfl⟩ : syracuseStep 639479 = 959219) B959219
theorem B639499 : Blo 638302 639499 := bstep (se 1 (by rfl) ⟨479624, by rfl⟩ : syracuseStep 639499 = 959249) B959249
theorem B639511 : Blo 638302 639511 := bstep (se 1 (by rfl) ⟨479633, by rfl⟩ : syracuseStep 639511 = 959267) B959267
theorem B1622551 : Blo 638302 1622551 := bstep (se 1 (by rfl) ⟨1216913, by rfl⟩ : syracuseStep 1622551 = 2433827) B2433827
theorem B639531 : Blo 638302 639531 := bstep (se 1 (by rfl) ⟨479648, by rfl⟩ : syracuseStep 639531 = 959297) B959297
theorem B5456429 : Blo 638302 5456429 := bstep (se 3 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 5456429 = 2046161) B2046161
theorem B639543 : Blo 638302 639543 := bstep (se 1 (by rfl) ⟨479657, by rfl⟩ : syracuseStep 639543 = 959315) B959315
theorem B639563 : Blo 638302 639563 := bstep (se 1 (by rfl) ⟨479672, by rfl⟩ : syracuseStep 639563 = 959345) B959345
theorem B639575 : Blo 638302 639575 := bstep (se 1 (by rfl) ⟨479681, by rfl⟩ : syracuseStep 639575 = 959363) B959363
theorem B3457637 : Blo 638302 3457637 := bstep (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) B648307
theorem B639595 : Blo 638302 639595 := bstep (se 1 (by rfl) ⟨479696, by rfl⟩ : syracuseStep 639595 = 959393) B959393
theorem B639607 : Blo 638302 639607 := bstep (se 1 (by rfl) ⟨479705, by rfl⟩ : syracuseStep 639607 = 959411) B959411
theorem B639627 : Blo 638302 639627 := bstep (se 1 (by rfl) ⟨479720, by rfl⟩ : syracuseStep 639627 = 959441) B959441
theorem B639639 : Blo 638302 639639 := bstep (se 1 (by rfl) ⟨479729, by rfl⟩ : syracuseStep 639639 = 959459) B959459
theorem B639659 : Blo 638302 639659 := bstep (se 1 (by rfl) ⟨479744, by rfl⟩ : syracuseStep 639659 = 959489) B959489
theorem B639671 : Blo 638302 639671 := bstep (se 1 (by rfl) ⟨479753, by rfl⟩ : syracuseStep 639671 = 959507) B959507
theorem B639691 : Blo 638302 639691 := bstep (se 1 (by rfl) ⟨479768, by rfl⟩ : syracuseStep 639691 = 959537) B959537
theorem B639703 : Blo 638302 639703 := bstep (se 1 (by rfl) ⟨479777, by rfl⟩ : syracuseStep 639703 = 959555) B959555
theorem B639723 : Blo 638302 639723 := bstep (se 1 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 639723 = 959585) B959585
theorem B639735 : Blo 638302 639735 := bstep (se 1 (by rfl) ⟨479801, by rfl⟩ : syracuseStep 639735 = 959603) B959603
theorem B639755 : Blo 638302 639755 := bstep (se 1 (by rfl) ⟨479816, by rfl⟩ : syracuseStep 639755 = 959633) B959633
theorem B639767 : Blo 638302 639767 := bstep (se 1 (by rfl) ⟨479825, by rfl⟩ : syracuseStep 639767 = 959651) B959651
theorem B1295129 : Blo 638302 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B639787 : Blo 638302 639787 := bstep (se 1 (by rfl) ⟨479840, by rfl⟩ : syracuseStep 639787 = 959681) B959681
theorem B639799 : Blo 638302 639799 := bstep (se 1 (by rfl) ⟨479849, by rfl⟩ : syracuseStep 639799 = 959699) B959699
theorem B13812545 : Blo 638302 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B639819 : Blo 638302 639819 := bstep (se 1 (by rfl) ⟨479864, by rfl⟩ : syracuseStep 639819 = 959729) B959729
theorem B639831 : Blo 638302 639831 := bstep (se 1 (by rfl) ⟨479873, by rfl⟩ : syracuseStep 639831 = 959747) B959747
theorem B1000279 : Blo 638302 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B639851 : Blo 638302 639851 := bstep (se 1 (by rfl) ⟨479888, by rfl⟩ : syracuseStep 639851 = 959777) B959777
theorem B639863 : Blo 638302 639863 := bstep (se 1 (by rfl) ⟨479897, by rfl⟩ : syracuseStep 639863 = 959795) B959795
theorem B639883 : Blo 638302 639883 := bstep (se 1 (by rfl) ⟨479912, by rfl⟩ : syracuseStep 639883 = 959825) B959825
theorem B639895 : Blo 638302 639895 := bstep (se 1 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 639895 = 959843) B959843
theorem B1098649 : Blo 638302 1098649 := bstep (se 2 (by rfl) ⟨411993, by rfl⟩ : syracuseStep 1098649 = 823987) B823987
theorem B639915 : Blo 638302 639915 := bstep (se 1 (by rfl) ⟨479936, by rfl⟩ : syracuseStep 639915 = 959873) B959873
theorem B8111027 : Blo 638302 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B639927 : Blo 638302 639927 := bstep (se 1 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 639927 = 959891) B959891
theorem B639947 : Blo 638302 639947 := bstep (se 1 (by rfl) ⟨479960, by rfl⟩ : syracuseStep 639947 = 959921) B959921
theorem B1622987 : Blo 638302 1622987 := bstep (se 1 (by rfl) ⟨1217240, by rfl⟩ : syracuseStep 1622987 = 2434481) B2434481
theorem B639959 : Blo 638302 639959 := bstep (se 1 (by rfl) ⟨479969, by rfl⟩ : syracuseStep 639959 = 959939) B959939
theorem B639979 : Blo 638302 639979 := bstep (se 1 (by rfl) ⟨479984, by rfl⟩ : syracuseStep 639979 = 959969) B959969
theorem B639991 : Blo 638302 639991 := bstep (se 1 (by rfl) ⟨479993, by rfl⟩ : syracuseStep 639991 = 959987) B959987
theorem B640011 : Blo 638302 640011 := bstep (se 1 (by rfl) ⟨480008, by rfl⟩ : syracuseStep 640011 = 960017) B960017
theorem B640023 : Blo 638302 640023 := bstep (se 1 (by rfl) ⟨480017, by rfl⟩ : syracuseStep 640023 = 960035) B960035
theorem B640043 : Blo 638302 640043 := bstep (se 1 (by rfl) ⟨480032, by rfl⟩ : syracuseStep 640043 = 960065) B960065
theorem B640055 : Blo 638302 640055 := bstep (se 1 (by rfl) ⟨480041, by rfl⟩ : syracuseStep 640055 = 960083) B960083
theorem B640075 : Blo 638302 640075 := bstep (se 1 (by rfl) ⟨480056, by rfl⟩ : syracuseStep 640075 = 960113) B960113
theorem B640087 : Blo 638302 640087 := bstep (se 1 (by rfl) ⟨480065, by rfl⟩ : syracuseStep 640087 = 960131) B960131
theorem B640107 : Blo 638302 640107 := bstep (se 1 (by rfl) ⟨480080, by rfl⟩ : syracuseStep 640107 = 960161) B960161
theorem B640119 : Blo 638302 640119 := bstep (se 1 (by rfl) ⟨480089, by rfl⟩ : syracuseStep 640119 = 960179) B960179
theorem B640139 : Blo 638302 640139 := bstep (se 1 (by rfl) ⟨480104, by rfl⟩ : syracuseStep 640139 = 960209) B960209
theorem B640151 : Blo 638302 640151 := bstep (se 1 (by rfl) ⟨480113, by rfl⟩ : syracuseStep 640151 = 960227) B960227
theorem B771223 : Blo 638302 771223 := bstep (se 1 (by rfl) ⟨578417, by rfl⟩ : syracuseStep 771223 = 1156835) B1156835
theorem B640171 : Blo 638302 640171 := bstep (se 1 (by rfl) ⟨480128, by rfl⟩ : syracuseStep 640171 = 960257) B960257
theorem B640183 : Blo 638302 640183 := bstep (se 1 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 640183 = 960275) B960275
theorem B640203 : Blo 638302 640203 := bstep (se 1 (by rfl) ⟨480152, by rfl⟩ : syracuseStep 640203 = 960305) B960305
theorem B640215 : Blo 638302 640215 := bstep (se 1 (by rfl) ⟨480161, by rfl⟩ : syracuseStep 640215 = 960323) B960323
theorem B4867289 : Blo 638302 4867289 := bstep (se 2 (by rfl) ⟨1825233, by rfl⟩ : syracuseStep 4867289 = 3650467) B3650467
theorem B640235 : Blo 638302 640235 := bstep (se 1 (by rfl) ⟨480176, by rfl⟩ : syracuseStep 640235 = 960353) B960353
theorem B640247 : Blo 638302 640247 := bstep (se 1 (by rfl) ⟨480185, by rfl⟩ : syracuseStep 640247 = 960371) B960371
theorem B640267 : Blo 638302 640267 := bstep (se 1 (by rfl) ⟨480200, by rfl⟩ : syracuseStep 640267 = 960401) B960401
theorem B640279 : Blo 638302 640279 := bstep (se 1 (by rfl) ⟨480209, by rfl⟩ : syracuseStep 640279 = 960419) B960419
theorem B640299 : Blo 638302 640299 := bstep (se 1 (by rfl) ⟨480224, by rfl⟩ : syracuseStep 640299 = 960449) B960449
theorem B640311 : Blo 638302 640311 := bstep (se 1 (by rfl) ⟨480233, by rfl⟩ : syracuseStep 640311 = 960467) B960467
theorem B1623361 : Blo 638302 1623361 := bstep (se 2 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 1623361 = 1217521) B1217521
theorem B1230155 : Blo 638302 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B640331 : Blo 638302 640331 := bstep (se 1 (by rfl) ⟨480248, by rfl⟩ : syracuseStep 640331 = 960497) B960497
theorem B640343 : Blo 638302 640343 := bstep (se 1 (by rfl) ⟨480257, by rfl⟩ : syracuseStep 640343 = 960515) B960515
theorem B640363 : Blo 638302 640363 := bstep (se 1 (by rfl) ⟨480272, by rfl⟩ : syracuseStep 640363 = 960545) B960545
theorem B640375 : Blo 638302 640375 := bstep (se 1 (by rfl) ⟨480281, by rfl⟩ : syracuseStep 640375 = 960563) B960563
theorem B640395 : Blo 638302 640395 := bstep (se 1 (by rfl) ⟨480296, by rfl⟩ : syracuseStep 640395 = 960593) B960593
theorem B640407 : Blo 638302 640407 := bstep (se 1 (by rfl) ⟨480305, by rfl⟩ : syracuseStep 640407 = 960611) B960611
theorem B640427 : Blo 638302 640427 := bstep (se 1 (by rfl) ⟨480320, by rfl⟩ : syracuseStep 640427 = 960641) B960641
theorem B640439 : Blo 638302 640439 := bstep (se 1 (by rfl) ⟨480329, by rfl⟩ : syracuseStep 640439 = 960659) B960659
theorem B640459 : Blo 638302 640459 := bstep (se 1 (by rfl) ⟨480344, by rfl⟩ : syracuseStep 640459 = 960689) B960689
theorem B640471 : Blo 638302 640471 := bstep (se 1 (by rfl) ⟨480353, by rfl⟩ : syracuseStep 640471 = 960707) B960707
theorem B640491 : Blo 638302 640491 := bstep (se 1 (by rfl) ⟨480368, by rfl⟩ : syracuseStep 640491 = 960737) B960737
theorem B640503 : Blo 638302 640503 := bstep (se 1 (by rfl) ⟨480377, by rfl⟩ : syracuseStep 640503 = 960755) B960755
theorem B640523 : Blo 638302 640523 := bstep (se 1 (by rfl) ⟨480392, by rfl⟩ : syracuseStep 640523 = 960785) B960785
theorem B640535 : Blo 638302 640535 := bstep (se 1 (by rfl) ⟨480401, by rfl⟩ : syracuseStep 640535 = 960803) B960803
theorem B771607 : Blo 638302 771607 := bstep (se 1 (by rfl) ⟨578705, by rfl⟩ : syracuseStep 771607 = 1157411) B1157411
theorem B640555 : Blo 638302 640555 := bstep (se 1 (by rfl) ⟨480416, by rfl⟩ : syracuseStep 640555 = 960833) B960833
theorem B640567 : Blo 638302 640567 := bstep (se 1 (by rfl) ⟨480425, by rfl⟩ : syracuseStep 640567 = 960851) B960851
theorem B640587 : Blo 638302 640587 := bstep (se 1 (by rfl) ⟨480440, by rfl⟩ : syracuseStep 640587 = 960881) B960881
theorem B640599 : Blo 638302 640599 := bstep (se 1 (by rfl) ⟨480449, by rfl⟩ : syracuseStep 640599 = 960899) B960899
theorem B640619 : Blo 638302 640619 := bstep (se 1 (by rfl) ⟨480464, by rfl⟩ : syracuseStep 640619 = 960929) B960929
theorem B640631 : Blo 638302 640631 := bstep (se 1 (by rfl) ⟨480473, by rfl⟩ : syracuseStep 640631 = 960947) B960947
theorem B640651 : Blo 638302 640651 := bstep (se 1 (by rfl) ⟨480488, by rfl⟩ : syracuseStep 640651 = 960977) B960977
theorem B640663 : Blo 638302 640663 := bstep (se 1 (by rfl) ⟨480497, by rfl⟩ : syracuseStep 640663 = 960995) B960995
theorem B640683 : Blo 638302 640683 := bstep (se 1 (by rfl) ⟨480512, by rfl⟩ : syracuseStep 640683 = 961025) B961025
theorem B640695 : Blo 638302 640695 := bstep (se 1 (by rfl) ⟨480521, by rfl⟩ : syracuseStep 640695 = 961043) B961043
theorem B640715 : Blo 638302 640715 := bstep (se 1 (by rfl) ⟨480536, by rfl⟩ : syracuseStep 640715 = 961073) B961073
theorem B640727 : Blo 638302 640727 := bstep (se 1 (by rfl) ⟨480545, by rfl⟩ : syracuseStep 640727 = 961091) B961091
theorem B640747 : Blo 638302 640747 := bstep (se 1 (by rfl) ⟨480560, by rfl⟩ : syracuseStep 640747 = 961121) B961121
theorem B640759 : Blo 638302 640759 := bstep (se 1 (by rfl) ⟨480569, by rfl⟩ : syracuseStep 640759 = 961139) B961139
theorem B640779 : Blo 638302 640779 := bstep (se 1 (by rfl) ⟨480584, by rfl⟩ : syracuseStep 640779 = 961169) B961169
theorem B640791 : Blo 638302 640791 := bstep (se 1 (by rfl) ⟨480593, by rfl⟩ : syracuseStep 640791 = 961187) B961187
theorem B640811 : Blo 638302 640811 := bstep (se 1 (by rfl) ⟨480608, by rfl⟩ : syracuseStep 640811 = 961217) B961217
theorem B640823 : Blo 638302 640823 := bstep (se 1 (by rfl) ⟨480617, by rfl⟩ : syracuseStep 640823 = 961235) B961235
theorem B640843 : Blo 638302 640843 := bstep (se 1 (by rfl) ⟨480632, by rfl⟩ : syracuseStep 640843 = 961265) B961265
theorem B640855 : Blo 638302 640855 := bstep (se 1 (by rfl) ⟨480641, by rfl⟩ : syracuseStep 640855 = 961283) B961283
theorem B640875 : Blo 638302 640875 := bstep (se 1 (by rfl) ⟨480656, by rfl⟩ : syracuseStep 640875 = 961313) B961313
theorem B640887 : Blo 638302 640887 := bstep (se 1 (by rfl) ⟨480665, by rfl⟩ : syracuseStep 640887 = 961331) B961331
theorem B640907 : Blo 638302 640907 := bstep (se 1 (by rfl) ⟨480680, by rfl⟩ : syracuseStep 640907 = 961361) B961361
theorem B2312081 : Blo 638302 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B640919 : Blo 638302 640919 := bstep (se 1 (by rfl) ⟨480689, by rfl⟩ : syracuseStep 640919 = 961379) B961379
theorem B1623959 : Blo 638302 1623959 := bstep (se 1 (by rfl) ⟨1217969, by rfl⟩ : syracuseStep 1623959 = 2435939) B2435939
theorem B640939 : Blo 638302 640939 := bstep (se 1 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 640939 = 961409) B961409
theorem B640951 : Blo 638302 640951 := bstep (se 1 (by rfl) ⟨480713, by rfl⟩ : syracuseStep 640951 = 961427) B961427
theorem B640971 : Blo 638302 640971 := bstep (se 1 (by rfl) ⟨480728, by rfl⟩ : syracuseStep 640971 = 961457) B961457
theorem B640983 : Blo 638302 640983 := bstep (se 1 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 640983 = 961475) B961475
theorem B4376537 : Blo 638302 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B641003 : Blo 638302 641003 := bstep (se 1 (by rfl) ⟨480752, by rfl⟩ : syracuseStep 641003 = 961505) B961505
theorem B641015 : Blo 638302 641015 := bstep (se 1 (by rfl) ⟨480761, by rfl⟩ : syracuseStep 641015 = 961523) B961523
theorem B641035 : Blo 638302 641035 := bstep (se 1 (by rfl) ⟨480776, by rfl⟩ : syracuseStep 641035 = 961553) B961553
theorem B641047 : Blo 638302 641047 := bstep (se 1 (by rfl) ⟨480785, by rfl⟩ : syracuseStep 641047 = 961571) B961571
theorem B641067 : Blo 638302 641067 := bstep (se 1 (by rfl) ⟨480800, by rfl⟩ : syracuseStep 641067 = 961601) B961601
theorem B641079 : Blo 638302 641079 := bstep (se 1 (by rfl) ⟨480809, by rfl⟩ : syracuseStep 641079 = 961619) B961619
theorem B641099 : Blo 638302 641099 := bstep (se 1 (by rfl) ⟨480824, by rfl⟩ : syracuseStep 641099 = 961649) B961649
theorem B641111 : Blo 638302 641111 := bstep (se 1 (by rfl) ⟨480833, by rfl⟩ : syracuseStep 641111 = 961667) B961667
theorem B641131 : Blo 638302 641131 := bstep (se 1 (by rfl) ⟨480848, by rfl⟩ : syracuseStep 641131 = 961697) B961697
theorem B641143 : Blo 638302 641143 := bstep (se 1 (by rfl) ⟨480857, by rfl⟩ : syracuseStep 641143 = 961715) B961715
theorem B641163 : Blo 638302 641163 := bstep (se 1 (by rfl) ⟨480872, by rfl⟩ : syracuseStep 641163 = 961745) B961745
theorem B641175 : Blo 638302 641175 := bstep (se 1 (by rfl) ⟨480881, by rfl⟩ : syracuseStep 641175 = 961763) B961763
theorem B641195 : Blo 638302 641195 := bstep (se 1 (by rfl) ⟨480896, by rfl⟩ : syracuseStep 641195 = 961793) B961793
theorem B641207 : Blo 638302 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B641227 : Blo 638302 641227 := bstep (se 1 (by rfl) ⟨480920, by rfl⟩ : syracuseStep 641227 = 961841) B961841
theorem B641239 : Blo 638302 641239 := bstep (se 1 (by rfl) ⟨480929, by rfl⟩ : syracuseStep 641239 = 961859) B961859
theorem B641259 : Blo 638302 641259 := bstep (se 1 (by rfl) ⟨480944, by rfl⟩ : syracuseStep 641259 = 961889) B961889
theorem B641271 : Blo 638302 641271 := bstep (se 1 (by rfl) ⟨480953, by rfl⟩ : syracuseStep 641271 = 961907) B961907
theorem B641291 : Blo 638302 641291 := bstep (se 1 (by rfl) ⟨480968, by rfl⟩ : syracuseStep 641291 = 961937) B961937
theorem B1820951 : Blo 638302 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B641303 : Blo 638302 641303 := bstep (se 1 (by rfl) ⟨480977, by rfl⟩ : syracuseStep 641303 = 961955) B961955
theorem B641323 : Blo 638302 641323 := bstep (se 1 (by rfl) ⟨480992, by rfl⟩ : syracuseStep 641323 = 961985) B961985
theorem B641335 : Blo 638302 641335 := bstep (se 1 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 641335 = 962003) B962003
theorem B641355 : Blo 638302 641355 := bstep (se 1 (by rfl) ⟨481016, by rfl⟩ : syracuseStep 641355 = 962033) B962033
theorem B641367 : Blo 638302 641367 := bstep (se 1 (by rfl) ⟨481025, by rfl⟩ : syracuseStep 641367 = 962051) B962051
theorem B641387 : Blo 638302 641387 := bstep (se 1 (by rfl) ⟨481040, by rfl⟩ : syracuseStep 641387 = 962081) B962081
theorem B641399 : Blo 638302 641399 := bstep (se 1 (by rfl) ⟨481049, by rfl⟩ : syracuseStep 641399 = 962099) B962099
theorem B641419 : Blo 638302 641419 := bstep (se 1 (by rfl) ⟨481064, by rfl⟩ : syracuseStep 641419 = 962129) B962129
theorem B641431 : Blo 638302 641431 := bstep (se 1 (by rfl) ⟨481073, by rfl⟩ : syracuseStep 641431 = 962147) B962147
theorem B2312599 : Blo 638302 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B641451 : Blo 638302 641451 := bstep (se 1 (by rfl) ⟨481088, by rfl⟩ : syracuseStep 641451 = 962177) B962177
theorem B641463 : Blo 638302 641463 := bstep (se 1 (by rfl) ⟨481097, by rfl⟩ : syracuseStep 641463 = 962195) B962195
theorem B641483 : Blo 638302 641483 := bstep (se 1 (by rfl) ⟨481112, by rfl⟩ : syracuseStep 641483 = 962225) B962225
theorem B641495 : Blo 638302 641495 := bstep (se 1 (by rfl) ⟨481121, by rfl⟩ : syracuseStep 641495 = 962243) B962243
theorem B641515 : Blo 638302 641515 := bstep (se 1 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 641515 = 962273) B962273
theorem B641527 : Blo 638302 641527 := bstep (se 1 (by rfl) ⟨481145, by rfl⟩ : syracuseStep 641527 = 962291) B962291
theorem B641547 : Blo 638302 641547 := bstep (se 1 (by rfl) ⟨481160, by rfl⟩ : syracuseStep 641547 = 962321) B962321
theorem B641559 : Blo 638302 641559 := bstep (se 1 (by rfl) ⟨481169, by rfl⟩ : syracuseStep 641559 = 962339) B962339
theorem B641579 : Blo 638302 641579 := bstep (se 1 (by rfl) ⟨481184, by rfl⟩ : syracuseStep 641579 = 962369) B962369
theorem B641591 : Blo 638302 641591 := bstep (se 1 (by rfl) ⟨481193, by rfl⟩ : syracuseStep 641591 = 962387) B962387
theorem B641611 : Blo 638302 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B641623 : Blo 638302 641623 := bstep (se 1 (by rfl) ⟨481217, by rfl⟩ : syracuseStep 641623 = 962435) B962435
theorem B641643 : Blo 638302 641643 := bstep (se 1 (by rfl) ⟨481232, by rfl⟩ : syracuseStep 641643 = 962465) B962465
theorem B641655 : Blo 638302 641655 := bstep (se 1 (by rfl) ⟨481241, by rfl⟩ : syracuseStep 641655 = 962483) B962483
theorem B641675 : Blo 638302 641675 := bstep (se 1 (by rfl) ⟨481256, by rfl⟩ : syracuseStep 641675 = 962513) B962513
theorem B641687 : Blo 638302 641687 := bstep (se 1 (by rfl) ⟨481265, by rfl⟩ : syracuseStep 641687 = 962531) B962531
theorem B641707 : Blo 638302 641707 := bstep (se 1 (by rfl) ⟨481280, by rfl⟩ : syracuseStep 641707 = 962561) B962561
theorem B641719 : Blo 638302 641719 := bstep (se 1 (by rfl) ⟨481289, by rfl⟩ : syracuseStep 641719 = 962579) B962579
theorem B1624769 : Blo 638302 1624769 := bstep (se 2 (by rfl) ⟨609288, by rfl⟩ : syracuseStep 1624769 = 1218577) B1218577
theorem B641739 : Blo 638302 641739 := bstep (se 1 (by rfl) ⟨481304, by rfl⟩ : syracuseStep 641739 = 962609) B962609
theorem B641751 : Blo 638302 641751 := bstep (se 1 (by rfl) ⟨481313, by rfl⟩ : syracuseStep 641751 = 962627) B962627
theorem B641771 : Blo 638302 641771 := bstep (se 1 (by rfl) ⟨481328, by rfl⟩ : syracuseStep 641771 = 962657) B962657
theorem B641783 : Blo 638302 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B641803 : Blo 638302 641803 := bstep (se 1 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 641803 = 962705) B962705
theorem B2771729 : Blo 638302 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B2804503 : Blo 638302 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B641815 : Blo 638302 641815 := bstep (se 1 (by rfl) ⟨481361, by rfl⟩ : syracuseStep 641815 = 962723) B962723
theorem B641835 : Blo 638302 641835 := bstep (se 1 (by rfl) ⟨481376, by rfl⟩ : syracuseStep 641835 = 962753) B962753
theorem B641847 : Blo 638302 641847 := bstep (se 1 (by rfl) ⟨481385, by rfl⟩ : syracuseStep 641847 = 962771) B962771
theorem B641867 : Blo 638302 641867 := bstep (se 1 (by rfl) ⟨481400, by rfl⟩ : syracuseStep 641867 = 962801) B962801
theorem B641879 : Blo 638302 641879 := bstep (se 1 (by rfl) ⟨481409, by rfl⟩ : syracuseStep 641879 = 962819) B962819
theorem B2313049 : Blo 638302 2313049 := bstep (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) B1734787
theorem B641899 : Blo 638302 641899 := bstep (se 1 (by rfl) ⟨481424, by rfl⟩ : syracuseStep 641899 = 962849) B962849
theorem B1461107 : Blo 638302 1461107 := bstep (se 1 (by rfl) ⟨1095830, by rfl⟩ : syracuseStep 1461107 = 2191661) B2191661
theorem B641911 : Blo 638302 641911 := bstep (se 1 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 641911 = 962867) B962867
theorem B641931 : Blo 638302 641931 := bstep (se 1 (by rfl) ⟨481448, by rfl⟩ : syracuseStep 641931 = 962897) B962897
theorem B641943 : Blo 638302 641943 := bstep (se 1 (by rfl) ⟨481457, by rfl⟩ : syracuseStep 641943 = 962915) B962915
theorem B641963 : Blo 638302 641963 := bstep (se 1 (by rfl) ⟨481472, by rfl⟩ : syracuseStep 641963 = 962945) B962945
theorem B641975 : Blo 638302 641975 := bstep (se 1 (by rfl) ⟨481481, by rfl⟩ : syracuseStep 641975 = 962963) B962963
theorem B641995 : Blo 638302 641995 := bstep (se 1 (by rfl) ⟨481496, by rfl⟩ : syracuseStep 641995 = 962993) B962993
theorem B642007 : Blo 638302 642007 := bstep (se 1 (by rfl) ⟨481505, by rfl⟩ : syracuseStep 642007 = 963011) B963011
theorem B642027 : Blo 638302 642027 := bstep (se 1 (by rfl) ⟨481520, by rfl⟩ : syracuseStep 642027 = 963041) B963041
theorem B642039 : Blo 638302 642039 := bstep (se 1 (by rfl) ⟨481529, by rfl⟩ : syracuseStep 642039 = 963059) B963059
theorem B2739203 : Blo 638302 2739203 := bstep (se 1 (by rfl) ⟨2054402, by rfl⟩ : syracuseStep 2739203 = 4108805) B4108805
theorem B642059 : Blo 638302 642059 := bstep (se 1 (by rfl) ⟨481544, by rfl⟩ : syracuseStep 642059 = 963089) B963089
theorem B642071 : Blo 638302 642071 := bstep (se 1 (by rfl) ⟨481553, by rfl⟩ : syracuseStep 642071 = 963107) B963107
theorem B1297433 : Blo 638302 1297433 := bstep (se 2 (by rfl) ⟨486537, by rfl⟩ : syracuseStep 1297433 = 973075) B973075
theorem B642091 : Blo 638302 642091 := bstep (se 1 (by rfl) ⟨481568, by rfl⟩ : syracuseStep 642091 = 963137) B963137
theorem B642103 : Blo 638302 642103 := bstep (se 1 (by rfl) ⟨481577, by rfl⟩ : syracuseStep 642103 = 963155) B963155
theorem B1821761 : Blo 638302 1821761 := bstep (se 2 (by rfl) ⟨683160, by rfl⟩ : syracuseStep 1821761 = 1366321) B1366321
theorem B642123 : Blo 638302 642123 := bstep (se 1 (by rfl) ⟨481592, by rfl⟩ : syracuseStep 642123 = 963185) B963185
theorem B642135 : Blo 638302 642135 := bstep (se 1 (by rfl) ⟨481601, by rfl⟩ : syracuseStep 642135 = 963203) B963203
theorem B642155 : Blo 638302 642155 := bstep (se 1 (by rfl) ⟨481616, by rfl⟩ : syracuseStep 642155 = 963233) B963233
theorem B642167 : Blo 638302 642167 := bstep (se 1 (by rfl) ⟨481625, by rfl⟩ : syracuseStep 642167 = 963251) B963251
theorem B642187 : Blo 638302 642187 := bstep (se 1 (by rfl) ⟨481640, by rfl⟩ : syracuseStep 642187 = 963281) B963281
theorem B642199 : Blo 638302 642199 := bstep (se 1 (by rfl) ⟨481649, by rfl⟩ : syracuseStep 642199 = 963299) B963299
theorem B642219 : Blo 638302 642219 := bstep (se 1 (by rfl) ⟨481664, by rfl⟩ : syracuseStep 642219 = 963329) B963329
theorem B642231 : Blo 638302 642231 := bstep (se 1 (by rfl) ⟨481673, by rfl⟩ : syracuseStep 642231 = 963347) B963347
theorem B1756363 : Blo 638302 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B642251 : Blo 638302 642251 := bstep (se 1 (by rfl) ⟨481688, by rfl⟩ : syracuseStep 642251 = 963377) B963377
theorem B642263 : Blo 638302 642263 := bstep (se 1 (by rfl) ⟨481697, by rfl⟩ : syracuseStep 642263 = 963395) B963395
theorem B1625305 : Blo 638302 1625305 := bstep (se 2 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 1625305 = 1218979) B1218979
theorem B642283 : Blo 638302 642283 := bstep (se 1 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 642283 = 963425) B963425
theorem B642295 : Blo 638302 642295 := bstep (se 1 (by rfl) ⟨481721, by rfl⟩ : syracuseStep 642295 = 963443) B963443
theorem B1232563 : Blo 638302 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B2051801 : Blo 638302 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B18665315 : Blo 638302 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B1331329 : Blo 638302 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B5460119 : Blo 638302 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B3068225 : Blo 638302 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B1364339 : Blo 638302 1364339 := bstep (se 1 (by rfl) ⟨1023254, by rfl⟩ : syracuseStep 1364339 = 2046509) B2046509
theorem B4870691 : Blo 638302 4870691 := bstep (se 1 (by rfl) ⟨3653018, by rfl⟩ : syracuseStep 4870691 = 7306037) B7306037
theorem B2052697 : Blo 638302 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B1823411 : Blo 638302 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1823435 : Blo 638302 1823435 := bstep (se 1 (by rfl) ⟨1367576, by rfl⟩ : syracuseStep 1823435 = 2735153) B2735153
theorem B1364825 : Blo 638302 1364825 := bstep (se 2 (by rfl) ⟨511809, by rfl⟩ : syracuseStep 1364825 = 1023619) B1023619
theorem B2184215 : Blo 638302 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B1725533 : Blo 638302 1725533 := bstep (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) B647075
theorem B2053313 : Blo 638302 2053313 := bstep (se 2 (by rfl) ⟨769992, by rfl⟩ : syracuseStep 2053313 = 1539985) B1539985
theorem B1758667 : Blo 638302 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1824221 : Blo 638302 1824221 := bstep (se 3 (by rfl) ⟨342041, by rfl⟩ : syracuseStep 1824221 = 684083) B684083
theorem B808471 : Blo 638302 808471 := bstep (se 1 (by rfl) ⟨606353, by rfl⟩ : syracuseStep 808471 = 1212707) B1212707
theorem B1365569 : Blo 638302 1365569 := bstep (se 2 (by rfl) ⟨512088, by rfl⟩ : syracuseStep 1365569 = 1024177) B1024177
theorem B1300531 : Blo 638302 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B1726667 : Blo 638302 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B809291 : Blo 638302 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B1366465 : Blo 638302 1366465 := bstep (se 2 (by rfl) ⟨512424, by rfl⟩ : syracuseStep 1366465 = 1024849) B1024849
theorem B4446899 : Blo 638302 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B2742977 : Blo 638302 2742977 := bstep (se 2 (by rfl) ⟨1028616, by rfl⟩ : syracuseStep 2742977 = 2057233) B2057233
theorem B1170163 : Blo 638302 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B1366807 : Blo 638302 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B3234653 : Blo 638302 3234653 := bstep (se 3 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 3234653 = 1212995) B1212995
theorem B5561189 : Blo 638302 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B2186135 : Blo 638302 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B809995 : Blo 638302 809995 := bstep (se 1 (by rfl) ⟨607496, by rfl⟩ : syracuseStep 809995 = 1214993) B1214993
theorem B3070993 : Blo 638302 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B3169373 : Blo 638302 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B1826009 : Blo 638302 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B810263 : Blo 638302 810263 := bstep (se 1 (by rfl) ⟨607697, by rfl⟩ : syracuseStep 810263 = 1215395) B1215395
theorem B1367371 : Blo 638302 1367371 := bstep (se 1 (by rfl) ⟨1025528, by rfl⟩ : syracuseStep 1367371 = 2051057) B2051057
theorem B1727833 : Blo 638302 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B1301875 : Blo 638302 1301875 := bstep (se 1 (by rfl) ⟨976406, by rfl⟩ : syracuseStep 1301875 = 1952813) B1952813
theorem B1826327 : Blo 638302 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B2055773 : Blo 638302 2055773 := bstep (se 3 (by rfl) ⟨385457, by rfl⟩ : syracuseStep 2055773 = 770915) B770915
theorem B7790231 : Blo 638302 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B2055901 : Blo 638302 2055901 := bstep (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) B770963
theorem B2154329 : Blo 638302 2154329 := bstep (se 2 (by rfl) ⟨807873, by rfl⟩ : syracuseStep 2154329 = 1615747) B1615747
theorem B4939613 : Blo 638302 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B15032243 : Blo 638302 15032243 := bstep (se 1 (by rfl) ⟨11274182, by rfl⟩ : syracuseStep 15032243 = 22548365) B22548365
theorem B810967 : Blo 638302 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B2056157 : Blo 638302 2056157 := bstep (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) B771059
theorem B5267587 : Blo 638302 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B1827137 : Blo 638302 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B2155031 : Blo 638302 2155031 := bstep (se 1 (by rfl) ⟨1616273, by rfl⟩ : syracuseStep 2155031 = 3232547) B3232547
theorem B975385 : Blo 638302 975385 := bstep (se 2 (by rfl) ⟨365769, by rfl⟩ : syracuseStep 975385 = 731539) B731539
theorem B647723 : Blo 638302 647723 := bstep (se 1 (by rfl) ⟨485792, by rfl⟩ : syracuseStep 647723 = 971585) B971585
theorem B1368755 : Blo 638302 1368755 := bstep (se 1 (by rfl) ⟨1026566, by rfl⟩ : syracuseStep 1368755 = 2053133) B2053133
theorem B1729217 : Blo 638302 1729217 := bstep (se 2 (by rfl) ⟨648456, by rfl⟩ : syracuseStep 1729217 = 1296913) B1296913
theorem B1368857 : Blo 638302 1368857 := bstep (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) B1026643
theorem B3236759 : Blo 638302 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B2155571 : Blo 638302 2155571 := bstep (se 1 (by rfl) ⟨1616678, by rfl⟩ : syracuseStep 2155571 = 3233357) B3233357
theorem B1369217 : Blo 638302 1369217 := bstep (se 2 (by rfl) ⟨513456, by rfl⟩ : syracuseStep 1369217 = 1026913) B1026913
theorem B910487 : Blo 638302 910487 := bstep (se 1 (by rfl) ⟨682865, by rfl⟩ : syracuseStep 910487 = 1365731) B1365731
theorem B5825741 : Blo 638302 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B3073241 : Blo 638302 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B2188595 : Blo 638302 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B2155841 : Blo 638302 2155841 := bstep (se 2 (by rfl) ⟨808440, by rfl⟩ : syracuseStep 2155841 = 1616881) B1616881
theorem B812683 : Blo 638302 812683 := bstep (se 1 (by rfl) ⟨609512, by rfl⟩ : syracuseStep 812683 = 1219025) B1219025
theorem B4876037 : Blo 638302 4876037 := bstep (se 4 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 4876037 = 914257) B914257
theorem B1369943 : Blo 638302 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B2156381 : Blo 638302 2156381 := bstep (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) B808643
theorem B1828811 : Blo 638302 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B649495 : Blo 638302 649495 := bstep (se 1 (by rfl) ⟨487121, by rfl⟩ : syracuseStep 649495 = 974243) B974243
theorem B682327 : Blo 638302 682327 := bstep (se 1 (by rfl) ⟨511745, by rfl⟩ : syracuseStep 682327 = 1023491) B1023491
theorem B846347 : Blo 638302 846347 := bstep (se 1 (by rfl) ⟨634760, by rfl⟩ : syracuseStep 846347 = 1269521) B1269521
theorem B1436183 : Blo 638302 1436183 := bstep (se 1 (by rfl) ⟨1077137, by rfl⟩ : syracuseStep 1436183 = 2154275) B2154275
theorem B1436363 : Blo 638302 1436363 := bstep (se 1 (by rfl) ⟨1077272, by rfl⟩ : syracuseStep 1436363 = 2154545) B2154545
theorem B1370839 : Blo 638302 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B1436417 : Blo 638302 1436417 := bstep (se 2 (by rfl) ⟨538656, by rfl⟩ : syracuseStep 1436417 = 1077313) B1077313
theorem B2157515 : Blo 638302 2157515 := bstep (se 1 (by rfl) ⟨1618136, by rfl⟩ : syracuseStep 2157515 = 3236273) B3236273
theorem B1436633 : Blo 638302 1436633 := bstep (se 2 (by rfl) ⟨538737, by rfl⟩ : syracuseStep 1436633 = 1077475) B1077475
theorem B1436723 : Blo 638302 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1436759 : Blo 638302 1436759 := bstep (se 1 (by rfl) ⟨1077569, by rfl⟩ : syracuseStep 1436759 = 2155139) B2155139
theorem B2157785 : Blo 638302 2157785 := bstep (se 2 (by rfl) ⟨809169, by rfl⟩ : syracuseStep 2157785 = 1618339) B1618339
theorem B1436939 : Blo 638302 1436939 := bstep (se 1 (by rfl) ⟨1077704, by rfl⟩ : syracuseStep 1436939 = 2155409) B2155409
theorem B1436993 : Blo 638302 1436993 := bstep (se 2 (by rfl) ⟨538872, by rfl⟩ : syracuseStep 1436993 = 1077745) B1077745
theorem B1535449 : Blo 638302 1535449 := bstep (se 2 (by rfl) ⟨575793, by rfl⟩ : syracuseStep 1535449 = 1151587) B1151587
theorem B650743 : Blo 638302 650743 := bstep (se 1 (by rfl) ⟨488057, by rfl⟩ : syracuseStep 650743 = 976115) B976115
theorem B1371659 : Blo 638302 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B1437209 : Blo 638302 1437209 := bstep (se 2 (by rfl) ⟨538953, by rfl⟩ : syracuseStep 1437209 = 1077907) B1077907
theorem B1437299 : Blo 638302 1437299 := bstep (se 1 (by rfl) ⟨1077974, by rfl⟩ : syracuseStep 1437299 = 2155949) B2155949
theorem B1437335 : Blo 638302 1437335 := bstep (se 1 (by rfl) ⟨1078001, by rfl⟩ : syracuseStep 1437335 = 2156003) B2156003
theorem B2191169 : Blo 638302 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B1437515 : Blo 638302 1437515 := bstep (se 1 (by rfl) ⟨1078136, by rfl⟩ : syracuseStep 1437515 = 2156273) B2156273
theorem B1437569 : Blo 638302 1437569 := bstep (se 2 (by rfl) ⟨539088, by rfl⟩ : syracuseStep 1437569 = 1078177) B1078177
theorem B2158487 : Blo 638302 2158487 := bstep (se 1 (by rfl) ⟨1618865, by rfl⟩ : syracuseStep 2158487 = 3237731) B3237731
theorem B683959 : Blo 638302 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B913369 : Blo 638302 913369 := bstep (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) B685027
theorem B1077259 : Blo 638302 1077259 := bstep (se 1 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 1077259 = 1615889) B1615889
theorem B6156323 : Blo 638302 6156323 := bstep (se 1 (by rfl) ⟨4617242, by rfl⟩ : syracuseStep 6156323 = 9234485) B9234485
theorem B1437785 : Blo 638302 1437785 := bstep (se 2 (by rfl) ⟨539169, by rfl⟩ : syracuseStep 1437785 = 1078339) B1078339
theorem B3469463 : Blo 638302 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B4944023 : Blo 638302 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B1077401 : Blo 638302 1077401 := bstep (se 2 (by rfl) ⟨404025, by rfl⟩ : syracuseStep 1077401 = 808051) B808051
theorem B1437875 : Blo 638302 1437875 := bstep (se 1 (by rfl) ⟨1078406, by rfl⟩ : syracuseStep 1437875 = 2156813) B2156813
theorem B1437911 : Blo 638302 1437911 := bstep (se 1 (by rfl) ⟨1078433, by rfl⟩ : syracuseStep 1437911 = 2156867) B2156867
theorem B1994969 : Blo 638302 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B1077529 : Blo 638302 1077529 := bstep (se 2 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 1077529 = 808147) B808147
theorem B3240323 : Blo 638302 3240323 := bstep (se 1 (by rfl) ⟨2430242, by rfl⟩ : syracuseStep 3240323 = 4860485) B4860485
theorem B1438091 : Blo 638302 1438091 := bstep (se 1 (by rfl) ⟨1078568, by rfl⟩ : syracuseStep 1438091 = 2157137) B2157137
theorem B5468593 : Blo 638302 5468593 := bstep (se 2 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 5468593 = 4101445) B4101445
theorem B2159027 : Blo 638302 2159027 := bstep (se 1 (by rfl) ⟨1619270, by rfl⟩ : syracuseStep 2159027 = 3238541) B3238541
theorem B1438145 : Blo 638302 1438145 := bstep (se 2 (by rfl) ⟨539304, by rfl⟩ : syracuseStep 1438145 = 1078609) B1078609
theorem B1438361 : Blo 638302 1438361 := bstep (se 2 (by rfl) ⟨539385, by rfl⟩ : syracuseStep 1438361 = 1078771) B1078771
theorem B2159297 : Blo 638302 2159297 := bstep (se 2 (by rfl) ⟨809736, by rfl⟩ : syracuseStep 2159297 = 1619473) B1619473
theorem B684779 : Blo 638302 684779 := bstep (se 1 (by rfl) ⟨513584, by rfl⟩ : syracuseStep 684779 = 1027169) B1027169
theorem B1438451 : Blo 638302 1438451 := bstep (se 1 (by rfl) ⟨1078838, by rfl⟩ : syracuseStep 1438451 = 2157677) B2157677
theorem B1438487 : Blo 638302 1438487 := bstep (se 1 (by rfl) ⟨1078865, by rfl⟩ : syracuseStep 1438487 = 2157731) B2157731
theorem B1078103 : Blo 638302 1078103 := bstep (se 1 (by rfl) ⟨808577, by rfl⟩ : syracuseStep 1078103 = 1617155) B1617155
theorem B1438667 : Blo 638302 1438667 := bstep (se 1 (by rfl) ⟨1079000, by rfl⟩ : syracuseStep 1438667 = 2158001) B2158001
theorem B1078231 : Blo 638302 1078231 := bstep (se 1 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 1078231 = 1617347) B1617347
theorem B1438721 : Blo 638302 1438721 := bstep (se 2 (by rfl) ⟨539520, by rfl⟩ : syracuseStep 1438721 = 1079041) B1079041
theorem B10515491 : Blo 638302 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B1438937 : Blo 638302 1438937 := bstep (se 2 (by rfl) ⟨539601, by rfl⟩ : syracuseStep 1438937 = 1079203) B1079203
theorem B2159837 : Blo 638302 2159837 := bstep (se 3 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 2159837 = 809939) B809939
theorem B718123 : Blo 638302 718123 := bstep (se 1 (by rfl) ⟨538592, by rfl⟩ : syracuseStep 718123 = 1077185) B1077185
theorem B1439027 : Blo 638302 1439027 := bstep (se 1 (by rfl) ⟨1079270, by rfl⟩ : syracuseStep 1439027 = 2158541) B2158541
theorem B1439063 : Blo 638302 1439063 := bstep (se 1 (by rfl) ⟨1079297, by rfl⟩ : syracuseStep 1439063 = 2158595) B2158595
theorem B718231 : Blo 638302 718231 := bstep (se 1 (by rfl) ⟨538673, by rfl⟩ : syracuseStep 718231 = 1077347) B1077347
theorem B1439243 : Blo 638302 1439243 := bstep (se 1 (by rfl) ⟨1079432, by rfl⟩ : syracuseStep 1439243 = 2158865) B2158865
theorem B1439297 : Blo 638302 1439297 := bstep (se 2 (by rfl) ⟨539736, by rfl⟩ : syracuseStep 1439297 = 1079473) B1079473
theorem B718411 : Blo 638302 718411 := bstep (se 1 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 718411 = 1077617) B1077617
theorem B1078859 : Blo 638302 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B718519 : Blo 638302 718519 := bstep (se 1 (by rfl) ⟨538889, by rfl⟩ : syracuseStep 718519 = 1077779) B1077779
theorem B1078987 : Blo 638302 1078987 := bstep (se 1 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 1078987 = 1618481) B1618481
theorem B685847 : Blo 638302 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B1439513 : Blo 638302 1439513 := bstep (se 2 (by rfl) ⟨539817, by rfl⟩ : syracuseStep 1439513 = 1079635) B1079635
theorem B3471149 : Blo 638302 3471149 := bstep (se 3 (by rfl) ⟨650840, by rfl⟩ : syracuseStep 3471149 = 1301681) B1301681
theorem B1079129 : Blo 638302 1079129 := bstep (se 2 (by rfl) ⟨404673, by rfl⟩ : syracuseStep 1079129 = 809347) B809347
theorem B718699 : Blo 638302 718699 := bstep (se 1 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 718699 = 1078049) B1078049
theorem B1439603 : Blo 638302 1439603 := bstep (se 1 (by rfl) ⟨1079702, by rfl⟩ : syracuseStep 1439603 = 2159405) B2159405
theorem B1439639 : Blo 638302 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B12318641 : Blo 638302 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B2193331 : Blo 638302 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B1537985 : Blo 638302 1537985 := bstep (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) B1153489
theorem B718807 : Blo 638302 718807 := bstep (se 1 (by rfl) ⟨539105, by rfl⟩ : syracuseStep 718807 = 1078211) B1078211
theorem B1079257 : Blo 638302 1079257 := bstep (se 2 (by rfl) ⟨404721, by rfl⟩ : syracuseStep 1079257 = 809443) B809443
theorem B1439819 : Blo 638302 1439819 := bstep (se 1 (by rfl) ⟨1079864, by rfl⟩ : syracuseStep 1439819 = 2159729) B2159729
theorem B1439873 : Blo 638302 1439873 := bstep (se 2 (by rfl) ⟨539952, by rfl⟩ : syracuseStep 1439873 = 1079905) B1079905
theorem B718987 : Blo 638302 718987 := bstep (se 1 (by rfl) ⟨539240, by rfl⟩ : syracuseStep 718987 = 1078481) B1078481
theorem B719095 : Blo 638302 719095 := bstep (se 1 (by rfl) ⟨539321, by rfl⟩ : syracuseStep 719095 = 1078643) B1078643
theorem B19757357 : Blo 638302 19757357 := bstep (se 3 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 19757357 = 7409009) B7409009
theorem B5536075 : Blo 638302 5536075 := bstep (se 1 (by rfl) ⟨4152056, by rfl⟩ : syracuseStep 5536075 = 8304113) B8304113
theorem B2160971 : Blo 638302 2160971 := bstep (se 1 (by rfl) ⟨1620728, by rfl⟩ : syracuseStep 2160971 = 3241457) B3241457
theorem B1440089 : Blo 638302 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B719275 : Blo 638302 719275 := bstep (se 1 (by rfl) ⟨539456, by rfl⟩ : syracuseStep 719275 = 1078913) B1078913
theorem B1440179 : Blo 638302 1440179 := bstep (se 1 (by rfl) ⟨1080134, by rfl⟩ : syracuseStep 1440179 = 2160269) B2160269
theorem B1440215 : Blo 638302 1440215 := bstep (se 1 (by rfl) ⟨1080161, by rfl⟩ : syracuseStep 1440215 = 2160323) B2160323
theorem B719383 : Blo 638302 719383 := bstep (se 1 (by rfl) ⟨539537, by rfl⟩ : syracuseStep 719383 = 1079075) B1079075
theorem B1079831 : Blo 638302 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B2161241 : Blo 638302 2161241 := bstep (se 2 (by rfl) ⟨810465, by rfl⟩ : syracuseStep 2161241 = 1620931) B1620931
theorem B1440395 : Blo 638302 1440395 := bstep (se 1 (by rfl) ⟨1080296, by rfl⟩ : syracuseStep 1440395 = 2160593) B2160593
theorem B1079959 : Blo 638302 1079959 := bstep (se 1 (by rfl) ⟨809969, by rfl⟩ : syracuseStep 1079959 = 1619939) B1619939
theorem B1440449 : Blo 638302 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B719563 : Blo 638302 719563 := bstep (se 1 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 719563 = 1079345) B1079345
theorem B1669835 : Blo 638302 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B719671 : Blo 638302 719671 := bstep (se 1 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 719671 = 1079507) B1079507
theorem B1440665 : Blo 638302 1440665 := bstep (se 2 (by rfl) ⟨540249, by rfl⟩ : syracuseStep 1440665 = 1080499) B1080499
theorem B719851 : Blo 638302 719851 := bstep (se 1 (by rfl) ⟨539888, by rfl⟩ : syracuseStep 719851 = 1079777) B1079777
theorem B1440755 : Blo 638302 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B1440791 : Blo 638302 1440791 := bstep (se 1 (by rfl) ⟨1080593, by rfl⟩ : syracuseStep 1440791 = 2161187) B2161187
theorem B719959 : Blo 638302 719959 := bstep (se 1 (by rfl) ⟨539969, by rfl⟩ : syracuseStep 719959 = 1079939) B1079939
theorem B1440971 : Blo 638302 1440971 := bstep (se 1 (by rfl) ⟨1080728, by rfl⟩ : syracuseStep 1440971 = 2161457) B2161457
theorem B1441025 : Blo 638302 1441025 := bstep (se 2 (by rfl) ⟨540384, by rfl⟩ : syracuseStep 1441025 = 1080769) B1080769
theorem B720139 : Blo 638302 720139 := bstep (se 1 (by rfl) ⟨540104, by rfl⟩ : syracuseStep 720139 = 1080209) B1080209
theorem B1080587 : Blo 638302 1080587 := bstep (se 1 (by rfl) ⟨810440, by rfl⟩ : syracuseStep 1080587 = 1620881) B1620881
theorem B2161943 : Blo 638302 2161943 := bstep (se 1 (by rfl) ⟨1621457, by rfl⟩ : syracuseStep 2161943 = 3242915) B3242915
theorem B720247 : Blo 638302 720247 := bstep (se 1 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 720247 = 1080371) B1080371
theorem B1080715 : Blo 638302 1080715 := bstep (se 1 (by rfl) ⟨810536, by rfl⟩ : syracuseStep 1080715 = 1621073) B1621073
theorem B2915777 : Blo 638302 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B1441241 : Blo 638302 1441241 := bstep (se 2 (by rfl) ⟨540465, by rfl⟩ : syracuseStep 1441241 = 1080931) B1080931
theorem B2588183 : Blo 638302 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B1080857 : Blo 638302 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B720427 : Blo 638302 720427 := bstep (se 1 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 720427 = 1080641) B1080641
theorem B1441331 : Blo 638302 1441331 := bstep (se 1 (by rfl) ⟨1080998, by rfl⟩ : syracuseStep 1441331 = 2161997) B2161997
theorem B1441367 : Blo 638302 1441367 := bstep (se 1 (by rfl) ⟨1081025, by rfl⟩ : syracuseStep 1441367 = 2162051) B2162051
theorem B1211993 : Blo 638302 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B3899011 : Blo 638302 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B2588311 : Blo 638302 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B720535 : Blo 638302 720535 := bstep (se 1 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 720535 = 1080803) B1080803
theorem B1080985 : Blo 638302 1080985 := bstep (se 2 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 1080985 = 810739) B810739
theorem B1441547 : Blo 638302 1441547 := bstep (se 1 (by rfl) ⟨1081160, by rfl⟩ : syracuseStep 1441547 = 2162321) B2162321
theorem B2424593 : Blo 638302 2424593 := bstep (se 2 (by rfl) ⟨909222, by rfl⟩ : syracuseStep 2424593 = 1818445) B1818445
theorem B2162483 : Blo 638302 2162483 := bstep (se 1 (by rfl) ⟨1621862, by rfl⟩ : syracuseStep 2162483 = 3243725) B3243725
theorem B1441601 : Blo 638302 1441601 := bstep (se 2 (by rfl) ⟨540600, by rfl⟩ : syracuseStep 1441601 = 1081201) B1081201
theorem B8224577 : Blo 638302 8224577 := bstep (se 2 (by rfl) ⟨3084216, by rfl⟩ : syracuseStep 8224577 = 6168433) B6168433
theorem B720715 : Blo 638302 720715 := bstep (se 1 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 720715 = 1081073) B1081073
theorem B720823 : Blo 638302 720823 := bstep (se 1 (by rfl) ⟨540617, by rfl⟩ : syracuseStep 720823 = 1081235) B1081235
theorem B1212403 : Blo 638302 1212403 := bstep (se 1 (by rfl) ⟨909302, by rfl⟩ : syracuseStep 1212403 = 1818605) B1818605
theorem B2162699 : Blo 638302 2162699 := bstep (se 1 (by rfl) ⟨1622024, by rfl⟩ : syracuseStep 2162699 = 3244049) B3244049
theorem B1441835 : Blo 638302 1441835 := bstep (se 1 (by rfl) ⟨1081376, by rfl⟩ : syracuseStep 1441835 = 2162753) B2162753
theorem B2162807 : Blo 638302 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B721039 : Blo 638302 721039 := bstep (se 1 (by rfl) ⟨540779, by rfl⟩ : syracuseStep 721039 = 1081559) B1081559
theorem B1212563 : Blo 638302 1212563 := bstep (se 1 (by rfl) ⟨909422, by rfl⟩ : syracuseStep 1212563 = 1818845) B1818845
theorem B23298293 : Blo 638302 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B3637619 : Blo 638302 3637619 := bstep (se 1 (by rfl) ⟨2728214, by rfl⟩ : syracuseStep 3637619 = 5456429) B5456429
theorem B1442195 : Blo 638302 1442195 := bstep (se 1 (by rfl) ⟨1081646, by rfl⟩ : syracuseStep 1442195 = 2163293) B2163293
theorem B1442249 : Blo 638302 1442249 := bstep (se 2 (by rfl) ⟨540843, by rfl⟩ : syracuseStep 1442249 = 1081687) B1081687
theorem B9208363 : Blo 638302 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B1081991 : Blo 638302 1081991 := bstep (se 1 (by rfl) ⟨811493, by rfl⟩ : syracuseStep 1081991 = 1622987) B1622987
theorem B721543 : Blo 638302 721543 := bstep (se 1 (by rfl) ⟨541157, by rfl⟩ : syracuseStep 721543 = 1082315) B1082315
theorem B2163401 : Blo 638302 2163401 := bstep (se 2 (by rfl) ⟨811275, by rfl⟩ : syracuseStep 2163401 = 1622551) B1622551
theorem B3244859 : Blo 638302 3244859 := bstep (se 1 (by rfl) ⟨2433644, by rfl⟩ : syracuseStep 3244859 = 4867289) B4867289
theorem B721723 : Blo 638302 721723 := bstep (se 1 (by rfl) ⟨541292, by rfl⟩ : syracuseStep 721723 = 1082585) B1082585
theorem B820103 : Blo 638302 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B2425747 : Blo 638302 2425747 := bstep (se 1 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 2425747 = 3638621) B3638621
theorem B3245021 : Blo 638302 3245021 := bstep (se 3 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 3245021 = 1216883) B1216883
theorem B1442951 : Blo 638302 1442951 := bstep (se 1 (by rfl) ⟨1082213, by rfl⟩ : syracuseStep 1442951 = 2164427) B2164427
theorem B1541387 : Blo 638302 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B1082639 : Blo 638302 1082639 := bstep (se 1 (by rfl) ⟨811979, by rfl⟩ : syracuseStep 1082639 = 1623959) B1623959
theorem B722191 : Blo 638302 722191 := bstep (se 1 (by rfl) ⟨541643, by rfl⟩ : syracuseStep 722191 = 1083287) B1083287
theorem B3245345 : Blo 638302 3245345 := bstep (se 2 (by rfl) ⟨1217004, by rfl⟩ : syracuseStep 3245345 = 2434009) B2434009
theorem B2917691 : Blo 638302 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B1443131 : Blo 638302 1443131 := bstep (se 1 (by rfl) ⟨1082348, by rfl⟩ : syracuseStep 1443131 = 2164697) B2164697
theorem B2164103 : Blo 638302 2164103 := bstep (se 1 (by rfl) ⟨1623077, by rfl⟩ : syracuseStep 2164103 = 3246155) B3246155
theorem B1443257 : Blo 638302 1443257 := bstep (se 2 (by rfl) ⟨541221, by rfl⟩ : syracuseStep 1443257 = 1082443) B1082443
theorem B1213967 : Blo 638302 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B22808141 : Blo 638302 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B2164481 : Blo 638302 2164481 := bstep (se 2 (by rfl) ⟨811680, by rfl⟩ : syracuseStep 2164481 = 1623361) B1623361
theorem B1443599 : Blo 638302 1443599 := bstep (se 1 (by rfl) ⟨1082699, by rfl⟩ : syracuseStep 1443599 = 2165399) B2165399
theorem B1443617 : Blo 638302 1443617 := bstep (se 2 (by rfl) ⟨541356, by rfl⟩ : syracuseStep 1443617 = 1082713) B1082713
theorem B3639077 : Blo 638302 3639077 := bstep (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) B682327
theorem B1083179 : Blo 638302 1083179 := bstep (se 1 (by rfl) ⟨812384, by rfl⟩ : syracuseStep 1083179 = 1624769) B1624769
theorem B1214507 : Blo 638302 1214507 := bstep (se 1 (by rfl) ⟨910880, by rfl⟩ : syracuseStep 1214507 = 1821761) B1821761
theorem B1443959 : Blo 638302 1443959 := bstep (se 1 (by rfl) ⟨1082969, by rfl⟩ : syracuseStep 1443959 = 2165939) B2165939
theorem B1083577 : Blo 638302 1083577 := bstep (se 2 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 1083577 = 812683) B812683
theorem B3246317 : Blo 638302 3246317 := bstep (se 3 (by rfl) ⟨608684, by rfl⟩ : syracuseStep 3246317 = 1217369) B1217369
theorem B1444139 : Blo 638302 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B7801235 : Blo 638302 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B3639761 : Blo 638302 3639761 := bstep (se 2 (by rfl) ⟨1364910, by rfl⟩ : syracuseStep 3639761 = 2729821) B2729821
theorem B21629405 : Blo 638302 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B2165291 : Blo 638302 2165291 := bstep (se 1 (by rfl) ⟨1623968, by rfl⟩ : syracuseStep 2165291 = 3247937) B3247937
theorem B2427479 : Blo 638302 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B1444499 : Blo 638302 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B1444553 : Blo 638302 1444553 := bstep (se 2 (by rfl) ⟨541707, by rfl⟩ : syracuseStep 1444553 = 1083415) B1083415
theorem B3640079 : Blo 638302 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B3247127 : Blo 638302 3247127 := bstep (se 1 (by rfl) ⟨2435345, by rfl⟩ : syracuseStep 3247127 = 4870691) B4870691
theorem B2427965 : Blo 638302 2427965 := bstep (se 3 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 2427965 = 910487) B910487
theorem B1215623 : Blo 638302 1215623 := bstep (se 1 (by rfl) ⟨911717, by rfl⟩ : syracuseStep 1215623 = 1823435) B1823435
theorem B3083465 : Blo 638302 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B15535309 : Blo 638302 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B986375 : Blo 638302 986375 := bstep (se 1 (by rfl) ⟨739781, by rfl⟩ : syracuseStep 986375 = 1479563) B1479563
theorem B1150355 : Blo 638302 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B1216147 : Blo 638302 1216147 := bstep (se 1 (by rfl) ⟨912110, by rfl⟩ : syracuseStep 1216147 = 1824221) B1824221
theorem B3739337 : Blo 638302 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B3084065 : Blo 638302 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B2166587 : Blo 638302 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B1151111 : Blo 638302 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B3641537 : Blo 638302 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B2167073 : Blo 638302 2167073 := bstep (se 2 (by rfl) ⟨812652, by rfl⟩ : syracuseStep 2167073 = 1625305) B1625305
theorem B3707459 : Blo 638302 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B1217339 : Blo 638302 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B2167667 : Blo 638302 2167667 := bstep (se 1 (by rfl) ⟨1625750, by rfl⟩ : syracuseStep 2167667 = 3251501) B3251501
theorem B1643417 : Blo 638302 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B4101293 : Blo 638302 4101293 := bstep (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) B1537985
theorem B1217825 : Blo 638302 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B1250707 : Blo 638302 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B1775105 : Blo 638302 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B1218091 : Blo 638302 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B1152811 : Blo 638302 1152811 := bstep (se 1 (by rfl) ⟨864608, by rfl⟩ : syracuseStep 1152811 = 1729217) B1729217
theorem B7804835 : Blo 638302 7804835 := bstep (se 1 (by rfl) ⟨5853626, by rfl⟩ : syracuseStep 7804835 = 11707253) B11707253
theorem B3250205 : Blo 638302 3250205 := bstep (se 3 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 3250205 = 1218827) B1218827
theorem B2431367 : Blo 638302 2431367 := bstep (se 1 (by rfl) ⟨1823525, by rfl⟩ : syracuseStep 2431367 = 3647051) B3647051
theorem B3250691 : Blo 638302 3250691 := bstep (se 1 (by rfl) ⟨2438018, by rfl⟩ : syracuseStep 3250691 = 4876037) B4876037
theorem B6232643 : Blo 638302 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B1219207 : Blo 638302 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B957455 : Blo 638302 957455 := bstep (se 1 (by rfl) ⟨718091, by rfl⟩ : syracuseStep 957455 = 1436183) B1436183
theorem B957497 : Blo 638302 957497 := bstep (se 2 (by rfl) ⟨359061, by rfl⟩ : syracuseStep 957497 = 718123) B718123
theorem B1645655 : Blo 638302 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B957575 : Blo 638302 957575 := bstep (se 1 (by rfl) ⟨718181, by rfl⟩ : syracuseStep 957575 = 1436363) B1436363
theorem B957611 : Blo 638302 957611 := bstep (se 1 (by rfl) ⟨718208, by rfl⟩ : syracuseStep 957611 = 1436417) B1436417
theorem B957641 : Blo 638302 957641 := bstep (se 2 (by rfl) ⟨359115, by rfl⟩ : syracuseStep 957641 = 718231) B718231
theorem B957755 : Blo 638302 957755 := bstep (se 1 (by rfl) ⟨718316, by rfl⟩ : syracuseStep 957755 = 1436633) B1436633
theorem B957815 : Blo 638302 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B957839 : Blo 638302 957839 := bstep (se 1 (by rfl) ⟨718379, by rfl⟩ : syracuseStep 957839 = 1436759) B1436759
theorem B957881 : Blo 638302 957881 := bstep (se 2 (by rfl) ⟨359205, by rfl⟩ : syracuseStep 957881 = 718411) B718411
theorem B957959 : Blo 638302 957959 := bstep (se 1 (by rfl) ⟨718469, by rfl⟩ : syracuseStep 957959 = 1436939) B1436939
theorem B957995 : Blo 638302 957995 := bstep (se 1 (by rfl) ⟨718496, by rfl⟩ : syracuseStep 957995 = 1436993) B1436993
theorem B958025 : Blo 638302 958025 := bstep (se 2 (by rfl) ⟨359259, by rfl⟩ : syracuseStep 958025 = 718519) B718519
theorem B958139 : Blo 638302 958139 := bstep (se 1 (by rfl) ⟨718604, by rfl⟩ : syracuseStep 958139 = 1437209) B1437209
theorem B958199 : Blo 638302 958199 := bstep (se 1 (by rfl) ⟨718649, by rfl⟩ : syracuseStep 958199 = 1437299) B1437299
theorem B958223 : Blo 638302 958223 := bstep (se 1 (by rfl) ⟨718667, by rfl⟩ : syracuseStep 958223 = 1437335) B1437335
theorem B958265 : Blo 638302 958265 := bstep (se 2 (by rfl) ⟨359349, by rfl⟩ : syracuseStep 958265 = 718699) B718699
theorem B958343 : Blo 638302 958343 := bstep (se 1 (by rfl) ⟨718757, by rfl⟩ : syracuseStep 958343 = 1437515) B1437515
theorem B2924441 : Blo 638302 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B958379 : Blo 638302 958379 := bstep (se 1 (by rfl) ⟨718784, by rfl⟩ : syracuseStep 958379 = 1437569) B1437569
theorem B958409 : Blo 638302 958409 := bstep (se 2 (by rfl) ⟨359403, by rfl⟩ : syracuseStep 958409 = 718807) B718807
theorem B4104215 : Blo 638302 4104215 := bstep (se 1 (by rfl) ⟨3078161, by rfl⟩ : syracuseStep 4104215 = 6156323) B6156323
theorem B958523 : Blo 638302 958523 := bstep (se 1 (by rfl) ⟨718892, by rfl⟩ : syracuseStep 958523 = 1437785) B1437785
theorem B958583 : Blo 638302 958583 := bstep (se 1 (by rfl) ⟨718937, by rfl⟩ : syracuseStep 958583 = 1437875) B1437875
theorem B958607 : Blo 638302 958607 := bstep (se 1 (by rfl) ⟨718955, by rfl⟩ : syracuseStep 958607 = 1437911) B1437911
theorem B958649 : Blo 638302 958649 := bstep (se 2 (by rfl) ⟨359493, by rfl⟩ : syracuseStep 958649 = 718987) B718987
theorem B958727 : Blo 638302 958727 := bstep (se 1 (by rfl) ⟨719045, by rfl⟩ : syracuseStep 958727 = 1438091) B1438091
theorem B958763 : Blo 638302 958763 := bstep (se 1 (by rfl) ⟨719072, by rfl⟩ : syracuseStep 958763 = 1438145) B1438145
theorem B958793 : Blo 638302 958793 := bstep (se 2 (by rfl) ⟨359547, by rfl⟩ : syracuseStep 958793 = 719095) B719095
theorem B7381433 : Blo 638302 7381433 := bstep (se 2 (by rfl) ⟨2768037, by rfl⟩ : syracuseStep 7381433 = 5536075) B5536075
theorem B958907 : Blo 638302 958907 := bstep (se 1 (by rfl) ⟨719180, by rfl⟩ : syracuseStep 958907 = 1438361) B1438361
theorem B958967 : Blo 638302 958967 := bstep (se 1 (by rfl) ⟨719225, by rfl⟩ : syracuseStep 958967 = 1438451) B1438451
theorem B958991 : Blo 638302 958991 := bstep (se 1 (by rfl) ⟨719243, by rfl⟩ : syracuseStep 958991 = 1438487) B1438487
theorem B959033 : Blo 638302 959033 := bstep (se 2 (by rfl) ⟨359637, by rfl⟩ : syracuseStep 959033 = 719275) B719275
theorem B959111 : Blo 638302 959111 := bstep (se 1 (by rfl) ⟨719333, by rfl⟩ : syracuseStep 959111 = 1438667) B1438667
theorem B959147 : Blo 638302 959147 := bstep (se 1 (by rfl) ⟨719360, by rfl⟩ : syracuseStep 959147 = 1438721) B1438721
theorem B959177 : Blo 638302 959177 := bstep (se 2 (by rfl) ⟨359691, by rfl⟩ : syracuseStep 959177 = 719383) B719383
theorem B14033699 : Blo 638302 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B959291 : Blo 638302 959291 := bstep (se 1 (by rfl) ⟨719468, by rfl⟩ : syracuseStep 959291 = 1438937) B1438937
theorem B959351 : Blo 638302 959351 := bstep (se 1 (by rfl) ⟨719513, by rfl⟩ : syracuseStep 959351 = 1439027) B1439027
theorem B959375 : Blo 638302 959375 := bstep (se 1 (by rfl) ⟨719531, by rfl⟩ : syracuseStep 959375 = 1439063) B1439063
theorem B959417 : Blo 638302 959417 := bstep (se 2 (by rfl) ⟨359781, by rfl⟩ : syracuseStep 959417 = 719563) B719563
theorem B959495 : Blo 638302 959495 := bstep (se 1 (by rfl) ⟨719621, by rfl⟩ : syracuseStep 959495 = 1439243) B1439243
theorem B959531 : Blo 638302 959531 := bstep (se 1 (by rfl) ⟨719648, by rfl⟩ : syracuseStep 959531 = 1439297) B1439297
theorem B959561 : Blo 638302 959561 := bstep (se 2 (by rfl) ⟨359835, by rfl⟩ : syracuseStep 959561 = 719671) B719671
theorem B959675 : Blo 638302 959675 := bstep (se 1 (by rfl) ⟨719756, by rfl⟩ : syracuseStep 959675 = 1439513) B1439513
theorem B959735 : Blo 638302 959735 := bstep (se 1 (by rfl) ⟨719801, by rfl⟩ : syracuseStep 959735 = 1439603) B1439603
theorem B959759 : Blo 638302 959759 := bstep (se 1 (by rfl) ⟨719819, by rfl⟩ : syracuseStep 959759 = 1439639) B1439639
theorem B959801 : Blo 638302 959801 := bstep (se 2 (by rfl) ⟨359925, by rfl⟩ : syracuseStep 959801 = 719851) B719851
theorem B959879 : Blo 638302 959879 := bstep (se 1 (by rfl) ⟨719909, by rfl⟩ : syracuseStep 959879 = 1439819) B1439819
theorem B959915 : Blo 638302 959915 := bstep (se 1 (by rfl) ⟨719936, by rfl⟩ : syracuseStep 959915 = 1439873) B1439873
theorem B959945 : Blo 638302 959945 := bstep (se 2 (by rfl) ⟨359979, by rfl⟩ : syracuseStep 959945 = 719959) B719959
theorem B960059 : Blo 638302 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B960119 : Blo 638302 960119 := bstep (se 1 (by rfl) ⟨720089, by rfl⟩ : syracuseStep 960119 = 1440179) B1440179
theorem B960143 : Blo 638302 960143 := bstep (se 1 (by rfl) ⟨720107, by rfl⟩ : syracuseStep 960143 = 1440215) B1440215
theorem B960185 : Blo 638302 960185 := bstep (se 2 (by rfl) ⟨360069, by rfl⟩ : syracuseStep 960185 = 720139) B720139
theorem B960263 : Blo 638302 960263 := bstep (se 1 (by rfl) ⟨720197, by rfl⟩ : syracuseStep 960263 = 1440395) B1440395
theorem B2303777 : Blo 638302 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B960299 : Blo 638302 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B960329 : Blo 638302 960329 := bstep (se 2 (by rfl) ⟨360123, by rfl⟩ : syracuseStep 960329 = 720247) B720247
theorem B960443 : Blo 638302 960443 := bstep (se 1 (by rfl) ⟨720332, by rfl⟩ : syracuseStep 960443 = 1440665) B1440665
theorem B960503 : Blo 638302 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B960527 : Blo 638302 960527 := bstep (se 1 (by rfl) ⟨720395, by rfl⟩ : syracuseStep 960527 = 1440791) B1440791
theorem B960569 : Blo 638302 960569 := bstep (se 2 (by rfl) ⟨360213, by rfl⟩ : syracuseStep 960569 = 720427) B720427
theorem B960647 : Blo 638302 960647 := bstep (se 1 (by rfl) ⟨720485, by rfl⟩ : syracuseStep 960647 = 1440971) B1440971
theorem B960683 : Blo 638302 960683 := bstep (se 1 (by rfl) ⟨720512, by rfl⟩ : syracuseStep 960683 = 1441025) B1441025
theorem B5843117 : Blo 638302 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B3451081 : Blo 638302 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B960713 : Blo 638302 960713 := bstep (se 2 (by rfl) ⟨360267, by rfl⟩ : syracuseStep 960713 = 720535) B720535
theorem B1943851 : Blo 638302 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B960827 : Blo 638302 960827 := bstep (se 1 (by rfl) ⟨720620, by rfl⟩ : syracuseStep 960827 = 1441241) B1441241
theorem B960887 : Blo 638302 960887 := bstep (se 1 (by rfl) ⟨720665, by rfl⟩ : syracuseStep 960887 = 1441331) B1441331
theorem B960911 : Blo 638302 960911 := bstep (se 1 (by rfl) ⟨720683, by rfl⟩ : syracuseStep 960911 = 1441367) B1441367
theorem B960953 : Blo 638302 960953 := bstep (se 2 (by rfl) ⟨360357, by rfl⟩ : syracuseStep 960953 = 720715) B720715
theorem B961031 : Blo 638302 961031 := bstep (se 1 (by rfl) ⟨720773, by rfl⟩ : syracuseStep 961031 = 1441547) B1441547
theorem B1616395 : Blo 638302 1616395 := bstep (se 1 (by rfl) ⟨1212296, by rfl⟩ : syracuseStep 1616395 = 2424593) B2424593
theorem B961067 : Blo 638302 961067 := bstep (se 1 (by rfl) ⟨720800, by rfl⟩ : syracuseStep 961067 = 1441601) B1441601
theorem B5483051 : Blo 638302 5483051 := bstep (se 1 (by rfl) ⟨4112288, by rfl⟩ : syracuseStep 5483051 = 8224577) B8224577
theorem B961097 : Blo 638302 961097 := bstep (se 2 (by rfl) ⟨360411, by rfl⟩ : syracuseStep 961097 = 720823) B720823
theorem B1616537 : Blo 638302 1616537 := bstep (se 2 (by rfl) ⟨606201, by rfl⟩ : syracuseStep 1616537 = 1212403) B1212403
theorem B961211 : Blo 638302 961211 := bstep (se 1 (by rfl) ⟨720908, by rfl⟩ : syracuseStep 961211 = 1441817) B1441817
theorem B961271 : Blo 638302 961271 := bstep (se 1 (by rfl) ⟨720953, by rfl⟩ : syracuseStep 961271 = 1441907) B1441907
theorem B961295 : Blo 638302 961295 := bstep (se 1 (by rfl) ⟨720971, by rfl⟩ : syracuseStep 961295 = 1441943) B1441943
theorem B961337 : Blo 638302 961337 := bstep (se 2 (by rfl) ⟨360501, by rfl⟩ : syracuseStep 961337 = 721003) B721003
theorem B1616699 : Blo 638302 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B7023449 : Blo 638302 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B961415 : Blo 638302 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B961451 : Blo 638302 961451 := bstep (se 1 (by rfl) ⟨721088, by rfl⟩ : syracuseStep 961451 = 1442177) B1442177
theorem B961481 : Blo 638302 961481 := bstep (se 2 (by rfl) ⟨360555, by rfl⟩ : syracuseStep 961481 = 721111) B721111
theorem B961595 : Blo 638302 961595 := bstep (se 1 (by rfl) ⟨721196, by rfl⟩ : syracuseStep 961595 = 1442393) B1442393
theorem B2305091 : Blo 638302 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B961655 : Blo 638302 961655 := bstep (se 1 (by rfl) ⟨721241, by rfl⟩ : syracuseStep 961655 = 1442483) B1442483
theorem B961679 : Blo 638302 961679 := bstep (se 1 (by rfl) ⟨721259, by rfl⟩ : syracuseStep 961679 = 1442519) B1442519
theorem B1617043 : Blo 638302 1617043 := bstep (se 1 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 1617043 = 2425565) B2425565
theorem B961721 : Blo 638302 961721 := bstep (se 2 (by rfl) ⟨360645, by rfl⟩ : syracuseStep 961721 = 721291) B721291
theorem B961799 : Blo 638302 961799 := bstep (se 1 (by rfl) ⟨721349, by rfl⟩ : syracuseStep 961799 = 1442699) B1442699
theorem B1617185 : Blo 638302 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B961835 : Blo 638302 961835 := bstep (se 1 (by rfl) ⟨721376, by rfl⟩ : syracuseStep 961835 = 1442753) B1442753
theorem B3648827 : Blo 638302 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B961865 : Blo 638302 961865 := bstep (se 2 (by rfl) ⟨360699, by rfl⟩ : syracuseStep 961865 = 721399) B721399
theorem B1027463 : Blo 638302 1027463 := bstep (se 1 (by rfl) ⟨770597, by rfl⟩ : syracuseStep 1027463 = 1541195) B1541195
theorem B961979 : Blo 638302 961979 := bstep (se 1 (by rfl) ⟨721484, by rfl⟩ : syracuseStep 961979 = 1442969) B1442969
theorem B962039 : Blo 638302 962039 := bstep (se 1 (by rfl) ⟨721529, by rfl⟩ : syracuseStep 962039 = 1443059) B1443059
theorem B4107779 : Blo 638302 4107779 := bstep (se 1 (by rfl) ⟨3080834, by rfl⟩ : syracuseStep 4107779 = 6161669) B6161669
theorem B962063 : Blo 638302 962063 := bstep (se 1 (by rfl) ⟨721547, by rfl⟩ : syracuseStep 962063 = 1443095) B1443095
theorem B962105 : Blo 638302 962105 := bstep (se 2 (by rfl) ⟨360789, by rfl⟩ : syracuseStep 962105 = 721579) B721579
theorem B1945223 : Blo 638302 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B962183 : Blo 638302 962183 := bstep (se 1 (by rfl) ⟨721637, by rfl⟩ : syracuseStep 962183 = 1443275) B1443275
theorem B962219 : Blo 638302 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B962249 : Blo 638302 962249 := bstep (se 2 (by rfl) ⟨360843, by rfl⟩ : syracuseStep 962249 = 721687) B721687
theorem B962363 : Blo 638302 962363 := bstep (se 1 (by rfl) ⟨721772, by rfl⟩ : syracuseStep 962363 = 1443545) B1443545
theorem B962423 : Blo 638302 962423 := bstep (se 1 (by rfl) ⟨721817, by rfl⟩ : syracuseStep 962423 = 1443635) B1443635
theorem B962447 : Blo 638302 962447 := bstep (se 1 (by rfl) ⟨721835, by rfl⟩ : syracuseStep 962447 = 1443671) B1443671
theorem B962489 : Blo 638302 962489 := bstep (se 2 (by rfl) ⟨360933, by rfl⟩ : syracuseStep 962489 = 721867) B721867
theorem B962567 : Blo 638302 962567 := bstep (se 1 (by rfl) ⟨721925, by rfl⟩ : syracuseStep 962567 = 1443851) B1443851
theorem B962603 : Blo 638302 962603 := bstep (se 1 (by rfl) ⟨721952, by rfl⟩ : syracuseStep 962603 = 1443905) B1443905
theorem B962633 : Blo 638302 962633 := bstep (se 2 (by rfl) ⟨360987, by rfl⟩ : syracuseStep 962633 = 721975) B721975
theorem B1093751 : Blo 638302 1093751 := bstep (se 1 (by rfl) ⟨820313, by rfl⟩ : syracuseStep 1093751 = 1640627) B1640627
theorem B962747 : Blo 638302 962747 := bstep (se 1 (by rfl) ⟨722060, by rfl⟩ : syracuseStep 962747 = 1444121) B1444121
theorem B1028297 : Blo 638302 1028297 := bstep (se 2 (by rfl) ⟨385611, by rfl⟩ : syracuseStep 1028297 = 771223) B771223
theorem B962807 : Blo 638302 962807 := bstep (se 1 (by rfl) ⟨722105, by rfl⟩ : syracuseStep 962807 = 1444211) B1444211
theorem B1618177 : Blo 638302 1618177 := bstep (se 2 (by rfl) ⟨606816, by rfl⟩ : syracuseStep 1618177 = 1213633) B1213633
theorem B962831 : Blo 638302 962831 := bstep (se 1 (by rfl) ⟨722123, by rfl⟩ : syracuseStep 962831 = 1444247) B1444247
theorem B962873 : Blo 638302 962873 := bstep (se 2 (by rfl) ⟨361077, by rfl⟩ : syracuseStep 962873 = 722155) B722155
theorem B962951 : Blo 638302 962951 := bstep (se 1 (by rfl) ⟨722213, by rfl⟩ : syracuseStep 962951 = 1444427) B1444427
theorem B2929043 : Blo 638302 2929043 := bstep (se 1 (by rfl) ⟨2196782, by rfl⟩ : syracuseStep 2929043 = 4393565) B4393565
theorem B962987 : Blo 638302 962987 := bstep (se 1 (by rfl) ⟨722240, by rfl⟩ : syracuseStep 962987 = 1444481) B1444481
theorem B963017 : Blo 638302 963017 := bstep (se 2 (by rfl) ⟨361131, by rfl⟩ : syracuseStep 963017 = 722263) B722263
theorem B4862429 : Blo 638302 4862429 := bstep (se 3 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 4862429 = 1823411) B1823411
theorem B2732555 : Blo 638302 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B1847819 : Blo 638302 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B963131 : Blo 638302 963131 := bstep (se 1 (by rfl) ⟨722348, by rfl⟩ : syracuseStep 963131 = 1444697) B1444697
theorem B963191 : Blo 638302 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B963215 : Blo 638302 963215 := bstep (se 1 (by rfl) ⟨722411, by rfl⟩ : syracuseStep 963215 = 1444823) B1444823
theorem B963257 : Blo 638302 963257 := bstep (se 2 (by rfl) ⟨361221, by rfl⟩ : syracuseStep 963257 = 722443) B722443
theorem B864955 : Blo 638302 864955 := bstep (se 1 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 864955 = 1297433) B1297433
theorem B1028809 : Blo 638302 1028809 := bstep (se 2 (by rfl) ⟨385803, by rfl⟩ : syracuseStep 1028809 = 771607) B771607
theorem B3453677 : Blo 638302 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B3650285 : Blo 638302 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B963335 : Blo 638302 963335 := bstep (se 1 (by rfl) ⟨722501, by rfl⟩ : syracuseStep 963335 = 1445003) B1445003
theorem B963371 : Blo 638302 963371 := bstep (se 1 (by rfl) ⟨722528, by rfl⟩ : syracuseStep 963371 = 1445057) B1445057
theorem B963401 : Blo 638302 963401 := bstep (se 2 (by rfl) ⟨361275, by rfl⟩ : syracuseStep 963401 = 722551) B722551
theorem B1618775 : Blo 638302 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B1750049 : Blo 638302 1750049 := bstep (se 2 (by rfl) ⟨656268, by rfl⟩ : syracuseStep 1750049 = 1312537) B1312537
theorem B1618987 : Blo 638302 1618987 := bstep (se 1 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 1618987 = 2428481) B2428481
theorem B1946683 : Blo 638302 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B1619129 : Blo 638302 1619129 := bstep (se 2 (by rfl) ⟨607173, by rfl⟩ : syracuseStep 1619129 = 1214347) B1214347
theorem B2045483 : Blo 638302 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B865993 : Blo 638302 865993 := bstep (se 2 (by rfl) ⟨324747, by rfl⟩ : syracuseStep 865993 = 649495) B649495
theorem B1620121 : Blo 638302 1620121 := bstep (se 2 (by rfl) ⟨607545, by rfl⟩ : syracuseStep 1620121 = 1215091) B1215091
theorem B22132909 : Blo 638302 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B2308333 : Blo 638302 2308333 := bstep (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) B865625
theorem B1620283 : Blo 638302 1620283 := bstep (se 1 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 1620283 = 2430425) B2430425
theorem B1620425 : Blo 638302 1620425 := bstep (se 2 (by rfl) ⟨607659, by rfl⟩ : syracuseStep 1620425 = 1215319) B1215319
theorem B768647 : Blo 638302 768647 := bstep (se 1 (by rfl) ⟨576485, by rfl⟩ : syracuseStep 768647 = 1152971) B1152971
theorem B2734829 : Blo 638302 2734829 := bstep (se 3 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 2734829 = 1025561) B1025561
theorem B1620769 : Blo 638302 1620769 := bstep (se 2 (by rfl) ⟨607788, by rfl⟩ : syracuseStep 1620769 = 1215577) B1215577
theorem B1948531 : Blo 638302 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B2341817 : Blo 638302 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B768955 : Blo 638302 768955 := bstep (se 1 (by rfl) ⟨576716, by rfl⟩ : syracuseStep 768955 = 1153433) B1153433
theorem B6929495 : Blo 638302 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B2964599 : Blo 638302 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B1457423 : Blo 638302 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B2047265 : Blo 638302 2047265 := bstep (se 2 (by rfl) ⟨767724, by rfl⟩ : syracuseStep 2047265 = 1535449) B1535449
theorem B1621367 : Blo 638302 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B638343 : Blo 638302 638343 := bstep (se 1 (by rfl) ⟨478757, by rfl⟩ : syracuseStep 638343 = 957515) B957515
theorem B638351 : Blo 638302 638351 := bstep (se 1 (by rfl) ⟨478763, by rfl⟩ : syracuseStep 638351 = 957527) B957527
theorem B638395 : Blo 638302 638395 := bstep (se 1 (by rfl) ⟨478796, by rfl⟩ : syracuseStep 638395 = 957593) B957593
theorem B638471 : Blo 638302 638471 := bstep (se 1 (by rfl) ⟨478853, by rfl⟩ : syracuseStep 638471 = 957707) B957707
theorem B638479 : Blo 638302 638479 := bstep (se 1 (by rfl) ⟨478859, by rfl⟩ : syracuseStep 638479 = 957719) B957719
theorem B638523 : Blo 638302 638523 := bstep (se 1 (by rfl) ⟨478892, by rfl⟩ : syracuseStep 638523 = 957785) B957785
theorem B638599 : Blo 638302 638599 := bstep (se 1 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 638599 = 957899) B957899
theorem B638607 : Blo 638302 638607 := bstep (se 1 (by rfl) ⟨478955, by rfl⟩ : syracuseStep 638607 = 957911) B957911
theorem B638651 : Blo 638302 638651 := bstep (se 1 (by rfl) ⟨478988, by rfl⟩ : syracuseStep 638651 = 957977) B957977
theorem B638727 : Blo 638302 638727 := bstep (se 1 (by rfl) ⟨479045, by rfl⟩ : syracuseStep 638727 = 958091) B958091
theorem B638735 : Blo 638302 638735 := bstep (se 1 (by rfl) ⟨479051, by rfl⟩ : syracuseStep 638735 = 958103) B958103
theorem B5193487 : Blo 638302 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B638779 : Blo 638302 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B638855 : Blo 638302 638855 := bstep (se 1 (by rfl) ⟨479141, by rfl⟩ : syracuseStep 638855 = 958283) B958283
theorem B638863 : Blo 638302 638863 := bstep (se 1 (by rfl) ⟨479147, by rfl⟩ : syracuseStep 638863 = 958295) B958295
theorem B3293075 : Blo 638302 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B638907 : Blo 638302 638907 := bstep (se 1 (by rfl) ⟨479180, by rfl⟩ : syracuseStep 638907 = 958361) B958361
theorem B638983 : Blo 638302 638983 := bstep (se 1 (by rfl) ⟨479237, by rfl⟩ : syracuseStep 638983 = 958475) B958475
theorem B638991 : Blo 638302 638991 := bstep (se 1 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 638991 = 958487) B958487
theorem B639035 : Blo 638302 639035 := bstep (se 1 (by rfl) ⟨479276, by rfl⟩ : syracuseStep 639035 = 958553) B958553
theorem B639111 : Blo 638302 639111 := bstep (se 1 (by rfl) ⟨479333, by rfl⟩ : syracuseStep 639111 = 958667) B958667
theorem B639119 : Blo 638302 639119 := bstep (se 1 (by rfl) ⟨479339, by rfl⟩ : syracuseStep 639119 = 958679) B958679
theorem B6144173 : Blo 638302 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B639163 : Blo 638302 639163 := bstep (se 1 (by rfl) ⟨479372, by rfl⟩ : syracuseStep 639163 = 958745) B958745
theorem B639239 : Blo 638302 639239 := bstep (se 1 (by rfl) ⟨479429, by rfl⟩ : syracuseStep 639239 = 958859) B958859
theorem B639247 : Blo 638302 639247 := bstep (se 1 (by rfl) ⟨479435, by rfl⟩ : syracuseStep 639247 = 958871) B958871
theorem B639291 : Blo 638302 639291 := bstep (se 1 (by rfl) ⟨479468, by rfl⟩ : syracuseStep 639291 = 958937) B958937
theorem B639367 : Blo 638302 639367 := bstep (se 1 (by rfl) ⟨479525, by rfl⟩ : syracuseStep 639367 = 959051) B959051
theorem B639375 : Blo 638302 639375 := bstep (se 1 (by rfl) ⟨479531, by rfl⟩ : syracuseStep 639375 = 959063) B959063
theorem B7782803 : Blo 638302 7782803 := bstep (se 1 (by rfl) ⟨5837102, by rfl⟩ : syracuseStep 7782803 = 11674205) B11674205
theorem B639419 : Blo 638302 639419 := bstep (se 1 (by rfl) ⟨479564, by rfl⟩ : syracuseStep 639419 = 959129) B959129
theorem B639495 : Blo 638302 639495 := bstep (se 1 (by rfl) ⟨479621, by rfl⟩ : syracuseStep 639495 = 959243) B959243
theorem B639503 : Blo 638302 639503 := bstep (se 1 (by rfl) ⟨479627, by rfl⟩ : syracuseStep 639503 = 959255) B959255
theorem B639547 : Blo 638302 639547 := bstep (se 1 (by rfl) ⟨479660, by rfl⟩ : syracuseStep 639547 = 959321) B959321
theorem B7291457 : Blo 638302 7291457 := bstep (se 2 (by rfl) ⟨2734296, by rfl⟩ : syracuseStep 7291457 = 5468593) B5468593
theorem B639623 : Blo 638302 639623 := bstep (se 1 (by rfl) ⟨479717, by rfl⟩ : syracuseStep 639623 = 959435) B959435
theorem B1622663 : Blo 638302 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B639631 : Blo 638302 639631 := bstep (se 1 (by rfl) ⟨479723, by rfl⟩ : syracuseStep 639631 = 959447) B959447
theorem B1622713 : Blo 638302 1622713 := bstep (se 2 (by rfl) ⟨608517, by rfl⟩ : syracuseStep 1622713 = 1217035) B1217035
theorem B639675 : Blo 638302 639675 := bstep (se 1 (by rfl) ⟨479756, by rfl⟩ : syracuseStep 639675 = 959513) B959513
theorem B639751 : Blo 638302 639751 := bstep (se 1 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 639751 = 959627) B959627
theorem B639759 : Blo 638302 639759 := bstep (se 1 (by rfl) ⟨479819, by rfl⟩ : syracuseStep 639759 = 959639) B959639
theorem B2736929 : Blo 638302 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B2048827 : Blo 638302 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B639803 : Blo 638302 639803 := bstep (se 1 (by rfl) ⟨479852, by rfl⟩ : syracuseStep 639803 = 959705) B959705
theorem B1459063 : Blo 638302 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B639879 : Blo 638302 639879 := bstep (se 1 (by rfl) ⟨479909, by rfl⟩ : syracuseStep 639879 = 959819) B959819
theorem B639887 : Blo 638302 639887 := bstep (se 1 (by rfl) ⟨479915, by rfl⟩ : syracuseStep 639887 = 959831) B959831
theorem B639931 : Blo 638302 639931 := bstep (se 1 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 639931 = 959897) B959897
theorem B3654659 : Blo 638302 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B640007 : Blo 638302 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B640015 : Blo 638302 640015 := bstep (se 1 (by rfl) ⟨480011, by rfl⟩ : syracuseStep 640015 = 960023) B960023
theorem B640059 : Blo 638302 640059 := bstep (se 1 (by rfl) ⟨480044, by rfl⟩ : syracuseStep 640059 = 960089) B960089
theorem B640135 : Blo 638302 640135 := bstep (se 1 (by rfl) ⟨480101, by rfl⟩ : syracuseStep 640135 = 960203) B960203
theorem B640143 : Blo 638302 640143 := bstep (se 1 (by rfl) ⟨480107, by rfl⟩ : syracuseStep 640143 = 960215) B960215
theorem B640187 : Blo 638302 640187 := bstep (se 1 (by rfl) ⟨480140, by rfl⟩ : syracuseStep 640187 = 960281) B960281
theorem B640263 : Blo 638302 640263 := bstep (se 1 (by rfl) ⟨480197, by rfl⟩ : syracuseStep 640263 = 960395) B960395
theorem B640271 : Blo 638302 640271 := bstep (se 1 (by rfl) ⟨480203, by rfl⟩ : syracuseStep 640271 = 960407) B960407
theorem B1623311 : Blo 638302 1623311 := bstep (se 1 (by rfl) ⟨1217483, by rfl⟩ : syracuseStep 1623311 = 2434967) B2434967
theorem B640315 : Blo 638302 640315 := bstep (se 1 (by rfl) ⟨480236, by rfl⟩ : syracuseStep 640315 = 960473) B960473
theorem B640391 : Blo 638302 640391 := bstep (se 1 (by rfl) ⟨480293, by rfl⟩ : syracuseStep 640391 = 960587) B960587
theorem B640399 : Blo 638302 640399 := bstep (se 1 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 640399 = 960599) B960599
theorem B640443 : Blo 638302 640443 := bstep (se 1 (by rfl) ⟨480332, by rfl⟩ : syracuseStep 640443 = 960665) B960665
theorem B3655115 : Blo 638302 3655115 := bstep (se 1 (by rfl) ⟨2741336, by rfl⟩ : syracuseStep 3655115 = 5482673) B5482673
theorem B640519 : Blo 638302 640519 := bstep (se 1 (by rfl) ⟨480389, by rfl⟩ : syracuseStep 640519 = 960779) B960779
theorem B640527 : Blo 638302 640527 := bstep (se 1 (by rfl) ⟨480395, by rfl⟩ : syracuseStep 640527 = 960791) B960791
theorem B640571 : Blo 638302 640571 := bstep (se 1 (by rfl) ⟨480428, by rfl⟩ : syracuseStep 640571 = 960857) B960857
theorem B640647 : Blo 638302 640647 := bstep (se 1 (by rfl) ⟨480485, by rfl⟩ : syracuseStep 640647 = 960971) B960971
theorem B640655 : Blo 638302 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B640699 : Blo 638302 640699 := bstep (se 1 (by rfl) ⟨480524, by rfl⟩ : syracuseStep 640699 = 961049) B961049
theorem B640775 : Blo 638302 640775 := bstep (se 1 (by rfl) ⟨480581, by rfl⟩ : syracuseStep 640775 = 961163) B961163
theorem B640783 : Blo 638302 640783 := bstep (se 1 (by rfl) ⟨480587, by rfl⟩ : syracuseStep 640783 = 961175) B961175
theorem B640827 : Blo 638302 640827 := bstep (se 1 (by rfl) ⟨480620, by rfl⟩ : syracuseStep 640827 = 961241) B961241
theorem B640903 : Blo 638302 640903 := bstep (se 1 (by rfl) ⟨480677, by rfl⟩ : syracuseStep 640903 = 961355) B961355
theorem B640911 : Blo 638302 640911 := bstep (se 1 (by rfl) ⟨480683, by rfl⟩ : syracuseStep 640911 = 961367) B961367
theorem B2344889 : Blo 638302 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B640955 : Blo 638302 640955 := bstep (se 1 (by rfl) ⟨480716, by rfl⟩ : syracuseStep 640955 = 961433) B961433
theorem B1624009 : Blo 638302 1624009 := bstep (se 2 (by rfl) ⟨609003, by rfl⟩ : syracuseStep 1624009 = 1218007) B1218007
theorem B641031 : Blo 638302 641031 := bstep (se 1 (by rfl) ⟨480773, by rfl⟩ : syracuseStep 641031 = 961547) B961547
theorem B641039 : Blo 638302 641039 := bstep (se 1 (by rfl) ⟨480779, by rfl⟩ : syracuseStep 641039 = 961559) B961559
theorem B641083 : Blo 638302 641083 := bstep (se 1 (by rfl) ⟨480812, by rfl⟩ : syracuseStep 641083 = 961625) B961625
theorem B1624151 : Blo 638302 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B3655799 : Blo 638302 3655799 := bstep (se 1 (by rfl) ⟨2741849, by rfl⟩ : syracuseStep 3655799 = 5483699) B5483699
theorem B641159 : Blo 638302 641159 := bstep (se 1 (by rfl) ⟨480869, by rfl⟩ : syracuseStep 641159 = 961739) B961739
theorem B641167 : Blo 638302 641167 := bstep (se 1 (by rfl) ⟨480875, by rfl⟩ : syracuseStep 641167 = 961751) B961751
theorem B641211 : Blo 638302 641211 := bstep (se 1 (by rfl) ⟨480908, by rfl⟩ : syracuseStep 641211 = 961817) B961817
theorem B641287 : Blo 638302 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B641295 : Blo 638302 641295 := bstep (se 1 (by rfl) ⟨480971, by rfl⟩ : syracuseStep 641295 = 961943) B961943
theorem B15616273 : Blo 638302 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B641339 : Blo 638302 641339 := bstep (se 1 (by rfl) ⟨481004, by rfl⟩ : syracuseStep 641339 = 962009) B962009
theorem B641415 : Blo 638302 641415 := bstep (se 1 (by rfl) ⟨481061, by rfl⟩ : syracuseStep 641415 = 962123) B962123
theorem B641423 : Blo 638302 641423 := bstep (se 1 (by rfl) ⟨481067, by rfl⟩ : syracuseStep 641423 = 962135) B962135
theorem B641467 : Blo 638302 641467 := bstep (se 1 (by rfl) ⟨481100, by rfl⟩ : syracuseStep 641467 = 962201) B962201
theorem B641543 : Blo 638302 641543 := bstep (se 1 (by rfl) ⟨481157, by rfl⟩ : syracuseStep 641543 = 962315) B962315
theorem B641551 : Blo 638302 641551 := bstep (se 1 (by rfl) ⟨481163, by rfl⟩ : syracuseStep 641551 = 962327) B962327
theorem B641595 : Blo 638302 641595 := bstep (se 1 (by rfl) ⟨481196, by rfl⟩ : syracuseStep 641595 = 962393) B962393
theorem B9226817 : Blo 638302 9226817 := bstep (se 2 (by rfl) ⟨3460056, by rfl⟩ : syracuseStep 9226817 = 6920113) B6920113
theorem B9226871 : Blo 638302 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B641671 : Blo 638302 641671 := bstep (se 1 (by rfl) ⟨481253, by rfl⟩ : syracuseStep 641671 = 962507) B962507
theorem B641679 : Blo 638302 641679 := bstep (se 1 (by rfl) ⟨481259, by rfl⟩ : syracuseStep 641679 = 962519) B962519
theorem B641723 : Blo 638302 641723 := bstep (se 1 (by rfl) ⟨481292, by rfl⟩ : syracuseStep 641723 = 962585) B962585
theorem B641799 : Blo 638302 641799 := bstep (se 1 (by rfl) ⟨481349, by rfl⟩ : syracuseStep 641799 = 962699) B962699
theorem B2312975 : Blo 638302 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B641807 : Blo 638302 641807 := bstep (se 1 (by rfl) ⟨481355, by rfl⟩ : syracuseStep 641807 = 962711) B962711
theorem B3296015 : Blo 638302 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B1329979 : Blo 638302 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B641851 : Blo 638302 641851 := bstep (se 1 (by rfl) ⟨481388, by rfl⟩ : syracuseStep 641851 = 962777) B962777
theorem B1297271 : Blo 638302 1297271 := bstep (se 1 (by rfl) ⟨972953, by rfl⟩ : syracuseStep 1297271 = 1945907) B1945907
theorem B641927 : Blo 638302 641927 := bstep (se 1 (by rfl) ⟨481445, by rfl⟩ : syracuseStep 641927 = 962891) B962891
theorem B641935 : Blo 638302 641935 := bstep (se 1 (by rfl) ⟨481451, by rfl⟩ : syracuseStep 641935 = 962903) B962903
theorem B641979 : Blo 638302 641979 := bstep (se 1 (by rfl) ⟨481484, by rfl⟩ : syracuseStep 641979 = 962969) B962969
theorem B642055 : Blo 638302 642055 := bstep (se 1 (by rfl) ⟨481541, by rfl⟩ : syracuseStep 642055 = 963083) B963083
theorem B642063 : Blo 638302 642063 := bstep (se 1 (by rfl) ⟨481547, by rfl⟩ : syracuseStep 642063 = 963095) B963095
theorem B642107 : Blo 638302 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B642183 : Blo 638302 642183 := bstep (se 1 (by rfl) ⟨481637, by rfl⟩ : syracuseStep 642183 = 963275) B963275
theorem B642191 : Blo 638302 642191 := bstep (se 1 (by rfl) ⟨481643, by rfl⟩ : syracuseStep 642191 = 963287) B963287
theorem B642235 : Blo 638302 642235 := bstep (se 1 (by rfl) ⟨481676, by rfl⟩ : syracuseStep 642235 = 963353) B963353
theorem B1821953 : Blo 638302 1821953 := bstep (se 2 (by rfl) ⟨683232, by rfl⟩ : syracuseStep 1821953 = 1366465) B1366465
theorem B4607441 : Blo 638302 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B1560217 : Blo 638302 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B1822409 : Blo 638302 1822409 := bstep (se 2 (by rfl) ⟨683403, by rfl⟩ : syracuseStep 1822409 = 1366807) B1366807
theorem B2314099 : Blo 638302 2314099 := bstep (se 1 (by rfl) ⟨1735574, by rfl⟩ : syracuseStep 2314099 = 3471149) B3471149
theorem B8212427 : Blo 638302 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B3657757 : Blo 638302 3657757 := bstep (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) B1371659
theorem B1822763 : Blo 638302 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B4870205 : Blo 638302 4870205 := bstep (se 3 (by rfl) ⟨913163, by rfl⟩ : syracuseStep 4870205 = 1826327) B1826327
theorem B1823161 : Blo 638302 1823161 := bstep (se 2 (by rfl) ⟨683685, by rfl⟩ : syracuseStep 1823161 = 1367371) B1367371
theorem B1364681 : Blo 638302 1364681 := bstep (se 2 (by rfl) ⟨511755, by rfl⟩ : syracuseStep 1364681 = 1023511) B1023511
theorem B5198681 : Blo 638302 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B3068857 : Blo 638302 3068857 := bstep (se 2 (by rfl) ⟨1150821, by rfl⟩ : syracuseStep 3068857 = 2301643) B2301643
theorem B2741201 : Blo 638302 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B8180747 : Blo 638302 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B1725455 : Blo 638302 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B807995 : Blo 638302 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B3691777 : Blo 638302 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B52450739 : Blo 638302 52450739 := bstep (se 1 (by rfl) ⟨39338054, by rfl⟩ : syracuseStep 52450739 = 78676109) B78676109
theorem B1824403 : Blo 638302 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B2054003 : Blo 638302 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B3233681 : Blo 638302 3233681 := bstep (se 2 (by rfl) ⟨1212630, by rfl⟩ : syracuseStep 3233681 = 2425261) B2425261
theorem B808967 : Blo 638302 808967 := bstep (se 1 (by rfl) ⟨606725, by rfl⟩ : syracuseStep 808967 = 1213451) B1213451
theorem B3889181 : Blo 638302 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B973001 : Blo 638302 973001 := bstep (se 2 (by rfl) ⟨364875, by rfl⟩ : syracuseStep 973001 = 729751) B729751
theorem B13162769 : Blo 638302 13162769 := bstep (se 2 (by rfl) ⟨4936038, by rfl⟩ : syracuseStep 13162769 = 9872077) B9872077
theorem B3070241 : Blo 638302 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B809615 : Blo 638302 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B1727261 : Blo 638302 1727261 := bstep (se 3 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 1727261 = 647723) B647723
theorem B1727531 : Blo 638302 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B1662137 : Blo 638302 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B974071 : Blo 638302 974071 := bstep (se 1 (by rfl) ⟨730553, by rfl⟩ : syracuseStep 974071 = 1461107) B1461107
theorem B1826077 : Blo 638302 1826077 := bstep (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) B684779
theorem B1826135 : Blo 638302 1826135 := bstep (se 1 (by rfl) ⟨1369601, by rfl⟩ : syracuseStep 1826135 = 2739203) B2739203
theorem B4873607 : Blo 638302 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B1367867 : Blo 638302 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B3497863 : Blo 638302 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B12443543 : Blo 638302 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B3235787 : Blo 638302 3235787 := bstep (se 1 (by rfl) ⟨2426840, by rfl⟩ : syracuseStep 3235787 = 4853681) B4853681
theorem B5202053 : Blo 638302 5202053 := bstep (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) B975385
theorem B909559 : Blo 638302 909559 := bstep (se 1 (by rfl) ⟨682169, by rfl⟩ : syracuseStep 909559 = 1364339) B1364339
theorem B3236111 : Blo 638302 3236111 := bstep (se 1 (by rfl) ⟨2427083, by rfl⟩ : syracuseStep 3236111 = 4854167) B4854167
theorem B6644227 : Blo 638302 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B909883 : Blo 638302 909883 := bstep (se 1 (by rfl) ⟨682412, by rfl⟩ : syracuseStep 909883 = 1364825) B1364825
theorem B975433 : Blo 638302 975433 := bstep (se 2 (by rfl) ⟨365787, by rfl⟩ : syracuseStep 975433 = 731575) B731575
theorem B2056823 : Blo 638302 2056823 := bstep (se 1 (by rfl) ⟨1542617, by rfl⟩ : syracuseStep 2056823 = 3085235) B3085235
theorem B1368875 : Blo 638302 1368875 := bstep (se 1 (by rfl) ⟨1026656, by rfl⟩ : syracuseStep 1368875 = 2053313) B2053313
theorem B1827785 : Blo 638302 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B910379 : Blo 638302 910379 := bstep (se 1 (by rfl) ⟨682784, by rfl⟩ : syracuseStep 910379 = 1365569) B1365569
theorem B812587 : Blo 638302 812587 := bstep (se 1 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 812587 = 1218881) B1218881
theorem B3237569 : Blo 638302 3237569 := bstep (se 2 (by rfl) ⟨1214088, by rfl⟩ : syracuseStep 3237569 = 2428177) B2428177
theorem B5334821 : Blo 638302 5334821 := bstep (se 4 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 5334821 = 1000279) B1000279
theorem B1828651 : Blo 638302 1828651 := bstep (se 1 (by rfl) ⟨1371488, by rfl⟩ : syracuseStep 1828651 = 2742977) B2742977
theorem B2156435 : Blo 638302 2156435 := bstep (se 1 (by rfl) ⟨1617326, by rfl⟩ : syracuseStep 2156435 = 3234653) B3234653
theorem B1828925 : Blo 638302 1828925 := bstep (se 3 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 1828925 = 685847) B685847
theorem B5859461 : Blo 638302 5859461 := bstep (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) B1098649
theorem B1534295 : Blo 638302 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B1370515 : Blo 638302 1370515 := bstep (se 1 (by rfl) ⟨1027886, by rfl⟩ : syracuseStep 1370515 = 2055773) B2055773
theorem B682511 : Blo 638302 682511 := bstep (se 1 (by rfl) ⟨511883, by rfl⟩ : syracuseStep 682511 = 1023767) B1023767
theorem B1436219 : Blo 638302 1436219 := bstep (se 1 (by rfl) ⟨1077164, by rfl⟩ : syracuseStep 1436219 = 2154329) B2154329
theorem B911945 : Blo 638302 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B10021495 : Blo 638302 10021495 := bstep (se 1 (by rfl) ⟨7516121, by rfl⟩ : syracuseStep 10021495 = 15032243) B15032243
theorem B1370771 : Blo 638302 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B1436345 : Blo 638302 1436345 := bstep (se 2 (by rfl) ⟨538629, by rfl⟩ : syracuseStep 1436345 = 1077259) B1077259
theorem B3238865 : Blo 638302 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B1436687 : Blo 638302 1436687 := bstep (se 1 (by rfl) ⟨1077515, by rfl⟩ : syracuseStep 1436687 = 2155031) B2155031
theorem B1436705 : Blo 638302 1436705 := bstep (se 2 (by rfl) ⟨538764, by rfl⟩ : syracuseStep 1436705 = 1077529) B1077529
theorem B912503 : Blo 638302 912503 := bstep (se 1 (by rfl) ⟨684377, by rfl⟩ : syracuseStep 912503 = 1368755) B1368755
theorem B2157839 : Blo 638302 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B1731899 : Blo 638302 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B1437047 : Blo 638302 1437047 := bstep (se 1 (by rfl) ⟨1077785, by rfl⟩ : syracuseStep 1437047 = 2155571) B2155571
theorem B912811 : Blo 638302 912811 := bstep (se 1 (by rfl) ⟨684608, by rfl⟩ : syracuseStep 912811 = 1369217) B1369217
theorem B8220113 : Blo 638302 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B2158109 : Blo 638302 2158109 := bstep (se 3 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 2158109 = 809291) B809291
theorem B15560221 : Blo 638302 15560221 := bstep (se 3 (by rfl) ⟨2917541, by rfl⟩ : syracuseStep 15560221 = 5835083) B5835083
theorem B1437227 : Blo 638302 1437227 := bstep (se 1 (by rfl) ⟨1077920, by rfl⟩ : syracuseStep 1437227 = 2155841) B2155841
theorem B4615973 : Blo 638302 4615973 := bstep (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) B865495
theorem B7401253 : Blo 638302 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B913295 : Blo 638302 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1437587 : Blo 638302 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B2813849 : Blo 638302 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1437641 : Blo 638302 1437641 := bstep (se 2 (by rfl) ⟨539115, by rfl⟩ : syracuseStep 1437641 = 1078231) B1078231
theorem B4616203 : Blo 638302 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B2256925 : Blo 638302 2256925 := bstep (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) B846347
theorem B1077367 : Blo 638302 1077367 := bstep (se 1 (by rfl) ⟨808025, by rfl⟩ : syracuseStep 1077367 = 1616051) B1616051
theorem B1077563 : Blo 638302 1077563 := bstep (se 1 (by rfl) ⟨808172, by rfl⟩ : syracuseStep 1077563 = 1616345) B1616345
theorem B4452893 : Blo 638302 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B6943333 : Blo 638302 6943333 := bstep (se 4 (by rfl) ⟨650937, by rfl⟩ : syracuseStep 6943333 = 1301875) B1301875
theorem B1438343 : Blo 638302 1438343 := bstep (se 1 (by rfl) ⟨1078757, by rfl⟩ : syracuseStep 1438343 = 2157515) B2157515
theorem B1077961 : Blo 638302 1077961 := bstep (se 2 (by rfl) ⟨404235, by rfl⟩ : syracuseStep 1077961 = 808471) B808471
theorem B1438523 : Blo 638302 1438523 := bstep (se 1 (by rfl) ⟨1078892, by rfl⟩ : syracuseStep 1438523 = 2157785) B2157785
theorem B2159513 : Blo 638302 2159513 := bstep (se 2 (by rfl) ⟨809817, by rfl⟩ : syracuseStep 2159513 = 1619635) B1619635
theorem B1438649 : Blo 638302 1438649 := bstep (se 2 (by rfl) ⟨539493, by rfl⟩ : syracuseStep 1438649 = 1078987) B1078987
theorem B3240971 : Blo 638302 3240971 := bstep (se 1 (by rfl) ⟨2430728, by rfl⟩ : syracuseStep 3240971 = 4861457) B4861457
theorem B3241133 : Blo 638302 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B1438991 : Blo 638302 1438991 := bstep (se 1 (by rfl) ⟨1079243, by rfl⟩ : syracuseStep 1438991 = 2158487) B2158487
theorem B1439009 : Blo 638302 1439009 := bstep (se 2 (by rfl) ⟨539628, by rfl⟩ : syracuseStep 1439009 = 1079257) B1079257
theorem B3470629 : Blo 638302 3470629 := bstep (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) B650743
theorem B7304579 : Blo 638302 7304579 := bstep (se 1 (by rfl) ⟨5478434, by rfl⟩ : syracuseStep 7304579 = 10956869) B10956869
theorem B1078663 : Blo 638302 1078663 := bstep (se 1 (by rfl) ⟨808997, by rfl⟩ : syracuseStep 1078663 = 1617995) B1617995
theorem B1537427 : Blo 638302 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B1734041 : Blo 638302 1734041 := bstep (se 2 (by rfl) ⟨650265, by rfl⟩ : syracuseStep 1734041 = 1300531) B1300531
theorem B718267 : Blo 638302 718267 := bstep (se 1 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 718267 = 1077401) B1077401
theorem B8451661 : Blo 638302 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B2160215 : Blo 638302 2160215 := bstep (se 1 (by rfl) ⟨1620161, by rfl⟩ : syracuseStep 2160215 = 3240323) B3240323
theorem B1439351 : Blo 638302 1439351 := bstep (se 1 (by rfl) ⟨1079513, by rfl⟩ : syracuseStep 1439351 = 2159027) B2159027
theorem B1439531 : Blo 638302 1439531 := bstep (se 1 (by rfl) ⟨1079648, by rfl⟩ : syracuseStep 1439531 = 2159297) B2159297
theorem B718735 : Blo 638302 718735 := bstep (se 1 (by rfl) ⟨539051, by rfl⟩ : syracuseStep 718735 = 1078103) B1078103
theorem B3340217 : Blo 638302 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B1079311 : Blo 638302 1079311 := bstep (se 1 (by rfl) ⟨809483, by rfl⟩ : syracuseStep 1079311 = 1618967) B1618967
theorem B7010327 : Blo 638302 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B37910551 : Blo 638302 37910551 := bstep (se 1 (by rfl) ⟨28432913, by rfl⟩ : syracuseStep 37910551 = 56865827) B56865827
theorem B2160701 : Blo 638302 2160701 := bstep (se 3 (by rfl) ⟨405131, by rfl⟩ : syracuseStep 2160701 = 810263) B810263
theorem B1439891 : Blo 638302 1439891 := bstep (se 1 (by rfl) ⟨1079918, by rfl⟩ : syracuseStep 1439891 = 2159837) B2159837
theorem B1439945 : Blo 638302 1439945 := bstep (se 2 (by rfl) ⟨539979, by rfl⟩ : syracuseStep 1439945 = 1079959) B1079959
theorem B719239 : Blo 638302 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B1079851 : Blo 638302 1079851 := bstep (se 1 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 1079851 = 1619777) B1619777
theorem B719419 : Blo 638302 719419 := bstep (se 1 (by rfl) ⟨539564, by rfl⟩ : syracuseStep 719419 = 1079129) B1079129
theorem B1079993 : Blo 638302 1079993 := bstep (se 2 (by rfl) ⟨404997, by rfl⟩ : syracuseStep 1079993 = 809995) B809995
theorem B4094657 : Blo 638302 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B3242753 : Blo 638302 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B7371557 : Blo 638302 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B13171571 : Blo 638302 13171571 := bstep (se 1 (by rfl) ⟨9878678, by rfl⟩ : syracuseStep 13171571 = 19757357) B19757357
theorem B1440647 : Blo 638302 1440647 := bstep (se 1 (by rfl) ⟨1080485, by rfl⟩ : syracuseStep 1440647 = 2160971) B2160971
theorem B719887 : Blo 638302 719887 := bstep (se 1 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 719887 = 1079831) B1079831
theorem B1440827 : Blo 638302 1440827 := bstep (se 1 (by rfl) ⟨1080620, by rfl⟩ : syracuseStep 1440827 = 2161241) B2161241
theorem B1735739 : Blo 638302 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B1440953 : Blo 638302 1440953 := bstep (se 2 (by rfl) ⟨540357, by rfl⟩ : syracuseStep 1440953 = 1080715) B1080715
theorem B1080695 : Blo 638302 1080695 := bstep (se 1 (by rfl) ⟨810521, by rfl⟩ : syracuseStep 1080695 = 1621043) B1621043
theorem B2162105 : Blo 638302 2162105 := bstep (se 2 (by rfl) ⟨810789, by rfl⟩ : syracuseStep 2162105 = 1621579) B1621579
theorem B720391 : Blo 638302 720391 := bstep (se 1 (by rfl) ⟨540293, by rfl⟩ : syracuseStep 720391 = 1080587) B1080587
theorem B1441295 : Blo 638302 1441295 := bstep (se 1 (by rfl) ⟨1080971, by rfl⟩ : syracuseStep 1441295 = 2161943) B2161943
theorem B1441313 : Blo 638302 1441313 := bstep (se 2 (by rfl) ⟨540492, by rfl⟩ : syracuseStep 1441313 = 1080985) B1080985
theorem B3243563 : Blo 638302 3243563 := bstep (se 1 (by rfl) ⟨2432672, by rfl⟩ : syracuseStep 3243563 = 4865345) B4865345
theorem B1212023 : Blo 638302 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B720571 : Blo 638302 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B1212175 : Blo 638302 1212175 := bstep (se 1 (by rfl) ⟨909131, by rfl⟩ : syracuseStep 1212175 = 1818263) B1818263
theorem B1081147 : Blo 638302 1081147 := bstep (se 1 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 1081147 = 1621721) B1621721
theorem B1441655 : Blo 638302 1441655 := bstep (se 1 (by rfl) ⟨1081241, by rfl⟩ : syracuseStep 1441655 = 2162483) B2162483
theorem B2424761 : Blo 638302 2424761 := bstep (se 2 (by rfl) ⟨909285, by rfl⟩ : syracuseStep 2424761 = 1818571) B1818571
theorem B1081289 : Blo 638302 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B1441799 : Blo 638302 1441799 := bstep (se 1 (by rfl) ⟨1081349, by rfl⟩ : syracuseStep 1441799 = 2162699) B2162699
theorem B1441871 : Blo 638302 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B4096115 : Blo 638302 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B15532195 : Blo 638302 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B2425079 : Blo 638302 2425079 := bstep (se 1 (by rfl) ⟨1818809, by rfl⟩ : syracuseStep 2425079 = 3637619) B3637619
theorem B1212745 : Blo 638302 1212745 := bstep (se 2 (by rfl) ⟨454779, by rfl⟩ : syracuseStep 1212745 = 909559) B909559
theorem B1081775 : Blo 638302 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B721327 : Blo 638302 721327 := bstep (se 1 (by rfl) ⟨540995, by rfl⟩ : syracuseStep 721327 = 1081991) B1081991
theorem B1442267 : Blo 638302 1442267 := bstep (se 1 (by rfl) ⟨1081700, by rfl⟩ : syracuseStep 1442267 = 2163401) B2163401
theorem B2163239 : Blo 638302 2163239 := bstep (se 1 (by rfl) ⟨1622429, by rfl⟩ : syracuseStep 2163239 = 3244859) B3244859
theorem B2163347 : Blo 638302 2163347 := bstep (se 1 (by rfl) ⟨1622510, by rfl⟩ : syracuseStep 2163347 = 3245021) B3245021
theorem B1082207 : Blo 638302 1082207 := bstep (se 1 (by rfl) ⟨811655, by rfl⟩ : syracuseStep 1082207 = 1623311) B1623311
theorem B721759 : Blo 638302 721759 := bstep (se 1 (by rfl) ⟨541319, by rfl⟩ : syracuseStep 721759 = 1082639) B1082639
theorem B2163563 : Blo 638302 2163563 := bstep (se 1 (by rfl) ⟨1622672, by rfl⟩ : syracuseStep 2163563 = 3245345) B3245345
theorem B2163617 : Blo 638302 2163617 := bstep (se 2 (by rfl) ⟨811356, by rfl⟩ : syracuseStep 2163617 = 1622713) B1622713
theorem B1442735 : Blo 638302 1442735 := bstep (se 1 (by rfl) ⟨1082051, by rfl⟩ : syracuseStep 1442735 = 2164103) B2164103
theorem B15205427 : Blo 638302 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1442987 : Blo 638302 1442987 := bstep (se 1 (by rfl) ⟨1082240, by rfl⟩ : syracuseStep 1442987 = 2164481) B2164481
theorem B2426051 : Blo 638302 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B722119 : Blo 638302 722119 := bstep (se 1 (by rfl) ⟨541589, by rfl⟩ : syracuseStep 722119 = 1083179) B1083179
theorem B1082767 : Blo 638302 1082767 := bstep (se 1 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 1082767 = 1624151) B1624151
theorem B2164211 : Blo 638302 2164211 := bstep (se 1 (by rfl) ⟨1623158, by rfl⟩ : syracuseStep 2164211 = 3246317) B3246317
theorem B20809237 : Blo 638302 20809237 := bstep (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) B975433
theorem B2426507 : Blo 638302 2426507 := bstep (se 1 (by rfl) ⟨1819880, by rfl⟩ : syracuseStep 2426507 = 3639761) B3639761
theorem B14419603 : Blo 638302 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B1443527 : Blo 638302 1443527 := bstep (se 1 (by rfl) ⟨1082645, by rfl⟩ : syracuseStep 1443527 = 2165291) B2165291
theorem B2426719 : Blo 638302 2426719 := bstep (se 1 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 2426719 = 3640079) B3640079
theorem B2197343 : Blo 638302 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B2164751 : Blo 638302 2164751 := bstep (se 1 (by rfl) ⟨1623563, by rfl⟩ : syracuseStep 2164751 = 3247127) B3247127
theorem B1083449 : Blo 638302 1083449 := bstep (se 2 (by rfl) ⟨406293, by rfl⟩ : syracuseStep 1083449 = 812587) B812587
theorem B2492891 : Blo 638302 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B1214939 : Blo 638302 1214939 := bstep (se 1 (by rfl) ⟨911204, by rfl⟩ : syracuseStep 1214939 = 1822409) B1822409
theorem B1444391 : Blo 638302 1444391 := bstep (se 1 (by rfl) ⟨1083293, by rfl⟩ : syracuseStep 1444391 = 2166587) B2166587
theorem B2165345 : Blo 638302 2165345 := bstep (se 2 (by rfl) ⟨812004, by rfl⟩ : syracuseStep 2165345 = 1624009) B1624009
theorem B5474951 : Blo 638302 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B1215175 : Blo 638302 1215175 := bstep (se 1 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 1215175 = 1822763) B1822763
theorem B3246803 : Blo 638302 3246803 := bstep (se 1 (by rfl) ⟨2435102, by rfl⟩ : syracuseStep 3246803 = 4870205) B4870205
theorem B2427677 : Blo 638302 2427677 := bstep (se 3 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 2427677 = 910379) B910379
theorem B2427691 : Blo 638302 2427691 := bstep (se 1 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 2427691 = 3641537) B3641537
theorem B1444715 : Blo 638302 1444715 := bstep (se 1 (by rfl) ⟨1083536, by rfl⟩ : syracuseStep 1444715 = 2167073) B2167073
theorem B1444769 : Blo 638302 1444769 := bstep (se 2 (by rfl) ⟨541788, by rfl⟩ : syracuseStep 1444769 = 1083577) B1083577
theorem B4852709 : Blo 638302 4852709 := bstep (se 4 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 4852709 = 909883) B909883
theorem B2591801 : Blo 638302 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B1445111 : Blo 638302 1445111 := bstep (se 1 (by rfl) ⟨1083833, by rfl⟩ : syracuseStep 1445111 = 2167667) B2167667
theorem B1150303 : Blo 638302 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B34967159 : Blo 638302 34967159 := bstep (se 1 (by rfl) ⟨26225369, by rfl⟩ : syracuseStep 34967159 = 52450739) B52450739
theorem B1183403 : Blo 638302 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B4099805 : Blo 638302 4099805 := bstep (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) B1537427
theorem B1773305 : Blo 638302 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B2166803 : Blo 638302 2166803 := bstep (se 1 (by rfl) ⟨1625102, by rfl⟩ : syracuseStep 2166803 = 3250205) B3250205
theorem B20713745 : Blo 638302 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B2167127 : Blo 638302 2167127 := bstep (se 1 (by rfl) ⟨1625345, by rfl⟩ : syracuseStep 2167127 = 3250691) B3250691
theorem B1151507 : Blo 638302 1151507 := bstep (se 1 (by rfl) ⟨863630, by rfl⟩ : syracuseStep 1151507 = 1727261) B1727261
theorem B1217081 : Blo 638302 1217081 := bstep (se 2 (by rfl) ⟨456405, by rfl⟩ : syracuseStep 1217081 = 912811) B912811
theorem B1151687 : Blo 638302 1151687 := bstep (se 1 (by rfl) ⟨863765, by rfl⟩ : syracuseStep 1151687 = 1727531) B1727531
theorem B20746961 : Blo 638302 20746961 := bstep (se 2 (by rfl) ⟨7780110, by rfl⟩ : syracuseStep 20746961 = 15560221) B15560221
theorem B1217423 : Blo 638302 1217423 := bstep (se 1 (by rfl) ⟨913067, by rfl⟩ : syracuseStep 1217423 = 1826135) B1826135
theorem B3249071 : Blo 638302 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B5477341 : Blo 638302 5477341 := bstep (se 3 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 5477341 = 2054003) B2054003
theorem B9868337 : Blo 638302 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B3085465 : Blo 638302 3085465 := bstep (se 2 (by rfl) ⟨1157049, by rfl⟩ : syracuseStep 3085465 = 2314099) B2314099
theorem B8295695 : Blo 638302 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B4920955 : Blo 638302 4920955 := bstep (se 1 (by rfl) ⟨3690716, by rfl⟩ : syracuseStep 4920955 = 7381433) B7381433
theorem B2430881 : Blo 638302 2430881 := bstep (se 2 (by rfl) ⟨911580, by rfl⟩ : syracuseStep 2430881 = 1823161) B1823161
theorem B1153273 : Blo 638302 1153273 := bstep (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) B864955
theorem B1219283 : Blo 638302 1219283 := bstep (se 1 (by rfl) ⟨914462, by rfl⟩ : syracuseStep 1219283 = 1828925) B1828925
theorem B2595577 : Blo 638302 2595577 := bstep (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) B1946683
theorem B3906307 : Blo 638302 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B2431853 : Blo 638302 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B1022863 : Blo 638302 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B4922369 : Blo 638302 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B957479 : Blo 638302 957479 := bstep (se 1 (by rfl) ⟨718109, by rfl⟩ : syracuseStep 957479 = 1436219) B1436219
theorem B4627505 : Blo 638302 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B957563 : Blo 638302 957563 := bstep (se 1 (by rfl) ⟨718172, by rfl⟩ : syracuseStep 957563 = 1436345) B1436345
theorem B957689 : Blo 638302 957689 := bstep (se 2 (by rfl) ⟨359133, by rfl⟩ : syracuseStep 957689 = 718267) B718267
theorem B957791 : Blo 638302 957791 := bstep (se 1 (by rfl) ⟨718343, by rfl⟩ : syracuseStep 957791 = 1436687) B1436687
theorem B957803 : Blo 638302 957803 := bstep (se 1 (by rfl) ⟨718352, by rfl⟩ : syracuseStep 957803 = 1436705) B1436705
theorem B6167933 : Blo 638302 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B2432537 : Blo 638302 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B2432551 : Blo 638302 2432551 := bstep (se 1 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 2432551 = 3648827) B3648827
theorem B958031 : Blo 638302 958031 := bstep (se 1 (by rfl) ⟨718523, by rfl⟩ : syracuseStep 958031 = 1437047) B1437047
theorem B1154657 : Blo 638302 1154657 := bstep (se 2 (by rfl) ⟨432996, by rfl⟩ : syracuseStep 1154657 = 865993) B865993
theorem B5480075 : Blo 638302 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B958151 : Blo 638302 958151 := bstep (se 1 (by rfl) ⟨718613, by rfl⟩ : syracuseStep 958151 = 1437227) B1437227
theorem B958313 : Blo 638302 958313 := bstep (se 2 (by rfl) ⟨359367, by rfl⟩ : syracuseStep 958313 = 718735) B718735
theorem B958391 : Blo 638302 958391 := bstep (se 1 (by rfl) ⟨718793, by rfl⟩ : syracuseStep 958391 = 1437587) B1437587
theorem B1875899 : Blo 638302 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B958427 : Blo 638302 958427 := bstep (se 1 (by rfl) ⟨718820, by rfl⟩ : syracuseStep 958427 = 1437641) B1437641
theorem B729167 : Blo 638302 729167 := bstep (se 1 (by rfl) ⟨546875, by rfl⟩ : syracuseStep 729167 = 1093751) B1093751
theorem B2433341 : Blo 638302 2433341 := bstep (se 3 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 2433341 = 912503) B912503
theorem B958895 : Blo 638302 958895 := bstep (se 1 (by rfl) ⟨719171, by rfl⟩ : syracuseStep 958895 = 1438343) B1438343
theorem B2302451 : Blo 638302 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B2433523 : Blo 638302 2433523 := bstep (se 1 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 2433523 = 3650285) B3650285
theorem B958985 : Blo 638302 958985 := bstep (se 2 (by rfl) ⟨359619, by rfl⟩ : syracuseStep 958985 = 719239) B719239
theorem B959015 : Blo 638302 959015 := bstep (se 1 (by rfl) ⟨719261, by rfl⟩ : syracuseStep 959015 = 1438523) B1438523
theorem B959099 : Blo 638302 959099 := bstep (se 1 (by rfl) ⟨719324, by rfl⟩ : syracuseStep 959099 = 1438649) B1438649
theorem B4858541 : Blo 638302 4858541 := bstep (se 3 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 4858541 = 1821953) B1821953
theorem B2630333 : Blo 638302 2630333 := bstep (se 3 (by rfl) ⟨493187, by rfl⟩ : syracuseStep 2630333 = 986375) B986375
theorem B959225 : Blo 638302 959225 := bstep (se 2 (by rfl) ⟨359709, by rfl⟩ : syracuseStep 959225 = 719419) B719419
theorem B959327 : Blo 638302 959327 := bstep (se 1 (by rfl) ⟨719495, by rfl⟩ : syracuseStep 959327 = 1438991) B1438991
theorem B959339 : Blo 638302 959339 := bstep (se 1 (by rfl) ⟨719504, by rfl⟩ : syracuseStep 959339 = 1439009) B1439009
theorem B1156027 : Blo 638302 1156027 := bstep (se 1 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 1156027 = 1734041) B1734041
theorem B959567 : Blo 638302 959567 := bstep (se 1 (by rfl) ⟨719675, by rfl⟩ : syracuseStep 959567 = 1439351) B1439351
theorem B2598041 : Blo 638302 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B959687 : Blo 638302 959687 := bstep (se 1 (by rfl) ⟨719765, by rfl⟩ : syracuseStep 959687 = 1439531) B1439531
theorem B1025273 : Blo 638302 1025273 := bstep (se 2 (by rfl) ⟨384477, by rfl⟩ : syracuseStep 1025273 = 768955) B768955
theorem B959849 : Blo 638302 959849 := bstep (se 2 (by rfl) ⟨359943, by rfl⟩ : syracuseStep 959849 = 719887) B719887
theorem B27698597 : Blo 638302 27698597 := bstep (se 4 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 27698597 = 5193487) B5193487
theorem B959927 : Blo 638302 959927 := bstep (se 1 (by rfl) ⟨719945, by rfl⟩ : syracuseStep 959927 = 1439891) B1439891
theorem B959963 : Blo 638302 959963 := bstep (se 1 (by rfl) ⟨719972, by rfl⟩ : syracuseStep 959963 = 1439945) B1439945
theorem B2434769 : Blo 638302 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B2729771 : Blo 638302 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B960431 : Blo 638302 960431 := bstep (se 1 (by rfl) ⟨720323, by rfl⟩ : syracuseStep 960431 = 1440647) B1440647
theorem B960521 : Blo 638302 960521 := bstep (se 2 (by rfl) ⟨360195, by rfl⟩ : syracuseStep 960521 = 720391) B720391
theorem B960551 : Blo 638302 960551 := bstep (se 1 (by rfl) ⟨720413, by rfl⟩ : syracuseStep 960551 = 1440827) B1440827
theorem B1157159 : Blo 638302 1157159 := bstep (se 1 (by rfl) ⟨867869, by rfl⟩ : syracuseStep 1157159 = 1735739) B1735739
theorem B1976399 : Blo 638302 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B960635 : Blo 638302 960635 := bstep (se 1 (by rfl) ⟨720476, by rfl⟩ : syracuseStep 960635 = 1440953) B1440953
theorem B960761 : Blo 638302 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B960863 : Blo 638302 960863 := bstep (se 1 (by rfl) ⟨720647, by rfl⟩ : syracuseStep 960863 = 1441295) B1441295
theorem B1616233 : Blo 638302 1616233 := bstep (se 2 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 1616233 = 1212175) B1212175
theorem B960875 : Blo 638302 960875 := bstep (se 1 (by rfl) ⟨720656, by rfl⟩ : syracuseStep 960875 = 1441313) B1441313
theorem B2435453 : Blo 638302 2435453 := bstep (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) B913295
theorem B4663817 : Blo 638302 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B961103 : Blo 638302 961103 := bstep (se 1 (by rfl) ⟨720827, by rfl⟩ : syracuseStep 961103 = 1441655) B1441655
theorem B1616507 : Blo 638302 1616507 := bstep (se 1 (by rfl) ⟨1212380, by rfl⟩ : syracuseStep 1616507 = 2424761) B2424761
theorem B961223 : Blo 638302 961223 := bstep (se 1 (by rfl) ⟨720917, by rfl⟩ : syracuseStep 961223 = 1441835) B1441835
theorem B961385 : Blo 638302 961385 := bstep (se 2 (by rfl) ⟨360519, by rfl⟩ : syracuseStep 961385 = 721039) B721039
theorem B5188535 : Blo 638302 5188535 := bstep (se 1 (by rfl) ⟨3891401, by rfl⟩ : syracuseStep 5188535 = 7782803) B7782803
theorem B961463 : Blo 638302 961463 := bstep (se 1 (by rfl) ⟨721097, by rfl⟩ : syracuseStep 961463 = 1442195) B1442195
theorem B961499 : Blo 638302 961499 := bstep (se 1 (by rfl) ⟨721124, by rfl⟩ : syracuseStep 961499 = 1442249) B1442249
theorem B4860971 : Blo 638302 4860971 := bstep (se 1 (by rfl) ⟨3645728, by rfl⟩ : syracuseStep 4860971 = 7291457) B7291457
theorem B2436439 : Blo 638302 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B8858969 : Blo 638302 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B961967 : Blo 638302 961967 := bstep (se 1 (by rfl) ⟨721475, by rfl⟩ : syracuseStep 961967 = 1442951) B1442951
theorem B962057 : Blo 638302 962057 := bstep (se 2 (by rfl) ⟨360771, by rfl⟩ : syracuseStep 962057 = 721543) B721543
theorem B1945127 : Blo 638302 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B962087 : Blo 638302 962087 := bstep (se 1 (by rfl) ⟨721565, by rfl⟩ : syracuseStep 962087 = 1443131) B1443131
theorem B118042181 : Blo 638302 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B962171 : Blo 638302 962171 := bstep (se 1 (by rfl) ⟨721628, by rfl⟩ : syracuseStep 962171 = 1443257) B1443257
theorem B2436743 : Blo 638302 2436743 := bstep (se 1 (by rfl) ⟨1827557, by rfl⟩ : syracuseStep 2436743 = 3655115) B3655115
theorem B2731769 : Blo 638302 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B962297 : Blo 638302 962297 := bstep (se 2 (by rfl) ⟨360861, by rfl⟩ : syracuseStep 962297 = 721723) B721723
theorem B962399 : Blo 638302 962399 := bstep (se 1 (by rfl) ⟨721799, by rfl⟩ : syracuseStep 962399 = 1443599) B1443599
theorem B962411 : Blo 638302 962411 := bstep (se 1 (by rfl) ⟨721808, by rfl⟩ : syracuseStep 962411 = 1443617) B1443617
theorem B4927517 : Blo 638302 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B962639 : Blo 638302 962639 := bstep (se 1 (by rfl) ⟨721979, by rfl⟩ : syracuseStep 962639 = 1443959) B1443959
theorem B2437199 : Blo 638302 2437199 := bstep (se 1 (by rfl) ⟨1827899, by rfl⟩ : syracuseStep 2437199 = 3655799) B3655799
theorem B962759 : Blo 638302 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B962921 : Blo 638302 962921 := bstep (se 2 (by rfl) ⟨361095, by rfl⟩ : syracuseStep 962921 = 722191) B722191
theorem B1618319 : Blo 638302 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B962999 : Blo 638302 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B963035 : Blo 638302 963035 := bstep (se 1 (by rfl) ⟨722276, by rfl⟩ : syracuseStep 963035 = 1444553) B1444553
theorem B864847 : Blo 638302 864847 := bstep (se 1 (by rfl) ⟨648635, by rfl⟩ : syracuseStep 864847 = 1297271) B1297271
theorem B1618643 : Blo 638302 1618643 := bstep (se 1 (by rfl) ⟨1213982, by rfl⟩ : syracuseStep 1618643 = 2427965) B2427965
theorem B766903 : Blo 638302 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B2438201 : Blo 638302 2438201 := bstep (se 2 (by rfl) ⟨914325, by rfl⟩ : syracuseStep 2438201 = 1828651) B1828651
theorem B767407 : Blo 638302 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B4601441 : Blo 638302 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B20821697 : Blo 638302 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B2471639 : Blo 638302 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B1095611 : Blo 638302 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B5453831 : Blo 638302 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B4110365 : Blo 638302 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B2734195 : Blo 638302 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B2046827 : Blo 638302 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B1620911 : Blo 638302 1620911 := bstep (se 1 (by rfl) ⟨1215683, by rfl⟩ : syracuseStep 1620911 = 2431367) B2431367
theorem B7781669 : Blo 638302 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B638303 : Blo 638302 638303 := bstep (se 1 (by rfl) ⟨478727, by rfl⟩ : syracuseStep 638303 = 957455) B957455
theorem B638331 : Blo 638302 638331 := bstep (se 1 (by rfl) ⟨478748, by rfl⟩ : syracuseStep 638331 = 957497) B957497
theorem B638383 : Blo 638302 638383 := bstep (se 1 (by rfl) ⟨478787, by rfl⟩ : syracuseStep 638383 = 957575) B957575
theorem B638407 : Blo 638302 638407 := bstep (se 1 (by rfl) ⟨478805, by rfl⟩ : syracuseStep 638407 = 957611) B957611
theorem B638427 : Blo 638302 638427 := bstep (se 1 (by rfl) ⟨478820, by rfl⟩ : syracuseStep 638427 = 957641) B957641
theorem B1621529 : Blo 638302 1621529 := bstep (se 2 (by rfl) ⟨608073, by rfl⟩ : syracuseStep 1621529 = 1216147) B1216147
theorem B2080289 : Blo 638302 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B638503 : Blo 638302 638503 := bstep (se 1 (by rfl) ⟨478877, by rfl⟩ : syracuseStep 638503 = 957755) B957755
theorem B638543 : Blo 638302 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B638559 : Blo 638302 638559 := bstep (se 1 (by rfl) ⟨478919, by rfl⟩ : syracuseStep 638559 = 957839) B957839
theorem B638587 : Blo 638302 638587 := bstep (se 1 (by rfl) ⟨478940, by rfl⟩ : syracuseStep 638587 = 957881) B957881
theorem B638639 : Blo 638302 638639 := bstep (se 1 (by rfl) ⟨478979, by rfl⟩ : syracuseStep 638639 = 957959) B957959
theorem B638663 : Blo 638302 638663 := bstep (se 1 (by rfl) ⟨478997, by rfl⟩ : syracuseStep 638663 = 957995) B957995
theorem B638683 : Blo 638302 638683 := bstep (se 1 (by rfl) ⟨479012, by rfl⟩ : syracuseStep 638683 = 958025) B958025
theorem B638759 : Blo 638302 638759 := bstep (se 1 (by rfl) ⟨479069, by rfl⟩ : syracuseStep 638759 = 958139) B958139
theorem B638799 : Blo 638302 638799 := bstep (se 1 (by rfl) ⟨479099, by rfl⟩ : syracuseStep 638799 = 958199) B958199
theorem B638815 : Blo 638302 638815 := bstep (se 1 (by rfl) ⟨479111, by rfl⟩ : syracuseStep 638815 = 958223) B958223
theorem B638843 : Blo 638302 638843 := bstep (se 1 (by rfl) ⟨479132, by rfl⟩ : syracuseStep 638843 = 958265) B958265
theorem B638895 : Blo 638302 638895 := bstep (se 1 (by rfl) ⟨479171, by rfl⟩ : syracuseStep 638895 = 958343) B958343
theorem B1949627 : Blo 638302 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B638919 : Blo 638302 638919 := bstep (se 1 (by rfl) ⟨479189, by rfl⟩ : syracuseStep 638919 = 958379) B958379
theorem B638939 : Blo 638302 638939 := bstep (se 1 (by rfl) ⟨479204, by rfl⟩ : syracuseStep 638939 = 958409) B958409
theorem B2736143 : Blo 638302 2736143 := bstep (se 1 (by rfl) ⟨2052107, by rfl⟩ : syracuseStep 2736143 = 4104215) B4104215
theorem B639015 : Blo 638302 639015 := bstep (se 1 (by rfl) ⟨479261, by rfl⟩ : syracuseStep 639015 = 958523) B958523
theorem B10371149 : Blo 638302 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B639055 : Blo 638302 639055 := bstep (se 1 (by rfl) ⟨479291, by rfl⟩ : syracuseStep 639055 = 958583) B958583
theorem B639071 : Blo 638302 639071 := bstep (se 1 (by rfl) ⟨479303, by rfl⟩ : syracuseStep 639071 = 958607) B958607
theorem B639099 : Blo 638302 639099 := bstep (se 1 (by rfl) ⟨479324, by rfl⟩ : syracuseStep 639099 = 958649) B958649
theorem B639151 : Blo 638302 639151 := bstep (se 1 (by rfl) ⟨479363, by rfl⟩ : syracuseStep 639151 = 958727) B958727
theorem B639175 : Blo 638302 639175 := bstep (se 1 (by rfl) ⟨479381, by rfl⟩ : syracuseStep 639175 = 958763) B958763
theorem B639195 : Blo 638302 639195 := bstep (se 1 (by rfl) ⟨479396, by rfl⟩ : syracuseStep 639195 = 958793) B958793
theorem B639271 : Blo 638302 639271 := bstep (se 1 (by rfl) ⟨479453, by rfl⟩ : syracuseStep 639271 = 958907) B958907
theorem B639311 : Blo 638302 639311 := bstep (se 1 (by rfl) ⟨479483, by rfl⟩ : syracuseStep 639311 = 958967) B958967
theorem B639327 : Blo 638302 639327 := bstep (se 1 (by rfl) ⟨479495, by rfl⟩ : syracuseStep 639327 = 958991) B958991
theorem B639355 : Blo 638302 639355 := bstep (se 1 (by rfl) ⟨479516, by rfl⟩ : syracuseStep 639355 = 959033) B959033
theorem B639407 : Blo 638302 639407 := bstep (se 1 (by rfl) ⟨479555, by rfl⟩ : syracuseStep 639407 = 959111) B959111
theorem B639431 : Blo 638302 639431 := bstep (se 1 (by rfl) ⟨479573, by rfl⟩ : syracuseStep 639431 = 959147) B959147
theorem B639451 : Blo 638302 639451 := bstep (se 1 (by rfl) ⟨479588, by rfl⟩ : syracuseStep 639451 = 959177) B959177
theorem B9355799 : Blo 638302 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B639527 : Blo 638302 639527 := bstep (se 1 (by rfl) ⟨479645, by rfl⟩ : syracuseStep 639527 = 959291) B959291
theorem B639567 : Blo 638302 639567 := bstep (se 1 (by rfl) ⟨479675, by rfl⟩ : syracuseStep 639567 = 959351) B959351
theorem B639583 : Blo 638302 639583 := bstep (se 1 (by rfl) ⟨479687, by rfl⟩ : syracuseStep 639583 = 959375) B959375
theorem B639611 : Blo 638302 639611 := bstep (se 1 (by rfl) ⟨479708, by rfl⟩ : syracuseStep 639611 = 959417) B959417
theorem B639663 : Blo 638302 639663 := bstep (se 1 (by rfl) ⟨479747, by rfl⟩ : syracuseStep 639663 = 959495) B959495
theorem B639687 : Blo 638302 639687 := bstep (se 1 (by rfl) ⟨479765, by rfl⟩ : syracuseStep 639687 = 959531) B959531
theorem B639707 : Blo 638302 639707 := bstep (se 1 (by rfl) ⟨479780, by rfl⟩ : syracuseStep 639707 = 959561) B959561
theorem B639783 : Blo 638302 639783 := bstep (se 1 (by rfl) ⟨479837, by rfl⟩ : syracuseStep 639783 = 959675) B959675
theorem B9257777 : Blo 638302 9257777 := bstep (se 2 (by rfl) ⟨3471666, by rfl⟩ : syracuseStep 9257777 = 6943333) B6943333
theorem B639823 : Blo 638302 639823 := bstep (se 1 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 639823 = 959735) B959735
theorem B639839 : Blo 638302 639839 := bstep (se 1 (by rfl) ⟨479879, by rfl⟩ : syracuseStep 639839 = 959759) B959759
theorem B639867 : Blo 638302 639867 := bstep (se 1 (by rfl) ⟨479900, by rfl⟩ : syracuseStep 639867 = 959801) B959801
theorem B639919 : Blo 638302 639919 := bstep (se 1 (by rfl) ⟨479939, by rfl⟩ : syracuseStep 639919 = 959879) B959879
theorem B639943 : Blo 638302 639943 := bstep (se 1 (by rfl) ⟨479957, by rfl⟩ : syracuseStep 639943 = 959915) B959915
theorem B639963 : Blo 638302 639963 := bstep (se 1 (by rfl) ⟨479972, by rfl⟩ : syracuseStep 639963 = 959945) B959945
theorem B640039 : Blo 638302 640039 := bstep (se 1 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 640039 = 960059) B960059
theorem B640079 : Blo 638302 640079 := bstep (se 1 (by rfl) ⟨480059, by rfl⟩ : syracuseStep 640079 = 960119) B960119
theorem B640095 : Blo 638302 640095 := bstep (se 1 (by rfl) ⟨480071, by rfl⟩ : syracuseStep 640095 = 960143) B960143
theorem B640123 : Blo 638302 640123 := bstep (se 1 (by rfl) ⟨480092, by rfl⟩ : syracuseStep 640123 = 960185) B960185
theorem B640175 : Blo 638302 640175 := bstep (se 1 (by rfl) ⟨480131, by rfl⟩ : syracuseStep 640175 = 960263) B960263
theorem B3556547 : Blo 638302 3556547 := bstep (se 1 (by rfl) ⟨2667410, by rfl⟩ : syracuseStep 3556547 = 5334821) B5334821
theorem B640199 : Blo 638302 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B640219 : Blo 638302 640219 := bstep (se 1 (by rfl) ⟨480164, by rfl⟩ : syracuseStep 640219 = 960329) B960329
theorem B640295 : Blo 638302 640295 := bstep (se 1 (by rfl) ⟨480221, by rfl⟩ : syracuseStep 640295 = 960443) B960443
theorem B640335 : Blo 638302 640335 := bstep (se 1 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 640335 = 960503) B960503
theorem B640351 : Blo 638302 640351 := bstep (se 1 (by rfl) ⟨480263, by rfl⟩ : syracuseStep 640351 = 960527) B960527
theorem B640379 : Blo 638302 640379 := bstep (se 1 (by rfl) ⟨480284, by rfl⟩ : syracuseStep 640379 = 960569) B960569
theorem B1820029 : Blo 638302 1820029 := bstep (se 3 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 1820029 = 682511) B682511
theorem B640431 : Blo 638302 640431 := bstep (se 1 (by rfl) ⟨480323, by rfl⟩ : syracuseStep 640431 = 960647) B960647
theorem B640455 : Blo 638302 640455 := bstep (se 1 (by rfl) ⟨480341, by rfl⟩ : syracuseStep 640455 = 960683) B960683
theorem B640475 : Blo 638302 640475 := bstep (se 1 (by rfl) ⟨480356, by rfl⟩ : syracuseStep 640475 = 960713) B960713
theorem B640551 : Blo 638302 640551 := bstep (se 1 (by rfl) ⟨480413, by rfl⟩ : syracuseStep 640551 = 960827) B960827
theorem B640591 : Blo 638302 640591 := bstep (se 1 (by rfl) ⟨480443, by rfl⟩ : syracuseStep 640591 = 960887) B960887
theorem B640607 : Blo 638302 640607 := bstep (se 1 (by rfl) ⟨480455, by rfl⟩ : syracuseStep 640607 = 960911) B960911
theorem B640635 : Blo 638302 640635 := bstep (se 1 (by rfl) ⟨480476, by rfl⟩ : syracuseStep 640635 = 960953) B960953
theorem B640687 : Blo 638302 640687 := bstep (se 1 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 640687 = 961031) B961031
theorem B2049725 : Blo 638302 2049725 := bstep (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) B768647
theorem B640711 : Blo 638302 640711 := bstep (se 1 (by rfl) ⟨480533, by rfl⟩ : syracuseStep 640711 = 961067) B961067
theorem B3655367 : Blo 638302 3655367 := bstep (se 1 (by rfl) ⟨2741525, by rfl⟩ : syracuseStep 3655367 = 5483051) B5483051
theorem B640731 : Blo 638302 640731 := bstep (se 1 (by rfl) ⟨480548, by rfl⟩ : syracuseStep 640731 = 961097) B961097
theorem B640807 : Blo 638302 640807 := bstep (se 1 (by rfl) ⟨480605, by rfl⟩ : syracuseStep 640807 = 961211) B961211
theorem B640847 : Blo 638302 640847 := bstep (se 1 (by rfl) ⟨480635, by rfl⟩ : syracuseStep 640847 = 961271) B961271
theorem B640863 : Blo 638302 640863 := bstep (se 1 (by rfl) ⟨480647, by rfl⟩ : syracuseStep 640863 = 961295) B961295
theorem B640891 : Blo 638302 640891 := bstep (se 1 (by rfl) ⟨480668, by rfl⟩ : syracuseStep 640891 = 961337) B961337
theorem B640943 : Blo 638302 640943 := bstep (se 1 (by rfl) ⟨480707, by rfl⟩ : syracuseStep 640943 = 961415) B961415
theorem B640967 : Blo 638302 640967 := bstep (se 1 (by rfl) ⟨480725, by rfl⟩ : syracuseStep 640967 = 961451) B961451
theorem B640987 : Blo 638302 640987 := bstep (se 1 (by rfl) ⟨480740, by rfl⟩ : syracuseStep 640987 = 961481) B961481
theorem B641063 : Blo 638302 641063 := bstep (se 1 (by rfl) ⟨480797, by rfl⟩ : syracuseStep 641063 = 961595) B961595
theorem B1624121 : Blo 638302 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B641103 : Blo 638302 641103 := bstep (se 1 (by rfl) ⟨480827, by rfl⟩ : syracuseStep 641103 = 961655) B961655
theorem B641119 : Blo 638302 641119 := bstep (se 1 (by rfl) ⟨480839, by rfl⟩ : syracuseStep 641119 = 961679) B961679
theorem B641147 : Blo 638302 641147 := bstep (se 1 (by rfl) ⟨480860, by rfl⟩ : syracuseStep 641147 = 961721) B961721
theorem B641199 : Blo 638302 641199 := bstep (se 1 (by rfl) ⟨480899, by rfl⟩ : syracuseStep 641199 = 961799) B961799
theorem B641223 : Blo 638302 641223 := bstep (se 1 (by rfl) ⟨480917, by rfl⟩ : syracuseStep 641223 = 961835) B961835
theorem B641243 : Blo 638302 641243 := bstep (se 1 (by rfl) ⟨480932, by rfl⟩ : syracuseStep 641243 = 961865) B961865
theorem B641319 : Blo 638302 641319 := bstep (se 1 (by rfl) ⟨480989, by rfl⟩ : syracuseStep 641319 = 961979) B961979
theorem B641359 : Blo 638302 641359 := bstep (se 1 (by rfl) ⟨481019, by rfl⟩ : syracuseStep 641359 = 962039) B962039
theorem B2738519 : Blo 638302 2738519 := bstep (se 1 (by rfl) ⟨2053889, by rfl⟩ : syracuseStep 2738519 = 4107779) B4107779
theorem B641375 : Blo 638302 641375 := bstep (se 1 (by rfl) ⟨481031, by rfl⟩ : syracuseStep 641375 = 962063) B962063
theorem B641403 : Blo 638302 641403 := bstep (se 1 (by rfl) ⟨481052, by rfl⟩ : syracuseStep 641403 = 962105) B962105
theorem B1296815 : Blo 638302 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B641455 : Blo 638302 641455 := bstep (se 1 (by rfl) ⟨481091, by rfl⟩ : syracuseStep 641455 = 962183) B962183
theorem B641479 : Blo 638302 641479 := bstep (se 1 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 641479 = 962219) B962219
theorem B641499 : Blo 638302 641499 := bstep (se 1 (by rfl) ⟨481124, by rfl⟩ : syracuseStep 641499 = 962249) B962249
theorem B641575 : Blo 638302 641575 := bstep (se 1 (by rfl) ⟨481181, by rfl⟩ : syracuseStep 641575 = 962363) B962363
theorem B641615 : Blo 638302 641615 := bstep (se 1 (by rfl) ⟨481211, by rfl⟩ : syracuseStep 641615 = 962423) B962423
theorem B641631 : Blo 638302 641631 := bstep (se 1 (by rfl) ⟨481223, by rfl⟩ : syracuseStep 641631 = 962447) B962447
theorem B641659 : Blo 638302 641659 := bstep (se 1 (by rfl) ⟨481244, by rfl⟩ : syracuseStep 641659 = 962489) B962489
theorem B641711 : Blo 638302 641711 := bstep (se 1 (by rfl) ⟨481283, by rfl⟩ : syracuseStep 641711 = 962567) B962567
theorem B641735 : Blo 638302 641735 := bstep (se 1 (by rfl) ⟨481301, by rfl⟩ : syracuseStep 641735 = 962603) B962603
theorem B50547401 : Blo 638302 50547401 := bstep (se 2 (by rfl) ⟨18955275, by rfl⟩ : syracuseStep 50547401 = 37910551) B37910551
theorem B641755 : Blo 638302 641755 := bstep (se 1 (by rfl) ⟨481316, by rfl⟩ : syracuseStep 641755 = 962633) B962633
theorem B641831 : Blo 638302 641831 := bstep (se 1 (by rfl) ⟨481373, by rfl⟩ : syracuseStep 641831 = 962747) B962747
theorem B641871 : Blo 638302 641871 := bstep (se 1 (by rfl) ⟨481403, by rfl⟩ : syracuseStep 641871 = 962807) B962807
theorem B641887 : Blo 638302 641887 := bstep (se 1 (by rfl) ⟨481415, by rfl⟩ : syracuseStep 641887 = 962831) B962831
theorem B641915 : Blo 638302 641915 := bstep (se 1 (by rfl) ⟨481436, by rfl⟩ : syracuseStep 641915 = 962873) B962873
theorem B641967 : Blo 638302 641967 := bstep (se 1 (by rfl) ⟨481475, by rfl⟩ : syracuseStep 641967 = 962951) B962951
theorem B1952695 : Blo 638302 1952695 := bstep (se 1 (by rfl) ⟨1464521, by rfl⟩ : syracuseStep 1952695 = 2929043) B2929043
theorem B641991 : Blo 638302 641991 := bstep (se 1 (by rfl) ⟨481493, by rfl⟩ : syracuseStep 641991 = 962987) B962987
theorem B642011 : Blo 638302 642011 := bstep (se 1 (by rfl) ⟨481508, by rfl⟩ : syracuseStep 642011 = 963017) B963017
theorem B1821703 : Blo 638302 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B2968595 : Blo 638302 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B642087 : Blo 638302 642087 := bstep (se 1 (by rfl) ⟨481565, by rfl⟩ : syracuseStep 642087 = 963131) B963131
theorem B642127 : Blo 638302 642127 := bstep (se 1 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 642127 = 963191) B963191
theorem B642143 : Blo 638302 642143 := bstep (se 1 (by rfl) ⟨481607, by rfl⟩ : syracuseStep 642143 = 963215) B963215
theorem B642171 : Blo 638302 642171 := bstep (se 1 (by rfl) ⟨481628, by rfl⟩ : syracuseStep 642171 = 963257) B963257
theorem B642223 : Blo 638302 642223 := bstep (se 1 (by rfl) ⟨481667, by rfl⟩ : syracuseStep 642223 = 963335) B963335
theorem B642247 : Blo 638302 642247 := bstep (se 1 (by rfl) ⟨481685, by rfl⟩ : syracuseStep 642247 = 963371) B963371
theorem B642267 : Blo 638302 642267 := bstep (se 1 (by rfl) ⟨481700, by rfl⟩ : syracuseStep 642267 = 963401) B963401
theorem B1166699 : Blo 638302 1166699 := bstep (se 1 (by rfl) ⟨875024, by rfl⟩ : syracuseStep 1166699 = 1750049) B1750049
theorem B1625609 : Blo 638302 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B4869719 : Blo 638302 4869719 := bstep (se 1 (by rfl) ⟨3652289, by rfl⟩ : syracuseStep 4869719 = 7304579) B7304579
theorem B2739901 : Blo 638302 2739901 := bstep (se 3 (by rfl) ⟨513731, by rfl⟩ : syracuseStep 2739901 = 1027463) B1027463
theorem B1363655 : Blo 638302 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B4673551 : Blo 638302 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B6148325 : Blo 638302 6148325 := bstep (se 4 (by rfl) ⟨576405, by rfl⟩ : syracuseStep 6148325 = 1152811) B1152811
theorem B3232061 : Blo 638302 3232061 := bstep (se 3 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 3232061 = 1212023) B1212023
theorem B1298761 : Blo 638302 1298761 := bstep (se 2 (by rfl) ⟨487035, by rfl⟩ : syracuseStep 1298761 = 974071) B974071
theorem B1823219 : Blo 638302 1823219 := bstep (se 1 (by rfl) ⟨1367414, by rfl⟩ : syracuseStep 1823219 = 2734829) B2734829
theorem B1561211 : Blo 638302 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B971615 : Blo 638302 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B1364843 : Blo 638302 1364843 := bstep (se 1 (by rfl) ⟨1023632, by rfl⟩ : syracuseStep 1364843 = 2047265) B2047265
theorem B808375 : Blo 638302 808375 := bstep (se 1 (by rfl) ⟨606281, by rfl⟩ : syracuseStep 808375 = 1212563) B1212563
theorem B1824619 : Blo 638302 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B12277817 : Blo 638302 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B3234329 : Blo 638302 3234329 := bstep (se 2 (by rfl) ⟨1212873, by rfl⟩ : syracuseStep 3234329 = 2425747) B2425747
theorem B1563259 : Blo 638302 1563259 := bstep (se 1 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 1563259 = 2344889) B2344889
theorem B809671 : Blo 638302 809671 := bstep (se 1 (by rfl) ⟨607253, by rfl⟩ : syracuseStep 809671 = 1214507) B1214507
theorem B5200823 : Blo 638302 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B6151211 : Blo 638302 6151211 := bstep (se 1 (by rfl) ⟨4613408, by rfl⟩ : syracuseStep 6151211 = 9226817) B9226817
theorem B6151247 : Blo 638302 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B810415 : Blo 638302 810415 := bstep (se 1 (by rfl) ⟨607811, by rfl⟩ : syracuseStep 810415 = 1215623) B1215623
theorem B3071627 : Blo 638302 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B2186941 : Blo 638302 2186941 := bstep (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) B820103
theorem B2056043 : Blo 638302 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B4874093 : Blo 638302 4874093 := bstep (se 3 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 4874093 = 1827785) B1827785
theorem B2154653 : Blo 638302 2154653 := bstep (se 3 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 2154653 = 807995) B807995
theorem B909787 : Blo 638302 909787 := bstep (se 1 (by rfl) ⟨682340, by rfl⟩ : syracuseStep 909787 = 1364681) B1364681
theorem B1827353 : Blo 638302 1827353 := bstep (se 2 (by rfl) ⟨685257, by rfl⟩ : syracuseStep 1827353 = 1370515) B1370515
theorem B811559 : Blo 638302 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B3465787 : Blo 638302 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B1827467 : Blo 638302 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B2155193 : Blo 638302 2155193 := bstep (se 2 (by rfl) ⟨808197, by rfl⟩ : syracuseStep 2155193 = 1616395) B1616395
theorem B13361993 : Blo 638302 13361993 := bstep (se 2 (by rfl) ⟨5010747, by rfl⟩ : syracuseStep 13361993 = 10021495) B10021495
theorem B811883 : Blo 638302 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B2155787 : Blo 638302 2155787 := bstep (se 1 (by rfl) ⟨1616840, by rfl⟩ : syracuseStep 2155787 = 3233681) B3233681
theorem B5203223 : Blo 638302 5203223 := bstep (se 1 (by rfl) ⟨3902417, by rfl⟩ : syracuseStep 5203223 = 7804835) B7804835
theorem B3237245 : Blo 638302 3237245 := bstep (se 3 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 3237245 = 1213967) B1213967
theorem B648667 : Blo 638302 648667 := bstep (se 1 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 648667 = 973001) B973001
theorem B8775179 : Blo 638302 8775179 := bstep (se 1 (by rfl) ⟨6581384, by rfl⟩ : syracuseStep 8775179 = 13162769) B13162769
theorem B2156057 : Blo 638302 2156057 := bstep (se 2 (by rfl) ⟨808521, by rfl⟩ : syracuseStep 2156057 = 1617043) B1617043
theorem B4155095 : Blo 638302 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B1108091 : Blo 638302 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B911911 : Blo 638302 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B2157191 : Blo 638302 2157191 := bstep (se 1 (by rfl) ⟨1617893, by rfl⟩ : syracuseStep 2157191 = 3235787) B3235787
theorem B6154937 : Blo 638302 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B2157245 : Blo 638302 2157245 := bstep (se 3 (by rfl) ⟨404483, by rfl⟩ : syracuseStep 2157245 = 808967) B808967
theorem B3009233 : Blo 638302 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B4877009 : Blo 638302 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B3468035 : Blo 638302 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B1436489 : Blo 638302 1436489 := bstep (se 2 (by rfl) ⟨538683, by rfl⟩ : syracuseStep 1436489 = 1077367) B1077367
theorem B2157407 : Blo 638302 2157407 := bstep (se 1 (by rfl) ⟨1618055, by rfl⟩ : syracuseStep 2157407 = 3236111) B3236111
theorem B2157569 : Blo 638302 2157569 := bstep (se 2 (by rfl) ⟨809088, by rfl⟩ : syracuseStep 2157569 = 1618177) B1618177
theorem B1371215 : Blo 638302 1371215 := bstep (se 1 (by rfl) ⟨1028411, by rfl⟩ : syracuseStep 1371215 = 2056823) B2056823
theorem B912583 : Blo 638302 912583 := bstep (se 1 (by rfl) ⟨684437, by rfl⟩ : syracuseStep 912583 = 1368875) B1368875
theorem B1437281 : Blo 638302 1437281 := bstep (se 2 (by rfl) ⟨538980, by rfl⟩ : syracuseStep 1437281 = 1077961) B1077961
theorem B1371745 : Blo 638302 1371745 := bstep (se 2 (by rfl) ⟨514404, by rfl⟩ : syracuseStep 1371745 = 1028809) B1028809
theorem B2158379 : Blo 638302 2158379 := bstep (se 1 (by rfl) ⟨1618784, by rfl⟩ : syracuseStep 2158379 = 3237569) B3237569
theorem B1535851 : Blo 638302 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B4091809 : Blo 638302 4091809 := bstep (se 2 (by rfl) ⟨1534428, by rfl⟩ : syracuseStep 4091809 = 3068857) B3068857
theorem B1437623 : Blo 638302 1437623 := bstep (se 1 (by rfl) ⟨1078217, by rfl⟩ : syracuseStep 1437623 = 2156435) B2156435
theorem B2158649 : Blo 638302 2158649 := bstep (se 2 (by rfl) ⟨809493, by rfl⟩ : syracuseStep 2158649 = 1618987) B1618987
theorem B3895411 : Blo 638302 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B2158973 : Blo 638302 2158973 := bstep (se 3 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 2158973 = 809615) B809615
theorem B913847 : Blo 638302 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B1077691 : Blo 638302 1077691 := bstep (se 1 (by rfl) ⟨808268, by rfl⟩ : syracuseStep 1077691 = 1616537) B1616537
theorem B1438217 : Blo 638302 1438217 := bstep (se 2 (by rfl) ⟨539331, by rfl⟩ : syracuseStep 1438217 = 1078663) B1078663
theorem B1667609 : Blo 638302 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B1077799 : Blo 638302 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B4682299 : Blo 638302 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B2159243 : Blo 638302 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B1536727 : Blo 638302 1536727 := bstep (se 1 (by rfl) ⟨1152545, by rfl⟩ : syracuseStep 1536727 = 2305091) B2305091
theorem B11268881 : Blo 638302 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B1438559 : Blo 638302 1438559 := bstep (se 1 (by rfl) ⟨1078919, by rfl⟩ : syracuseStep 1438559 = 2157839) B2157839
theorem B1078123 : Blo 638302 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B1438739 : Blo 638302 1438739 := bstep (se 1 (by rfl) ⟨1079054, by rfl⟩ : syracuseStep 1438739 = 2158109) B2158109
theorem B3077315 : Blo 638302 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B1439081 : Blo 638302 1439081 := bstep (se 2 (by rfl) ⟨539655, by rfl⟩ : syracuseStep 1439081 = 1079311) B1079311
theorem B685531 : Blo 638302 685531 := bstep (se 1 (by rfl) ⟨514148, by rfl⟩ : syracuseStep 685531 = 1028297) B1028297
theorem B2160161 : Blo 638302 2160161 := bstep (se 2 (by rfl) ⟨810060, by rfl⟩ : syracuseStep 2160161 = 1620121) B1620121
theorem B718375 : Blo 638302 718375 := bstep (se 1 (by rfl) ⟨538781, by rfl⟩ : syracuseStep 718375 = 1077563) B1077563
theorem B4388413 : Blo 638302 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B3077777 : Blo 638302 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B3241619 : Blo 638302 3241619 := bstep (se 1 (by rfl) ⟨2431214, by rfl⟩ : syracuseStep 3241619 = 4862429) B4862429
theorem B2160377 : Blo 638302 2160377 := bstep (se 2 (by rfl) ⟨810141, by rfl⟩ : syracuseStep 2160377 = 1620283) B1620283
theorem B8222573 : Blo 638302 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B1079183 : Blo 638302 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1439675 : Blo 638302 1439675 := bstep (se 1 (by rfl) ⟨1079756, by rfl⟩ : syracuseStep 1439675 = 2159513) B2159513
theorem B2160647 : Blo 638302 2160647 := bstep (se 1 (by rfl) ⟨1620485, by rfl⟩ : syracuseStep 2160647 = 3240971) B3240971
theorem B1439801 : Blo 638302 1439801 := bstep (se 2 (by rfl) ⟨539925, by rfl⟩ : syracuseStep 1439801 = 1079851) B1079851
theorem B2160755 : Blo 638302 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B1079419 : Blo 638302 1079419 := bstep (se 1 (by rfl) ⟨809564, by rfl⟩ : syracuseStep 1079419 = 1619129) B1619129
theorem B4618397 : Blo 638302 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B2161025 : Blo 638302 2161025 := bstep (se 2 (by rfl) ⟨810384, by rfl⟩ : syracuseStep 2161025 = 1620769) B1620769
theorem B1440143 : Blo 638302 1440143 := bstep (se 1 (by rfl) ⟨1080107, by rfl⟩ : syracuseStep 1440143 = 2160215) B2160215
theorem B2226811 : Blo 638302 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B1440467 : Blo 638302 1440467 := bstep (se 1 (by rfl) ⟨1080350, by rfl⟩ : syracuseStep 1440467 = 2160701) B2160701
theorem B1080283 : Blo 638302 1080283 := bstep (se 1 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 1080283 = 1620425) B1620425
theorem B719995 : Blo 638302 719995 := bstep (se 1 (by rfl) ⟨539996, by rfl⟩ : syracuseStep 719995 = 1079993) B1079993
theorem B2161835 : Blo 638302 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B4914371 : Blo 638302 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B8781047 : Blo 638302 8781047 := bstep (se 1 (by rfl) ⟨6585785, by rfl⟩ : syracuseStep 8781047 = 13171571) B13171571
theorem B4619663 : Blo 638302 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B720463 : Blo 638302 720463 := bstep (se 1 (by rfl) ⟨540347, by rfl⟩ : syracuseStep 720463 = 1080695) B1080695
theorem B1080911 : Blo 638302 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B1441403 : Blo 638302 1441403 := bstep (se 1 (by rfl) ⟨1081052, by rfl⟩ : syracuseStep 1441403 = 2162105) B2162105
theorem B2162375 : Blo 638302 2162375 := bstep (se 1 (by rfl) ⟨1621781, by rfl⟩ : syracuseStep 2162375 = 3243563) B3243563
theorem B8781533 : Blo 638302 8781533 := bstep (se 3 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 8781533 = 3293075) B3293075
theorem B1441529 : Blo 638302 1441529 := bstep (se 2 (by rfl) ⟨540573, by rfl⟩ : syracuseStep 1441529 = 1081147) B1081147
theorem B720859 : Blo 638302 720859 := bstep (se 1 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 720859 = 1081289) B1081289
theorem B6914099 : Blo 638302 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B20709593 : Blo 638302 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B721183 : Blo 638302 721183 := bstep (se 1 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 721183 = 1081775) B1081775
theorem B1442159 : Blo 638302 1442159 := bstep (se 1 (by rfl) ⟨1081619, by rfl⟩ : syracuseStep 1442159 = 2163239) B2163239
theorem B1442231 : Blo 638302 1442231 := bstep (se 1 (by rfl) ⟨1081673, by rfl⟩ : syracuseStep 1442231 = 2163347) B2163347
theorem B721471 : Blo 638302 721471 := bstep (se 1 (by rfl) ⟨541103, by rfl⟩ : syracuseStep 721471 = 1082207) B1082207
theorem B1442375 : Blo 638302 1442375 := bstep (se 1 (by rfl) ⟨1081781, by rfl⟩ : syracuseStep 1442375 = 2163563) B2163563
theorem B1442411 : Blo 638302 1442411 := bstep (se 1 (by rfl) ⟨1081808, by rfl⟩ : syracuseStep 1442411 = 2163617) B2163617
theorem B1213049 : Blo 638302 1213049 := bstep (se 2 (by rfl) ⟨454893, by rfl⟩ : syracuseStep 1213049 = 909787) B909787
theorem B3244697 : Blo 638302 3244697 := bstep (se 2 (by rfl) ⟨1216761, by rfl⟩ : syracuseStep 3244697 = 2433523) B2433523
theorem B4621049 : Blo 638302 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B1442807 : Blo 638302 1442807 := bstep (se 1 (by rfl) ⟨1082105, by rfl⟩ : syracuseStep 1442807 = 2164211) B2164211
theorem B1541369 : Blo 638302 1541369 := bstep (se 2 (by rfl) ⟨578013, by rfl⟩ : syracuseStep 1541369 = 1156027) B1156027
theorem B1443167 : Blo 638302 1443167 := bstep (se 1 (by rfl) ⟨1082375, by rfl⟩ : syracuseStep 1443167 = 2164751) B2164751
theorem B1082747 : Blo 638302 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B722299 : Blo 638302 722299 := bstep (se 1 (by rfl) ⟨541724, by rfl⟩ : syracuseStep 722299 = 1083449) B1083449
theorem B2164157 : Blo 638302 2164157 := bstep (se 3 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 2164157 = 811559) B811559
theorem B1443563 : Blo 638302 1443563 := bstep (se 1 (by rfl) ⟨1082672, by rfl⟩ : syracuseStep 1443563 = 2165345) B2165345
theorem B2164535 : Blo 638302 2164535 := bstep (se 1 (by rfl) ⟨1623401, by rfl⟩ : syracuseStep 2164535 = 3246803) B3246803
theorem B2426705 : Blo 638302 2426705 := bstep (se 2 (by rfl) ⟨910014, by rfl⟩ : syracuseStep 2426705 = 1820029) B1820029
theorem B1443689 : Blo 638302 1443689 := bstep (se 2 (by rfl) ⟨541383, by rfl⟩ : syracuseStep 1443689 = 1082767) B1082767
theorem B2590973 : Blo 638302 2590973 := bstep (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) B971615
theorem B2165021 : Blo 638302 2165021 := bstep (se 3 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 2165021 = 811883) B811883
theorem B1083739 : Blo 638302 1083739 := bstep (se 1 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 1083739 = 1625609) B1625609
theorem B3246479 : Blo 638302 3246479 := bstep (se 1 (by rfl) ⟨2434859, by rfl⟩ : syracuseStep 3246479 = 4869719) B4869719
theorem B788935 : Blo 638302 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B1182203 : Blo 638302 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B1444535 : Blo 638302 1444535 := bstep (se 1 (by rfl) ⟨1083401, by rfl⟩ : syracuseStep 1444535 = 2166803) B2166803
theorem B4098883 : Blo 638302 4098883 := bstep (se 1 (by rfl) ⟨3074162, by rfl⟩ : syracuseStep 4098883 = 6148325) B6148325
theorem B1444751 : Blo 638302 1444751 := bstep (se 1 (by rfl) ⟨1083563, by rfl⟩ : syracuseStep 1444751 = 2167127) B2167127
theorem B1215479 : Blo 638302 1215479 := bstep (se 1 (by rfl) ⟨911609, by rfl⟩ : syracuseStep 1215479 = 1823219) B1823219
theorem B13831307 : Blo 638302 13831307 := bstep (se 1 (by rfl) ⟨10373480, by rfl⟩ : syracuseStep 13831307 = 20746961) B20746961
theorem B2166047 : Blo 638302 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B1215881 : Blo 638302 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B2428937 : Blo 638302 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B1216777 : Blo 638302 1216777 := bstep (se 2 (by rfl) ⟨456291, by rfl⟩ : syracuseStep 1216777 = 912583) B912583
theorem B3248585 : Blo 638302 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B13832693 : Blo 638302 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B11080253 : Blo 638302 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B3281579 : Blo 638302 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B4100807 : Blo 638302 4100807 := bstep (se 1 (by rfl) ⟨3075605, by rfl⟩ : syracuseStep 4100807 = 6151211) B6151211
theorem B3085003 : Blo 638302 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B4100831 : Blo 638302 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B3249395 : Blo 638302 3249395 := bstep (se 1 (by rfl) ⟨2437046, by rfl⟩ : syracuseStep 3249395 = 4874093) B4874093
theorem B6231401 : Blo 638302 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B1218235 : Blo 638302 1218235 := bstep (se 1 (by rfl) ⟨913676, by rfl⟩ : syracuseStep 1218235 = 1827353) B1827353
theorem B1218311 : Blo 638302 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B1153129 : Blo 638302 1153129 := bstep (se 2 (by rfl) ⟨432423, by rfl⟩ : syracuseStep 1153129 = 864847) B864847
theorem B1022537 : Blo 638302 1022537 := bstep (se 2 (by rfl) ⟨383451, by rfl⟩ : syracuseStep 1022537 = 766903) B766903
theorem B1317599 : Blo 638302 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B4103291 : Blo 638302 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B2006155 : Blo 638302 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B3251339 : Blo 638302 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B957659 : Blo 638302 957659 := bstep (se 1 (by rfl) ⟨718244, by rfl⟩ : syracuseStep 957659 = 1436489) B1436489
theorem B1023209 : Blo 638302 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B9248093 : Blo 638302 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B957833 : Blo 638302 957833 := bstep (se 2 (by rfl) ⟨359187, by rfl⟩ : syracuseStep 957833 = 718375) B718375
theorem B5905979 : Blo 638302 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B958187 : Blo 638302 958187 := bstep (se 1 (by rfl) ⟨718640, by rfl⟩ : syracuseStep 958187 = 1437281) B1437281
theorem B2432825 : Blo 638302 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B958415 : Blo 638302 958415 := bstep (se 1 (by rfl) ⟨718811, by rfl⟩ : syracuseStep 958415 = 1437623) B1437623
theorem B3285011 : Blo 638302 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B3645593 : Blo 638302 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B958811 : Blo 638302 958811 := bstep (se 1 (by rfl) ⟨719108, by rfl⟩ : syracuseStep 958811 = 1438217) B1438217
theorem B7512587 : Blo 638302 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B959039 : Blo 638302 959039 := bstep (se 1 (by rfl) ⟨719279, by rfl⟩ : syracuseStep 959039 = 1438559) B1438559
theorem B959159 : Blo 638302 959159 := bstep (se 1 (by rfl) ⟨719369, by rfl⟩ : syracuseStep 959159 = 1438739) B1438739
theorem B959387 : Blo 638302 959387 := bstep (se 1 (by rfl) ⟨719540, by rfl⟩ : syracuseStep 959387 = 1439081) B1439081
theorem B5481715 : Blo 638302 5481715 := bstep (se 1 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 5481715 = 8222573) B8222573
theorem B959783 : Blo 638302 959783 := bstep (se 1 (by rfl) ⟨719837, by rfl⟩ : syracuseStep 959783 = 1439675) B1439675
theorem B959867 : Blo 638302 959867 := bstep (se 1 (by rfl) ⟨719900, by rfl⟩ : syracuseStep 959867 = 1439801) B1439801
theorem B5547437 : Blo 638302 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B959993 : Blo 638302 959993 := bstep (se 2 (by rfl) ⟨359997, by rfl⟩ : syracuseStep 959993 = 719995) B719995
theorem B960095 : Blo 638302 960095 := bstep (se 1 (by rfl) ⟨720071, by rfl⟩ : syracuseStep 960095 = 1440143) B1440143
theorem B960311 : Blo 638302 960311 := bstep (se 1 (by rfl) ⟨720233, by rfl⟩ : syracuseStep 960311 = 1440467) B1440467
theorem B960617 : Blo 638302 960617 := bstep (se 2 (by rfl) ⟨360231, by rfl⟩ : syracuseStep 960617 = 720463) B720463
theorem B5187779 : Blo 638302 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B960935 : Blo 638302 960935 := bstep (se 1 (by rfl) ⟨720701, by rfl⟩ : syracuseStep 960935 = 1441403) B1441403
theorem B961019 : Blo 638302 961019 := bstep (se 1 (by rfl) ⟨720764, by rfl⟩ : syracuseStep 961019 = 1441529) B1441529
theorem B961145 : Blo 638302 961145 := bstep (se 2 (by rfl) ⟨360429, by rfl⟩ : syracuseStep 961145 = 720859) B720859
theorem B961199 : Blo 638302 961199 := bstep (se 1 (by rfl) ⟨720899, by rfl⟩ : syracuseStep 961199 = 1441799) B1441799
theorem B961247 : Blo 638302 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B2730743 : Blo 638302 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B1616719 : Blo 638302 1616719 := bstep (se 1 (by rfl) ⟨1212539, by rfl⟩ : syracuseStep 1616719 = 2425079) B2425079
theorem B1944445 : Blo 638302 1944445 := bstep (se 3 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 1944445 = 729167) B729167
theorem B961511 : Blo 638302 961511 := bstep (se 1 (by rfl) ⟨721133, by rfl⟩ : syracuseStep 961511 = 1442267) B1442267
theorem B6237199 : Blo 638302 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B1616993 : Blo 638302 1616993 := bstep (se 2 (by rfl) ⟨606372, by rfl⟩ : syracuseStep 1616993 = 1212745) B1212745
theorem B6171851 : Blo 638302 6171851 := bstep (se 1 (by rfl) ⟨4628888, by rfl⟩ : syracuseStep 6171851 = 9257777) B9257777
theorem B961769 : Blo 638302 961769 := bstep (se 2 (by rfl) ⟨360663, by rfl⟩ : syracuseStep 961769 = 721327) B721327
theorem B961823 : Blo 638302 961823 := bstep (se 1 (by rfl) ⟨721367, by rfl⟩ : syracuseStep 961823 = 1442735) B1442735
theorem B10136951 : Blo 638302 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B961991 : Blo 638302 961991 := bstep (se 1 (by rfl) ⟨721493, by rfl⟩ : syracuseStep 961991 = 1442987) B1442987
theorem B1617367 : Blo 638302 1617367 := bstep (se 1 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 1617367 = 2426051) B2426051
theorem B2371031 : Blo 638302 2371031 := bstep (se 1 (by rfl) ⟨1778273, by rfl⟩ : syracuseStep 2371031 = 3556547) B3556547
theorem B1617671 : Blo 638302 1617671 := bstep (se 1 (by rfl) ⟨1213253, by rfl⟩ : syracuseStep 1617671 = 2426507) B2426507
theorem B962345 : Blo 638302 962345 := bstep (se 2 (by rfl) ⟨360879, by rfl⟩ : syracuseStep 962345 = 721759) B721759
theorem B962351 : Blo 638302 962351 := bstep (se 1 (by rfl) ⟨721763, by rfl⟩ : syracuseStep 962351 = 1443527) B1443527
theorem B2436911 : Blo 638302 2436911 := bstep (se 1 (by rfl) ⟨1827683, by rfl⟩ : syracuseStep 2436911 = 3655367) B3655367
theorem B2436925 : Blo 638302 2436925 := bstep (se 3 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 2436925 = 913847) B913847
theorem B962825 : Blo 638302 962825 := bstep (se 2 (by rfl) ⟨361059, by rfl⟩ : syracuseStep 962825 = 722119) B722119
theorem B962927 : Blo 638302 962927 := bstep (se 1 (by rfl) ⟨722195, by rfl⟩ : syracuseStep 962927 = 1444391) B1444391
theorem B6926725 : Blo 638302 6926725 := bstep (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) B1298761
theorem B3649967 : Blo 638302 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B33698267 : Blo 638302 33698267 := bstep (se 1 (by rfl) ⟨25273700, by rfl⟩ : syracuseStep 33698267 = 50547401) B50547401
theorem B1618451 : Blo 638302 1618451 := bstep (se 1 (by rfl) ⟨1213838, by rfl⟩ : syracuseStep 1618451 = 2427677) B2427677
theorem B963143 : Blo 638302 963143 := bstep (se 1 (by rfl) ⟨722357, by rfl⟩ : syracuseStep 963143 = 1444715) B1444715
theorem B963179 : Blo 638302 963179 := bstep (se 1 (by rfl) ⟨722384, by rfl⟩ : syracuseStep 963179 = 1444769) B1444769
theorem B1979063 : Blo 638302 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B963407 : Blo 638302 963407 := bstep (se 1 (by rfl) ⟨722555, by rfl⟩ : syracuseStep 963407 = 1445111) B1445111
theorem B23311439 : Blo 638302 23311439 := bstep (se 1 (by rfl) ⟨17483579, by rfl⟩ : syracuseStep 23311439 = 34967159) B34967159
theorem B2733203 : Blo 638302 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B13809163 : Blo 638302 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B6928109 : Blo 638302 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B767791 : Blo 638302 767791 := bstep (se 1 (by rfl) ⟨575843, by rfl⟩ : syracuseStep 767791 = 1151687) B1151687
theorem B1620233 : Blo 638302 1620233 := bstep (se 2 (by rfl) ⟨607587, by rfl⟩ : syracuseStep 1620233 = 1215175) B1215175
theorem B2603593 : Blo 638302 2603593 := bstep (se 2 (by rfl) ⟨976347, by rfl⟩ : syracuseStep 2603593 = 1952695) B1952695
theorem B1620587 : Blo 638302 1620587 := bstep (se 1 (by rfl) ⟨1215440, by rfl⟩ : syracuseStep 1620587 = 2430881) B2430881
theorem B1621235 : Blo 638302 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B638319 : Blo 638302 638319 := bstep (se 1 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 638319 = 957479) B957479
theorem B638375 : Blo 638302 638375 := bstep (se 1 (by rfl) ⟨478781, by rfl⟩ : syracuseStep 638375 = 957563) B957563
theorem B638459 : Blo 638302 638459 := bstep (se 1 (by rfl) ⟨478844, by rfl⟩ : syracuseStep 638459 = 957689) B957689
theorem B638527 : Blo 638302 638527 := bstep (se 1 (by rfl) ⟨478895, by rfl⟩ : syracuseStep 638527 = 957791) B957791
theorem B638535 : Blo 638302 638535 := bstep (se 1 (by rfl) ⟨478901, by rfl⟩ : syracuseStep 638535 = 957803) B957803
theorem B3653201 : Blo 638302 3653201 := bstep (se 2 (by rfl) ⟨1369950, by rfl⟩ : syracuseStep 3653201 = 2739901) B2739901
theorem B4111955 : Blo 638302 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B26590837 : Blo 638302 26590837 := bstep (se 5 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 26590837 = 2492891) B2492891
theorem B1621691 : Blo 638302 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B638687 : Blo 638302 638687 := bstep (se 1 (by rfl) ⟨479015, by rfl⟩ : syracuseStep 638687 = 958031) B958031
theorem B769771 : Blo 638302 769771 := bstep (se 1 (by rfl) ⟨577328, by rfl⟩ : syracuseStep 769771 = 1154657) B1154657
theorem B2047751 : Blo 638302 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B3653383 : Blo 638302 3653383 := bstep (se 1 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 3653383 = 5480075) B5480075
theorem B638767 : Blo 638302 638767 := bstep (se 1 (by rfl) ⟨479075, by rfl⟩ : syracuseStep 638767 = 958151) B958151
theorem B5455745 : Blo 638302 5455745 := bstep (se 2 (by rfl) ⟨2045904, by rfl⟩ : syracuseStep 5455745 = 4091809) B4091809
theorem B638875 : Blo 638302 638875 := bstep (se 1 (by rfl) ⟨479156, by rfl⟩ : syracuseStep 638875 = 958313) B958313
theorem B638927 : Blo 638302 638927 := bstep (se 1 (by rfl) ⟨479195, by rfl⟩ : syracuseStep 638927 = 958391) B958391
theorem B638951 : Blo 638302 638951 := bstep (se 1 (by rfl) ⟨479213, by rfl⟩ : syracuseStep 638951 = 958427) B958427
theorem B5193881 : Blo 638302 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B1622227 : Blo 638302 1622227 := bstep (se 1 (by rfl) ⟨1216670, by rfl⟩ : syracuseStep 1622227 = 2433341) B2433341
theorem B639263 : Blo 638302 639263 := bstep (se 1 (by rfl) ⟨479447, by rfl⟩ : syracuseStep 639263 = 958895) B958895
theorem B639323 : Blo 638302 639323 := bstep (se 1 (by rfl) ⟨479492, by rfl⟩ : syracuseStep 639323 = 958985) B958985
theorem B639343 : Blo 638302 639343 := bstep (se 1 (by rfl) ⟨479507, by rfl⟩ : syracuseStep 639343 = 959015) B959015
theorem B639399 : Blo 638302 639399 := bstep (se 1 (by rfl) ⟨479549, by rfl⟩ : syracuseStep 639399 = 959099) B959099
theorem B1753555 : Blo 638302 1753555 := bstep (se 1 (by rfl) ⟨1315166, by rfl⟩ : syracuseStep 1753555 = 2630333) B2630333
theorem B639483 : Blo 638302 639483 := bstep (se 1 (by rfl) ⟨479612, by rfl⟩ : syracuseStep 639483 = 959225) B959225
theorem B639551 : Blo 638302 639551 := bstep (se 1 (by rfl) ⟨479663, by rfl⟩ : syracuseStep 639551 = 959327) B959327
theorem B639559 : Blo 638302 639559 := bstep (se 1 (by rfl) ⟨479669, by rfl⟩ : syracuseStep 639559 = 959339) B959339
theorem B639711 : Blo 638302 639711 := bstep (se 1 (by rfl) ⟨479783, by rfl⟩ : syracuseStep 639711 = 959567) B959567
theorem B6243065 : Blo 638302 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B639791 : Blo 638302 639791 := bstep (se 1 (by rfl) ⟨479843, by rfl⟩ : syracuseStep 639791 = 959687) B959687
theorem B639899 : Blo 638302 639899 := bstep (se 1 (by rfl) ⟨479924, by rfl⟩ : syracuseStep 639899 = 959849) B959849
theorem B18465731 : Blo 638302 18465731 := bstep (se 1 (by rfl) ⟨13849298, by rfl⟩ : syracuseStep 18465731 = 27698597) B27698597
theorem B2048969 : Blo 638302 2048969 := bstep (se 2 (by rfl) ⟨768363, by rfl⟩ : syracuseStep 2048969 = 1536727) B1536727
theorem B639951 : Blo 638302 639951 := bstep (se 1 (by rfl) ⟨479963, by rfl⟩ : syracuseStep 639951 = 959927) B959927
theorem B639975 : Blo 638302 639975 := bstep (se 1 (by rfl) ⟨479981, by rfl⟩ : syracuseStep 639975 = 959963) B959963
theorem B5850119 : Blo 638302 5850119 := bstep (se 1 (by rfl) ⟨4387589, by rfl⟩ : syracuseStep 5850119 = 8775179) B8775179
theorem B1623179 : Blo 638302 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B1819847 : Blo 638302 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B640287 : Blo 638302 640287 := bstep (se 1 (by rfl) ⟨480215, by rfl⟩ : syracuseStep 640287 = 960431) B960431
theorem B640347 : Blo 638302 640347 := bstep (se 1 (by rfl) ⟨480260, by rfl⟩ : syracuseStep 640347 = 960521) B960521
theorem B640367 : Blo 638302 640367 := bstep (se 1 (by rfl) ⟨480275, by rfl⟩ : syracuseStep 640367 = 960551) B960551
theorem B771439 : Blo 638302 771439 := bstep (se 1 (by rfl) ⟨578579, by rfl⟩ : syracuseStep 771439 = 1157159) B1157159
theorem B738727 : Blo 638302 738727 := bstep (se 1 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 738727 = 1108091) B1108091
theorem B640423 : Blo 638302 640423 := bstep (se 1 (by rfl) ⟨480317, by rfl⟩ : syracuseStep 640423 = 960635) B960635
theorem B640507 : Blo 638302 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B4113953 : Blo 638302 4113953 := bstep (se 2 (by rfl) ⟨1542732, by rfl⟩ : syracuseStep 4113953 = 3085465) B3085465
theorem B640575 : Blo 638302 640575 := bstep (se 1 (by rfl) ⟨480431, by rfl⟩ : syracuseStep 640575 = 960863) B960863
theorem B640583 : Blo 638302 640583 := bstep (se 1 (by rfl) ⟨480437, by rfl⟩ : syracuseStep 640583 = 960875) B960875
theorem B1623635 : Blo 638302 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B640735 : Blo 638302 640735 := bstep (se 1 (by rfl) ⟨480551, by rfl⟩ : syracuseStep 640735 = 961103) B961103
theorem B640815 : Blo 638302 640815 := bstep (se 1 (by rfl) ⟨480611, by rfl⟩ : syracuseStep 640815 = 961223) B961223
theorem B640923 : Blo 638302 640923 := bstep (se 1 (by rfl) ⟨480692, by rfl⟩ : syracuseStep 640923 = 961385) B961385
theorem B3459023 : Blo 638302 3459023 := bstep (se 1 (by rfl) ⟨2594267, by rfl⟩ : syracuseStep 3459023 = 5188535) B5188535
theorem B640975 : Blo 638302 640975 := bstep (se 1 (by rfl) ⟨480731, by rfl⟩ : syracuseStep 640975 = 961463) B961463
theorem B640999 : Blo 638302 640999 := bstep (se 1 (by rfl) ⟨480749, by rfl⟩ : syracuseStep 640999 = 961499) B961499
theorem B5851217 : Blo 638302 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B26364149 : Blo 638302 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B5458205 : Blo 638302 5458205 := bstep (se 3 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 5458205 = 2046827) B2046827
theorem B641311 : Blo 638302 641311 := bstep (se 1 (by rfl) ⟨480983, by rfl⟩ : syracuseStep 641311 = 961967) B961967
theorem B641371 : Blo 638302 641371 := bstep (se 1 (by rfl) ⟨481028, by rfl⟩ : syracuseStep 641371 = 962057) B962057
theorem B1296751 : Blo 638302 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B641391 : Blo 638302 641391 := bstep (se 1 (by rfl) ⟨481043, by rfl⟩ : syracuseStep 641391 = 962087) B962087
theorem B78694787 : Blo 638302 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B641447 : Blo 638302 641447 := bstep (se 1 (by rfl) ⟨481085, by rfl⟩ : syracuseStep 641447 = 962171) B962171
theorem B1624495 : Blo 638302 1624495 := bstep (se 1 (by rfl) ⟨1218371, by rfl⟩ : syracuseStep 1624495 = 2436743) B2436743
theorem B3459557 : Blo 638302 3459557 := bstep (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) B648667
theorem B1821179 : Blo 638302 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B641531 : Blo 638302 641531 := bstep (se 1 (by rfl) ⟨481148, by rfl⟩ : syracuseStep 641531 = 962297) B962297
theorem B641599 : Blo 638302 641599 := bstep (se 1 (by rfl) ⟨481199, by rfl⟩ : syracuseStep 641599 = 962399) B962399
theorem B641607 : Blo 638302 641607 := bstep (se 1 (by rfl) ⟨481205, by rfl⟩ : syracuseStep 641607 = 962411) B962411
theorem B641759 : Blo 638302 641759 := bstep (se 1 (by rfl) ⟨481319, by rfl⟩ : syracuseStep 641759 = 962639) B962639
theorem B1624799 : Blo 638302 1624799 := bstep (se 1 (by rfl) ⟨1218599, by rfl⟩ : syracuseStep 1624799 = 2437199) B2437199
theorem B641839 : Blo 638302 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B3656573 : Blo 638302 3656573 := bstep (se 3 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 3656573 = 1371215) B1371215
theorem B641947 : Blo 638302 641947 := bstep (se 1 (by rfl) ⟨481460, by rfl⟩ : syracuseStep 641947 = 962921) B962921
theorem B641999 : Blo 638302 641999 := bstep (se 1 (by rfl) ⟨481499, by rfl⟩ : syracuseStep 641999 = 962999) B962999
theorem B642023 : Blo 638302 642023 := bstep (se 1 (by rfl) ⟨481517, by rfl⟩ : syracuseStep 642023 = 963035) B963035
theorem B1625467 : Blo 638302 1625467 := bstep (se 1 (by rfl) ⟨1219100, by rfl⟩ : syracuseStep 1625467 = 2438201) B2438201
theorem B2051543 : Blo 638302 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B2084345 : Blo 638302 2084345 := bstep (se 2 (by rfl) ⟨781629, by rfl⟩ : syracuseStep 2084345 = 1563259) B1563259
theorem B2969081 : Blo 638302 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B3460769 : Blo 638302 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B3067627 : Blo 638302 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B2051851 : Blo 638302 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B13881131 : Blo 638302 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B1363817 : Blo 638302 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B2740243 : Blo 638302 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B11686517 : Blo 638302 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B5854031 : Blo 638302 5854031 := bstep (se 1 (by rfl) ⟨4390523, by rfl⟩ : syracuseStep 5854031 = 8781047) B8781047
theorem B5854355 : Blo 638302 5854355 := bstep (se 1 (by rfl) ⟨4390766, by rfl⟩ : syracuseStep 5854355 = 8781533) B8781533
theorem B5199005 : Blo 638302 5199005 := bstep (se 3 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 5199005 = 1949627) B1949627
theorem B5002397 : Blo 638302 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B1824095 : Blo 638302 1824095 := bstep (se 1 (by rfl) ⟨1368071, by rfl⟩ : syracuseStep 1824095 = 2736143) B2736143
theorem B1366483 : Blo 638302 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B1464895 : Blo 638302 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B3070685 : Blo 638302 3070685 := bstep (se 3 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 3070685 = 1151507) B1151507
theorem B1825679 : Blo 638302 1825679 := bstep (se 1 (by rfl) ⟨1369259, by rfl⟩ : syracuseStep 1825679 = 2738519) B2738519
theorem B3235139 : Blo 638302 3235139 := bstep (se 1 (by rfl) ⟨2426354, by rfl⟩ : syracuseStep 3235139 = 4852709) B4852709
theorem B27745649 : Blo 638302 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B1727867 : Blo 638302 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B777799 : Blo 638302 777799 := bstep (se 1 (by rfl) ⟨583349, by rfl⟩ : syracuseStep 777799 = 1166699) B1166699
theorem B3235625 : Blo 638302 3235625 := bstep (se 2 (by rfl) ⟨1213359, by rfl⟩ : syracuseStep 3235625 = 2426719) B2426719
theorem B2154707 : Blo 638302 2154707 := bstep (se 1 (by rfl) ⟨1616030, by rfl⟩ : syracuseStep 2154707 = 3232061) B3232061
theorem B811387 : Blo 638302 811387 := bstep (se 1 (by rfl) ⟨608540, by rfl⟩ : syracuseStep 811387 = 1217081) B1217081
theorem B1040807 : Blo 638302 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B2154977 : Blo 638302 2154977 := bstep (se 2 (by rfl) ⟨808116, by rfl⟩ : syracuseStep 2154977 = 1616233) B1616233
theorem B909895 : Blo 638302 909895 := bstep (se 1 (by rfl) ⟨682421, by rfl⟩ : syracuseStep 909895 = 1364843) B1364843
theorem B811615 : Blo 638302 811615 := bstep (se 1 (by rfl) ⟨608711, by rfl⟩ : syracuseStep 811615 = 1217423) B1217423
theorem B6578891 : Blo 638302 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B5530463 : Blo 638302 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B3236921 : Blo 638302 3236921 := bstep (se 2 (by rfl) ⟨1213845, by rfl⟩ : syracuseStep 3236921 = 2427691) B2427691
theorem B8185211 : Blo 638302 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B2156219 : Blo 638302 2156219 := bstep (se 1 (by rfl) ⟨1617164, by rfl⟩ : syracuseStep 2156219 = 3234329) B3234329
theorem B1533737 : Blo 638302 1533737 := bstep (se 2 (by rfl) ⟨575151, by rfl⟩ : syracuseStep 1533737 = 1150303) B1150303
theorem B812855 : Blo 638302 812855 := bstep (se 1 (by rfl) ⟨609641, by rfl⟩ : syracuseStep 812855 = 1219283) B1219283
theorem B3467215 : Blo 638302 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B1828993 : Blo 638302 1828993 := bstep (se 2 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 1828993 = 1371745) B1371745
theorem B1370695 : Blo 638302 1370695 := bstep (se 1 (by rfl) ⟨1028021, by rfl⟩ : syracuseStep 1370695 = 2056043) B2056043
theorem B1436435 : Blo 638302 1436435 := bstep (se 1 (by rfl) ⟨1077326, by rfl⟩ : syracuseStep 1436435 = 2154653) B2154653
theorem B1534967 : Blo 638302 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B3239027 : Blo 638302 3239027 := bstep (se 1 (by rfl) ⟨2429270, by rfl⟩ : syracuseStep 3239027 = 4858541) B4858541
theorem B1436795 : Blo 638302 1436795 := bstep (se 1 (by rfl) ⟨1077596, by rfl⟩ : syracuseStep 1436795 = 2155193) B2155193
theorem B8907995 : Blo 638302 8907995 := bstep (se 1 (by rfl) ⟨6680996, by rfl⟩ : syracuseStep 8907995 = 13361993) B13361993
theorem B1436921 : Blo 638302 1436921 := bstep (se 2 (by rfl) ⟨538845, by rfl⟩ : syracuseStep 1436921 = 1077691) B1077691
theorem B1437065 : Blo 638302 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B683515 : Blo 638302 683515 := bstep (se 1 (by rfl) ⟨512636, by rfl⟩ : syracuseStep 683515 = 1025273) B1025273
theorem B1437191 : Blo 638302 1437191 := bstep (se 1 (by rfl) ⟨1077893, by rfl⟩ : syracuseStep 1437191 = 2155787) B2155787
theorem B3468815 : Blo 638302 3468815 := bstep (se 1 (by rfl) ⟨2601611, by rfl⟩ : syracuseStep 3468815 = 5203223) B5203223
theorem B2158163 : Blo 638302 2158163 := bstep (se 1 (by rfl) ⟨1618622, by rfl⟩ : syracuseStep 2158163 = 3237245) B3237245
theorem B1437371 : Blo 638302 1437371 := bstep (se 1 (by rfl) ⟨1078028, by rfl⟩ : syracuseStep 1437371 = 2156057) B2156057
theorem B1437497 : Blo 638302 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B3239837 : Blo 638302 3239837 := bstep (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) B1214939
theorem B7303121 : Blo 638302 7303121 := bstep (se 2 (by rfl) ⟨2738670, by rfl⟩ : syracuseStep 7303121 = 5477341) B5477341
theorem B3109211 : Blo 638302 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B1077671 : Blo 638302 1077671 := bstep (se 1 (by rfl) ⟨808253, by rfl⟩ : syracuseStep 1077671 = 1616507) B1616507
theorem B1438127 : Blo 638302 1438127 := bstep (se 1 (by rfl) ⟨1078595, by rfl⟩ : syracuseStep 1438127 = 2157191) B2157191
theorem B1438163 : Blo 638302 1438163 := bstep (se 1 (by rfl) ⟨1078622, by rfl⟩ : syracuseStep 1438163 = 2157245) B2157245
theorem B1438271 : Blo 638302 1438271 := bstep (se 1 (by rfl) ⟨1078703, by rfl⟩ : syracuseStep 1438271 = 2157407) B2157407
theorem B1077833 : Blo 638302 1077833 := bstep (se 2 (by rfl) ⟨404187, by rfl⟩ : syracuseStep 1077833 = 808375) B808375
theorem B914041 : Blo 638302 914041 := bstep (se 2 (by rfl) ⟨342765, by rfl⟩ : syracuseStep 914041 = 685531) B685531
theorem B1438379 : Blo 638302 1438379 := bstep (se 1 (by rfl) ⟨1078784, by rfl⟩ : syracuseStep 1438379 = 2157569) B2157569
theorem B3240647 : Blo 638302 3240647 := bstep (se 1 (by rfl) ⟨2430485, by rfl⟩ : syracuseStep 3240647 = 4860971) B4860971
theorem B1438919 : Blo 638302 1438919 := bstep (se 1 (by rfl) ⟨1079189, by rfl⟩ : syracuseStep 1438919 = 2158379) B2158379
theorem B1439099 : Blo 638302 1439099 := bstep (se 1 (by rfl) ⟨1079324, by rfl⟩ : syracuseStep 1439099 = 2158649) B2158649
theorem B1439225 : Blo 638302 1439225 := bstep (se 2 (by rfl) ⟨539709, by rfl⟩ : syracuseStep 1439225 = 1079419) B1079419
theorem B1439315 : Blo 638302 1439315 := bstep (se 1 (by rfl) ⟨1079486, by rfl⟩ : syracuseStep 1439315 = 2158973) B2158973
theorem B1078879 : Blo 638302 1078879 := bstep (se 1 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 1078879 = 1618319) B1618319
theorem B1537697 : Blo 638302 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B1111739 : Blo 638302 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B1439495 : Blo 638302 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B1079095 : Blo 638302 1079095 := bstep (se 1 (by rfl) ⟨809321, by rfl⟩ : syracuseStep 1079095 = 1618643) B1618643
theorem B26245093 : Blo 638302 26245093 := bstep (se 4 (by rfl) ⟨2460477, by rfl⟩ : syracuseStep 26245093 = 4920955) B4920955
theorem B76904549 : Blo 638302 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B1079561 : Blo 638302 1079561 := bstep (se 2 (by rfl) ⟨404835, by rfl⟩ : syracuseStep 1079561 = 809671) B809671
theorem B5208409 : Blo 638302 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B1440107 : Blo 638302 1440107 := bstep (se 1 (by rfl) ⟨1080080, by rfl⟩ : syracuseStep 1440107 = 2160161) B2160161
theorem B2161079 : Blo 638302 2161079 := bstep (se 1 (by rfl) ⟨1620809, by rfl⟩ : syracuseStep 2161079 = 3241619) B3241619
theorem B1440251 : Blo 638302 1440251 := bstep (se 1 (by rfl) ⟨1080188, by rfl⟩ : syracuseStep 1440251 = 2160377) B2160377
theorem B719455 : Blo 638302 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B1440377 : Blo 638302 1440377 := bstep (se 2 (by rfl) ⟨540141, by rfl⟩ : syracuseStep 1440377 = 1080283) B1080283
theorem B3635887 : Blo 638302 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B1440431 : Blo 638302 1440431 := bstep (se 1 (by rfl) ⟨1080323, by rfl⟩ : syracuseStep 1440431 = 2160647) B2160647
theorem B1440503 : Blo 638302 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B3078931 : Blo 638302 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B1440683 : Blo 638302 1440683 := bstep (se 1 (by rfl) ⟨1080512, by rfl⟩ : syracuseStep 1440683 = 2161025) B2161025
theorem B3636413 : Blo 638302 3636413 := bstep (se 3 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 3636413 = 1363655) B1363655
theorem B8191205 : Blo 638302 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B1080553 : Blo 638302 1080553 := bstep (se 2 (by rfl) ⟨405207, by rfl⟩ : syracuseStep 1080553 = 810415) B810415
theorem B1080607 : Blo 638302 1080607 := bstep (se 1 (by rfl) ⟨810455, by rfl⟩ : syracuseStep 1080607 = 1620911) B1620911
theorem B3243401 : Blo 638302 3243401 := bstep (se 2 (by rfl) ⟨1216275, by rfl⟩ : syracuseStep 3243401 = 2432551) B2432551
theorem B1441223 : Blo 638302 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B3276247 : Blo 638302 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B2915921 : Blo 638302 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B3079775 : Blo 638302 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B1081019 : Blo 638302 1081019 := bstep (se 1 (by rfl) ⟨810764, by rfl⟩ : syracuseStep 1081019 = 1621529) B1621529
theorem B720607 : Blo 638302 720607 := bstep (se 1 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 720607 = 1080911) B1080911
theorem B1441583 : Blo 638302 1441583 := bstep (se 1 (by rfl) ⟨1081187, by rfl⟩ : syracuseStep 1441583 = 2162375) B2162375
theorem B2162969 : Blo 638302 2162969 := bstep (se 2 (by rfl) ⟨811113, by rfl⟩ : syracuseStep 2162969 = 1622227) B1622227
theorem B2163131 : Blo 638302 2163131 := bstep (se 1 (by rfl) ⟨1622348, by rfl⟩ : syracuseStep 2163131 = 3244697) B3244697
theorem B1081849 : Blo 638302 1081849 := bstep (se 2 (by rfl) ⟨405693, by rfl⟩ : syracuseStep 1081849 = 811387) B811387
theorem B4162043 : Blo 638302 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B3080699 : Blo 638302 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B3900079 : Blo 638302 3900079 := bstep (se 1 (by rfl) ⟨2925059, by rfl⟩ : syracuseStep 3900079 = 5850119) B5850119
theorem B1082119 : Blo 638302 1082119 := bstep (se 1 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 1082119 = 1623179) B1623179
theorem B1213193 : Blo 638302 1213193 := bstep (se 2 (by rfl) ⟨454947, by rfl⟩ : syracuseStep 1213193 = 909895) B909895
theorem B1082153 : Blo 638302 1082153 := bstep (se 2 (by rfl) ⟨405807, by rfl⟩ : syracuseStep 1082153 = 811615) B811615
theorem B1213231 : Blo 638302 1213231 := bstep (se 1 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 1213231 = 1819847) B1819847
theorem B721831 : Blo 638302 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B1442771 : Blo 638302 1442771 := bstep (se 1 (by rfl) ⟨1082078, by rfl⟩ : syracuseStep 1442771 = 2164157) B2164157
theorem B1082423 : Blo 638302 1082423 := bstep (se 1 (by rfl) ⟨811817, by rfl⟩ : syracuseStep 1082423 = 1623635) B1623635
theorem B1443023 : Blo 638302 1443023 := bstep (se 1 (by rfl) ⟨1082267, by rfl⟩ : syracuseStep 1443023 = 2164535) B2164535
theorem B3900811 : Blo 638302 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B3638803 : Blo 638302 3638803 := bstep (se 1 (by rfl) ⟨2729102, by rfl⟩ : syracuseStep 3638803 = 5458205) B5458205
theorem B1443347 : Blo 638302 1443347 := bstep (se 1 (by rfl) ⟨1082510, by rfl⟩ : syracuseStep 1443347 = 2165021) B2165021
theorem B2164319 : Blo 638302 2164319 := bstep (se 1 (by rfl) ⟨1623239, by rfl⟩ : syracuseStep 2164319 = 3246479) B3246479
theorem B7308953 : Blo 638302 7308953 := bstep (se 2 (by rfl) ⟨2740857, by rfl⟩ : syracuseStep 7308953 = 5481715) B5481715
theorem B788135 : Blo 638302 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B1214119 : Blo 638302 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B1083199 : Blo 638302 1083199 := bstep (se 1 (by rfl) ⟨812399, by rfl⟩ : syracuseStep 1083199 = 1624799) B1624799
theorem B1444031 : Blo 638302 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B4622953 : Blo 638302 4622953 := bstep (se 2 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 4622953 = 3467215) B3467215
theorem B2165723 : Blo 638302 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B1444985 : Blo 638302 1444985 := bstep (se 2 (by rfl) ⟨541869, by rfl⟩ : syracuseStep 1444985 = 1083739) B1083739
theorem B3902687 : Blo 638302 3902687 := bstep (se 1 (by rfl) ⟨2927015, by rfl⟩ : syracuseStep 3902687 = 5854031) B5854031
theorem B2165993 : Blo 638302 2165993 := bstep (se 2 (by rfl) ⟨812247, by rfl⟩ : syracuseStep 2165993 = 1624495) B1624495
theorem B1051913 : Blo 638302 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B3902903 : Blo 638302 3902903 := bstep (se 1 (by rfl) ⟨2927177, by rfl⟩ : syracuseStep 3902903 = 5854355) B5854355
theorem B2166263 : Blo 638302 2166263 := bstep (se 1 (by rfl) ⟨1624697, by rfl⟩ : syracuseStep 2166263 = 3249395) B3249395
theorem B1216063 : Blo 638302 1216063 := bstep (se 1 (by rfl) ⟨912047, by rfl⟩ : syracuseStep 1216063 = 1824095) B1824095
theorem B2592593 : Blo 638302 2592593 := bstep (se 2 (by rfl) ⟨972222, by rfl⟩ : syracuseStep 2592593 = 1944445) B1944445
theorem B2167289 : Blo 638302 2167289 := bstep (se 2 (by rfl) ⟨812733, by rfl⟩ : syracuseStep 2167289 = 1625467) B1625467
theorem B1217119 : Blo 638302 1217119 := bstep (se 1 (by rfl) ⟨912839, by rfl⟩ : syracuseStep 1217119 = 1825679) B1825679
theorem B2167559 : Blo 638302 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B2167613 : Blo 638302 2167613 := bstep (se 3 (by rfl) ⟨406427, by rfl⟩ : syracuseStep 2167613 = 812855) B812855
theorem B6165395 : Blo 638302 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B1151911 : Blo 638302 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B3937319 : Blo 638302 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B3249233 : Blo 638302 3249233 := bstep (se 2 (by rfl) ⟨1218462, by rfl⟩ : syracuseStep 3249233 = 2436925) B2436925
theorem B2430395 : Blo 638302 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B1218721 : Blo 638302 1218721 := bstep (se 2 (by rfl) ⟨457020, by rfl⟩ : syracuseStep 1218721 = 914041) B914041
theorem B209852765 : Blo 638302 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B1022491 : Blo 638302 1022491 := bstep (se 1 (by rfl) ⟨766868, by rfl⟩ : syracuseStep 1022491 = 1533737) B1533737
theorem B957623 : Blo 638302 957623 := bstep (se 1 (by rfl) ⟨718217, by rfl⟩ : syracuseStep 957623 = 1436435) B1436435
theorem B1023311 : Blo 638302 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B957863 : Blo 638302 957863 := bstep (se 1 (by rfl) ⟨718397, by rfl⟩ : syracuseStep 957863 = 1436795) B1436795
theorem B957947 : Blo 638302 957947 := bstep (se 1 (by rfl) ⟨718460, by rfl⟩ : syracuseStep 957947 = 1436921) B1436921
theorem B3939877 : Blo 638302 3939877 := bstep (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) B738727
theorem B6757967 : Blo 638302 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B958043 : Blo 638302 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B1580687 : Blo 638302 1580687 := bstep (se 1 (by rfl) ⟨1185515, by rfl⟩ : syracuseStep 1580687 = 2371031) B2371031
theorem B958127 : Blo 638302 958127 := bstep (se 1 (by rfl) ⟨718595, by rfl⟩ : syracuseStep 958127 = 1437191) B1437191
theorem B1023721 : Blo 638302 1023721 := bstep (se 2 (by rfl) ⟨383895, by rfl⟩ : syracuseStep 1023721 = 767791) B767791
theorem B958247 : Blo 638302 958247 := bstep (se 1 (by rfl) ⟨718685, by rfl⟩ : syracuseStep 958247 = 1437371) B1437371
theorem B958331 : Blo 638302 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B2072807 : Blo 638302 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B958751 : Blo 638302 958751 := bstep (se 1 (by rfl) ⟨719063, by rfl⟩ : syracuseStep 958751 = 1438127) B1438127
theorem B2433311 : Blo 638302 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B958775 : Blo 638302 958775 := bstep (se 1 (by rfl) ⟨719081, by rfl⟩ : syracuseStep 958775 = 1438163) B1438163
theorem B958847 : Blo 638302 958847 := bstep (se 1 (by rfl) ⟨719135, by rfl⟩ : syracuseStep 958847 = 1438271) B1438271
theorem B958919 : Blo 638302 958919 := bstep (se 1 (by rfl) ⟨719189, by rfl⟩ : syracuseStep 958919 = 1438379) B1438379
theorem B1319375 : Blo 638302 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B15540959 : Blo 638302 15540959 := bstep (se 1 (by rfl) ⟨11655719, by rfl⟩ : syracuseStep 15540959 = 23311439) B23311439
theorem B959273 : Blo 638302 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B959279 : Blo 638302 959279 := bstep (se 1 (by rfl) ⟨719459, by rfl⟩ : syracuseStep 959279 = 1438919) B1438919
theorem B959399 : Blo 638302 959399 := bstep (se 1 (by rfl) ⟨719549, by rfl⟩ : syracuseStep 959399 = 1439099) B1439099
theorem B959483 : Blo 638302 959483 := bstep (se 1 (by rfl) ⟨719612, by rfl⟩ : syracuseStep 959483 = 1439225) B1439225
theorem B4105241 : Blo 638302 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B959543 : Blo 638302 959543 := bstep (se 1 (by rfl) ⟨719657, by rfl⟩ : syracuseStep 959543 = 1439315) B1439315
theorem B1025131 : Blo 638302 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B959663 : Blo 638302 959663 := bstep (se 1 (by rfl) ⟨719747, by rfl⟩ : syracuseStep 959663 = 1439495) B1439495
theorem B960071 : Blo 638302 960071 := bstep (se 1 (by rfl) ⟨720053, by rfl⟩ : syracuseStep 960071 = 1440107) B1440107
theorem B960167 : Blo 638302 960167 := bstep (se 1 (by rfl) ⟨720125, by rfl⟩ : syracuseStep 960167 = 1440251) B1440251
theorem B960251 : Blo 638302 960251 := bstep (se 1 (by rfl) ⟨720188, by rfl⟩ : syracuseStep 960251 = 1440377) B1440377
theorem B960287 : Blo 638302 960287 := bstep (se 1 (by rfl) ⟨720215, by rfl⟩ : syracuseStep 960287 = 1440431) B1440431
theorem B960335 : Blo 638302 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B960455 : Blo 638302 960455 := bstep (se 1 (by rfl) ⟨720341, by rfl⟩ : syracuseStep 960455 = 1440683) B1440683
theorem B4368329 : Blo 638302 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B960809 : Blo 638302 960809 := bstep (se 2 (by rfl) ⟨360303, by rfl⟩ : syracuseStep 960809 = 720607) B720607
theorem B960815 : Blo 638302 960815 := bstep (se 1 (by rfl) ⟨720611, by rfl⟩ : syracuseStep 960815 = 1441223) B1441223
theorem B1026361 : Blo 638302 1026361 := bstep (se 2 (by rfl) ⟨384885, by rfl⟩ : syracuseStep 1026361 = 769771) B769771
theorem B1943947 : Blo 638302 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B2435467 : Blo 638302 2435467 := bstep (se 1 (by rfl) ⟨1826600, by rfl⟩ : syracuseStep 2435467 = 3653201) B3653201
theorem B961055 : Blo 638302 961055 := bstep (se 1 (by rfl) ⟨720791, by rfl⟩ : syracuseStep 961055 = 1441583) B1441583
theorem B13806395 : Blo 638302 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B961439 : Blo 638302 961439 := bstep (se 1 (by rfl) ⟨721079, by rfl⟩ : syracuseStep 961439 = 1442159) B1442159
theorem B961487 : Blo 638302 961487 := bstep (se 1 (by rfl) ⟨721115, by rfl⟩ : syracuseStep 961487 = 1442231) B1442231
theorem B961577 : Blo 638302 961577 := bstep (se 2 (by rfl) ⟨360591, by rfl⟩ : syracuseStep 961577 = 721183) B721183
theorem B961583 : Blo 638302 961583 := bstep (se 1 (by rfl) ⟨721187, by rfl⟩ : syracuseStep 961583 = 1442375) B1442375
theorem B961607 : Blo 638302 961607 := bstep (se 1 (by rfl) ⟨721205, by rfl⟩ : syracuseStep 961607 = 1442411) B1442411
theorem B2338073 : Blo 638302 2338073 := bstep (se 2 (by rfl) ⟨876777, by rfl⟩ : syracuseStep 2338073 = 1753555) B1753555
theorem B961871 : Blo 638302 961871 := bstep (se 1 (by rfl) ⟨721403, by rfl⟩ : syracuseStep 961871 = 1442807) B1442807
theorem B961961 : Blo 638302 961961 := bstep (se 2 (by rfl) ⟨360735, by rfl⟩ : syracuseStep 961961 = 721471) B721471
theorem B1027579 : Blo 638302 1027579 := bstep (se 1 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 1027579 = 1541369) B1541369
theorem B962111 : Blo 638302 962111 := bstep (se 1 (by rfl) ⟨721583, by rfl⟩ : syracuseStep 962111 = 1443167) B1443167
theorem B962375 : Blo 638302 962375 := bstep (se 1 (by rfl) ⟨721781, by rfl⟩ : syracuseStep 962375 = 1443563) B1443563
theorem B1617803 : Blo 638302 1617803 := bstep (se 1 (by rfl) ⟨1213352, by rfl⟩ : syracuseStep 1617803 = 2426705) B2426705
theorem B962459 : Blo 638302 962459 := bstep (se 1 (by rfl) ⟨721844, by rfl⟩ : syracuseStep 962459 = 1443689) B1443689
theorem B2306015 : Blo 638302 2306015 := bstep (se 1 (by rfl) ⟨1729511, by rfl⟩ : syracuseStep 2306015 = 3459023) B3459023
theorem B17576099 : Blo 638302 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B963023 : Blo 638302 963023 := bstep (se 1 (by rfl) ⟨722267, by rfl⟩ : syracuseStep 963023 = 1444535) B1444535
theorem B1028585 : Blo 638302 1028585 := bstep (se 2 (by rfl) ⟨385719, by rfl⟩ : syracuseStep 1028585 = 771439) B771439
theorem B963065 : Blo 638302 963065 := bstep (se 2 (by rfl) ⟨361149, by rfl⟩ : syracuseStep 963065 = 722299) B722299
theorem B2437715 : Blo 638302 2437715 := bstep (se 1 (by rfl) ⟨1828286, by rfl⟩ : syracuseStep 2437715 = 3656573) B3656573
theorem B963167 : Blo 638302 963167 := bstep (se 1 (by rfl) ⟨722375, by rfl⟩ : syracuseStep 963167 = 1444751) B1444751
theorem B9220871 : Blo 638302 9220871 := bstep (se 1 (by rfl) ⟨6915653, by rfl⟩ : syracuseStep 9220871 = 13831307) B13831307
theorem B1389563 : Blo 638302 1389563 := bstep (se 1 (by rfl) ⟨1042172, by rfl⟩ : syracuseStep 1389563 = 2084345) B2084345
theorem B1979387 : Blo 638302 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B2307179 : Blo 638302 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B9254087 : Blo 638302 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B1619291 : Blo 638302 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B2438657 : Blo 638302 2438657 := bstep (se 2 (by rfl) ⟨914496, by rfl⟩ : syracuseStep 2438657 = 1828993) B1828993
theorem B9221795 : Blo 638302 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B7288541 : Blo 638302 7288541 := bstep (se 3 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 7288541 = 2733203) B2733203
theorem B2733871 : Blo 638302 2733871 := bstep (se 1 (by rfl) ⟨2050403, by rfl⟩ : syracuseStep 2733871 = 4100807) B4100807
theorem B2733887 : Blo 638302 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B2047123 : Blo 638302 2047123 := bstep (se 1 (by rfl) ⟨1535342, by rfl⟩ : syracuseStep 2047123 = 3070685) B3070685
theorem B2964637 : Blo 638302 2964637 := bstep (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) B1111739
theorem B2735527 : Blo 638302 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B638439 : Blo 638302 638439 := bstep (se 1 (by rfl) ⟨478829, by rfl⟩ : syracuseStep 638439 = 957659) B957659
theorem B18497099 : Blo 638302 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B638555 : Blo 638302 638555 := bstep (se 1 (by rfl) ⟨478916, by rfl⟩ : syracuseStep 638555 = 957833) B957833
theorem B2735801 : Blo 638302 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B638791 : Blo 638302 638791 := bstep (se 1 (by rfl) ⟨479093, by rfl⟩ : syracuseStep 638791 = 958187) B958187
theorem B1621883 : Blo 638302 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B638943 : Blo 638302 638943 := bstep (se 1 (by rfl) ⟨479207, by rfl⟩ : syracuseStep 638943 = 958415) B958415
theorem B3653657 : Blo 638302 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B639207 : Blo 638302 639207 := bstep (se 1 (by rfl) ⟨479405, by rfl⟩ : syracuseStep 639207 = 958811) B958811
theorem B1622369 : Blo 638302 1622369 := bstep (se 2 (by rfl) ⟨608388, by rfl⟩ : syracuseStep 1622369 = 1216777) B1216777
theorem B639359 : Blo 638302 639359 := bstep (se 1 (by rfl) ⟨479519, by rfl⟩ : syracuseStep 639359 = 959039) B959039
theorem B639439 : Blo 638302 639439 := bstep (se 1 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 639439 = 959159) B959159
theorem B3686975 : Blo 638302 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B639591 : Blo 638302 639591 := bstep (se 1 (by rfl) ⟨479693, by rfl⟩ : syracuseStep 639591 = 959387) B959387
theorem B639855 : Blo 638302 639855 := bstep (se 1 (by rfl) ⟨479891, by rfl⟩ : syracuseStep 639855 = 959783) B959783
theorem B5456807 : Blo 638302 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B639911 : Blo 638302 639911 := bstep (se 1 (by rfl) ⟨479933, by rfl⟩ : syracuseStep 639911 = 959867) B959867
theorem B4113337 : Blo 638302 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B639995 : Blo 638302 639995 := bstep (se 1 (by rfl) ⟨479996, by rfl⟩ : syracuseStep 639995 = 959993) B959993
theorem B640063 : Blo 638302 640063 := bstep (se 1 (by rfl) ⟨480047, by rfl⟩ : syracuseStep 640063 = 960095) B960095
theorem B640207 : Blo 638302 640207 := bstep (se 1 (by rfl) ⟨480155, by rfl⟩ : syracuseStep 640207 = 960311) B960311
theorem B9225485 : Blo 638302 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B640411 : Blo 638302 640411 := bstep (se 1 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 640411 = 960617) B960617
theorem B3458519 : Blo 638302 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B640623 : Blo 638302 640623 := bstep (se 1 (by rfl) ⟨480467, by rfl⟩ : syracuseStep 640623 = 960935) B960935
theorem B640679 : Blo 638302 640679 := bstep (se 1 (by rfl) ⟨480509, by rfl⟩ : syracuseStep 640679 = 961019) B961019
theorem B640763 : Blo 638302 640763 := bstep (se 1 (by rfl) ⟨480572, by rfl⟩ : syracuseStep 640763 = 961145) B961145
theorem B640799 : Blo 638302 640799 := bstep (se 1 (by rfl) ⟨480599, by rfl⟩ : syracuseStep 640799 = 961199) B961199
theorem B640831 : Blo 638302 640831 := bstep (se 1 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 640831 = 961247) B961247
theorem B1820495 : Blo 638302 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B641007 : Blo 638302 641007 := bstep (se 1 (by rfl) ⟨480755, by rfl⟩ : syracuseStep 641007 = 961511) B961511
theorem B4114567 : Blo 638302 4114567 := bstep (se 1 (by rfl) ⟨3085925, by rfl⟩ : syracuseStep 4114567 = 6171851) B6171851
theorem B641179 : Blo 638302 641179 := bstep (se 1 (by rfl) ⟨480884, by rfl⟩ : syracuseStep 641179 = 961769) B961769
theorem B641215 : Blo 638302 641215 := bstep (se 1 (by rfl) ⟨480911, by rfl⟩ : syracuseStep 641215 = 961823) B961823
theorem B1624313 : Blo 638302 1624313 := bstep (se 2 (by rfl) ⟨609117, by rfl⟩ : syracuseStep 1624313 = 1218235) B1218235
theorem B641327 : Blo 638302 641327 := bstep (se 1 (by rfl) ⟨480995, by rfl⟩ : syracuseStep 641327 = 961991) B961991
theorem B2312543 : Blo 638302 2312543 := bstep (se 1 (by rfl) ⟨1734407, by rfl⟩ : syracuseStep 2312543 = 3468815) B3468815
theorem B641563 : Blo 638302 641563 := bstep (se 1 (by rfl) ⟨481172, by rfl⟩ : syracuseStep 641563 = 962345) B962345
theorem B641567 : Blo 638302 641567 := bstep (se 1 (by rfl) ⟨481175, by rfl⟩ : syracuseStep 641567 = 962351) B962351
theorem B1624607 : Blo 638302 1624607 := bstep (se 1 (by rfl) ⟨1218455, by rfl⟩ : syracuseStep 1624607 = 2436911) B2436911
theorem B4868747 : Blo 638302 4868747 := bstep (se 1 (by rfl) ⟨3651560, by rfl⟩ : syracuseStep 4868747 = 7303121) B7303121
theorem B641883 : Blo 638302 641883 := bstep (se 1 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 641883 = 962825) B962825
theorem B641951 : Blo 638302 641951 := bstep (se 1 (by rfl) ⟨481463, by rfl⟩ : syracuseStep 641951 = 962927) B962927
theorem B22465511 : Blo 638302 22465511 := bstep (se 1 (by rfl) ⟨16849133, by rfl⟩ : syracuseStep 22465511 = 33698267) B33698267
theorem B4148261 : Blo 638302 4148261 := bstep (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) B777799
theorem B642095 : Blo 638302 642095 := bstep (se 1 (by rfl) ⟨481571, by rfl⟩ : syracuseStep 642095 = 963143) B963143
theorem B642119 : Blo 638302 642119 := bstep (se 1 (by rfl) ⟨481589, by rfl⟩ : syracuseStep 642119 = 963179) B963179
theorem B642271 : Blo 638302 642271 := bstep (se 1 (by rfl) ⟨481703, by rfl⟩ : syracuseStep 642271 = 963407) B963407
theorem B1821977 : Blo 638302 1821977 := bstep (se 2 (by rfl) ⟨683241, by rfl⟩ : syracuseStep 1821977 = 1366483) B1366483
theorem B1953193 : Blo 638302 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B51269699 : Blo 638302 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B2674873 : Blo 638302 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B5460803 : Blo 638302 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B4871177 : Blo 638302 4871177 := bstep (se 2 (by rfl) ⟨1826691, by rfl⟩ : syracuseStep 4871177 = 3653383) B3653383
theorem B2741303 : Blo 638302 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B2053183 : Blo 638302 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B1365167 : Blo 638302 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B4609399 : Blo 638302 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B3462587 : Blo 638302 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B808699 : Blo 638302 808699 := bstep (se 1 (by rfl) ⟨606524, by rfl⟩ : syracuseStep 808699 = 1213049) B1213049
theorem B12310487 : Blo 638302 12310487 := bstep (se 1 (by rfl) ⟨9232865, by rfl⟩ : syracuseStep 12310487 = 18465731) B18465731
theorem B1365979 : Blo 638302 1365979 := bstep (se 1 (by rfl) ⟨1024484, by rfl⟩ : syracuseStep 1365979 = 2048969) B2048969
theorem B2742635 : Blo 638302 2742635 := bstep (se 1 (by rfl) ⟨2056976, by rfl⟩ : syracuseStep 2742635 = 4113953) B4113953
theorem B2775485 : Blo 638302 2775485 := bstep (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) B1040807
theorem B29547341 : Blo 638302 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B1727315 : Blo 638302 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B810319 : Blo 638302 810319 := bstep (se 1 (by rfl) ⟨607739, by rfl⟩ : syracuseStep 810319 = 1215479) B1215479
theorem B810587 : Blo 638302 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B1367695 : Blo 638302 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B7791011 : Blo 638302 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B2187719 : Blo 638302 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B1729001 : Blo 638302 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B1827593 : Blo 638302 1827593 := bstep (se 2 (by rfl) ⟨685347, by rfl⟩ : syracuseStep 1827593 = 1370695) B1370695
theorem B3466003 : Blo 638302 3466003 := bstep (se 1 (by rfl) ⟨2599502, by rfl⟩ : syracuseStep 3466003 = 5199005) B5199005
theorem B3334931 : Blo 638302 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B4154267 : Blo 638302 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B5465177 : Blo 638302 5465177 := bstep (se 2 (by rfl) ⟨2049441, by rfl⟩ : syracuseStep 5465177 = 4098883) B4098883
theorem B2155625 : Blo 638302 2155625 := bstep (se 2 (by rfl) ⟨808359, by rfl⟩ : syracuseStep 2155625 = 1616719) B1616719
theorem B812207 : Blo 638302 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B8316265 : Blo 638302 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B681691 : Blo 638302 681691 := bstep (se 1 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 681691 = 1022537) B1022537
theorem B878399 : Blo 638302 878399 := bstep (se 1 (by rfl) ⟨658799, by rfl⟩ : syracuseStep 878399 = 1317599) B1317599
theorem B2156489 : Blo 638302 2156489 := bstep (se 2 (by rfl) ⟨808683, by rfl⟩ : syracuseStep 2156489 = 1617367) B1617367
theorem B911353 : Blo 638302 911353 := bstep (se 2 (by rfl) ⟨341757, by rfl⟩ : syracuseStep 911353 = 683515) B683515
theorem B682139 : Blo 638302 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B2156759 : Blo 638302 2156759 := bstep (se 1 (by rfl) ⟨1617569, by rfl⟩ : syracuseStep 2156759 = 3235139) B3235139
theorem B4090169 : Blo 638302 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B2157083 : Blo 638302 2157083 := bstep (se 1 (by rfl) ⟨1617812, by rfl⟩ : syracuseStep 2157083 = 3235625) B3235625
theorem B2190007 : Blo 638302 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B1436471 : Blo 638302 1436471 := bstep (se 1 (by rfl) ⟨1077353, by rfl⟩ : syracuseStep 1436471 = 2154707) B2154707
theorem B1436651 : Blo 638302 1436651 := bstep (se 1 (by rfl) ⟨1077488, by rfl⟩ : syracuseStep 1436651 = 2154977) B2154977
theorem B5008391 : Blo 638302 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B4385927 : Blo 638302 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B9235633 : Blo 638302 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B2157947 : Blo 638302 2157947 := bstep (se 1 (by rfl) ⟨1618460, by rfl⟩ : syracuseStep 2157947 = 3236921) B3236921
theorem B3698291 : Blo 638302 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B1437479 : Blo 638302 1437479 := bstep (se 1 (by rfl) ⟨1078109, by rfl⟩ : syracuseStep 1437479 = 2156219) B2156219
theorem B18412217 : Blo 638302 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B1077995 : Blo 638302 1077995 := bstep (se 1 (by rfl) ⟨808496, by rfl⟩ : syracuseStep 1077995 = 1616993) B1616993
theorem B2159351 : Blo 638302 2159351 := bstep (se 1 (by rfl) ⟨1619513, by rfl⟩ : syracuseStep 2159351 = 3239027) B3239027
theorem B1438505 : Blo 638302 1438505 := bstep (se 2 (by rfl) ⟨539439, by rfl⟩ : syracuseStep 1438505 = 1078879) B1078879
theorem B1438775 : Blo 638302 1438775 := bstep (se 1 (by rfl) ⟨1079081, by rfl⟩ : syracuseStep 1438775 = 2158163) B2158163
theorem B1438793 : Blo 638302 1438793 := bstep (se 2 (by rfl) ⟨539547, by rfl⟩ : syracuseStep 1438793 = 1079095) B1079095
theorem B1078447 : Blo 638302 1078447 := bstep (se 1 (by rfl) ⟨808835, by rfl⟩ : syracuseStep 1078447 = 1617671) B1617671
theorem B2159891 : Blo 638302 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B34993457 : Blo 638302 34993457 := bstep (se 2 (by rfl) ⟨13122546, by rfl⟩ : syracuseStep 34993457 = 26245093) B26245093
theorem B1537505 : Blo 638302 1537505 := bstep (se 2 (by rfl) ⟨576564, by rfl⟩ : syracuseStep 1537505 = 1153129) B1153129
theorem B718447 : Blo 638302 718447 := bstep (se 1 (by rfl) ⟨538835, by rfl⟩ : syracuseStep 718447 = 1077671) B1077671
theorem B1078967 : Blo 638302 1078967 := bstep (se 1 (by rfl) ⟨809225, by rfl⟩ : syracuseStep 1078967 = 1618451) B1618451
theorem B718555 : Blo 638302 718555 := bstep (se 1 (by rfl) ⟨538916, by rfl⟩ : syracuseStep 718555 = 1077833) B1077833
theorem B6944545 : Blo 638302 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B2160431 : Blo 638302 2160431 := bstep (se 1 (by rfl) ⟨1620323, by rfl⟩ : syracuseStep 2160431 = 3240647) B3240647
theorem B23754653 : Blo 638302 23754653 := bstep (se 3 (by rfl) ⟨4453997, by rfl⟩ : syracuseStep 23754653 = 8907995) B8907995
theorem B3471457 : Blo 638302 3471457 := bstep (se 2 (by rfl) ⟨1301796, by rfl⟩ : syracuseStep 3471457 = 2603593) B2603593
theorem B4847849 : Blo 638302 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B4618739 : Blo 638302 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B719707 : Blo 638302 719707 := bstep (se 1 (by rfl) ⟨539780, by rfl⟩ : syracuseStep 719707 = 1079561) B1079561
theorem B1080155 : Blo 638302 1080155 := bstep (se 1 (by rfl) ⟨810116, by rfl⟩ : syracuseStep 1080155 = 1620233) B1620233
theorem B1440719 : Blo 638302 1440719 := bstep (se 1 (by rfl) ⟨1080539, by rfl⟩ : syracuseStep 1440719 = 2161079) B2161079
theorem B1440737 : Blo 638302 1440737 := bstep (se 2 (by rfl) ⟨540276, by rfl⟩ : syracuseStep 1440737 = 1080553) B1080553
theorem B1440809 : Blo 638302 1440809 := bstep (se 2 (by rfl) ⟨540303, by rfl⟩ : syracuseStep 1440809 = 1080607) B1080607
theorem B1080391 : Blo 638302 1080391 := bstep (se 1 (by rfl) ⟨810293, by rfl⟩ : syracuseStep 1080391 = 1620587) B1620587
theorem B2424275 : Blo 638302 2424275 := bstep (se 1 (by rfl) ⟨1818206, by rfl⟩ : syracuseStep 2424275 = 3636413) B3636413
theorem B35454449 : Blo 638302 35454449 := bstep (se 2 (by rfl) ⟨13295418, by rfl⟩ : syracuseStep 35454449 = 26590837) B26590837
theorem B1080823 : Blo 638302 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B2162267 : Blo 638302 2162267 := bstep (se 1 (by rfl) ⟨1621700, by rfl⟩ : syracuseStep 2162267 = 3243401) B3243401
theorem B3636845 : Blo 638302 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B720679 : Blo 638302 720679 := bstep (se 1 (by rfl) ⟨540509, by rfl⟩ : syracuseStep 720679 = 1081019) B1081019
theorem B1081127 : Blo 638302 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B3637163 : Blo 638302 3637163 := bstep (se 1 (by rfl) ⟨2727872, by rfl⟩ : syracuseStep 3637163 = 5455745) B5455745
theorem B1441979 : Blo 638302 1441979 := bstep (se 1 (by rfl) ⟨1081484, by rfl⟩ : syracuseStep 1441979 = 2162969) B2162969
theorem B1081579 : Blo 638302 1081579 := bstep (se 1 (by rfl) ⟨811184, by rfl⟩ : syracuseStep 1081579 = 1622369) B1622369
theorem B1442087 : Blo 638302 1442087 := bstep (se 1 (by rfl) ⟨1081565, by rfl⟩ : syracuseStep 1442087 = 2163131) B2163131
theorem B2457983 : Blo 638302 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B721435 : Blo 638302 721435 := bstep (se 1 (by rfl) ⟨541076, by rfl⟩ : syracuseStep 721435 = 1082153) B1082153
theorem B3637871 : Blo 638302 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B1442465 : Blo 638302 1442465 := bstep (se 2 (by rfl) ⟨540924, by rfl⟩ : syracuseStep 1442465 = 1081849) B1081849
theorem B721615 : Blo 638302 721615 := bstep (se 1 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 721615 = 1082423) B1082423
theorem B1442825 : Blo 638302 1442825 := bstep (se 2 (by rfl) ⟨541059, by rfl⟩ : syracuseStep 1442825 = 1082119) B1082119
theorem B4621337 : Blo 638302 4621337 := bstep (se 2 (by rfl) ⟨1733001, by rfl⟩ : syracuseStep 4621337 = 3466003) B3466003
theorem B1442879 : Blo 638302 1442879 := bstep (se 1 (by rfl) ⟨1082159, by rfl⟩ : syracuseStep 1442879 = 2164319) B2164319
theorem B1082875 : Blo 638302 1082875 := bstep (se 1 (by rfl) ⟨812156, by rfl⟩ : syracuseStep 1082875 = 1624313) B1624313
theorem B1541695 : Blo 638302 1541695 := bstep (se 1 (by rfl) ⟨1156271, by rfl⟩ : syracuseStep 1541695 = 2312543) B2312543
theorem B5473925 : Blo 638302 5473925 := bstep (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) B1026361
theorem B1083071 : Blo 638302 1083071 := bstep (se 1 (by rfl) ⟨812303, by rfl⟩ : syracuseStep 1083071 = 1624607) B1624607
theorem B3245831 : Blo 638302 3245831 := bstep (se 1 (by rfl) ⟨2434373, by rfl⟩ : syracuseStep 3245831 = 4868747) B4868747
theorem B1443815 : Blo 638302 1443815 := bstep (se 1 (by rfl) ⟨1082861, by rfl⟩ : syracuseStep 1443815 = 2165723) B2165723
theorem B14977007 : Blo 638302 14977007 := bstep (se 1 (by rfl) ⟨11232755, by rfl⟩ : syracuseStep 14977007 = 22465511) B22465511
theorem B4851737 : Blo 638302 4851737 := bstep (se 2 (by rfl) ⟨1819401, by rfl⟩ : syracuseStep 4851737 = 3638803) B3638803
theorem B1443995 : Blo 638302 1443995 := bstep (se 1 (by rfl) ⟨1082996, by rfl⟩ : syracuseStep 1443995 = 2165993) B2165993
theorem B1214651 : Blo 638302 1214651 := bstep (se 1 (by rfl) ⟨910988, by rfl⟩ : syracuseStep 1214651 = 1821977) B1821977
theorem B1444175 : Blo 638302 1444175 := bstep (se 1 (by rfl) ⟨1083131, by rfl⟩ : syracuseStep 1444175 = 2166263) B2166263
theorem B11078045 : Blo 638302 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B1444265 : Blo 638302 1444265 := bstep (se 2 (by rfl) ⟨541599, by rfl⟩ : syracuseStep 1444265 = 1083199) B1083199
theorem B1215137 : Blo 638302 1215137 := bstep (se 2 (by rfl) ⟨455676, by rfl⟩ : syracuseStep 1215137 = 911353) B911353
theorem B1444859 : Blo 638302 1444859 := bstep (se 1 (by rfl) ⟨1083644, by rfl⟩ : syracuseStep 1444859 = 2167289) B2167289
theorem B2165885 : Blo 638302 2165885 := bstep (se 3 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 2165885 = 812207) B812207
theorem B1445039 : Blo 638302 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B2591929 : Blo 638302 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B3247289 : Blo 638302 3247289 := bstep (se 2 (by rfl) ⟨1217733, by rfl⟩ : syracuseStep 3247289 = 2435467) B2435467
theorem B1445075 : Blo 638302 1445075 := bstep (se 1 (by rfl) ⟨1083806, by rfl⟩ : syracuseStep 1445075 = 2167613) B2167613
theorem B3640535 : Blo 638302 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B3247451 : Blo 638302 3247451 := bstep (se 1 (by rfl) ⟨2435588, by rfl⟩ : syracuseStep 3247451 = 4871177) B4871177
theorem B2624879 : Blo 638302 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B2166155 : Blo 638302 2166155 := bstep (se 1 (by rfl) ⟨1624616, by rfl⟩ : syracuseStep 2166155 = 3249233) B3249233
theorem B6163937 : Blo 638302 6163937 := bstep (se 2 (by rfl) ⟨2311476, by rfl⟩ : syracuseStep 6163937 = 4622953) B4622953
theorem B19698227 : Blo 638302 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B1151543 : Blo 638302 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B4854653 : Blo 638302 4854653 := bstep (se 3 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 4854653 = 1820495) B1820495
theorem B1053791 : Blo 638302 1053791 := bstep (se 1 (by rfl) ⟨790343, by rfl⟩ : syracuseStep 1053791 = 1580687) B1580687
theorem B1381871 : Blo 638302 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B1152667 : Blo 638302 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B10360639 : Blo 638302 10360639 := bstep (se 1 (by rfl) ⟨7770479, by rfl⟩ : syracuseStep 10360639 = 15540959) B15540959
theorem B1218395 : Blo 638302 1218395 := bstep (se 1 (by rfl) ⟨913796, by rfl⟩ : syracuseStep 1218395 = 1827593) B1827593
theorem B3643451 : Blo 638302 3643451 := bstep (se 1 (by rfl) ⟨2732588, by rfl⟩ : syracuseStep 3643451 = 5465177) B5465177
theorem B2726779 : Blo 638302 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B957647 : Blo 638302 957647 := bstep (se 1 (by rfl) ⟨718235, by rfl⟩ : syracuseStep 957647 = 1436471) B1436471
theorem B957767 : Blo 638302 957767 := bstep (se 1 (by rfl) ⟨718325, by rfl⟩ : syracuseStep 957767 = 1436651) B1436651
theorem B2923951 : Blo 638302 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B957929 : Blo 638302 957929 := bstep (se 2 (by rfl) ⟨359223, by rfl⟩ : syracuseStep 957929 = 718447) B718447
theorem B958073 : Blo 638302 958073 := bstep (se 2 (by rfl) ⟨359277, by rfl⟩ : syracuseStep 958073 = 718555) B718555
theorem B3645161 : Blo 638302 3645161 := bstep (se 2 (by rfl) ⟨1366935, by rfl⟩ : syracuseStep 3645161 = 2733871) B2733871
theorem B2465527 : Blo 638302 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B958319 : Blo 638302 958319 := bstep (se 1 (by rfl) ⟨718739, by rfl⟩ : syracuseStep 958319 = 1437479) B1437479
theorem B4628609 : Blo 638302 4628609 := bstep (se 2 (by rfl) ⟨1735728, by rfl⟩ : syracuseStep 4628609 = 3471457) B3471457
theorem B959003 : Blo 638302 959003 := bstep (se 1 (by rfl) ⟨719252, by rfl⟩ : syracuseStep 959003 = 1438505) B1438505
theorem B926375 : Blo 638302 926375 := bstep (se 1 (by rfl) ⟨694781, by rfl⟩ : syracuseStep 926375 = 1389563) B1389563
theorem B1319591 : Blo 638302 1319591 := bstep (se 1 (by rfl) ⟨989693, by rfl⟩ : syracuseStep 1319591 = 1979387) B1979387
theorem B959183 : Blo 638302 959183 := bstep (se 1 (by rfl) ⟨719387, by rfl⟩ : syracuseStep 959183 = 1438775) B1438775
theorem B959195 : Blo 638302 959195 := bstep (se 1 (by rfl) ⟨719396, by rfl⟩ : syracuseStep 959195 = 1438793) B1438793
theorem B6169391 : Blo 638302 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B2728829 : Blo 638302 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B1025003 : Blo 638302 1025003 := bstep (se 1 (by rfl) ⟨768752, by rfl⟩ : syracuseStep 1025003 = 1537505) B1537505
theorem B959609 : Blo 638302 959609 := bstep (se 2 (by rfl) ⟨359853, by rfl⟩ : syracuseStep 959609 = 719707) B719707
theorem B4859027 : Blo 638302 4859027 := bstep (se 1 (by rfl) ⟨3644270, by rfl⟩ : syracuseStep 4859027 = 7288541) B7288541
theorem B15836435 : Blo 638302 15836435 := bstep (se 1 (by rfl) ⟨11877326, by rfl⟩ : syracuseStep 15836435 = 23754653) B23754653
theorem B2729497 : Blo 638302 2729497 := bstep (se 2 (by rfl) ⟨1023561, by rfl⟩ : syracuseStep 2729497 = 2047123) B2047123
theorem B3647369 : Blo 638302 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B960479 : Blo 638302 960479 := bstep (se 1 (by rfl) ⟨720359, by rfl⟩ : syracuseStep 960479 = 1440719) B1440719
theorem B960491 : Blo 638302 960491 := bstep (se 1 (by rfl) ⟨720368, by rfl⟩ : syracuseStep 960491 = 1440737) B1440737
theorem B960539 : Blo 638302 960539 := bstep (se 1 (by rfl) ⟨720404, by rfl⟩ : syracuseStep 960539 = 1440809) B1440809
theorem B5253169 : Blo 638302 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B1616183 : Blo 638302 1616183 := bstep (se 1 (by rfl) ⟨1212137, by rfl⟩ : syracuseStep 1616183 = 2424275) B2424275
theorem B23636299 : Blo 638302 23636299 := bstep (se 1 (by rfl) ⟨17727224, by rfl⟩ : syracuseStep 23636299 = 35454449) B35454449
theorem B12331399 : Blo 638302 12331399 := bstep (se 1 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 12331399 = 18497099) B18497099
theorem B960905 : Blo 638302 960905 := bstep (se 2 (by rfl) ⟨360339, by rfl⟩ : syracuseStep 960905 = 720679) B720679
theorem B2435771 : Blo 638302 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B136719197 : Blo 638302 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B961847 : Blo 638302 961847 := bstep (se 1 (by rfl) ⟨721385, by rfl⟩ : syracuseStep 961847 = 1442771) B1442771
theorem B962015 : Blo 638302 962015 := bstep (se 1 (by rfl) ⟨721511, by rfl⟩ : syracuseStep 962015 = 1443023) B1443023
theorem B2305679 : Blo 638302 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B962231 : Blo 638302 962231 := bstep (se 1 (by rfl) ⟨721673, by rfl⟩ : syracuseStep 962231 = 1443347) B1443347
theorem B1617641 : Blo 638302 1617641 := bstep (se 2 (by rfl) ⟨606615, by rfl⟩ : syracuseStep 1617641 = 1213231) B1213231
theorem B3518333 : Blo 638302 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B962441 : Blo 638302 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B5484449 : Blo 638302 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B962687 : Blo 638302 962687 := bstep (se 1 (by rfl) ⟨722015, by rfl⟩ : syracuseStep 962687 = 1444031) B1444031
theorem B11088353 : Blo 638302 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B2765507 : Blo 638302 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B963323 : Blo 638302 963323 := bstep (se 1 (by rfl) ⟨722492, by rfl⟩ : syracuseStep 963323 = 1444985) B1444985
theorem B2601791 : Blo 638302 2601791 := bstep (se 1 (by rfl) ⟨1951343, by rfl⟩ : syracuseStep 2601791 = 3902687) B3902687
theorem B1618825 : Blo 638302 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B2601935 : Blo 638302 2601935 := bstep (se 1 (by rfl) ⟨1951451, by rfl⟩ : syracuseStep 2601935 = 3902903) B3902903
theorem B5486089 : Blo 638302 5486089 := bstep (se 2 (by rfl) ⟨2057283, by rfl⟩ : syracuseStep 5486089 = 4114567) B4114567
theorem B4110263 : Blo 638302 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B11680037 : Blo 638302 11680037 := bstep (se 4 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 11680037 = 2190007) B2190007
theorem B1620263 : Blo 638302 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B2308391 : Blo 638302 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B8206991 : Blo 638302 8206991 := bstep (se 1 (by rfl) ⟨6155243, by rfl⟩ : syracuseStep 8206991 = 12310487) B12310487
theorem B139901843 : Blo 638302 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B1850323 : Blo 638302 1850323 := bstep (se 1 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 1850323 = 2775485) B2775485
theorem B2604257 : Blo 638302 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B1621417 : Blo 638302 1621417 := bstep (se 2 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 1621417 = 1216063) B1216063
theorem B638415 : Blo 638302 638415 := bstep (se 1 (by rfl) ⟨478811, by rfl⟩ : syracuseStep 638415 = 957623) B957623
theorem B6143525 : Blo 638302 6143525 := bstep (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) B1151911
theorem B638575 : Blo 638302 638575 := bstep (se 1 (by rfl) ⟨478931, by rfl⟩ : syracuseStep 638575 = 957863) B957863
theorem B638631 : Blo 638302 638631 := bstep (se 1 (by rfl) ⟨478973, by rfl⟩ : syracuseStep 638631 = 957947) B957947
theorem B4505311 : Blo 638302 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B638695 : Blo 638302 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B638751 : Blo 638302 638751 := bstep (se 1 (by rfl) ⟨479063, by rfl⟩ : syracuseStep 638751 = 958127) B958127
theorem B638831 : Blo 638302 638831 := bstep (se 1 (by rfl) ⟨479123, by rfl⟩ : syracuseStep 638831 = 958247) B958247
theorem B638887 : Blo 638302 638887 := bstep (se 1 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 638887 = 958331) B958331
theorem B639167 : Blo 638302 639167 := bstep (se 1 (by rfl) ⟨479375, by rfl⟩ : syracuseStep 639167 = 958751) B958751
theorem B1622207 : Blo 638302 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B639183 : Blo 638302 639183 := bstep (se 1 (by rfl) ⟨479387, by rfl⟩ : syracuseStep 639183 = 958775) B958775
theorem B639231 : Blo 638302 639231 := bstep (se 1 (by rfl) ⟨479423, by rfl⟩ : syracuseStep 639231 = 958847) B958847
theorem B5194007 : Blo 638302 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B639279 : Blo 638302 639279 := bstep (se 1 (by rfl) ⟨479459, by rfl⟩ : syracuseStep 639279 = 958919) B958919
theorem B1458479 : Blo 638302 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B1819037 : Blo 638302 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B639515 : Blo 638302 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B639519 : Blo 638302 639519 := bstep (se 1 (by rfl) ⟨479639, by rfl⟩ : syracuseStep 639519 = 959279) B959279
theorem B639599 : Blo 638302 639599 := bstep (se 1 (by rfl) ⟨479699, by rfl⟩ : syracuseStep 639599 = 959399) B959399
theorem B639655 : Blo 638302 639655 := bstep (se 1 (by rfl) ⟨479741, by rfl⟩ : syracuseStep 639655 = 959483) B959483
theorem B2736827 : Blo 638302 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B639695 : Blo 638302 639695 := bstep (se 1 (by rfl) ⟨479771, by rfl⟩ : syracuseStep 639695 = 959543) B959543
theorem B639775 : Blo 638302 639775 := bstep (se 1 (by rfl) ⟨479831, by rfl⟩ : syracuseStep 639775 = 959663) B959663
theorem B1622825 : Blo 638302 1622825 := bstep (se 2 (by rfl) ⟨608559, by rfl⟩ : syracuseStep 1622825 = 1217119) B1217119
theorem B640047 : Blo 638302 640047 := bstep (se 1 (by rfl) ⟨480035, by rfl⟩ : syracuseStep 640047 = 960071) B960071
theorem B640111 : Blo 638302 640111 := bstep (se 1 (by rfl) ⟨480083, by rfl⟩ : syracuseStep 640111 = 960167) B960167
theorem B640167 : Blo 638302 640167 := bstep (se 1 (by rfl) ⟨480125, by rfl⟩ : syracuseStep 640167 = 960251) B960251
theorem B640191 : Blo 638302 640191 := bstep (se 1 (by rfl) ⟨480143, by rfl⟩ : syracuseStep 640191 = 960287) B960287
theorem B640223 : Blo 638302 640223 := bstep (se 1 (by rfl) ⟨480167, by rfl⟩ : syracuseStep 640223 = 960335) B960335
theorem B640303 : Blo 638302 640303 := bstep (se 1 (by rfl) ⟨480227, by rfl⟩ : syracuseStep 640303 = 960455) B960455
theorem B2737577 : Blo 638302 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B640539 : Blo 638302 640539 := bstep (se 1 (by rfl) ⟨480404, by rfl⟩ : syracuseStep 640539 = 960809) B960809
theorem B640543 : Blo 638302 640543 := bstep (se 1 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 640543 = 960815) B960815
theorem B640703 : Blo 638302 640703 := bstep (se 1 (by rfl) ⟨480527, by rfl⟩ : syracuseStep 640703 = 961055) B961055
theorem B8406773 : Blo 638302 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B6145865 : Blo 638302 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B640959 : Blo 638302 640959 := bstep (se 1 (by rfl) ⟨480719, by rfl⟩ : syracuseStep 640959 = 961439) B961439
theorem B640991 : Blo 638302 640991 := bstep (se 1 (by rfl) ⟨480743, by rfl⟩ : syracuseStep 640991 = 961487) B961487
theorem B641051 : Blo 638302 641051 := bstep (se 1 (by rfl) ⟨480788, by rfl⟩ : syracuseStep 641051 = 961577) B961577
theorem B641055 : Blo 638302 641055 := bstep (se 1 (by rfl) ⟨480791, by rfl⟩ : syracuseStep 641055 = 961583) B961583
theorem B641071 : Blo 638302 641071 := bstep (se 1 (by rfl) ⟨480803, by rfl⟩ : syracuseStep 641071 = 961607) B961607
theorem B1558715 : Blo 638302 1558715 := bstep (se 1 (by rfl) ⟨1169036, by rfl⟩ : syracuseStep 1558715 = 2338073) B2338073
theorem B641247 : Blo 638302 641247 := bstep (se 1 (by rfl) ⟨480935, by rfl⟩ : syracuseStep 641247 = 961871) B961871
theorem B641307 : Blo 638302 641307 := bstep (se 1 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 641307 = 961961) B961961
theorem B641407 : Blo 638302 641407 := bstep (se 1 (by rfl) ⟨481055, by rfl⟩ : syracuseStep 641407 = 962111) B962111
theorem B9259393 : Blo 638302 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B641583 : Blo 638302 641583 := bstep (se 1 (by rfl) ⟨481187, by rfl⟩ : syracuseStep 641583 = 962375) B962375
theorem B641639 : Blo 638302 641639 := bstep (se 1 (by rfl) ⟨481229, by rfl⟩ : syracuseStep 641639 = 962459) B962459
theorem B1821305 : Blo 638302 1821305 := bstep (se 2 (by rfl) ⟨682989, by rfl⟩ : syracuseStep 1821305 = 1365979) B1365979
theorem B11717399 : Blo 638302 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1624961 : Blo 638302 1624961 := bstep (se 2 (by rfl) ⟨609360, by rfl⟩ : syracuseStep 1624961 = 1218721) B1218721
theorem B642015 : Blo 638302 642015 := bstep (se 1 (by rfl) ⟨481511, by rfl⟩ : syracuseStep 642015 = 963023) B963023
theorem B642043 : Blo 638302 642043 := bstep (se 1 (by rfl) ⟨481532, by rfl⟩ : syracuseStep 642043 = 963065) B963065
theorem B1625143 : Blo 638302 1625143 := bstep (se 1 (by rfl) ⟨1218857, by rfl⟩ : syracuseStep 1625143 = 2437715) B2437715
theorem B642111 : Blo 638302 642111 := bstep (se 1 (by rfl) ⟨481583, by rfl⟩ : syracuseStep 642111 = 963167) B963167
theorem B12274811 : Blo 638302 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B6147247 : Blo 638302 6147247 := bstep (se 1 (by rfl) ⟨4610435, by rfl⟩ : syracuseStep 6147247 = 9220871) B9220871
theorem B2805101 : Blo 638302 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B1363321 : Blo 638302 1363321 := bstep (se 2 (by rfl) ⟨511245, by rfl⟩ : syracuseStep 1363321 = 1022491) B1022491
theorem B7294373 : Blo 638302 7294373 := bstep (se 4 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 7294373 = 1367695) B1367695
theorem B1625771 : Blo 638302 1625771 := bstep (se 1 (by rfl) ⟨1219328, by rfl⟩ : syracuseStep 1625771 = 2438657) B2438657
theorem B6147863 : Blo 638302 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B1822591 : Blo 638302 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B5459845 : Blo 638302 5459845 := bstep (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) B1023721
theorem B3231899 : Blo 638302 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B3952849 : Blo 638302 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B1823867 : Blo 638302 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B2774695 : Blo 638302 2774695 := bstep (se 1 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 2774695 = 4162043) B4162043
theorem B2053799 : Blo 638302 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B808795 : Blo 638302 808795 := bstep (se 1 (by rfl) ⟨606596, by rfl⟩ : syracuseStep 808795 = 1213193) B1213193
theorem B6150323 : Blo 638302 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B4872635 : Blo 638302 4872635 := bstep (se 1 (by rfl) ⟨3654476, by rfl⟩ : syracuseStep 4872635 = 7308953) B7308953
theorem B2742893 : Blo 638302 2742893 := bstep (se 3 (by rfl) ⟨514292, by rfl⟩ : syracuseStep 2742893 = 1028585) B1028585
theorem B1366841 : Blo 638302 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B5201081 : Blo 638302 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B908921 : Blo 638302 908921 := bstep (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) B681691
theorem B1728395 : Blo 638302 1728395 := bstep (se 1 (by rfl) ⟨1296296, by rfl⟩ : syracuseStep 1728395 = 2592593) B2592593
theorem B1827535 : Blo 638302 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B910111 : Blo 638302 910111 := bstep (se 1 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 910111 = 1365167) B1365167
theorem B20800421 : Blo 638302 20800421 := bstep (se 4 (by rfl) ⟨1950039, by rfl⟩ : syracuseStep 20800421 = 3900079) B3900079
theorem B12314177 : Blo 638302 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B1828423 : Blo 638302 1828423 := bstep (se 1 (by rfl) ⟨1371317, by rfl⟩ : syracuseStep 1828423 = 2742635) B2742635
theorem B1370105 : Blo 638302 1370105 := bstep (se 2 (by rfl) ⟨513789, by rfl⟩ : syracuseStep 1370105 = 1027579) B1027579
theorem B3566497 : Blo 638302 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B2223287 : Blo 638302 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B1437083 : Blo 638302 1437083 := bstep (se 1 (by rfl) ⟨1077812, by rfl⟩ : syracuseStep 1437083 = 2155625) B2155625
theorem B2912219 : Blo 638302 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B1437659 : Blo 638302 1437659 := bstep (se 1 (by rfl) ⟨1078244, by rfl⟩ : syracuseStep 1437659 = 2156489) B2156489
theorem B12316637 : Blo 638302 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B1437839 : Blo 638302 1437839 := bstep (se 1 (by rfl) ⟨1078379, by rfl⟩ : syracuseStep 1437839 = 2156759) B2156759
theorem B1437929 : Blo 638302 1437929 := bstep (se 2 (by rfl) ⟨539223, by rfl⟩ : syracuseStep 1437929 = 1078447) B1078447
theorem B1438055 : Blo 638302 1438055 := bstep (se 1 (by rfl) ⟨1078541, by rfl⟩ : syracuseStep 1438055 = 2157083) B2157083
theorem B9204263 : Blo 638302 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B3338927 : Blo 638302 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B1438631 : Blo 638302 1438631 := bstep (se 1 (by rfl) ⟨1078973, by rfl⟩ : syracuseStep 1438631 = 2157947) B2157947
theorem B1078265 : Blo 638302 1078265 := bstep (se 2 (by rfl) ⟨404349, by rfl⟩ : syracuseStep 1078265 = 808699) B808699
theorem B1078535 : Blo 638302 1078535 := bstep (se 1 (by rfl) ⟨808901, by rfl⟩ : syracuseStep 1078535 = 1617803) B1617803
theorem B1537343 : Blo 638302 1537343 := bstep (se 1 (by rfl) ⟨1153007, by rfl⟩ : syracuseStep 1537343 = 2306015) B2306015
theorem B718663 : Blo 638302 718663 := bstep (se 1 (by rfl) ⟨538997, by rfl⟩ : syracuseStep 718663 = 1077995) B1077995
theorem B1439567 : Blo 638302 1439567 := bstep (se 1 (by rfl) ⟨1079675, by rfl⟩ : syracuseStep 1439567 = 2159351) B2159351
theorem B9369589 : Blo 638302 9369589 := bstep (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) B878399
theorem B1538119 : Blo 638302 1538119 := bstep (se 1 (by rfl) ⟨1153589, by rfl⟩ : syracuseStep 1538119 = 2307179) B2307179
theorem B1439927 : Blo 638302 1439927 := bstep (se 1 (by rfl) ⟨1079945, by rfl⟩ : syracuseStep 1439927 = 2159891) B2159891
theorem B23328971 : Blo 638302 23328971 := bstep (se 1 (by rfl) ⟨17496728, by rfl⟩ : syracuseStep 23328971 = 34993457) B34993457
theorem B1079527 : Blo 638302 1079527 := bstep (se 1 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 1079527 = 1619291) B1619291
theorem B719311 : Blo 638302 719311 := bstep (se 1 (by rfl) ⟨539483, by rfl⟩ : syracuseStep 719311 = 1078967) B1078967
theorem B1440287 : Blo 638302 1440287 := bstep (se 1 (by rfl) ⟨1080215, by rfl⟩ : syracuseStep 1440287 = 2160431) B2160431
theorem B1440521 : Blo 638302 1440521 := bstep (se 2 (by rfl) ⟨540195, by rfl⟩ : syracuseStep 1440521 = 1080391) B1080391
theorem B2161565 : Blo 638302 2161565 := bstep (se 3 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 2161565 = 810587) B810587
theorem B1080425 : Blo 638302 1080425 := bstep (se 2 (by rfl) ⟨405159, by rfl⟩ : syracuseStep 1080425 = 810319) B810319
theorem B720103 : Blo 638302 720103 := bstep (se 1 (by rfl) ⟨540077, by rfl⟩ : syracuseStep 720103 = 1080155) B1080155
theorem B1441097 : Blo 638302 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B1441511 : Blo 638302 1441511 := bstep (se 1 (by rfl) ⟨1081133, by rfl⟩ : syracuseStep 1441511 = 2162267) B2162267
theorem B2424563 : Blo 638302 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B720751 : Blo 638302 720751 := bstep (se 1 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 720751 = 1081127) B1081127
theorem B1081255 : Blo 638302 1081255 := bstep (se 1 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 1081255 = 1621883) B1621883
theorem B2424775 : Blo 638302 2424775 := bstep (se 1 (by rfl) ⟨1818581, by rfl⟩ : syracuseStep 2424775 = 3637163) B3637163
theorem B1081471 : Blo 638302 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B1442105 : Blo 638302 1442105 := bstep (se 2 (by rfl) ⟨540789, by rfl⟩ : syracuseStep 1442105 = 1081579) B1081579
theorem B2425247 : Blo 638302 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B1081883 : Blo 638302 1081883 := bstep (se 1 (by rfl) ⟨811412, by rfl⟩ : syracuseStep 1081883 = 1622825) B1622825
theorem B3080891 : Blo 638302 3080891 := bstep (se 1 (by rfl) ⟨2310668, by rfl⟩ : syracuseStep 3080891 = 4621337) B4621337
theorem B6554621 : Blo 638302 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B1213481 : Blo 638302 1213481 := bstep (se 2 (by rfl) ⟨455055, by rfl⟩ : syracuseStep 1213481 = 910111) B910111
theorem B4850765 : Blo 638302 4850765 := bstep (se 3 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 4850765 = 1819037) B1819037
theorem B722047 : Blo 638302 722047 := bstep (se 1 (by rfl) ⟨541535, by rfl⟩ : syracuseStep 722047 = 1083071) B1083071
theorem B5604515 : Blo 638302 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B2163887 : Blo 638302 2163887 := bstep (se 1 (by rfl) ⟨1622915, by rfl⟩ : syracuseStep 2163887 = 3245831) B3245831
theorem B4097243 : Blo 638302 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B1214203 : Blo 638302 1214203 := bstep (se 1 (by rfl) ⟨910652, by rfl⟩ : syracuseStep 1214203 = 1821305) B1821305
theorem B7374685 : Blo 638302 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B1083307 : Blo 638302 1083307 := bstep (se 1 (by rfl) ⟨812480, by rfl⟩ : syracuseStep 1083307 = 1624961) B1624961
theorem B1443833 : Blo 638302 1443833 := bstep (se 2 (by rfl) ⟨541437, by rfl⟩ : syracuseStep 1443833 = 1082875) B1082875
theorem B3639329 : Blo 638302 3639329 := bstep (se 2 (by rfl) ⟨1364748, by rfl⟩ : syracuseStep 3639329 = 2729497) B2729497
theorem B1443923 : Blo 638302 1443923 := bstep (se 1 (by rfl) ⟨1082942, by rfl⟩ : syracuseStep 1443923 = 2165885) B2165885
theorem B2164859 : Blo 638302 2164859 := bstep (se 1 (by rfl) ⟨1623644, by rfl⟩ : syracuseStep 2164859 = 3247289) B3247289
theorem B2427023 : Blo 638302 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B2164967 : Blo 638302 2164967 := bstep (se 1 (by rfl) ⟨1623725, by rfl⟩ : syracuseStep 2164967 = 3247451) B3247451
theorem B1870067 : Blo 638302 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1444103 : Blo 638302 1444103 := bstep (se 1 (by rfl) ⟨1083077, by rfl⟩ : syracuseStep 1444103 = 2166155) B2166155
theorem B7276877 : Blo 638302 7276877 := bstep (se 3 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 7276877 = 2728829) B2728829
theorem B1083847 : Blo 638302 1083847 := bstep (se 1 (by rfl) ⟨812885, by rfl⟩ : syracuseStep 1083847 = 1625771) B1625771
theorem B4098575 : Blo 638302 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B1215911 : Blo 638302 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B4755329 : Blo 638302 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B2428967 : Blo 638302 2428967 := bstep (se 1 (by rfl) ⟨1821725, by rfl⟩ : syracuseStep 2428967 = 3643451) B3643451
theorem B2166857 : Blo 638302 2166857 := bstep (se 2 (by rfl) ⟨812571, by rfl⟩ : syracuseStep 2166857 = 1625143) B1625143
theorem B4100215 : Blo 638302 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B8196329 : Blo 638302 8196329 := bstep (se 2 (by rfl) ⟨3073623, by rfl⟩ : syracuseStep 8196329 = 6147247) B6147247
theorem B3248423 : Blo 638302 3248423 := bstep (se 1 (by rfl) ⟨2436317, by rfl⟩ : syracuseStep 3248423 = 4872635) B4872635
theorem B2430107 : Blo 638302 2430107 := bstep (se 1 (by rfl) ⟨1822580, by rfl⟩ : syracuseStep 2430107 = 3645161) B3645161
theorem B2430121 : Blo 638302 2430121 := bstep (se 2 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 2430121 = 1822591) B1822591
theorem B7279793 : Blo 638302 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B1152263 : Blo 638302 1152263 := bstep (se 1 (by rfl) ⟨864197, by rfl⟩ : syracuseStep 1152263 = 1728395) B1728395
theorem B3085739 : Blo 638302 3085739 := bstep (se 1 (by rfl) ⟨2314304, by rfl⟩ : syracuseStep 3085739 = 4628609) B4628609
theorem B13866947 : Blo 638302 13866947 := bstep (se 1 (by rfl) ⟨10400210, by rfl⟩ : syracuseStep 13866947 = 20800421) B20800421
theorem B10557623 : Blo 638302 10557623 := bstep (se 1 (by rfl) ⟨7918217, by rfl⟩ : syracuseStep 10557623 = 15836435) B15836435
theorem B2431579 : Blo 638302 2431579 := bstep (se 1 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 2431579 = 3647369) B3647369
theorem B7314785 : Blo 638302 7314785 := bstep (se 2 (by rfl) ⟨2743044, by rfl⟩ : syracuseStep 7314785 = 5486089) B5486089
theorem B1482191 : Blo 638302 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B3644909 : Blo 638302 3644909 := bstep (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) B1366841
theorem B958055 : Blo 638302 958055 := bstep (se 1 (by rfl) ⟨718541, by rfl⟩ : syracuseStep 958055 = 1437083) B1437083
theorem B958217 : Blo 638302 958217 := bstep (se 2 (by rfl) ⟨359331, by rfl⟩ : syracuseStep 958217 = 718663) B718663
theorem B1941479 : Blo 638302 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B958439 : Blo 638302 958439 := bstep (se 1 (by rfl) ⟨718829, by rfl⟩ : syracuseStep 958439 = 1437659) B1437659
theorem B12492785 : Blo 638302 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B958559 : Blo 638302 958559 := bstep (se 1 (by rfl) ⟨718919, by rfl⟩ : syracuseStep 958559 = 1437839) B1437839
theorem B958619 : Blo 638302 958619 := bstep (se 1 (by rfl) ⟨718964, by rfl⟩ : syracuseStep 958619 = 1437929) B1437929
theorem B958703 : Blo 638302 958703 := bstep (se 1 (by rfl) ⟨719027, by rfl⟩ : syracuseStep 958703 = 1438055) B1438055
theorem B6136175 : Blo 638302 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B959081 : Blo 638302 959081 := bstep (se 2 (by rfl) ⟨359655, by rfl⟩ : syracuseStep 959081 = 719311) B719311
theorem B959087 : Blo 638302 959087 := bstep (se 1 (by rfl) ⟨719315, by rfl⟩ : syracuseStep 959087 = 1438631) B1438631
theorem B1024895 : Blo 638302 1024895 := bstep (se 1 (by rfl) ⟨768671, by rfl⟩ : syracuseStep 1024895 = 1537343) B1537343
theorem B959711 : Blo 638302 959711 := bstep (se 1 (by rfl) ⟨719783, by rfl⟩ : syracuseStep 959711 = 1439567) B1439567
theorem B2467097 : Blo 638302 2467097 := bstep (se 2 (by rfl) ⟨925161, by rfl⟩ : syracuseStep 2467097 = 1850323) B1850323
theorem B959951 : Blo 638302 959951 := bstep (se 1 (by rfl) ⟨719963, by rfl⟩ : syracuseStep 959951 = 1439927) B1439927
theorem B960137 : Blo 638302 960137 := bstep (se 2 (by rfl) ⟨360051, by rfl⟩ : syracuseStep 960137 = 720103) B720103
theorem B960191 : Blo 638302 960191 := bstep (se 1 (by rfl) ⟨720143, by rfl⟩ : syracuseStep 960191 = 1440287) B1440287
theorem B960347 : Blo 638302 960347 := bstep (se 1 (by rfl) ⟨720260, by rfl⟩ : syracuseStep 960347 = 1440521) B1440521
theorem B93267895 : Blo 638302 93267895 := bstep (se 1 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 93267895 = 139901843) B139901843
theorem B960731 : Blo 638302 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B6007081 : Blo 638302 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B3287369 : Blo 638302 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B961001 : Blo 638302 961001 := bstep (se 2 (by rfl) ⟨360375, by rfl⟩ : syracuseStep 961001 = 720751) B720751
theorem B961007 : Blo 638302 961007 := bstep (se 1 (by rfl) ⟨720755, by rfl⟩ : syracuseStep 961007 = 1441511) B1441511
theorem B1616375 : Blo 638302 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B961319 : Blo 638302 961319 := bstep (se 1 (by rfl) ⟨720989, by rfl⟩ : syracuseStep 961319 = 1441979) B1441979
theorem B961391 : Blo 638302 961391 := bstep (se 1 (by rfl) ⟨721043, by rfl⟩ : syracuseStep 961391 = 1442087) B1442087
theorem B8203301 : Blo 638302 8203301 := bstep (se 4 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 8203301 = 1538119) B1538119
theorem B961643 : Blo 638302 961643 := bstep (se 1 (by rfl) ⟨721232, by rfl⟩ : syracuseStep 961643 = 1442465) B1442465
theorem B961883 : Blo 638302 961883 := bstep (se 1 (by rfl) ⟨721412, by rfl⟩ : syracuseStep 961883 = 1442825) B1442825
theorem B961913 : Blo 638302 961913 := bstep (se 2 (by rfl) ⟨360717, by rfl⟩ : syracuseStep 961913 = 721435) B721435
theorem B961919 : Blo 638302 961919 := bstep (se 1 (by rfl) ⟨721439, by rfl⟩ : syracuseStep 961919 = 1442879) B1442879
theorem B962153 : Blo 638302 962153 := bstep (se 2 (by rfl) ⟨360807, by rfl⟩ : syracuseStep 962153 = 721615) B721615
theorem B2436713 : Blo 638302 2436713 := bstep (se 2 (by rfl) ⟨913767, by rfl⟩ : syracuseStep 2436713 = 1827535) B1827535
theorem B3649283 : Blo 638302 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B962543 : Blo 638302 962543 := bstep (se 1 (by rfl) ⟨721907, by rfl⟩ : syracuseStep 962543 = 1443815) B1443815
theorem B962663 : Blo 638302 962663 := bstep (se 1 (by rfl) ⟨721997, by rfl⟩ : syracuseStep 962663 = 1443995) B1443995
theorem B962783 : Blo 638302 962783 := bstep (se 1 (by rfl) ⟨722087, by rfl⟩ : syracuseStep 962783 = 1444175) B1444175
theorem B7385363 : Blo 638302 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B962843 : Blo 638302 962843 := bstep (se 1 (by rfl) ⟨722132, by rfl⟩ : syracuseStep 962843 = 1444265) B1444265
theorem B2470333 : Blo 638302 2470333 := bstep (se 3 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 2470333 = 926375) B926375
theorem B7811599 : Blo 638302 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B16626293 : Blo 638302 16626293 := bstep (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) B1558715
theorem B963239 : Blo 638302 963239 := bstep (se 1 (by rfl) ⟨722429, by rfl⟩ : syracuseStep 963239 = 1444859) B1444859
theorem B2437897 : Blo 638302 2437897 := bstep (se 2 (by rfl) ⟨914211, by rfl⟩ : syracuseStep 2437897 = 1828423) B1828423
theorem B963359 : Blo 638302 963359 := bstep (se 1 (by rfl) ⟨722519, by rfl⟩ : syracuseStep 963359 = 1445039) B1445039
theorem B963383 : Blo 638302 963383 := bstep (se 1 (by rfl) ⟨722537, by rfl⟩ : syracuseStep 963383 = 1445075) B1445075
theorem B1749919 : Blo 638302 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B4862915 : Blo 638302 4862915 := bstep (se 1 (by rfl) ⟨3647186, by rfl⟩ : syracuseStep 4862915 = 7294373) B7294373
theorem B4109291 : Blo 638302 4109291 := bstep (se 1 (by rfl) ⟨3081968, by rfl⟩ : syracuseStep 4109291 = 6163937) B6163937
theorem B702527 : Blo 638302 702527 := bstep (se 1 (by rfl) ⟨526895, by rfl⟩ : syracuseStep 702527 = 1053791) B1053791
theorem B3684989 : Blo 638302 3684989 := bstep (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) B1381871
theorem B3455905 : Blo 638302 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B638431 : Blo 638302 638431 := bstep (se 1 (by rfl) ⟨478823, by rfl⟩ : syracuseStep 638431 = 957647) B957647
theorem B638511 : Blo 638302 638511 := bstep (se 1 (by rfl) ⟨478883, by rfl⟩ : syracuseStep 638511 = 957767) B957767
theorem B638619 : Blo 638302 638619 := bstep (se 1 (by rfl) ⟨478964, by rfl⟩ : syracuseStep 638619 = 957929) B957929
theorem B638715 : Blo 638302 638715 := bstep (se 1 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 638715 = 958073) B958073
theorem B638879 : Blo 638302 638879 := bstep (se 1 (by rfl) ⟨479159, by rfl⟩ : syracuseStep 638879 = 958319) B958319
theorem B639335 : Blo 638302 639335 := bstep (se 1 (by rfl) ⟨479501, by rfl⟩ : syracuseStep 639335 = 959003) B959003
theorem B639455 : Blo 638302 639455 := bstep (se 1 (by rfl) ⟨479591, by rfl⟩ : syracuseStep 639455 = 959183) B959183
theorem B639463 : Blo 638302 639463 := bstep (se 1 (by rfl) ⟨479597, by rfl⟩ : syracuseStep 639463 = 959195) B959195
theorem B4112927 : Blo 638302 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B639739 : Blo 638302 639739 := bstep (se 1 (by rfl) ⟨479804, by rfl⟩ : syracuseStep 639739 = 959609) B959609
theorem B8209451 : Blo 638302 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B640319 : Blo 638302 640319 := bstep (se 1 (by rfl) ⟨480239, by rfl⟩ : syracuseStep 640319 = 960479) B960479
theorem B640327 : Blo 638302 640327 := bstep (se 1 (by rfl) ⟨480245, by rfl⟩ : syracuseStep 640327 = 960491) B960491
theorem B640359 : Blo 638302 640359 := bstep (se 1 (by rfl) ⟨480269, by rfl⟩ : syracuseStep 640359 = 960539) B960539
theorem B640603 : Blo 638302 640603 := bstep (se 1 (by rfl) ⟨480452, by rfl⟩ : syracuseStep 640603 = 960905) B960905
theorem B1623847 : Blo 638302 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B91146131 : Blo 638302 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B641231 : Blo 638302 641231 := bstep (se 1 (by rfl) ⟨480923, by rfl⟩ : syracuseStep 641231 = 961847) B961847
theorem B641343 : Blo 638302 641343 := bstep (se 1 (by rfl) ⟨481007, by rfl⟩ : syracuseStep 641343 = 962015) B962015
theorem B13814185 : Blo 638302 13814185 := bstep (se 2 (by rfl) ⟨5180319, by rfl⟩ : syracuseStep 13814185 = 10360639) B10360639
theorem B641487 : Blo 638302 641487 := bstep (se 1 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 641487 = 962231) B962231
theorem B2345555 : Blo 638302 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B641627 : Blo 638302 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B3656299 : Blo 638302 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B8211091 : Blo 638302 8211091 := bstep (se 1 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 8211091 = 12316637) B12316637
theorem B641791 : Blo 638302 641791 := bstep (se 1 (by rfl) ⟨481343, by rfl⟩ : syracuseStep 641791 = 962687) B962687
theorem B7392235 : Blo 638302 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B642215 : Blo 638302 642215 := bstep (se 1 (by rfl) ⟨481661, by rfl⟩ : syracuseStep 642215 = 963323) B963323
theorem B2740175 : Blo 638302 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B15552647 : Blo 638302 15552647 := bstep (se 1 (by rfl) ⟨11664485, by rfl⟩ : syracuseStep 15552647 = 23328971) B23328971
theorem B7786691 : Blo 638302 7786691 := bstep (se 1 (by rfl) ⟨5840018, by rfl⟩ : syracuseStep 7786691 = 11680037) B11680037
theorem B6148477 : Blo 638302 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B3233033 : Blo 638302 3233033 := bstep (se 2 (by rfl) ⟨1212387, by rfl⟩ : syracuseStep 3233033 = 2424775) B2424775
theorem B3462671 : Blo 638302 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B1824551 : Blo 638302 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B3889277 : Blo 638302 3889277 := bstep (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) B1458479
theorem B9984671 : Blo 638302 9984671 := bstep (se 1 (by rfl) ⟨7488503, by rfl⟩ : syracuseStep 9984671 = 14977007) B14977007
theorem B3234491 : Blo 638302 3234491 := bstep (se 1 (by rfl) ⟨2425868, by rfl⟩ : syracuseStep 3234491 = 4851737) B4851737
theorem B809767 : Blo 638302 809767 := bstep (se 1 (by rfl) ⟨607325, by rfl⟩ : syracuseStep 809767 = 1214651) B1214651
theorem B3070781 : Blo 638302 3070781 := bstep (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) B1151543
theorem B810091 : Blo 638302 810091 := bstep (se 1 (by rfl) ⟨607568, by rfl⟩ : syracuseStep 810091 = 1215137) B1215137
theorem B8183207 : Blo 638302 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B2055593 : Blo 638302 2055593 := bstep (se 2 (by rfl) ⟨770847, by rfl⟩ : syracuseStep 2055593 = 1541695) B1541695
theorem B7004225 : Blo 638302 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B2154599 : Blo 638302 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B13132151 : Blo 638302 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B31515065 : Blo 638302 31515065 := bstep (se 2 (by rfl) ⟨11818149, by rfl⟩ : syracuseStep 31515065 = 23636299) B23636299
theorem B12345857 : Blo 638302 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B16441865 : Blo 638302 16441865 := bstep (se 2 (by rfl) ⟨6165699, by rfl⟩ : syracuseStep 16441865 = 12331399) B12331399
theorem B3236435 : Blo 638302 3236435 := bstep (se 1 (by rfl) ⟨2427326, by rfl⟩ : syracuseStep 3236435 = 4854653) B4854653
theorem B7300205 : Blo 638302 7300205 := bstep (se 3 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 7300205 = 2737577) B2737577
theorem B1369199 : Blo 638302 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B812263 : Blo 638302 812263 := bstep (se 1 (by rfl) ⟨609197, by rfl⟩ : syracuseStep 812263 = 1218395) B1218395
theorem B1828595 : Blo 638302 1828595 := bstep (se 1 (by rfl) ⟨1371446, by rfl⟩ : syracuseStep 1828595 = 2742893) B2742893
theorem B3467387 : Blo 638302 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B5270465 : Blo 638302 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B879727 : Blo 638302 879727 := bstep (se 1 (by rfl) ⟨659795, by rfl⟩ : syracuseStep 879727 = 1319591) B1319591
theorem B683335 : Blo 638302 683335 := bstep (se 1 (by rfl) ⟨512501, by rfl⟩ : syracuseStep 683335 = 1025003) B1025003
theorem B3239351 : Blo 638302 3239351 := bstep (se 1 (by rfl) ⟨2429513, by rfl⟩ : syracuseStep 3239351 = 4859027) B4859027
theorem B2158433 : Blo 638302 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B913403 : Blo 638302 913403 := bstep (se 1 (by rfl) ⟨685052, by rfl⟩ : syracuseStep 913403 = 1370105) B1370105
theorem B1077455 : Blo 638302 1077455 := bstep (se 1 (by rfl) ⟨808091, by rfl⟩ : syracuseStep 1077455 = 1616183) B1616183
theorem B7271045 : Blo 638302 7271045 := bstep (se 4 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 7271045 = 1363321) B1363321
theorem B1536889 : Blo 638302 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B3699593 : Blo 638302 3699593 := bstep (se 2 (by rfl) ⟨1387347, by rfl⟩ : syracuseStep 3699593 = 2774695) B2774695
theorem B1078393 : Blo 638302 1078393 := bstep (se 2 (by rfl) ⟨404397, by rfl⟩ : syracuseStep 1078393 = 808795) B808795
theorem B1078427 : Blo 638302 1078427 := bstep (se 1 (by rfl) ⟨808820, by rfl⟩ : syracuseStep 1078427 = 1617641) B1617641
theorem B1439369 : Blo 638302 1439369 := bstep (se 2 (by rfl) ⟨539763, by rfl⟩ : syracuseStep 1439369 = 1079527) B1079527
theorem B2225951 : Blo 638302 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B1734527 : Blo 638302 1734527 := bstep (se 1 (by rfl) ⟨1300895, by rfl⟩ : syracuseStep 1734527 = 2601791) B2601791
theorem B1734623 : Blo 638302 1734623 := bstep (se 1 (by rfl) ⟨1300967, by rfl⟩ : syracuseStep 1734623 = 2601935) B2601935
theorem B718843 : Blo 638302 718843 := bstep (se 1 (by rfl) ⟨539132, by rfl⟩ : syracuseStep 718843 = 1078265) B1078265
theorem B719023 : Blo 638302 719023 := bstep (se 1 (by rfl) ⟨539267, by rfl⟩ : syracuseStep 719023 = 1078535) B1078535
theorem B3635705 : Blo 638302 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B1080175 : Blo 638302 1080175 := bstep (se 1 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 1080175 = 1620263) B1620263
theorem B1538927 : Blo 638302 1538927 := bstep (se 1 (by rfl) ⟨1154195, by rfl⟩ : syracuseStep 1538927 = 2308391) B2308391
theorem B2423789 : Blo 638302 2423789 := bstep (se 3 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 2423789 = 908921) B908921
theorem B5471327 : Blo 638302 5471327 := bstep (se 1 (by rfl) ⟨4103495, by rfl⟩ : syracuseStep 5471327 = 8206991) B8206991
theorem B2161889 : Blo 638302 2161889 := bstep (se 2 (by rfl) ⟨810708, by rfl⟩ : syracuseStep 2161889 = 1621417) B1621417
theorem B3898601 : Blo 638302 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B1441043 : Blo 638302 1441043 := bstep (se 1 (by rfl) ⟨1080782, by rfl⟩ : syracuseStep 1441043 = 2161565) B2161565
theorem B720283 : Blo 638302 720283 := bstep (se 1 (by rfl) ⟨540212, by rfl⟩ : syracuseStep 720283 = 1080425) B1080425
theorem B1736171 : Blo 638302 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B4095683 : Blo 638302 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B1441673 : Blo 638302 1441673 := bstep (se 2 (by rfl) ⟨540627, by rfl⟩ : syracuseStep 1441673 = 1081255) B1081255
theorem B1441961 : Blo 638302 1441961 := bstep (se 2 (by rfl) ⟨540735, by rfl⟩ : syracuseStep 1441961 = 1081471) B1081471
theorem B721255 : Blo 638302 721255 := bstep (se 1 (by rfl) ⟨540941, by rfl⟩ : syracuseStep 721255 = 1081883) B1081883
theorem B5472967 : Blo 638302 5472967 := bstep (se 1 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 5472967 = 8209451) B8209451
theorem B3736343 : Blo 638302 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B1442591 : Blo 638302 1442591 := bstep (se 1 (by rfl) ⟨1081943, by rfl⟩ : syracuseStep 1442591 = 2163887) B2163887
theorem B2426219 : Blo 638302 2426219 := bstep (se 1 (by rfl) ⟨1819664, by rfl⟩ : syracuseStep 2426219 = 3639329) B3639329
theorem B1443239 : Blo 638302 1443239 := bstep (se 1 (by rfl) ⟨1082429, by rfl⟩ : syracuseStep 1443239 = 2164859) B2164859
theorem B1443311 : Blo 638302 1443311 := bstep (se 1 (by rfl) ⟨1082483, by rfl⟩ : syracuseStep 1443311 = 2164967) B2164967
theorem B4851251 : Blo 638302 4851251 := bstep (se 1 (by rfl) ⟨3638438, by rfl⟩ : syracuseStep 4851251 = 7276877) B7276877
theorem B1083017 : Blo 638302 1083017 := bstep (se 2 (by rfl) ⟨406131, by rfl⟩ : syracuseStep 1083017 = 812263) B812263
theorem B2165129 : Blo 638302 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B9832913 : Blo 638302 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B1444409 : Blo 638302 1444409 := bstep (se 2 (by rfl) ⟨541653, by rfl⟩ : syracuseStep 1444409 = 1083307) B1083307
theorem B124357193 : Blo 638302 124357193 := bstep (se 2 (by rfl) ⟨46633947, by rfl⟩ : syracuseStep 124357193 = 93267895) B93267895
theorem B1444571 : Blo 638302 1444571 := bstep (se 1 (by rfl) ⟨1083428, by rfl⟩ : syracuseStep 1444571 = 2166857) B2166857
theorem B2165615 : Blo 638302 2165615 := bstep (se 1 (by rfl) ⟨1624211, by rfl⟩ : syracuseStep 2165615 = 3248423) B3248423
theorem B18418913 : Blo 638302 18418913 := bstep (se 2 (by rfl) ⟨6907092, by rfl⟩ : syracuseStep 18418913 = 13814185) B13814185
theorem B1445129 : Blo 638302 1445129 := bstep (se 2 (by rfl) ⟨541923, by rfl⟩ : syracuseStep 1445129 = 1083847) B1083847
theorem B4853195 : Blo 638302 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B10948121 : Blo 638302 10948121 := bstep (se 2 (by rfl) ⟨4105545, by rfl⟩ : syracuseStep 10948121 = 8211091) B8211091
theorem B1216367 : Blo 638302 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B9244631 : Blo 638302 9244631 := bstep (se 1 (by rfl) ⟨6933473, by rfl⟩ : syracuseStep 9244631 = 13866947) B13866947
theorem B2592851 : Blo 638302 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B6656447 : Blo 638302 6656447 := bstep (se 1 (by rfl) ⟨4992335, by rfl⟩ : syracuseStep 6656447 = 9984671) B9984671
theorem B988127 : Blo 638302 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B2429939 : Blo 638302 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B1873405 : Blo 638302 1873405 := bstep (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) B702527
theorem B8754767 : Blo 638302 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B21010043 : Blo 638302 21010043 := bstep (se 1 (by rfl) ⟨15757532, by rfl⟩ : syracuseStep 21010043 = 31515065) B31515065
theorem B8230571 : Blo 638302 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B8197969 : Blo 638302 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B4986845 : Blo 638302 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B1644731 : Blo 638302 1644731 := bstep (se 1 (by rfl) ⟨1233548, by rfl⟩ : syracuseStep 1644731 = 2467097) B2467097
theorem B3250529 : Blo 638302 3250529 := bstep (se 2 (by rfl) ⟨1218948, by rfl⟩ : syracuseStep 3250529 = 2437897) B2437897
theorem B1219063 : Blo 638302 1219063 := bstep (se 1 (by rfl) ⟨914297, by rfl⟩ : syracuseStep 1219063 = 1828595) B1828595
theorem B2333225 : Blo 638302 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B3644453 : Blo 638302 3644453 := bstep (se 4 (by rfl) ⟨341667, by rfl⟩ : syracuseStep 3644453 = 683335) B683335
theorem B2432855 : Blo 638302 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B958457 : Blo 638302 958457 := bstep (se 2 (by rfl) ⟨359421, by rfl⟩ : syracuseStep 958457 = 718843) B718843
theorem B4923575 : Blo 638302 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B958697 : Blo 638302 958697 := bstep (se 2 (by rfl) ⟨359511, by rfl⟩ : syracuseStep 958697 = 719023) B719023
theorem B11084195 : Blo 638302 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B2466395 : Blo 638302 2466395 := bstep (se 1 (by rfl) ⟨1849796, by rfl⟩ : syracuseStep 2466395 = 3699593) B3699593
theorem B959579 : Blo 638302 959579 := bstep (se 1 (by rfl) ⟨719684, by rfl⟩ : syracuseStep 959579 = 1439369) B1439369
theorem B1483967 : Blo 638302 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B1156351 : Blo 638302 1156351 := bstep (se 1 (by rfl) ⟨867263, by rfl⟩ : syracuseStep 1156351 = 1734527) B1734527
theorem B1156415 : Blo 638302 1156415 := bstep (se 1 (by rfl) ⟨867311, by rfl⟩ : syracuseStep 1156415 = 1734623) B1734623
theorem B960377 : Blo 638302 960377 := bstep (se 2 (by rfl) ⟨360141, by rfl⟩ : syracuseStep 960377 = 720283) B720283
theorem B1025951 : Blo 638302 1025951 := bstep (se 1 (by rfl) ⟨769463, by rfl⟩ : syracuseStep 1025951 = 1538927) B1538927
theorem B1615859 : Blo 638302 1615859 := bstep (se 1 (by rfl) ⟨1211894, by rfl⟩ : syracuseStep 1615859 = 2423789) B2423789
theorem B3647551 : Blo 638302 3647551 := bstep (se 1 (by rfl) ⟨2735663, by rfl⟩ : syracuseStep 3647551 = 5471327) B5471327
theorem B2599067 : Blo 638302 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B960695 : Blo 638302 960695 := bstep (se 1 (by rfl) ⟨720521, by rfl⟩ : syracuseStep 960695 = 1441043) B1441043
theorem B1157447 : Blo 638302 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B2730455 : Blo 638302 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B961115 : Blo 638302 961115 := bstep (se 1 (by rfl) ⟨720836, by rfl⟩ : syracuseStep 961115 = 1441673) B1441673
theorem B2435741 : Blo 638302 2435741 := bstep (se 3 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 2435741 = 913403) B913403
theorem B961403 : Blo 638302 961403 := bstep (se 1 (by rfl) ⟨721052, by rfl⟩ : syracuseStep 961403 = 1442105) B1442105
theorem B1616831 : Blo 638302 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B4369747 : Blo 638302 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B2731495 : Blo 638302 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B16363133 : Blo 638302 16363133 := bstep (se 3 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 16363133 = 6136175) B6136175
theorem B60764087 : Blo 638302 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B962555 : Blo 638302 962555 := bstep (se 1 (by rfl) ⟨721916, by rfl⟩ : syracuseStep 962555 = 1443833) B1443833
theorem B962615 : Blo 638302 962615 := bstep (se 1 (by rfl) ⟨721961, by rfl⟩ : syracuseStep 962615 = 1443923) B1443923
theorem B1618015 : Blo 638302 1618015 := bstep (se 1 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 1618015 = 2427023) B2427023
theorem B962729 : Blo 638302 962729 := bstep (se 2 (by rfl) ⟨361023, by rfl⟩ : syracuseStep 962729 = 722047) B722047
theorem B962735 : Blo 638302 962735 := bstep (se 1 (by rfl) ⟨722051, by rfl⟩ : syracuseStep 962735 = 1444103) B1444103
theorem B2732383 : Blo 638302 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B1618937 : Blo 638302 1618937 := bstep (se 2 (by rfl) ⟨607101, by rfl⟩ : syracuseStep 1618937 = 1214203) B1214203
theorem B1619311 : Blo 638302 1619311 := bstep (se 1 (by rfl) ⟨1214483, by rfl⟩ : syracuseStep 1619311 = 2428967) B2428967
theorem B10368431 : Blo 638302 10368431 := bstep (se 1 (by rfl) ⟨7776323, by rfl⟩ : syracuseStep 10368431 = 15552647) B15552647
theorem B5191127 : Blo 638302 5191127 := bstep (se 1 (by rfl) ⟨3893345, by rfl⟩ : syracuseStep 5191127 = 7786691) B7786691
theorem B8009441 : Blo 638302 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B1620071 : Blo 638302 1620071 := bstep (se 1 (by rfl) ⟨1215053, by rfl⟩ : syracuseStep 1620071 = 2430107) B2430107
theorem B2308447 : Blo 638302 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B2047187 : Blo 638302 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B5455471 : Blo 638302 5455471 := bstep (se 1 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 5455471 = 8183207) B8183207
theorem B638703 : Blo 638302 638703 := bstep (se 1 (by rfl) ⟨479027, by rfl⟩ : syracuseStep 638703 = 958055) B958055
theorem B638811 : Blo 638302 638811 := bstep (se 1 (by rfl) ⟨479108, by rfl⟩ : syracuseStep 638811 = 958217) B958217
theorem B1294319 : Blo 638302 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B638959 : Blo 638302 638959 := bstep (se 1 (by rfl) ⟨479219, by rfl⟩ : syracuseStep 638959 = 958439) B958439
theorem B4669483 : Blo 638302 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B639039 : Blo 638302 639039 := bstep (se 1 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 639039 = 958559) B958559
theorem B639079 : Blo 638302 639079 := bstep (se 1 (by rfl) ⟨479309, by rfl⟩ : syracuseStep 639079 = 958619) B958619
theorem B639135 : Blo 638302 639135 := bstep (se 1 (by rfl) ⟨479351, by rfl⟩ : syracuseStep 639135 = 958703) B958703
theorem B10961243 : Blo 638302 10961243 := bstep (se 1 (by rfl) ⟨8220932, by rfl⟩ : syracuseStep 10961243 = 16441865) B16441865
theorem B639387 : Blo 638302 639387 := bstep (se 1 (by rfl) ⟨479540, by rfl⟩ : syracuseStep 639387 = 959081) B959081
theorem B639391 : Blo 638302 639391 := bstep (se 1 (by rfl) ⟨479543, by rfl⟩ : syracuseStep 639391 = 959087) B959087
theorem B3293777 : Blo 638302 3293777 := bstep (se 2 (by rfl) ⟨1235166, by rfl⟩ : syracuseStep 3293777 = 2470333) B2470333
theorem B4866803 : Blo 638302 4866803 := bstep (se 1 (by rfl) ⟨3650102, by rfl⟩ : syracuseStep 4866803 = 7300205) B7300205
theorem B639807 : Blo 638302 639807 := bstep (se 1 (by rfl) ⟨479855, by rfl⟩ : syracuseStep 639807 = 959711) B959711
theorem B639967 : Blo 638302 639967 := bstep (se 1 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 639967 = 959951) B959951
theorem B640091 : Blo 638302 640091 := bstep (se 1 (by rfl) ⟨480068, by rfl⟩ : syracuseStep 640091 = 960137) B960137
theorem B640127 : Blo 638302 640127 := bstep (se 1 (by rfl) ⟨480095, by rfl⟩ : syracuseStep 640127 = 960191) B960191
theorem B2049185 : Blo 638302 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B640231 : Blo 638302 640231 := bstep (se 1 (by rfl) ⟨480173, by rfl⟩ : syracuseStep 640231 = 960347) B960347
theorem B2311591 : Blo 638302 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B640487 : Blo 638302 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B640667 : Blo 638302 640667 := bstep (se 1 (by rfl) ⟨480500, by rfl⟩ : syracuseStep 640667 = 961001) B961001
theorem B640671 : Blo 638302 640671 := bstep (se 1 (by rfl) ⟨480503, by rfl⟩ : syracuseStep 640671 = 961007) B961007
theorem B640879 : Blo 638302 640879 := bstep (se 1 (by rfl) ⟨480659, by rfl⟩ : syracuseStep 640879 = 961319) B961319
theorem B640927 : Blo 638302 640927 := bstep (se 1 (by rfl) ⟨480695, by rfl⟩ : syracuseStep 640927 = 961391) B961391
theorem B641095 : Blo 638302 641095 := bstep (se 1 (by rfl) ⟨480821, by rfl⟩ : syracuseStep 641095 = 961643) B961643
theorem B641255 : Blo 638302 641255 := bstep (se 1 (by rfl) ⟨480941, by rfl⟩ : syracuseStep 641255 = 961883) B961883
theorem B641275 : Blo 638302 641275 := bstep (se 1 (by rfl) ⟨480956, by rfl⟩ : syracuseStep 641275 = 961913) B961913
theorem B641279 : Blo 638302 641279 := bstep (se 1 (by rfl) ⟨480959, by rfl⟩ : syracuseStep 641279 = 961919) B961919
theorem B641435 : Blo 638302 641435 := bstep (se 1 (by rfl) ⟨481076, by rfl⟩ : syracuseStep 641435 = 962153) B962153
theorem B1624475 : Blo 638302 1624475 := bstep (se 1 (by rfl) ⟨1218356, by rfl⟩ : syracuseStep 1624475 = 2436713) B2436713
theorem B641695 : Blo 638302 641695 := bstep (se 1 (by rfl) ⟨481271, by rfl⟩ : syracuseStep 641695 = 962543) B962543
theorem B641775 : Blo 638302 641775 := bstep (se 1 (by rfl) ⟨481331, by rfl⟩ : syracuseStep 641775 = 962663) B962663
theorem B641855 : Blo 638302 641855 := bstep (se 1 (by rfl) ⟨481391, by rfl⟩ : syracuseStep 641855 = 962783) B962783
theorem B641895 : Blo 638302 641895 := bstep (se 1 (by rfl) ⟨481421, by rfl⟩ : syracuseStep 641895 = 962843) B962843
theorem B642159 : Blo 638302 642159 := bstep (se 1 (by rfl) ⟨481619, by rfl⟩ : syracuseStep 642159 = 963239) B963239
theorem B642239 : Blo 638302 642239 := bstep (se 1 (by rfl) ⟨481679, by rfl⟩ : syracuseStep 642239 = 963359) B963359
theorem B642255 : Blo 638302 642255 := bstep (se 1 (by rfl) ⟨481691, by rfl⟩ : syracuseStep 642255 = 963383) B963383
theorem B2739527 : Blo 638302 2739527 := bstep (se 1 (by rfl) ⟨2054645, by rfl⟩ : syracuseStep 2739527 = 4109291) B4109291
theorem B4607873 : Blo 638302 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B33314093 : Blo 638302 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B2741951 : Blo 638302 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B2053927 : Blo 638302 2053927 := bstep (se 1 (by rfl) ⟨1540445, by rfl⟩ : syracuseStep 2053927 = 3080891) B3080891
theorem B3233843 : Blo 638302 3233843 := bstep (se 1 (by rfl) ⟨2425382, by rfl⟩ : syracuseStep 3233843 = 4850765) B4850765
theorem B3170219 : Blo 638302 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B1826783 : Blo 638302 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B3235949 : Blo 638302 3235949 := bstep (se 3 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 3235949 = 1213481) B1213481
theorem B5464219 : Blo 638302 5464219 := bstep (se 1 (by rfl) ⟨4098164, by rfl⟩ : syracuseStep 5464219 = 8196329) B8196329
theorem B3072701 : Blo 638302 3072701 := bstep (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) B1152263
theorem B4875065 : Blo 638302 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B2155355 : Blo 638302 2155355 := bstep (se 1 (by rfl) ⟨1616516, by rfl⟩ : syracuseStep 2155355 = 3233033) B3233033
theorem B2057159 : Blo 638302 2057159 := bstep (se 1 (by rfl) ⟨1542869, by rfl⟩ : syracuseStep 2057159 = 3085739) B3085739
theorem B9856313 : Blo 638302 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B7038415 : Blo 638302 7038415 := bstep (se 1 (by rfl) ⟨5278811, by rfl⟩ : syracuseStep 7038415 = 10557623) B10557623
theorem B1172969 : Blo 638302 1172969 := bstep (se 2 (by rfl) ⟨439863, by rfl⟩ : syracuseStep 1172969 = 879727) B879727
theorem B2156327 : Blo 638302 2156327 := bstep (se 1 (by rfl) ⟨1617245, by rfl⟩ : syracuseStep 2156327 = 3234491) B3234491
theorem B4876523 : Blo 638302 4876523 := bstep (se 1 (by rfl) ⟨3657392, by rfl⟩ : syracuseStep 4876523 = 7314785) B7314785
theorem B1370395 : Blo 638302 1370395 := bstep (se 1 (by rfl) ⟨1027796, by rfl⟩ : syracuseStep 1370395 = 2055593) B2055593
theorem B1436399 : Blo 638302 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B5466953 : Blo 638302 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B2157623 : Blo 638302 2157623 := bstep (se 1 (by rfl) ⟨1618217, by rfl⟩ : syracuseStep 2157623 = 3236435) B3236435
theorem B683263 : Blo 638302 683263 := bstep (se 1 (by rfl) ⟨512447, by rfl⟩ : syracuseStep 683263 = 1024895) B1024895
theorem B10415465 : Blo 638302 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B912799 : Blo 638302 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B1437857 : Blo 638302 1437857 := bstep (se 2 (by rfl) ⟨539196, by rfl⟩ : syracuseStep 1437857 = 1078393) B1078393
theorem B2191579 : Blo 638302 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B6254813 : Blo 638302 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B3240161 : Blo 638302 3240161 := bstep (se 2 (by rfl) ⟨1215060, by rfl⟩ : syracuseStep 3240161 = 2430121) B2430121
theorem B1077583 : Blo 638302 1077583 := bstep (se 1 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 1077583 = 1616375) B1616375
theorem B5468867 : Blo 638302 5468867 := bstep (se 1 (by rfl) ⟨4101650, by rfl⟩ : syracuseStep 5468867 = 8203301) B8203301
theorem B2159567 : Blo 638302 2159567 := bstep (se 1 (by rfl) ⟨1619675, by rfl⟩ : syracuseStep 2159567 = 3239351) B3239351
theorem B14054573 : Blo 638302 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B1438955 : Blo 638302 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B718303 : Blo 638302 718303 := bstep (se 1 (by rfl) ⟨538727, by rfl⟩ : syracuseStep 718303 = 1077455) B1077455
theorem B4847363 : Blo 638302 4847363 := bstep (se 1 (by rfl) ⟨3635522, by rfl⟩ : syracuseStep 4847363 = 7271045) B7271045
theorem B3241943 : Blo 638302 3241943 := bstep (se 1 (by rfl) ⟨2431457, by rfl⟩ : syracuseStep 3241943 = 4862915) B4862915
theorem B718951 : Blo 638302 718951 := bstep (se 1 (by rfl) ⟨539213, by rfl⟩ : syracuseStep 718951 = 1078427) B1078427
theorem B3242105 : Blo 638302 3242105 := bstep (se 2 (by rfl) ⟨1215789, by rfl⟩ : syracuseStep 3242105 = 2431579) B2431579
theorem B1079689 : Blo 638302 1079689 := bstep (se 2 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 1079689 = 809767) B809767
theorem B3242429 : Blo 638302 3242429 := bstep (se 3 (by rfl) ⟨607955, by rfl⟩ : syracuseStep 3242429 = 1215911) B1215911
theorem B1440233 : Blo 638302 1440233 := bstep (se 2 (by rfl) ⟨540087, by rfl⟩ : syracuseStep 1440233 = 1080175) B1080175
theorem B1080121 : Blo 638302 1080121 := bstep (se 2 (by rfl) ⟨405045, by rfl⟩ : syracuseStep 1080121 = 810091) B810091
theorem B2423803 : Blo 638302 2423803 := bstep (se 1 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 2423803 = 3635705) B3635705
theorem B2456659 : Blo 638302 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B1441259 : Blo 638302 1441259 := bstep (se 1 (by rfl) ⟨1080944, by rfl⟩ : syracuseStep 1441259 = 2161889) B2161889
theorem B6225977 : Blo 638302 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B6914269 : Blo 638302 6914269 := bstep (se 3 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 6914269 = 2592851) B2592851
theorem B7307495 : Blo 638302 7307495 := bstep (se 1 (by rfl) ⟨5480621, by rfl⟩ : syracuseStep 7307495 = 10961243) B10961243
theorem B2195851 : Blo 638302 2195851 := bstep (se 1 (by rfl) ⟨1646888, by rfl⟩ : syracuseStep 2195851 = 3293777) B3293777
theorem B3244535 : Blo 638302 3244535 := bstep (se 1 (by rfl) ⟨2433401, by rfl⟩ : syracuseStep 3244535 = 4866803) B4866803
theorem B2490895 : Blo 638302 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B722011 : Blo 638302 722011 := bstep (se 1 (by rfl) ⟨541508, by rfl⟩ : syracuseStep 722011 = 1083017) B1083017
theorem B1443419 : Blo 638302 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B1082983 : Blo 638302 1082983 := bstep (se 1 (by rfl) ⟨812237, by rfl⟩ : syracuseStep 1082983 = 1624475) B1624475
theorem B6555275 : Blo 638302 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B1541801 : Blo 638302 1541801 := bstep (se 2 (by rfl) ⟨578175, by rfl⟩ : syracuseStep 1541801 = 1156351) B1156351
theorem B82904795 : Blo 638302 82904795 := bstep (se 1 (by rfl) ⟨62178596, by rfl⟩ : syracuseStep 82904795 = 124357193) B124357193
theorem B8193869 : Blo 638302 8193869 := bstep (se 3 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 8193869 = 3072701) B3072701
theorem B3082121 : Blo 638302 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B1443743 : Blo 638302 1443743 := bstep (se 1 (by rfl) ⟨1082807, by rfl⟩ : syracuseStep 1443743 = 2165615) B2165615
theorem B6163087 : Blo 638302 6163087 := bstep (se 1 (by rfl) ⟨4622315, by rfl⟩ : syracuseStep 6163087 = 9244631) B9244631
theorem B658751 : Blo 638302 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B3083773 : Blo 638302 3083773 := bstep (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) B1156415
theorem B5836511 : Blo 638302 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B2167019 : Blo 638302 2167019 := bstep (se 1 (by rfl) ⟨1625264, by rfl⟩ : syracuseStep 2167019 = 3250529) B3250529
theorem B7311869 : Blo 638302 7311869 := bstep (se 3 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 7311869 = 2741951) B2741951
theorem B3641993 : Blo 638302 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B2429635 : Blo 638302 2429635 := bstep (se 1 (by rfl) ⟨1822226, by rfl⟩ : syracuseStep 2429635 = 3644453) B3644453
theorem B1217855 : Blo 638302 1217855 := bstep (se 1 (by rfl) ⟨913391, by rfl⟩ : syracuseStep 1217855 = 1826783) B1826783
theorem B3282383 : Blo 638302 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B1644263 : Blo 638302 1644263 := bstep (se 1 (by rfl) ⟨1233197, by rfl⟩ : syracuseStep 1644263 = 2466395) B2466395
theorem B3643177 : Blo 638302 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B3250043 : Blo 638302 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B3086525 : Blo 638302 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B3251015 : Blo 638302 3251015 := bstep (se 1 (by rfl) ⟨2438261, by rfl⟩ : syracuseStep 3251015 = 4876523) B4876523
theorem B957599 : Blo 638302 957599 := bstep (se 1 (by rfl) ⟨718199, by rfl⟩ : syracuseStep 957599 = 1436399) B1436399
theorem B3644635 : Blo 638302 3644635 := bstep (se 1 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 3644635 = 5466953) B5466953
theorem B957737 : Blo 638302 957737 := bstep (se 2 (by rfl) ⟨359151, by rfl⟩ : syracuseStep 957737 = 718303) B718303
theorem B2497873 : Blo 638302 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B40509391 : Blo 638302 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B958571 : Blo 638302 958571 := bstep (se 1 (by rfl) ⟨718928, by rfl⟩ : syracuseStep 958571 = 1437857) B1437857
theorem B958601 : Blo 638302 958601 := bstep (se 2 (by rfl) ⟨359475, by rfl⟩ : syracuseStep 958601 = 718951) B718951
theorem B4169875 : Blo 638302 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B3645911 : Blo 638302 3645911 := bstep (se 1 (by rfl) ⟨2734433, by rfl⟩ : syracuseStep 3645911 = 5468867) B5468867
theorem B959303 : Blo 638302 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B960155 : Blo 638302 960155 := bstep (se 1 (by rfl) ⟨720116, by rfl⟩ : syracuseStep 960155 = 1440233) B1440233
theorem B960839 : Blo 638302 960839 := bstep (se 1 (by rfl) ⟨720629, by rfl⟩ : syracuseStep 960839 = 1441259) B1441259
theorem B862879 : Blo 638302 862879 := bstep (se 1 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 862879 = 1294319) B1294319
theorem B961307 : Blo 638302 961307 := bstep (se 1 (by rfl) ⟨720980, by rfl⟩ : syracuseStep 961307 = 1441961) B1441961
theorem B7285625 : Blo 638302 7285625 := bstep (se 2 (by rfl) ⟨2732109, by rfl⟩ : syracuseStep 7285625 = 5464219) B5464219
theorem B961673 : Blo 638302 961673 := bstep (se 2 (by rfl) ⟨360627, by rfl⟩ : syracuseStep 961673 = 721255) B721255
theorem B961727 : Blo 638302 961727 := bstep (se 1 (by rfl) ⟨721295, by rfl⟩ : syracuseStep 961727 = 1442591) B1442591
theorem B1617479 : Blo 638302 1617479 := bstep (se 1 (by rfl) ⟨1213109, by rfl⟩ : syracuseStep 1617479 = 2426219) B2426219
theorem B962159 : Blo 638302 962159 := bstep (se 1 (by rfl) ⟨721619, by rfl⟩ : syracuseStep 962159 = 1443239) B1443239
theorem B962207 : Blo 638302 962207 := bstep (se 1 (by rfl) ⟨721655, by rfl⟩ : syracuseStep 962207 = 1443311) B1443311
theorem B962939 : Blo 638302 962939 := bstep (se 1 (by rfl) ⟨722204, by rfl⟩ : syracuseStep 962939 = 1444409) B1444409
theorem B963047 : Blo 638302 963047 := bstep (se 1 (by rfl) ⟨722285, by rfl⟩ : syracuseStep 963047 = 1444571) B1444571
theorem B9384553 : Blo 638302 9384553 := bstep (se 2 (by rfl) ⟨3519207, by rfl⟩ : syracuseStep 9384553 = 7038415) B7038415
theorem B963419 : Blo 638302 963419 := bstep (se 1 (by rfl) ⟨722564, by rfl⟩ : syracuseStep 963419 = 1445129) B1445129
theorem B4863401 : Blo 638302 4863401 := bstep (se 2 (by rfl) ⟨1823775, by rfl⟩ : syracuseStep 4863401 = 3647551) B3647551
theorem B4437631 : Blo 638302 4437631 := bstep (se 1 (by rfl) ⟨3328223, by rfl⟩ : syracuseStep 4437631 = 6656447) B6656447
theorem B1619959 : Blo 638302 1619959 := bstep (se 1 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 1619959 = 2429939) B2429939
theorem B14006695 : Blo 638302 14006695 := bstep (se 1 (by rfl) ⟨10505021, by rfl⟩ : syracuseStep 14006695 = 21010043) B21010043
theorem B5487047 : Blo 638302 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B3324563 : Blo 638302 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B1096487 : Blo 638302 1096487 := bstep (se 1 (by rfl) ⟨822365, by rfl⟩ : syracuseStep 1096487 = 1644731) B1644731
theorem B2735869 : Blo 638302 2735869 := bstep (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) B1025951
theorem B1621903 : Blo 638302 1621903 := bstep (se 1 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 1621903 = 2432855) B2432855
theorem B638971 : Blo 638302 638971 := bstep (se 1 (by rfl) ⟨479228, by rfl⟩ : syracuseStep 638971 = 958457) B958457
theorem B639131 : Blo 638302 639131 := bstep (se 1 (by rfl) ⟨479348, by rfl⟩ : syracuseStep 639131 = 958697) B958697
theorem B7389463 : Blo 638302 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B6930845 : Blo 638302 6930845 := bstep (se 3 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 6930845 = 2599067) B2599067
theorem B639719 : Blo 638302 639719 := bstep (se 1 (by rfl) ⟨479789, by rfl⟩ : syracuseStep 639719 = 959579) B959579
theorem B6570875 : Blo 638302 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B640251 : Blo 638302 640251 := bstep (se 1 (by rfl) ⟨480188, by rfl⟩ : syracuseStep 640251 = 960377) B960377
theorem B640463 : Blo 638302 640463 := bstep (se 1 (by rfl) ⟨480347, by rfl⟩ : syracuseStep 640463 = 960695) B960695
theorem B1820303 : Blo 638302 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B640743 : Blo 638302 640743 := bstep (se 1 (by rfl) ⟨480557, by rfl⟩ : syracuseStep 640743 = 961115) B961115
theorem B1623827 : Blo 638302 1623827 := bstep (se 1 (by rfl) ⟨1217870, by rfl⟩ : syracuseStep 1623827 = 2435741) B2435741
theorem B640935 : Blo 638302 640935 := bstep (se 1 (by rfl) ⟨480701, by rfl⟩ : syracuseStep 640935 = 961403) B961403
theorem B4868261 : Blo 638302 4868261 := bstep (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) B912799
theorem B2738569 : Blo 638302 2738569 := bstep (se 2 (by rfl) ⟨1026963, by rfl⟩ : syracuseStep 2738569 = 2053927) B2053927
theorem B10930625 : Blo 638302 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B641703 : Blo 638302 641703 := bstep (se 1 (by rfl) ⟨481277, by rfl⟩ : syracuseStep 641703 = 962555) B962555
theorem B641743 : Blo 638302 641743 := bstep (se 1 (by rfl) ⟨481307, by rfl⟩ : syracuseStep 641743 = 962615) B962615
theorem B641819 : Blo 638302 641819 := bstep (se 1 (by rfl) ⟨481364, by rfl⟩ : syracuseStep 641819 = 962729) B962729
theorem B641823 : Blo 638302 641823 := bstep (se 1 (by rfl) ⟨481367, by rfl⟩ : syracuseStep 641823 = 962735) B962735
theorem B1625417 : Blo 638302 1625417 := bstep (se 2 (by rfl) ⟨609531, by rfl⟩ : syracuseStep 1625417 = 1219063) B1219063
theorem B3460751 : Blo 638302 3460751 := bstep (se 1 (by rfl) ⟨2595563, by rfl⟩ : syracuseStep 3460751 = 5191127) B5191127
theorem B3231575 : Blo 638302 3231575 := bstep (se 1 (by rfl) ⟨2423681, by rfl⟩ : syracuseStep 3231575 = 4847363) B4847363
theorem B3231737 : Blo 638302 3231737 := bstep (se 2 (by rfl) ⟨1211901, by rfl⟩ : syracuseStep 3231737 = 2423803) B2423803
theorem B1364791 : Blo 638302 1364791 := bstep (se 1 (by rfl) ⟨1023593, by rfl⟩ : syracuseStep 1364791 = 2047187) B2047187
theorem B7297289 : Blo 638302 7297289 := bstep (se 2 (by rfl) ⟨2736483, by rfl⟩ : syracuseStep 7297289 = 5472967) B5472967
theorem B3234167 : Blo 638302 3234167 := bstep (se 1 (by rfl) ⟨2425625, by rfl⟩ : syracuseStep 3234167 = 4851251) B4851251
theorem B11688421 : Blo 638302 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B12279275 : Blo 638302 12279275 := bstep (se 1 (by rfl) ⟨9209456, by rfl⟩ : syracuseStep 12279275 = 18418913) B18418913
theorem B1826351 : Blo 638302 1826351 := bstep (se 1 (by rfl) ⟨1369763, by rfl⟩ : syracuseStep 1826351 = 2739527) B2739527
theorem B3235463 : Blo 638302 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B7298747 : Blo 638302 7298747 := bstep (se 1 (by rfl) ⟨5474060, by rfl⟩ : syracuseStep 7298747 = 10948121) B10948121
theorem B810911 : Blo 638302 810911 := bstep (se 1 (by rfl) ⟨608183, by rfl⟩ : syracuseStep 810911 = 1216367) B1216367
theorem B3071915 : Blo 638302 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B1827193 : Blo 638302 1827193 := bstep (se 2 (by rfl) ⟨685197, by rfl⟩ : syracuseStep 1827193 = 1370395) B1370395
theorem B5464493 : Blo 638302 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B37478861 : Blo 638302 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B3957245 : Blo 638302 3957245 := bstep (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) B1483967
theorem B22209395 : Blo 638302 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B2155895 : Blo 638302 2155895 := bstep (se 1 (by rfl) ⟨1616921, by rfl⟩ : syracuseStep 2155895 = 3233843) B3233843
theorem B911017 : Blo 638302 911017 := bstep (se 2 (by rfl) ⟨341631, by rfl⟩ : syracuseStep 911017 = 683263) B683263
theorem B5826329 : Blo 638302 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B2157299 : Blo 638302 2157299 := bstep (se 1 (by rfl) ⟨1617974, by rfl⟩ : syracuseStep 2157299 = 3235949) B3235949
theorem B2157353 : Blo 638302 2157353 := bstep (se 2 (by rfl) ⟨809007, by rfl⟩ : syracuseStep 2157353 = 1618015) B1618015
theorem B13102181 : Blo 638302 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B1436777 : Blo 638302 1436777 := bstep (se 2 (by rfl) ⟨538791, by rfl⟩ : syracuseStep 1436777 = 1077583) B1077583
theorem B1436903 : Blo 638302 1436903 := bstep (se 1 (by rfl) ⟨1077677, by rfl⟩ : syracuseStep 1436903 = 2155355) B2155355
theorem B1371439 : Blo 638302 1371439 := bstep (se 1 (by rfl) ⟨1028579, by rfl⟩ : syracuseStep 1371439 = 2057159) B2057159
theorem B781979 : Blo 638302 781979 := bstep (se 1 (by rfl) ⟨586484, by rfl⟩ : syracuseStep 781979 = 1172969) B1172969
theorem B1437551 : Blo 638302 1437551 := bstep (se 1 (by rfl) ⟨1078163, by rfl⟩ : syracuseStep 1437551 = 2156327) B2156327
theorem B1077239 : Blo 638302 1077239 := bstep (se 1 (by rfl) ⟨807929, by rfl⟩ : syracuseStep 1077239 = 1615859) B1615859
theorem B6221933 : Blo 638302 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B2159081 : Blo 638302 2159081 := bstep (se 2 (by rfl) ⟨809655, by rfl⟩ : syracuseStep 2159081 = 1619311) B1619311
theorem B1077887 : Blo 638302 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B1438415 : Blo 638302 1438415 := bstep (se 1 (by rfl) ⟨1078811, by rfl⟩ : syracuseStep 1438415 = 2157623) B2157623
theorem B6943643 : Blo 638302 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B10908755 : Blo 638302 10908755 := bstep (se 1 (by rfl) ⟨8181566, by rfl⟩ : syracuseStep 10908755 = 16363133) B16363133
theorem B2160107 : Blo 638302 2160107 := bstep (se 1 (by rfl) ⟨1620080, by rfl⟩ : syracuseStep 2160107 = 3240161) B3240161
theorem B3077929 : Blo 638302 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B1439585 : Blo 638302 1439585 := bstep (se 2 (by rfl) ⟨539844, by rfl⟩ : syracuseStep 1439585 = 1079689) B1079689
theorem B1439711 : Blo 638302 1439711 := bstep (se 1 (by rfl) ⟨1079783, by rfl⟩ : syracuseStep 1439711 = 2159567) B2159567
theorem B1079291 : Blo 638302 1079291 := bstep (se 1 (by rfl) ⟨809468, by rfl⟩ : syracuseStep 1079291 = 1618937) B1618937
theorem B6912287 : Blo 638302 6912287 := bstep (se 1 (by rfl) ⟨5184215, by rfl⟩ : syracuseStep 6912287 = 10368431) B10368431
theorem B1440161 : Blo 638302 1440161 := bstep (se 2 (by rfl) ⟨540060, by rfl⟩ : syracuseStep 1440161 = 1080121) B1080121
theorem B5339627 : Blo 638302 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B2161295 : Blo 638302 2161295 := bstep (se 1 (by rfl) ⟨1620971, by rfl⟩ : syracuseStep 2161295 = 3241943) B3241943
theorem B1080047 : Blo 638302 1080047 := bstep (se 1 (by rfl) ⟨810035, by rfl⟩ : syracuseStep 1080047 = 1620071) B1620071
theorem B2161403 : Blo 638302 2161403 := bstep (se 1 (by rfl) ⟨1621052, by rfl⟩ : syracuseStep 2161403 = 3242105) B3242105
theorem B2161619 : Blo 638302 2161619 := bstep (se 1 (by rfl) ⟨1621214, by rfl⟩ : syracuseStep 2161619 = 3242429) B3242429
theorem B7273961 : Blo 638302 7273961 := bstep (se 2 (by rfl) ⟨2727735, by rfl⟩ : syracuseStep 7273961 = 5455471) B5455471
theorem B8453917 : Blo 638302 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B4620563 : Blo 638302 4620563 := bstep (se 1 (by rfl) ⟨3465422, by rfl⟩ : syracuseStep 4620563 = 6930845) B6930845
theorem B2163023 : Blo 638302 2163023 := bstep (se 1 (by rfl) ⟨1622267, by rfl⟩ : syracuseStep 2163023 = 3244535) B3244535
theorem B1213535 : Blo 638302 1213535 := bstep (se 1 (by rfl) ⟨910151, by rfl⟩ : syracuseStep 1213535 = 1820303) B1820303
theorem B1082551 : Blo 638302 1082551 := bstep (se 1 (by rfl) ⟨811913, by rfl⟩ : syracuseStep 1082551 = 1623827) B1623827
theorem B3245507 : Blo 638302 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B1443977 : Blo 638302 1443977 := bstep (se 2 (by rfl) ⟨541491, by rfl⟩ : syracuseStep 1443977 = 1082983) B1082983
theorem B1083611 : Blo 638302 1083611 := bstep (se 1 (by rfl) ⟨812708, by rfl⟩ : syracuseStep 1083611 = 1625417) B1625417
theorem B1214689 : Blo 638302 1214689 := bstep (se 2 (by rfl) ⟨455508, by rfl⟩ : syracuseStep 1214689 = 911017) B911017
theorem B1444679 : Blo 638302 1444679 := bstep (se 1 (by rfl) ⟨1083509, by rfl⟩ : syracuseStep 1444679 = 2167019) B2167019
theorem B2427995 : Blo 638302 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B3247613 : Blo 638302 3247613 := bstep (se 3 (by rfl) ⟨608927, by rfl⟩ : syracuseStep 3247613 = 1217855) B1217855
theorem B1150505 : Blo 638302 1150505 := bstep (se 2 (by rfl) ⟨431439, by rfl⟩ : syracuseStep 1150505 = 862879) B862879
theorem B2166695 : Blo 638302 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B2167343 : Blo 638302 2167343 := bstep (se 1 (by rfl) ⟨1625507, by rfl⟩ : syracuseStep 2167343 = 3251015) B3251015
theorem B1217567 : Blo 638302 1217567 := bstep (se 1 (by rfl) ⟨913175, by rfl⟩ : syracuseStep 1217567 = 1826351) B1826351
theorem B3642995 : Blo 638302 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B2430607 : Blo 638302 2430607 := bstep (se 1 (by rfl) ⟨1822955, by rfl⟩ : syracuseStep 2430607 = 3645911) B3645911
theorem B4857083 : Blo 638302 4857083 := bstep (se 1 (by rfl) ⟨3642812, by rfl⟩ : syracuseStep 4857083 = 7285625) B7285625
theorem B957851 : Blo 638302 957851 := bstep (se 1 (by rfl) ⟨718388, by rfl⟩ : syracuseStep 957851 = 1436777) B1436777
theorem B957935 : Blo 638302 957935 := bstep (se 1 (by rfl) ⟨718451, by rfl⟩ : syracuseStep 957935 = 1436903) B1436903
theorem B4857569 : Blo 638302 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B958367 : Blo 638302 958367 := bstep (se 1 (by rfl) ⟨718775, by rfl⟩ : syracuseStep 958367 = 1437551) B1437551
theorem B958943 : Blo 638302 958943 := bstep (se 1 (by rfl) ⟨719207, by rfl⟩ : syracuseStep 958943 = 1438415) B1438415
theorem B4629095 : Blo 638302 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B23667365 : Blo 638302 23667365 := bstep (se 4 (by rfl) ⟨2218815, by rfl⟩ : syracuseStep 23667365 = 4437631) B4437631
theorem B959723 : Blo 638302 959723 := bstep (se 1 (by rfl) ⟨719792, by rfl⟩ : syracuseStep 959723 = 1439585) B1439585
theorem B959807 : Blo 638302 959807 := bstep (se 1 (by rfl) ⟨719855, by rfl⟩ : syracuseStep 959807 = 1439711) B1439711
theorem B960107 : Blo 638302 960107 := bstep (se 1 (by rfl) ⟨720080, by rfl⟩ : syracuseStep 960107 = 1440161) B1440161
theorem B4859513 : Blo 638302 4859513 := bstep (se 2 (by rfl) ⟨1822317, by rfl⟩ : syracuseStep 4859513 = 3644635) B3644635
theorem B730991 : Blo 638302 730991 := bstep (se 1 (by rfl) ⟨548243, by rfl⟩ : syracuseStep 730991 = 1096487) B1096487
theorem B3647825 : Blo 638302 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B54012521 : Blo 638302 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B9219025 : Blo 638302 9219025 := bstep (se 2 (by rfl) ⟨3457134, by rfl⟩ : syracuseStep 9219025 = 6914269) B6914269
theorem B2436257 : Blo 638302 2436257 := bstep (se 2 (by rfl) ⟨913596, by rfl⟩ : syracuseStep 2436257 = 1827193) B1827193
theorem B2927801 : Blo 638302 2927801 := bstep (se 2 (by rfl) ⟨1097925, by rfl⟩ : syracuseStep 2927801 = 2195851) B2195851
theorem B962279 : Blo 638302 962279 := bstep (se 1 (by rfl) ⟨721709, by rfl⟩ : syracuseStep 962279 = 1443419) B1443419
theorem B4370183 : Blo 638302 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B962495 : Blo 638302 962495 := bstep (se 1 (by rfl) ⟨721871, by rfl⟩ : syracuseStep 962495 = 1443743) B1443743
theorem B962681 : Blo 638302 962681 := bstep (se 2 (by rfl) ⟨361005, by rfl⟩ : syracuseStep 962681 = 722011) B722011
theorem B7287083 : Blo 638302 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B2307167 : Blo 638302 2307167 := bstep (se 1 (by rfl) ⟨1730375, by rfl⟩ : syracuseStep 2307167 = 3460751) B3460751
theorem B13284773 : Blo 638302 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B3651425 : Blo 638302 3651425 := bstep (se 2 (by rfl) ⟨1369284, by rfl⟩ : syracuseStep 3651425 = 2738569) B2738569
theorem B1096175 : Blo 638302 1096175 := bstep (se 1 (by rfl) ⟨822131, by rfl⟩ : syracuseStep 1096175 = 1644263) B1644263
theorem B4864859 : Blo 638302 4864859 := bstep (se 1 (by rfl) ⟨3648644, by rfl⟩ : syracuseStep 4864859 = 7297289) B7297289
theorem B4111469 : Blo 638302 4111469 := bstep (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) B1541801
theorem B4111697 : Blo 638302 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B638399 : Blo 638302 638399 := bstep (se 1 (by rfl) ⟨478799, by rfl⟩ : syracuseStep 638399 = 957599) B957599
theorem B638491 : Blo 638302 638491 := bstep (se 1 (by rfl) ⟨478868, by rfl⟩ : syracuseStep 638491 = 957737) B957737
theorem B4865831 : Blo 638302 4865831 := bstep (se 1 (by rfl) ⟨3649373, by rfl⟩ : syracuseStep 4865831 = 7298747) B7298747
theorem B2047943 : Blo 638302 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B639047 : Blo 638302 639047 := bstep (se 1 (by rfl) ⟨479285, by rfl⟩ : syracuseStep 639047 = 958571) B958571
theorem B639067 : Blo 638302 639067 := bstep (se 1 (by rfl) ⟨479300, by rfl⟩ : syracuseStep 639067 = 958601) B958601
theorem B24985907 : Blo 638302 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B2638163 : Blo 638302 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B639535 : Blo 638302 639535 := bstep (se 1 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 639535 = 959303) B959303
theorem B1819721 : Blo 638302 1819721 := bstep (se 2 (by rfl) ⟨682395, by rfl⟩ : syracuseStep 1819721 = 1364791) B1364791
theorem B640103 : Blo 638302 640103 := bstep (se 1 (by rfl) ⟨480077, by rfl⟩ : syracuseStep 640103 = 960155) B960155
theorem B3884219 : Blo 638302 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B640559 : Blo 638302 640559 := bstep (se 1 (by rfl) ⟨480419, by rfl⟩ : syracuseStep 640559 = 960839) B960839
theorem B640871 : Blo 638302 640871 := bstep (se 1 (by rfl) ⟨480653, by rfl⟩ : syracuseStep 640871 = 961307) B961307
theorem B8734787 : Blo 638302 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B641115 : Blo 638302 641115 := bstep (se 1 (by rfl) ⟨480836, by rfl⟩ : syracuseStep 641115 = 961673) B961673
theorem B641151 : Blo 638302 641151 := bstep (se 1 (by rfl) ⟨480863, by rfl⟩ : syracuseStep 641151 = 961727) B961727
theorem B641439 : Blo 638302 641439 := bstep (se 1 (by rfl) ⟨481079, by rfl⟩ : syracuseStep 641439 = 962159) B962159
theorem B641471 : Blo 638302 641471 := bstep (se 1 (by rfl) ⟨481103, by rfl⟩ : syracuseStep 641471 = 962207) B962207
theorem B4147955 : Blo 638302 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B641959 : Blo 638302 641959 := bstep (se 1 (by rfl) ⟨481469, by rfl⟩ : syracuseStep 641959 = 962939) B962939
theorem B642031 : Blo 638302 642031 := bstep (se 1 (by rfl) ⟨481523, by rfl⟩ : syracuseStep 642031 = 963047) B963047
theorem B642279 : Blo 638302 642279 := bstep (se 1 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 642279 = 963419) B963419
theorem B15584561 : Blo 638302 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B1756669 : Blo 638302 1756669 := bstep (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) B658751
theorem B236900213 : Blo 638302 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B4608191 : Blo 638302 4608191 := bstep (se 1 (by rfl) ⟨3456143, by rfl⟩ : syracuseStep 4608191 = 6912287) B6912287
theorem B3658031 : Blo 638302 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B3559751 : Blo 638302 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B2085277 : Blo 638302 2085277 := bstep (se 3 (by rfl) ⟨390989, by rfl⟩ : syracuseStep 2085277 = 781979) B781979
theorem B2216375 : Blo 638302 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B3330497 : Blo 638302 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B4150651 : Blo 638302 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B4871663 : Blo 638302 4871663 := bstep (se 1 (by rfl) ⟨3653747, by rfl⟩ : syracuseStep 4871663 = 7307495) B7307495
theorem B5559833 : Blo 638302 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B9852617 : Blo 638302 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B4380583 : Blo 638302 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B55269863 : Blo 638302 55269863 := bstep (se 1 (by rfl) ⟨41452397, by rfl⟩ : syracuseStep 55269863 = 82904795) B82904795
theorem B5462579 : Blo 638302 5462579 := bstep (se 1 (by rfl) ⟨4096934, by rfl⟩ : syracuseStep 5462579 = 8193869) B8193869
theorem B2054747 : Blo 638302 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B3891007 : Blo 638302 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B2154383 : Blo 638302 2154383 := bstep (se 1 (by rfl) ⟨1615787, by rfl⟩ : syracuseStep 2154383 = 3231575) B3231575
theorem B2154491 : Blo 638302 2154491 := bstep (se 1 (by rfl) ⟨1615868, by rfl⟩ : syracuseStep 2154491 = 3231737) B3231737
theorem B4874579 : Blo 638302 4874579 := bstep (se 1 (by rfl) ⟨3655934, by rfl⟩ : syracuseStep 4874579 = 7311869) B7311869
theorem B8217449 : Blo 638302 8217449 := bstep (se 2 (by rfl) ⟨3081543, by rfl⟩ : syracuseStep 8217449 = 6163087) B6163087
theorem B2188255 : Blo 638302 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B2057683 : Blo 638302 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B2156111 : Blo 638302 2156111 := bstep (se 1 (by rfl) ⟨1617083, by rfl⟩ : syracuseStep 2156111 = 3234167) B3234167
theorem B1828585 : Blo 638302 1828585 := bstep (se 2 (by rfl) ⟨685719, by rfl⟩ : syracuseStep 1828585 = 1371439) B1371439
theorem B8186183 : Blo 638302 8186183 := bstep (se 1 (by rfl) ⟨6139637, by rfl⟩ : syracuseStep 8186183 = 12279275) B12279275
theorem B2156975 : Blo 638302 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B12512737 : Blo 638302 12512737 := bstep (se 2 (by rfl) ⟨4692276, by rfl⟩ : syracuseStep 12512737 = 9384553) B9384553
theorem B1437263 : Blo 638302 1437263 := bstep (se 1 (by rfl) ⟨1077947, by rfl⟩ : syracuseStep 1437263 = 2155895) B2155895
theorem B3239513 : Blo 638302 3239513 := bstep (se 2 (by rfl) ⟨1214817, by rfl⟩ : syracuseStep 3239513 = 2429635) B2429635
theorem B1438199 : Blo 638302 1438199 := bstep (se 1 (by rfl) ⟨1078649, by rfl⟩ : syracuseStep 1438199 = 2157299) B2157299
theorem B1438235 : Blo 638302 1438235 := bstep (se 1 (by rfl) ⟨1078676, by rfl⟩ : syracuseStep 1438235 = 2157353) B2157353
theorem B1078319 : Blo 638302 1078319 := bstep (se 1 (by rfl) ⟨808739, by rfl⟩ : syracuseStep 1078319 = 1617479) B1617479
theorem B2159945 : Blo 638302 2159945 := bstep (se 2 (by rfl) ⟨809979, by rfl⟩ : syracuseStep 2159945 = 1619959) B1619959
theorem B718159 : Blo 638302 718159 := bstep (se 1 (by rfl) ⟨538619, by rfl⟩ : syracuseStep 718159 = 1077239) B1077239
theorem B1439387 : Blo 638302 1439387 := bstep (se 1 (by rfl) ⟨1079540, by rfl⟩ : syracuseStep 1439387 = 2159081) B2159081
theorem B718591 : Blo 638302 718591 := bstep (se 1 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 718591 = 1077887) B1077887
theorem B18675593 : Blo 638302 18675593 := bstep (se 2 (by rfl) ⟨7003347, by rfl⟩ : syracuseStep 18675593 = 14006695) B14006695
theorem B7272503 : Blo 638302 7272503 := bstep (se 1 (by rfl) ⟨5454377, by rfl⟩ : syracuseStep 7272503 = 10908755) B10908755
theorem B3242267 : Blo 638302 3242267 := bstep (se 1 (by rfl) ⟨2431700, by rfl⟩ : syracuseStep 3242267 = 4863401) B4863401
theorem B1440071 : Blo 638302 1440071 := bstep (se 1 (by rfl) ⟨1080053, by rfl⟩ : syracuseStep 1440071 = 2160107) B2160107
theorem B719527 : Blo 638302 719527 := bstep (se 1 (by rfl) ⟨539645, by rfl⟩ : syracuseStep 719527 = 1079291) B1079291
theorem B16415621 : Blo 638302 16415621 := bstep (se 4 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 16415621 = 3077929) B3077929
theorem B1440863 : Blo 638302 1440863 := bstep (se 1 (by rfl) ⟨1080647, by rfl⟩ : syracuseStep 1440863 = 2161295) B2161295
theorem B720031 : Blo 638302 720031 := bstep (se 1 (by rfl) ⟨540023, by rfl⟩ : syracuseStep 720031 = 1080047) B1080047
theorem B1440935 : Blo 638302 1440935 := bstep (se 1 (by rfl) ⟨1080701, by rfl⟩ : syracuseStep 1440935 = 2161403) B2161403
theorem B1441079 : Blo 638302 1441079 := bstep (se 1 (by rfl) ⟨1080809, by rfl⟩ : syracuseStep 1441079 = 2161619) B2161619
theorem B4849307 : Blo 638302 4849307 := bstep (se 1 (by rfl) ⟨3636980, by rfl⟩ : syracuseStep 4849307 = 7273961) B7273961
theorem B11271889 : Blo 638302 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B2162429 : Blo 638302 2162429 := bstep (se 3 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 2162429 = 810911) B810911
theorem B2162537 : Blo 638302 2162537 := bstep (se 2 (by rfl) ⟨810951, by rfl⟩ : syracuseStep 2162537 = 1621903) B1621903
theorem B3080375 : Blo 638302 3080375 := bstep (se 1 (by rfl) ⟨2310281, by rfl⟩ : syracuseStep 3080375 = 4620563) B4620563
theorem B1442015 : Blo 638302 1442015 := bstep (se 1 (by rfl) ⟨1081511, by rfl⟩ : syracuseStep 1442015 = 2163023) B2163023
theorem B1213147 : Blo 638302 1213147 := bstep (se 1 (by rfl) ⟨909860, by rfl⟩ : syracuseStep 1213147 = 1819721) B1819721
theorem B2589479 : Blo 638302 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B2163671 : Blo 638302 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B8881325 : Blo 638302 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B2917673 : Blo 638302 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B722407 : Blo 638302 722407 := bstep (se 1 (by rfl) ⟨541805, by rfl⟩ : syracuseStep 722407 = 1083611) B1083611
theorem B1443401 : Blo 638302 1443401 := bstep (se 2 (by rfl) ⟨541275, by rfl⟩ : syracuseStep 1443401 = 1082551) B1082551
theorem B10389707 : Blo 638302 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B2165075 : Blo 638302 2165075 := bstep (se 1 (by rfl) ⟨1623806, by rfl⟩ : syracuseStep 2165075 = 3247613) B3247613
theorem B1444463 : Blo 638302 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B1444895 : Blo 638302 1444895 := bstep (se 1 (by rfl) ⟨1083671, by rfl⟩ : syracuseStep 1444895 = 2167343) B2167343
theorem B3247775 : Blo 638302 3247775 := bstep (se 1 (by rfl) ⟨2435831, by rfl⟩ : syracuseStep 3247775 = 4871663) B4871663
theorem B3706555 : Blo 638302 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B2428663 : Blo 638302 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B12292033 : Blo 638302 12292033 := bstep (se 2 (by rfl) ⟨4609512, by rfl⟩ : syracuseStep 12292033 = 9219025) B9219025
theorem B3641719 : Blo 638302 3641719 := bstep (se 1 (by rfl) ⟨2731289, by rfl⟩ : syracuseStep 3641719 = 5462579) B5462579
theorem B3249719 : Blo 638302 3249719 := bstep (se 1 (by rfl) ⟨2437289, by rfl⟩ : syracuseStep 3249719 = 4874579) B4874579
theorem B3086063 : Blo 638302 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B5478299 : Blo 638302 5478299 := bstep (se 1 (by rfl) ⟨4108724, by rfl⟩ : syracuseStep 5478299 = 8217449) B8217449
theorem B2431883 : Blo 638302 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B5479325 : Blo 638302 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B957545 : Blo 638302 957545 := bstep (se 2 (by rfl) ⟨359079, by rfl⟩ : syracuseStep 957545 = 718159) B718159
theorem B958121 : Blo 638302 958121 := bstep (se 2 (by rfl) ⟨359295, by rfl⟩ : syracuseStep 958121 = 718591) B718591
theorem B958175 : Blo 638302 958175 := bstep (se 1 (by rfl) ⟨718631, by rfl⟩ : syracuseStep 958175 = 1437263) B1437263
theorem B5840777 : Blo 638302 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B4858055 : Blo 638302 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B958799 : Blo 638302 958799 := bstep (se 1 (by rfl) ⟨719099, by rfl⟩ : syracuseStep 958799 = 1438199) B1438199
theorem B958823 : Blo 638302 958823 := bstep (se 1 (by rfl) ⟨719117, by rfl⟩ : syracuseStep 958823 = 1438235) B1438235
theorem B959369 : Blo 638302 959369 := bstep (se 2 (by rfl) ⟨359763, by rfl⟩ : syracuseStep 959369 = 719527) B719527
theorem B8856515 : Blo 638302 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B959591 : Blo 638302 959591 := bstep (se 1 (by rfl) ⟨719693, by rfl⟩ : syracuseStep 959591 = 1439387) B1439387
theorem B2434283 : Blo 638302 2434283 := bstep (se 1 (by rfl) ⟨1825712, by rfl⟩ : syracuseStep 2434283 = 3651425) B3651425
theorem B960041 : Blo 638302 960041 := bstep (se 2 (by rfl) ⟨360015, by rfl⟩ : syracuseStep 960041 = 720031) B720031
theorem B960047 : Blo 638302 960047 := bstep (se 1 (by rfl) ⟨720035, by rfl⟩ : syracuseStep 960047 = 1440071) B1440071
theorem B730783 : Blo 638302 730783 := bstep (se 1 (by rfl) ⟨548087, by rfl⟩ : syracuseStep 730783 = 1096175) B1096175
theorem B960575 : Blo 638302 960575 := bstep (se 1 (by rfl) ⟨720431, by rfl⟩ : syracuseStep 960575 = 1440863) B1440863
theorem B960623 : Blo 638302 960623 := bstep (se 1 (by rfl) ⟨720467, by rfl⟩ : syracuseStep 960623 = 1440935) B1440935
theorem B960719 : Blo 638302 960719 := bstep (se 1 (by rfl) ⟨720539, by rfl⟩ : syracuseStep 960719 = 1441079) B1441079
theorem B5188009 : Blo 638302 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B16657271 : Blo 638302 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B962651 : Blo 638302 962651 := bstep (se 1 (by rfl) ⟨721988, by rfl⟩ : syracuseStep 962651 = 1443977) B1443977
theorem B2765303 : Blo 638302 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B963119 : Blo 638302 963119 := bstep (se 1 (by rfl) ⟨722339, by rfl⟩ : syracuseStep 963119 = 1444679) B1444679
theorem B1618663 : Blo 638302 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B2438113 : Blo 638302 2438113 := bstep (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) B1828585
theorem B767003 : Blo 638302 767003 := bstep (se 1 (by rfl) ⟨575252, by rfl⟩ : syracuseStep 767003 = 1150505) B1150505
theorem B2438687 : Blo 638302 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B2373167 : Blo 638302 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B1619585 : Blo 638302 1619585 := bstep (se 2 (by rfl) ⟨607344, by rfl⟩ : syracuseStep 1619585 = 1214689) B1214689
theorem B6568411 : Blo 638302 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B36846575 : Blo 638302 36846575 := bstep (se 1 (by rfl) ⟨27634931, by rfl⟩ : syracuseStep 36846575 = 55269863) B55269863
theorem B2342225 : Blo 638302 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B638567 : Blo 638302 638567 := bstep (se 1 (by rfl) ⟨478925, by rfl⟩ : syracuseStep 638567 = 957851) B957851
theorem B1949309 : Blo 638302 1949309 := bstep (se 3 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 1949309 = 730991) B730991
theorem B638623 : Blo 638302 638623 := bstep (se 1 (by rfl) ⟨478967, by rfl⟩ : syracuseStep 638623 = 957935) B957935
theorem B638911 : Blo 638302 638911 := bstep (se 1 (by rfl) ⟨479183, by rfl⟩ : syracuseStep 638911 = 958367) B958367
theorem B639295 : Blo 638302 639295 := bstep (se 1 (by rfl) ⟨479471, by rfl⟩ : syracuseStep 639295 = 958943) B958943
theorem B15778243 : Blo 638302 15778243 := bstep (se 1 (by rfl) ⟨11833682, by rfl⟩ : syracuseStep 15778243 = 23667365) B23667365
theorem B639815 : Blo 638302 639815 := bstep (se 1 (by rfl) ⟨479861, by rfl⟩ : syracuseStep 639815 = 959723) B959723
theorem B639871 : Blo 638302 639871 := bstep (se 1 (by rfl) ⟨479903, by rfl⟩ : syracuseStep 639871 = 959807) B959807
theorem B640071 : Blo 638302 640071 := bstep (se 1 (by rfl) ⟨480053, by rfl⟩ : syracuseStep 640071 = 960107) B960107
theorem B5457455 : Blo 638302 5457455 := bstep (se 1 (by rfl) ⟨4093091, by rfl⟩ : syracuseStep 5457455 = 8186183) B8186183
theorem B1624171 : Blo 638302 1624171 := bstep (se 1 (by rfl) ⟨1218128, by rfl⟩ : syracuseStep 1624171 = 2436257) B2436257
theorem B1951867 : Blo 638302 1951867 := bstep (se 1 (by rfl) ⟨1463900, by rfl⟩ : syracuseStep 1951867 = 2927801) B2927801
theorem B641519 : Blo 638302 641519 := bstep (se 1 (by rfl) ⟨481139, by rfl⟩ : syracuseStep 641519 = 962279) B962279
theorem B66734597 : Blo 638302 66734597 := bstep (se 4 (by rfl) ⟨6256368, by rfl⟩ : syracuseStep 66734597 = 12512737) B12512737
theorem B641663 : Blo 638302 641663 := bstep (se 1 (by rfl) ⟨481247, by rfl⟩ : syracuseStep 641663 = 962495) B962495
theorem B641787 : Blo 638302 641787 := bstep (se 1 (by rfl) ⟨481340, by rfl⟩ : syracuseStep 641787 = 962681) B962681
theorem B2740979 : Blo 638302 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B2741131 : Blo 638302 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B15029185 : Blo 638302 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B3232871 : Blo 638302 3232871 := bstep (se 1 (by rfl) ⟨2424653, by rfl⟩ : syracuseStep 3232871 = 4849307) B4849307
theorem B5461181 : Blo 638302 5461181 := bstep (se 3 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 5461181 = 2047943) B2047943
theorem B1758775 : Blo 638302 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B809023 : Blo 638302 809023 := bstep (se 1 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 809023 = 1213535) B1213535
theorem B5823191 : Blo 638302 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B2743577 : Blo 638302 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B157933475 : Blo 638302 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B3072127 : Blo 638302 3072127 := bstep (se 1 (by rfl) ⟨2304095, by rfl⟩ : syracuseStep 3072127 = 4608191) B4608191
theorem B811711 : Blo 638302 811711 := bstep (se 1 (by rfl) ⟨608783, by rfl⟩ : syracuseStep 811711 = 1217567) B1217567
theorem B3238055 : Blo 638302 3238055 := bstep (se 1 (by rfl) ⟨2428541, by rfl⟩ : syracuseStep 3238055 = 4857083) B4857083
theorem B3238379 : Blo 638302 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B1436255 : Blo 638302 1436255 := bstep (se 1 (by rfl) ⟨1077191, by rfl⟩ : syracuseStep 1436255 = 2154383) B2154383
theorem B1436327 : Blo 638302 1436327 := bstep (se 1 (by rfl) ⟨1077245, by rfl⟩ : syracuseStep 1436327 = 2154491) B2154491
theorem B2780369 : Blo 638302 2780369 := bstep (se 2 (by rfl) ⟨1042638, by rfl⟩ : syracuseStep 2780369 = 2085277) B2085277
theorem B1437407 : Blo 638302 1437407 := bstep (se 1 (by rfl) ⟨1078055, by rfl⟩ : syracuseStep 1437407 = 2156111) B2156111
theorem B3239675 : Blo 638302 3239675 := bstep (se 1 (by rfl) ⟨2429756, by rfl⟩ : syracuseStep 3239675 = 4859513) B4859513
theorem B1437983 : Blo 638302 1437983 := bstep (se 1 (by rfl) ⟨1078487, by rfl⟩ : syracuseStep 1437983 = 2156975) B2156975
theorem B36008347 : Blo 638302 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B5534201 : Blo 638302 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B3240809 : Blo 638302 3240809 := bstep (se 2 (by rfl) ⟨1215303, by rfl⟩ : syracuseStep 3240809 = 2430607) B2430607
theorem B94565333 : Blo 638302 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B2159675 : Blo 638302 2159675 := bstep (se 1 (by rfl) ⟨1619756, by rfl⟩ : syracuseStep 2159675 = 3239513) B3239513
theorem B2913455 : Blo 638302 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B718879 : Blo 638302 718879 := bstep (se 1 (by rfl) ⟨539159, by rfl⟩ : syracuseStep 718879 = 1078319) B1078319
theorem B1538111 : Blo 638302 1538111 := bstep (se 1 (by rfl) ⟨1153583, by rfl⟩ : syracuseStep 1538111 = 2307167) B2307167
theorem B1439963 : Blo 638302 1439963 := bstep (se 1 (by rfl) ⟨1079972, by rfl⟩ : syracuseStep 1439963 = 2159945) B2159945
theorem B12450395 : Blo 638302 12450395 := bstep (se 1 (by rfl) ⟨9337796, by rfl⟩ : syracuseStep 12450395 = 18675593) B18675593
theorem B4848335 : Blo 638302 4848335 := bstep (se 1 (by rfl) ⟨3636251, by rfl⟩ : syracuseStep 4848335 = 7272503) B7272503
theorem B2161511 : Blo 638302 2161511 := bstep (se 1 (by rfl) ⟨1621133, by rfl⟩ : syracuseStep 2161511 = 3242267) B3242267
theorem B3243239 : Blo 638302 3243239 := bstep (se 1 (by rfl) ⟨2432429, by rfl⟩ : syracuseStep 3243239 = 4864859) B4864859
theorem B10943747 : Blo 638302 10943747 := bstep (se 1 (by rfl) ⟨8207810, by rfl⟩ : syracuseStep 10943747 = 16415621) B16415621
theorem B1441619 : Blo 638302 1441619 := bstep (se 1 (by rfl) ⟨1081214, by rfl⟩ : syracuseStep 1441619 = 2162429) B2162429
theorem B3243887 : Blo 638302 3243887 := bstep (se 1 (by rfl) ⟨2432915, by rfl⟩ : syracuseStep 3243887 = 4865831) B4865831
theorem B1441691 : Blo 638302 1441691 := bstep (se 1 (by rfl) ⟨1081268, by rfl⟩ : syracuseStep 1441691 = 2162537) B2162537
theorem B4096169 : Blo 638302 4096169 := bstep (se 2 (by rfl) ⟨1536063, by rfl⟩ : syracuseStep 4096169 = 3072127) B3072127
theorem B21037657 : Blo 638302 21037657 := bstep (se 2 (by rfl) ⟨7889121, by rfl⟩ : syracuseStep 21037657 = 15778243) B15778243
theorem B1442447 : Blo 638302 1442447 := bstep (se 1 (by rfl) ⟨1081835, by rfl⟩ : syracuseStep 1442447 = 2163671) B2163671
theorem B1082281 : Blo 638302 1082281 := bstep (se 2 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 1082281 = 811711) B811711
theorem B3638303 : Blo 638302 3638303 := bstep (se 1 (by rfl) ⟨2728727, by rfl⟩ : syracuseStep 3638303 = 5457455) B5457455
theorem B1443383 : Blo 638302 1443383 := bstep (se 1 (by rfl) ⟨1082537, by rfl⟩ : syracuseStep 1443383 = 2165075) B2165075
theorem B2165183 : Blo 638302 2165183 := bstep (se 1 (by rfl) ⟨1623887, by rfl⟩ : syracuseStep 2165183 = 3247775) B3247775
theorem B2165561 : Blo 638302 2165561 := bstep (se 2 (by rfl) ⟨812085, by rfl⟩ : syracuseStep 2165561 = 1624171) B1624171
theorem B6917345 : Blo 638302 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B3640787 : Blo 638302 3640787 := bstep (se 1 (by rfl) ⟨2730590, by rfl⟩ : syracuseStep 3640787 = 5461181) B5461181
theorem B2166479 : Blo 638302 2166479 := bstep (se 1 (by rfl) ⟨1624859, by rfl⟩ : syracuseStep 2166479 = 3249719) B3249719
theorem B16389377 : Blo 638302 16389377 := bstep (se 2 (by rfl) ⟨6146016, by rfl⟩ : syracuseStep 16389377 = 12292033) B12292033
theorem B105288983 : Blo 638302 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B4855625 : Blo 638302 4855625 := bstep (se 2 (by rfl) ⟨1820859, by rfl⟩ : syracuseStep 4855625 = 3641719) B3641719
theorem B48011129 : Blo 638302 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B5904343 : Blo 638302 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B3250817 : Blo 638302 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B33201053 : Blo 638302 33201053 := bstep (se 3 (by rfl) ⟨6225197, by rfl⟩ : syracuseStep 33201053 = 12450395) B12450395
theorem B957503 : Blo 638302 957503 := bstep (se 1 (by rfl) ⟨718127, by rfl⟩ : syracuseStep 957503 = 1436255) B1436255
theorem B957551 : Blo 638302 957551 := bstep (se 1 (by rfl) ⟨718163, by rfl⟩ : syracuseStep 957551 = 1436327) B1436327
theorem B958271 : Blo 638302 958271 := bstep (se 1 (by rfl) ⟨718703, by rfl⟩ : syracuseStep 958271 = 1437407) B1437407
theorem B958505 : Blo 638302 958505 := bstep (se 2 (by rfl) ⟨359439, by rfl⟩ : syracuseStep 958505 = 718879) B718879
theorem B958655 : Blo 638302 958655 := bstep (se 1 (by rfl) ⟨718991, by rfl⟩ : syracuseStep 958655 = 1437983) B1437983
theorem B1843535 : Blo 638302 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B8757881 : Blo 638302 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B1942303 : Blo 638302 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B1582111 : Blo 638302 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1025407 : Blo 638302 1025407 := bstep (se 1 (by rfl) ⟨769055, by rfl⟩ : syracuseStep 1025407 = 1538111) B1538111
theorem B959975 : Blo 638302 959975 := bstep (se 1 (by rfl) ⟨719981, by rfl⟩ : syracuseStep 959975 = 1439963) B1439963
theorem B961079 : Blo 638302 961079 := bstep (se 1 (by rfl) ⟨720809, by rfl⟩ : syracuseStep 961079 = 1441619) B1441619
theorem B961127 : Blo 638302 961127 := bstep (se 1 (by rfl) ⟨720845, by rfl⟩ : syracuseStep 961127 = 1441691) B1441691
theorem B961343 : Blo 638302 961343 := bstep (se 1 (by rfl) ⟨721007, by rfl⟩ : syracuseStep 961343 = 1442015) B1442015
theorem B1945115 : Blo 638302 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B1617529 : Blo 638302 1617529 := bstep (se 2 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 1617529 = 1213147) B1213147
theorem B962267 : Blo 638302 962267 := bstep (se 1 (by rfl) ⟨721700, by rfl⟩ : syracuseStep 962267 = 1443401) B1443401
theorem B14757869 : Blo 638302 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B6926471 : Blo 638302 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B962975 : Blo 638302 962975 := bstep (se 1 (by rfl) ⟨722231, by rfl⟩ : syracuseStep 962975 = 1444463) B1444463
theorem B963209 : Blo 638302 963209 := bstep (se 2 (by rfl) ⟨361203, by rfl⟩ : syracuseStep 963209 = 722407) B722407
theorem B963263 : Blo 638302 963263 := bstep (se 1 (by rfl) ⟨722447, by rfl⟩ : syracuseStep 963263 = 1444895) B1444895
theorem B2045341 : Blo 638302 2045341 := bstep (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) B767003
theorem B2602489 : Blo 638302 2602489 := bstep (se 2 (by rfl) ⟨975933, by rfl⟩ : syracuseStep 2602489 = 1951867) B1951867
theorem B3652199 : Blo 638302 3652199 := bstep (se 1 (by rfl) ⟨2739149, by rfl⟩ : syracuseStep 3652199 = 5478299) B5478299
theorem B3882127 : Blo 638302 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B1621255 : Blo 638302 1621255 := bstep (se 1 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 1621255 = 2431883) B2431883
theorem B3652883 : Blo 638302 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B638363 : Blo 638302 638363 := bstep (se 1 (by rfl) ⟨478772, by rfl⟩ : syracuseStep 638363 = 957545) B957545
theorem B638747 : Blo 638302 638747 := bstep (se 1 (by rfl) ⟨479060, by rfl⟩ : syracuseStep 638747 = 958121) B958121
theorem B638783 : Blo 638302 638783 := bstep (se 1 (by rfl) ⟨479087, by rfl⟩ : syracuseStep 638783 = 958175) B958175
theorem B639199 : Blo 638302 639199 := bstep (se 1 (by rfl) ⟨479399, by rfl⟩ : syracuseStep 639199 = 958799) B958799
theorem B639215 : Blo 638302 639215 := bstep (se 1 (by rfl) ⟨479411, by rfl⟩ : syracuseStep 639215 = 958823) B958823
theorem B639579 : Blo 638302 639579 := bstep (se 1 (by rfl) ⟨479684, by rfl⟩ : syracuseStep 639579 = 959369) B959369
theorem B639727 : Blo 638302 639727 := bstep (se 1 (by rfl) ⟨479795, by rfl⟩ : syracuseStep 639727 = 959591) B959591
theorem B1622855 : Blo 638302 1622855 := bstep (se 1 (by rfl) ⟨1217141, by rfl⟩ : syracuseStep 1622855 = 2434283) B2434283
theorem B640027 : Blo 638302 640027 := bstep (se 1 (by rfl) ⟨480020, by rfl⟩ : syracuseStep 640027 = 960041) B960041
theorem B640031 : Blo 638302 640031 := bstep (se 1 (by rfl) ⟨480023, by rfl⟩ : syracuseStep 640031 = 960047) B960047
theorem B3654841 : Blo 638302 3654841 := bstep (se 2 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 3654841 = 2741131) B2741131
theorem B20038913 : Blo 638302 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B20792629 : Blo 638302 20792629 := bstep (se 5 (by rfl) ⟨974654, by rfl⟩ : syracuseStep 20792629 = 1949309) B1949309
theorem B640383 : Blo 638302 640383 := bstep (se 1 (by rfl) ⟨480287, by rfl⟩ : syracuseStep 640383 = 960575) B960575
theorem B640415 : Blo 638302 640415 := bstep (se 1 (by rfl) ⟨480311, by rfl⟩ : syracuseStep 640415 = 960623) B960623
theorem B640479 : Blo 638302 640479 := bstep (se 1 (by rfl) ⟨480359, by rfl⟩ : syracuseStep 640479 = 960719) B960719
theorem B2345033 : Blo 638302 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B1853579 : Blo 638302 1853579 := bstep (se 1 (by rfl) ⟨1390184, by rfl⟩ : syracuseStep 1853579 = 2780369) B2780369
theorem B641767 : Blo 638302 641767 := bstep (se 1 (by rfl) ⟨481325, by rfl⟩ : syracuseStep 641767 = 962651) B962651
theorem B642079 : Blo 638302 642079 := bstep (se 1 (by rfl) ⟨481559, by rfl⟩ : syracuseStep 642079 = 963119) B963119
theorem B1625791 : Blo 638302 1625791 := bstep (se 1 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 1625791 = 2438687) B2438687
theorem B3232223 : Blo 638302 3232223 := bstep (se 1 (by rfl) ⟨2424167, by rfl⟩ : syracuseStep 3232223 = 4848335) B4848335
theorem B24564383 : Blo 638302 24564383 := bstep (se 1 (by rfl) ⟨18423287, by rfl⟩ : syracuseStep 24564383 = 36846575) B36846575
theorem B7295831 : Blo 638302 7295831 := bstep (se 1 (by rfl) ⟨5471873, by rfl⟩ : syracuseStep 7295831 = 10943747) B10943747
theorem B1561483 : Blo 638302 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B2053583 : Blo 638302 2053583 := bstep (se 1 (by rfl) ⟨1540187, by rfl⟩ : syracuseStep 2053583 = 3080375) B3080375
theorem B1726319 : Blo 638302 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B5920883 : Blo 638302 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B44489731 : Blo 638302 44489731 := bstep (se 1 (by rfl) ⟨33367298, by rfl⟩ : syracuseStep 44489731 = 66734597) B66734597
theorem B974377 : Blo 638302 974377 := bstep (se 2 (by rfl) ⟨365391, by rfl⟩ : syracuseStep 974377 = 730783) B730783
theorem B252174221 : Blo 638302 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B1827319 : Blo 638302 1827319 := bstep (se 1 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 1827319 = 2740979) B2740979
theorem B2155247 : Blo 638302 2155247 := bstep (se 1 (by rfl) ⟨1616435, by rfl⟩ : syracuseStep 2155247 = 3232871) B3232871
theorem B2057375 : Blo 638302 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1829051 : Blo 638302 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B4942073 : Blo 638302 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B3238217 : Blo 638302 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B3893851 : Blo 638302 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B3238703 : Blo 638302 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B2158217 : Blo 638302 2158217 := bstep (se 2 (by rfl) ⟨809331, by rfl⟩ : syracuseStep 2158217 = 1618663) B1618663
theorem B2158703 : Blo 638302 2158703 := bstep (se 1 (by rfl) ⟨1619027, by rfl⟩ : syracuseStep 2158703 = 3238055) B3238055
theorem B2158919 : Blo 638302 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B11104847 : Blo 638302 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B2159783 : Blo 638302 2159783 := bstep (se 1 (by rfl) ⟨1619837, by rfl⟩ : syracuseStep 2159783 = 3239675) B3239675
theorem B1078697 : Blo 638302 1078697 := bstep (se 2 (by rfl) ⟨404511, by rfl⟩ : syracuseStep 1078697 = 809023) B809023
theorem B2160539 : Blo 638302 2160539 := bstep (se 1 (by rfl) ⟨1620404, by rfl⟩ : syracuseStep 2160539 = 3240809) B3240809
theorem B1439783 : Blo 638302 1439783 := bstep (se 1 (by rfl) ⟨1079837, by rfl⟩ : syracuseStep 1439783 = 2159675) B2159675
theorem B1079723 : Blo 638302 1079723 := bstep (se 1 (by rfl) ⟨809792, by rfl⟩ : syracuseStep 1079723 = 1619585) B1619585
theorem B1441007 : Blo 638302 1441007 := bstep (se 1 (by rfl) ⟨1080755, by rfl⟩ : syracuseStep 1441007 = 2161511) B2161511
theorem B2162159 : Blo 638302 2162159 := bstep (se 1 (by rfl) ⟨1621619, by rfl⟩ : syracuseStep 2162159 = 3243239) B3243239
theorem B2162591 : Blo 638302 2162591 := bstep (se 1 (by rfl) ⟨1621943, by rfl⟩ : syracuseStep 2162591 = 3243887) B3243887
theorem B1081903 : Blo 638302 1081903 := bstep (se 1 (by rfl) ⟨811427, by rfl⟩ : syracuseStep 1081903 = 1622855) B1622855
theorem B2425535 : Blo 638302 2425535 := bstep (se 1 (by rfl) ⟨1819151, by rfl⟩ : syracuseStep 2425535 = 3638303) B3638303
theorem B28050209 : Blo 638302 28050209 := bstep (se 2 (by rfl) ⟨10518828, by rfl⟩ : syracuseStep 28050209 = 21037657) B21037657
theorem B2589737 : Blo 638302 2589737 := bstep (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) B1942303
theorem B1443041 : Blo 638302 1443041 := bstep (se 2 (by rfl) ⟨541140, by rfl⟩ : syracuseStep 1443041 = 1082281) B1082281
theorem B1443455 : Blo 638302 1443455 := bstep (se 1 (by rfl) ⟨1082591, by rfl⟩ : syracuseStep 1443455 = 2165183) B2165183
theorem B27723505 : Blo 638302 27723505 := bstep (se 2 (by rfl) ⟨10396314, by rfl⟩ : syracuseStep 27723505 = 20792629) B20792629
theorem B1443707 : Blo 638302 1443707 := bstep (se 1 (by rfl) ⟨1082780, by rfl⟩ : syracuseStep 1443707 = 2165561) B2165561
theorem B2427191 : Blo 638302 2427191 := bstep (se 1 (by rfl) ⟨1820393, by rfl⟩ : syracuseStep 2427191 = 3640787) B3640787
theorem B1444319 : Blo 638302 1444319 := bstep (se 1 (by rfl) ⟨1083239, by rfl⟩ : syracuseStep 1444319 = 2166479) B2166479
theorem B70192655 : Blo 638302 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B2167211 : Blo 638302 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B8327909 : Blo 638302 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B2167721 : Blo 638302 2167721 := bstep (se 2 (by rfl) ⟨812895, by rfl⟩ : syracuseStep 2167721 = 1625791) B1625791
theorem B5838587 : Blo 638302 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B13178861 : Blo 638302 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B1219367 : Blo 638302 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B2727121 : Blo 638302 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B9838579 : Blo 638302 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B59319641 : Blo 638302 59319641 := bstep (se 2 (by rfl) ⟨22244865, by rfl⟩ : syracuseStep 59319641 = 44489731) B44489731
theorem B959855 : Blo 638302 959855 := bstep (se 1 (by rfl) ⟨719891, by rfl⟩ : syracuseStep 959855 = 1439783) B1439783
theorem B2434799 : Blo 638302 2434799 := bstep (se 1 (by rfl) ⟨1826099, by rfl⟩ : syracuseStep 2434799 = 3652199) B3652199
theorem B960671 : Blo 638302 960671 := bstep (se 1 (by rfl) ⟨720503, by rfl⟩ : syracuseStep 960671 = 1441007) B1441007
theorem B2435255 : Blo 638302 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B2730779 : Blo 638302 2730779 := bstep (se 1 (by rfl) ⟨2048084, by rfl⟩ : syracuseStep 2730779 = 4096169) B4096169
theorem B961631 : Blo 638302 961631 := bstep (se 1 (by rfl) ⟨721223, by rfl⟩ : syracuseStep 961631 = 1442447) B1442447
theorem B2436425 : Blo 638302 2436425 := bstep (se 2 (by rfl) ⟨913659, by rfl⟩ : syracuseStep 2436425 = 1827319) B1827319
theorem B962255 : Blo 638302 962255 := bstep (se 1 (by rfl) ⟨721691, by rfl⟩ : syracuseStep 962255 = 1443383) B1443383
theorem B4863887 : Blo 638302 4863887 := bstep (se 1 (by rfl) ⟨3647915, by rfl⟩ : syracuseStep 4863887 = 7295831) B7295831
theorem B10926251 : Blo 638302 10926251 := bstep (se 1 (by rfl) ⟨8194688, by rfl⟩ : syracuseStep 10926251 = 16389377) B16389377
theorem B3947255 : Blo 638302 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B22134035 : Blo 638302 22134035 := bstep (se 1 (by rfl) ⟨16600526, by rfl⟩ : syracuseStep 22134035 = 33201053) B33201053
theorem B638335 : Blo 638302 638335 := bstep (se 1 (by rfl) ⟨478751, by rfl⟩ : syracuseStep 638335 = 957503) B957503
theorem B638367 : Blo 638302 638367 := bstep (se 1 (by rfl) ⟨478775, by rfl⟩ : syracuseStep 638367 = 957551) B957551
theorem B4603517 : Blo 638302 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B638847 : Blo 638302 638847 := bstep (se 1 (by rfl) ⟨479135, by rfl⟩ : syracuseStep 638847 = 958271) B958271
theorem B168116147 : Blo 638302 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B639003 : Blo 638302 639003 := bstep (se 1 (by rfl) ⟨479252, by rfl⟩ : syracuseStep 639003 = 958505) B958505
theorem B639103 : Blo 638302 639103 := bstep (se 1 (by rfl) ⟨479327, by rfl⟩ : syracuseStep 639103 = 958655) B958655
theorem B8437925 : Blo 638302 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1229023 : Blo 638302 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B639983 : Blo 638302 639983 := bstep (se 1 (by rfl) ⟨479987, by rfl⟩ : syracuseStep 639983 = 959975) B959975
theorem B640719 : Blo 638302 640719 := bstep (se 1 (by rfl) ⟨480539, by rfl⟩ : syracuseStep 640719 = 961079) B961079
theorem B640751 : Blo 638302 640751 := bstep (se 1 (by rfl) ⟨480563, by rfl⟩ : syracuseStep 640751 = 961127) B961127
theorem B640895 : Blo 638302 640895 := bstep (se 1 (by rfl) ⟨480671, by rfl⟩ : syracuseStep 640895 = 961343) B961343
theorem B1296743 : Blo 638302 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B641511 : Blo 638302 641511 := bstep (se 1 (by rfl) ⟨481133, by rfl⟩ : syracuseStep 641511 = 962267) B962267
theorem B641983 : Blo 638302 641983 := bstep (se 1 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 641983 = 962975) B962975
theorem B642139 : Blo 638302 642139 := bstep (se 1 (by rfl) ⟨481604, by rfl⟩ : syracuseStep 642139 = 963209) B963209
theorem B642175 : Blo 638302 642175 := bstep (se 1 (by rfl) ⟨481631, by rfl⟩ : syracuseStep 642175 = 963263) B963263
theorem B1299169 : Blo 638302 1299169 := bstep (se 2 (by rfl) ⟨487188, by rfl⟩ : syracuseStep 1299169 = 974377) B974377
theorem B13359275 : Blo 638302 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B1563355 : Blo 638302 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B1235719 : Blo 638302 1235719 := bstep (se 1 (by rfl) ⟨926789, by rfl⟩ : syracuseStep 1235719 = 1853579) B1853579
theorem B4873121 : Blo 638302 4873121 := bstep (se 2 (by rfl) ⟨1827420, by rfl⟩ : syracuseStep 4873121 = 3654841) B3654841
theorem B1367209 : Blo 638302 1367209 := bstep (se 2 (by rfl) ⟨512703, by rfl⟩ : syracuseStep 1367209 = 1025407) B1025407
theorem B4611563 : Blo 638302 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B2154815 : Blo 638302 2154815 := bstep (se 1 (by rfl) ⟨1616111, by rfl⟩ : syracuseStep 2154815 = 3232223) B3232223
theorem B16376255 : Blo 638302 16376255 := bstep (se 1 (by rfl) ⟨12282191, by rfl⟩ : syracuseStep 16376255 = 24564383) B24564383
theorem B20767205 : Blo 638302 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B1369055 : Blo 638302 1369055 := bstep (se 1 (by rfl) ⟨1026791, by rfl⟩ : syracuseStep 1369055 = 2053583) B2053583
theorem B3237083 : Blo 638302 3237083 := bstep (se 1 (by rfl) ⟨2427812, by rfl⟩ : syracuseStep 3237083 = 4855625) B4855625
theorem B32007419 : Blo 638302 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B2156705 : Blo 638302 2156705 := bstep (se 2 (by rfl) ⟨808764, by rfl⟩ : syracuseStep 2156705 = 1617529) B1617529
theorem B1436831 : Blo 638302 1436831 := bstep (se 1 (by rfl) ⟨1077623, by rfl⟩ : syracuseStep 1436831 = 2155247) B2155247
theorem B1371583 : Blo 638302 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B2158811 : Blo 638302 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B2159135 : Blo 638302 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B3469985 : Blo 638302 3469985 := bstep (se 2 (by rfl) ⟨1301244, by rfl⟩ : syracuseStep 3469985 = 2602489) B2602489
theorem B1438811 : Blo 638302 1438811 := bstep (se 1 (by rfl) ⟨1079108, by rfl⟩ : syracuseStep 1438811 = 2158217) B2158217
theorem B1439135 : Blo 638302 1439135 := bstep (se 1 (by rfl) ⟨1079351, by rfl⟩ : syracuseStep 1439135 = 2158703) B2158703
theorem B4617647 : Blo 638302 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B1439279 : Blo 638302 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B7403231 : Blo 638302 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B1439855 : Blo 638302 1439855 := bstep (se 1 (by rfl) ⟨1079891, by rfl⟩ : syracuseStep 1439855 = 2159783) B2159783
theorem B719131 : Blo 638302 719131 := bstep (se 1 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 719131 = 1078697) B1078697
theorem B1440359 : Blo 638302 1440359 := bstep (se 1 (by rfl) ⟨1080269, by rfl⟩ : syracuseStep 1440359 = 2160539) B2160539
theorem B5176169 : Blo 638302 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B719815 : Blo 638302 719815 := bstep (se 1 (by rfl) ⟨539861, by rfl⟩ : syracuseStep 719815 = 1079723) B1079723
theorem B2161673 : Blo 638302 2161673 := bstep (se 2 (by rfl) ⟨810627, by rfl⟩ : syracuseStep 2161673 = 1621255) B1621255
theorem B1441439 : Blo 638302 1441439 := bstep (se 1 (by rfl) ⟨1081079, by rfl⟩ : syracuseStep 1441439 = 2162159) B2162159
theorem B31489829 : Blo 638302 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B1441727 : Blo 638302 1441727 := bstep (se 1 (by rfl) ⟨1081295, by rfl⟩ : syracuseStep 1441727 = 2162591) B2162591
theorem B27623861 : Blo 638302 27623861 := bstep (se 5 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 27623861 = 2589737) B2589737
theorem B1442537 : Blo 638302 1442537 := bstep (se 2 (by rfl) ⟨540951, by rfl⟩ : syracuseStep 1442537 = 1081903) B1081903
theorem B6554789 : Blo 638302 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B36964673 : Blo 638302 36964673 := bstep (se 2 (by rfl) ⟨13861752, by rfl⟩ : syracuseStep 36964673 = 27723505) B27723505
theorem B46795103 : Blo 638302 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B1444807 : Blo 638302 1444807 := bstep (se 1 (by rfl) ⟨1083605, by rfl⟩ : syracuseStep 1444807 = 2167211) B2167211
theorem B1445147 : Blo 638302 1445147 := bstep (se 1 (by rfl) ⟨1083860, by rfl⟩ : syracuseStep 1445147 = 2167721) B2167721
theorem B8785907 : Blo 638302 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B3248747 : Blo 638302 3248747 := bstep (se 1 (by rfl) ⟨2436560, by rfl⟩ : syracuseStep 3248747 = 4873121) B4873121
theorem B10917503 : Blo 638302 10917503 := bstep (se 1 (by rfl) ⟨8188127, by rfl⟩ : syracuseStep 10917503 = 16376255) B16376255
theorem B21338279 : Blo 638302 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B957887 : Blo 638302 957887 := bstep (se 1 (by rfl) ⟨718415, by rfl⟩ : syracuseStep 957887 = 1436831) B1436831
theorem B958841 : Blo 638302 958841 := bstep (se 2 (by rfl) ⟨359565, by rfl⟩ : syracuseStep 958841 = 719131) B719131
theorem B959207 : Blo 638302 959207 := bstep (se 1 (by rfl) ⟨719405, by rfl⟩ : syracuseStep 959207 = 1438811) B1438811
theorem B959423 : Blo 638302 959423 := bstep (se 1 (by rfl) ⟨719567, by rfl⟩ : syracuseStep 959423 = 1439135) B1439135
theorem B1647625 : Blo 638302 1647625 := bstep (se 2 (by rfl) ⟨617859, by rfl⟩ : syracuseStep 1647625 = 1235719) B1235719
theorem B959519 : Blo 638302 959519 := bstep (se 1 (by rfl) ⟨719639, by rfl⟩ : syracuseStep 959519 = 1439279) B1439279
theorem B959753 : Blo 638302 959753 := bstep (se 2 (by rfl) ⟨359907, by rfl⟩ : syracuseStep 959753 = 719815) B719815
theorem B959903 : Blo 638302 959903 := bstep (se 1 (by rfl) ⟨719927, by rfl⟩ : syracuseStep 959903 = 1439855) B1439855
theorem B7284167 : Blo 638302 7284167 := bstep (se 1 (by rfl) ⟨5463125, by rfl⟩ : syracuseStep 7284167 = 10926251) B10926251
theorem B960239 : Blo 638302 960239 := bstep (se 1 (by rfl) ⟨720179, by rfl⟩ : syracuseStep 960239 = 1440359) B1440359
theorem B2631503 : Blo 638302 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B3450779 : Blo 638302 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B14756023 : Blo 638302 14756023 := bstep (se 1 (by rfl) ⟨11067017, by rfl⟩ : syracuseStep 14756023 = 22134035) B22134035
theorem B960959 : Blo 638302 960959 := bstep (se 1 (by rfl) ⟨720719, by rfl⟩ : syracuseStep 960959 = 1441439) B1441439
theorem B112077431 : Blo 638302 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B961151 : Blo 638302 961151 := bstep (se 1 (by rfl) ⟨720863, by rfl⟩ : syracuseStep 961151 = 1441727) B1441727
theorem B13118105 : Blo 638302 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B1617023 : Blo 638302 1617023 := bstep (se 1 (by rfl) ⟨1212767, by rfl⟩ : syracuseStep 1617023 = 2425535) B2425535
theorem B962027 : Blo 638302 962027 := bstep (se 1 (by rfl) ⟨721520, by rfl⟩ : syracuseStep 962027 = 1443041) B1443041
theorem B962303 : Blo 638302 962303 := bstep (se 1 (by rfl) ⟨721727, by rfl⟩ : syracuseStep 962303 = 1443455) B1443455
theorem B962471 : Blo 638302 962471 := bstep (se 1 (by rfl) ⟨721853, by rfl⟩ : syracuseStep 962471 = 1443707) B1443707
theorem B1618127 : Blo 638302 1618127 := bstep (se 1 (by rfl) ⟨1213595, by rfl⟩ : syracuseStep 1618127 = 2427191) B2427191
theorem B962879 : Blo 638302 962879 := bstep (se 1 (by rfl) ⟨722159, by rfl⟩ : syracuseStep 962879 = 1444319) B1444319
theorem B5551939 : Blo 638302 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B158185709 : Blo 638302 158185709 := bstep (se 3 (by rfl) ⟨29659820, by rfl⟩ : syracuseStep 158185709 = 59319641) B59319641
theorem B13844803 : Blo 638302 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B639903 : Blo 638302 639903 := bstep (se 1 (by rfl) ⟨479927, by rfl⟩ : syracuseStep 639903 = 959855) B959855
theorem B3457981 : Blo 638302 3457981 := bstep (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) B1296743
theorem B1623199 : Blo 638302 1623199 := bstep (se 1 (by rfl) ⟨1217399, by rfl⟩ : syracuseStep 1623199 = 2434799) B2434799
theorem B640447 : Blo 638302 640447 := bstep (se 1 (by rfl) ⟨480335, by rfl⟩ : syracuseStep 640447 = 960671) B960671
theorem B1623503 : Blo 638302 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B1820519 : Blo 638302 1820519 := bstep (se 1 (by rfl) ⟨1365389, by rfl⟩ : syracuseStep 1820519 = 2730779) B2730779
theorem B641087 : Blo 638302 641087 := bstep (se 1 (by rfl) ⟨480815, by rfl⟩ : syracuseStep 641087 = 961631) B961631
theorem B1624283 : Blo 638302 1624283 := bstep (se 1 (by rfl) ⟨1218212, by rfl⟩ : syracuseStep 1624283 = 2436425) B2436425
theorem B641503 : Blo 638302 641503 := bstep (se 1 (by rfl) ⟨481127, by rfl⟩ : syracuseStep 641503 = 962255) B962255
theorem B2313323 : Blo 638302 2313323 := bstep (se 1 (by rfl) ⟨1734992, by rfl⟩ : syracuseStep 2313323 = 3469985) B3469985
theorem B2084473 : Blo 638302 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B4935487 : Blo 638302 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B1822945 : Blo 638302 1822945 := bstep (se 2 (by rfl) ⟨683604, by rfl⟩ : syracuseStep 1822945 = 1367209) B1367209
theorem B3069011 : Blo 638302 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B20993219 : Blo 638302 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B5625283 : Blo 638302 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B18700139 : Blo 638302 18700139 := bstep (se 1 (by rfl) ⟨14025104, by rfl⟩ : syracuseStep 18700139 = 28050209) B28050209
theorem B3892391 : Blo 638302 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B8906183 : Blo 638302 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B812911 : Blo 638302 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B1828777 : Blo 638302 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B3074375 : Blo 638302 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B1436543 : Blo 638302 1436543 := bstep (se 1 (by rfl) ⟨1077407, by rfl⟩ : syracuseStep 1436543 = 2154815) B2154815
theorem B912703 : Blo 638302 912703 := bstep (se 1 (by rfl) ⟨684527, by rfl⟩ : syracuseStep 912703 = 1369055) B1369055
theorem B2158055 : Blo 638302 2158055 := bstep (se 1 (by rfl) ⟨1618541, by rfl⟩ : syracuseStep 2158055 = 3237083) B3237083
theorem B1732225 : Blo 638302 1732225 := bstep (se 2 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 1732225 = 1299169) B1299169
theorem B1437803 : Blo 638302 1437803 := bstep (se 1 (by rfl) ⟨1078352, by rfl⟩ : syracuseStep 1437803 = 2156705) B2156705
theorem B1439207 : Blo 638302 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B1439423 : Blo 638302 1439423 := bstep (se 1 (by rfl) ⟨1079567, by rfl⟩ : syracuseStep 1439423 = 2159135) B2159135
theorem B3078431 : Blo 638302 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B3242591 : Blo 638302 3242591 := bstep (se 1 (by rfl) ⟨2431943, by rfl⟩ : syracuseStep 3242591 = 4863887) B4863887
theorem B3636161 : Blo 638302 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B1441115 : Blo 638302 1441115 := bstep (se 1 (by rfl) ⟨1080836, by rfl⟩ : syracuseStep 1441115 = 2161673) B2161673
theorem B18415907 : Blo 638302 18415907 := bstep (se 1 (by rfl) ⟨13811930, by rfl⟩ : syracuseStep 18415907 = 27623861) B27623861
theorem B1082335 : Blo 638302 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B1213679 : Blo 638302 1213679 := bstep (se 1 (by rfl) ⟨910259, by rfl⟩ : syracuseStep 1213679 = 1820519) B1820519
theorem B2196833 : Blo 638302 2196833 := bstep (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) B1647625
theorem B1082855 : Blo 638302 1082855 := bstep (se 1 (by rfl) ⟨812141, by rfl⟩ : syracuseStep 1082855 = 1624283) B1624283
theorem B2164265 : Blo 638302 2164265 := bstep (se 2 (by rfl) ⟨811599, by rfl⟩ : syracuseStep 2164265 = 1623199) B1623199
theorem B24643115 : Blo 638302 24643115 := bstep (se 1 (by rfl) ⟨18482336, by rfl⟩ : syracuseStep 24643115 = 36964673) B36964673
theorem B31196735 : Blo 638302 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B1542215 : Blo 638302 1542215 := bstep (se 1 (by rfl) ⟨1156661, by rfl⟩ : syracuseStep 1542215 = 2313323) B2313323
theorem B1083881 : Blo 638302 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B2165831 : Blo 638302 2165831 := bstep (se 1 (by rfl) ⟨1624373, by rfl⟩ : syracuseStep 2165831 = 3248747) B3248747
theorem B13995479 : Blo 638302 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B7278335 : Blo 638302 7278335 := bstep (se 1 (by rfl) ⟨5458751, by rfl⟩ : syracuseStep 7278335 = 10917503) B10917503
theorem B14225519 : Blo 638302 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B1216937 : Blo 638302 1216937 := bstep (se 2 (by rfl) ⟨456351, by rfl⟩ : syracuseStep 1216937 = 912703) B912703
theorem B7705637 : Blo 638302 7705637 := bstep (se 4 (by rfl) ⟨722403, by rfl⟩ : syracuseStep 7705637 = 1444807) B1444807
theorem B2430593 : Blo 638302 2430593 := bstep (se 2 (by rfl) ⟨911472, by rfl⟩ : syracuseStep 2430593 = 1822945) B1822945
theorem B2594927 : Blo 638302 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B8198333 : Blo 638302 8198333 := bstep (se 3 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 8198333 = 3074375) B3074375
theorem B4856111 : Blo 638302 4856111 := bstep (se 1 (by rfl) ⟨3642083, by rfl⟩ : syracuseStep 4856111 = 7284167) B7284167
theorem B5937455 : Blo 638302 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B2300519 : Blo 638302 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B74718287 : Blo 638302 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B957695 : Blo 638302 957695 := bstep (se 1 (by rfl) ⟨718271, by rfl⟩ : syracuseStep 957695 = 1436543) B1436543
theorem B958535 : Blo 638302 958535 := bstep (se 1 (by rfl) ⟨718901, by rfl⟩ : syracuseStep 958535 = 1437803) B1437803
theorem B11117189 : Blo 638302 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B959471 : Blo 638302 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B959615 : Blo 638302 959615 := bstep (se 1 (by rfl) ⟨719711, by rfl⟩ : syracuseStep 959615 = 1439423) B1439423
theorem B105457139 : Blo 638302 105457139 := bstep (se 1 (by rfl) ⟨79092854, by rfl⟩ : syracuseStep 105457139 = 158185709) B158185709
theorem B960743 : Blo 638302 960743 := bstep (se 1 (by rfl) ⟨720557, by rfl⟩ : syracuseStep 960743 = 1441115) B1441115
theorem B18459737 : Blo 638302 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B961691 : Blo 638302 961691 := bstep (se 1 (by rfl) ⟨721268, by rfl⟩ : syracuseStep 961691 = 1442537) B1442537
theorem B4369859 : Blo 638302 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B963431 : Blo 638302 963431 := bstep (se 1 (by rfl) ⟨722573, by rfl⟩ : syracuseStep 963431 = 1445147) B1445147
theorem B2438369 : Blo 638302 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B19674697 : Blo 638302 19674697 := bstep (se 2 (by rfl) ⟨7378011, by rfl⟩ : syracuseStep 19674697 = 14756023) B14756023
theorem B2046007 : Blo 638302 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B12466759 : Blo 638302 12466759 := bstep (se 1 (by rfl) ⟨9350069, by rfl⟩ : syracuseStep 12466759 = 18700139) B18700139
theorem B2309633 : Blo 638302 2309633 := bstep (se 2 (by rfl) ⟨866112, by rfl⟩ : syracuseStep 2309633 = 1732225) B1732225
theorem B638591 : Blo 638302 638591 := bstep (se 1 (by rfl) ⟨478943, by rfl⟩ : syracuseStep 638591 = 957887) B957887
theorem B639227 : Blo 638302 639227 := bstep (se 1 (by rfl) ⟨479420, by rfl⟩ : syracuseStep 639227 = 958841) B958841
theorem B639471 : Blo 638302 639471 := bstep (se 1 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 639471 = 959207) B959207
theorem B639615 : Blo 638302 639615 := bstep (se 1 (by rfl) ⟨479711, by rfl⟩ : syracuseStep 639615 = 959423) B959423
theorem B639679 : Blo 638302 639679 := bstep (se 1 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 639679 = 959519) B959519
theorem B639835 : Blo 638302 639835 := bstep (se 1 (by rfl) ⟨479876, by rfl⟩ : syracuseStep 639835 = 959753) B959753
theorem B639935 : Blo 638302 639935 := bstep (se 1 (by rfl) ⟨479951, by rfl⟩ : syracuseStep 639935 = 959903) B959903
theorem B640159 : Blo 638302 640159 := bstep (se 1 (by rfl) ⟨480119, by rfl⟩ : syracuseStep 640159 = 960239) B960239
theorem B1754335 : Blo 638302 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B640639 : Blo 638302 640639 := bstep (se 1 (by rfl) ⟨480479, by rfl⟩ : syracuseStep 640639 = 960959) B960959
theorem B640767 : Blo 638302 640767 := bstep (se 1 (by rfl) ⟨480575, by rfl⟩ : syracuseStep 640767 = 961151) B961151
theorem B641351 : Blo 638302 641351 := bstep (se 1 (by rfl) ⟨481013, by rfl⟩ : syracuseStep 641351 = 962027) B962027
theorem B641535 : Blo 638302 641535 := bstep (se 1 (by rfl) ⟨481151, by rfl⟩ : syracuseStep 641535 = 962303) B962303
theorem B641647 : Blo 638302 641647 := bstep (se 1 (by rfl) ⟨481235, by rfl⟩ : syracuseStep 641647 = 962471) B962471
theorem B641919 : Blo 638302 641919 := bstep (se 1 (by rfl) ⟨481439, by rfl⟩ : syracuseStep 641919 = 962879) B962879
theorem B2052287 : Blo 638302 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B4610641 : Blo 638302 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B5857271 : Blo 638302 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B6580649 : Blo 638302 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B8745403 : Blo 638302 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B7500377 : Blo 638302 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B1078015 : Blo 638302 1078015 := bstep (se 1 (by rfl) ⟨808511, by rfl⟩ : syracuseStep 1078015 = 1617023) B1617023
theorem B1438703 : Blo 638302 1438703 := bstep (se 1 (by rfl) ⟨1079027, by rfl⟩ : syracuseStep 1438703 = 2158055) B2158055
theorem B7402585 : Blo 638302 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B1078751 : Blo 638302 1078751 := bstep (se 1 (by rfl) ⟨809063, by rfl⟩ : syracuseStep 1078751 = 1618127) B1618127
theorem B2161727 : Blo 638302 2161727 := bstep (se 1 (by rfl) ⟨1621295, by rfl⟩ : syracuseStep 2161727 = 3242591) B3242591
theorem B2424107 : Blo 638302 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B721903 : Blo 638302 721903 := bstep (se 1 (by rfl) ⟨541427, by rfl⟩ : syracuseStep 721903 = 1082855) B1082855
theorem B1442843 : Blo 638302 1442843 := bstep (se 1 (by rfl) ⟨1082132, by rfl⟩ : syracuseStep 1442843 = 2164265) B2164265
theorem B1443113 : Blo 638302 1443113 := bstep (se 2 (by rfl) ⟨541167, by rfl⟩ : syracuseStep 1443113 = 1082335) B1082335
theorem B722587 : Blo 638302 722587 := bstep (se 1 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 722587 = 1083881) B1083881
theorem B1443887 : Blo 638302 1443887 := bstep (se 1 (by rfl) ⟨1082915, by rfl⟩ : syracuseStep 1443887 = 2165831) B2165831
theorem B4852223 : Blo 638302 4852223 := bstep (se 1 (by rfl) ⟨3639167, by rfl⟩ : syracuseStep 4852223 = 7278335) B7278335
theorem B23432885 : Blo 638302 23432885 := bstep (se 5 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 23432885 = 2196833) B2196833
theorem B49812191 : Blo 638302 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B3904847 : Blo 638302 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B6919805 : Blo 638302 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B7411459 : Blo 638302 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B9870113 : Blo 638302 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B6134717 : Blo 638302 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B2728009 : Blo 638302 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B959135 : Blo 638302 959135 := bstep (se 1 (by rfl) ⟨719351, by rfl⟩ : syracuseStep 959135 = 1438703) B1438703
theorem B16622345 : Blo 638302 16622345 := bstep (se 2 (by rfl) ⟨6233379, by rfl⟩ : syracuseStep 16622345 = 12466759) B12466759
theorem B1616071 : Blo 638302 1616071 := bstep (se 1 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 1616071 = 2424107) B2424107
theorem B16428743 : Blo 638302 16428743 := bstep (se 1 (by rfl) ⟨12321557, by rfl⟩ : syracuseStep 16428743 = 24643115) B24643115
theorem B1028143 : Blo 638302 1028143 := bstep (se 1 (by rfl) ⟨771107, by rfl⟩ : syracuseStep 1028143 = 1542215) B1542215
theorem B20001005 : Blo 638302 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B2339113 : Blo 638302 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B9483679 : Blo 638302 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B1620395 : Blo 638302 1620395 := bstep (se 1 (by rfl) ⟨1215296, by rfl⟩ : syracuseStep 1620395 = 2430593) B2430593
theorem B638463 : Blo 638302 638463 := bstep (se 1 (by rfl) ⟨478847, by rfl⟩ : syracuseStep 638463 = 957695) B957695
theorem B639023 : Blo 638302 639023 := bstep (se 1 (by rfl) ⟨479267, by rfl⟩ : syracuseStep 639023 = 958535) B958535
theorem B639647 : Blo 638302 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B639743 : Blo 638302 639743 := bstep (se 1 (by rfl) ⟨479807, by rfl⟩ : syracuseStep 639743 = 959615) B959615
theorem B70304759 : Blo 638302 70304759 := bstep (se 1 (by rfl) ⟨52728569, by rfl⟩ : syracuseStep 70304759 = 105457139) B105457139
theorem B17548397 : Blo 638302 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B640495 : Blo 638302 640495 := bstep (se 1 (by rfl) ⟨480371, by rfl⟩ : syracuseStep 640495 = 960743) B960743
theorem B12306491 : Blo 638302 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B26232929 : Blo 638302 26232929 := bstep (se 2 (by rfl) ⟨9837348, by rfl⟩ : syracuseStep 26232929 = 19674697) B19674697
theorem B641127 : Blo 638302 641127 := bstep (se 1 (by rfl) ⟨480845, by rfl⟩ : syracuseStep 641127 = 961691) B961691
theorem B642287 : Blo 638302 642287 := bstep (se 1 (by rfl) ⟨481715, by rfl⟩ : syracuseStep 642287 = 963431) B963431
theorem B6147521 : Blo 638302 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B1625579 : Blo 638302 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B12277271 : Blo 638302 12277271 := bstep (se 1 (by rfl) ⟨9207953, by rfl⟩ : syracuseStep 12277271 = 18415907) B18415907
theorem B809119 : Blo 638302 809119 := bstep (se 1 (by rfl) ⟨606839, by rfl⟩ : syracuseStep 809119 = 1213679) B1213679
theorem B20797823 : Blo 638302 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B9330319 : Blo 638302 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B1368191 : Blo 638302 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B811291 : Blo 638302 811291 := bstep (se 1 (by rfl) ⟨608468, by rfl⟩ : syracuseStep 811291 = 1216937) B1216937
theorem B5137091 : Blo 638302 5137091 := bstep (se 1 (by rfl) ⟨3852818, by rfl⟩ : syracuseStep 5137091 = 7705637) B7705637
theorem B5465555 : Blo 638302 5465555 := bstep (se 1 (by rfl) ⟨4099166, by rfl⟩ : syracuseStep 5465555 = 8198333) B8198333
theorem B3237407 : Blo 638302 3237407 := bstep (se 1 (by rfl) ⟨2428055, by rfl⟩ : syracuseStep 3237407 = 4856111) B4856111
theorem B3958303 : Blo 638302 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B11660537 : Blo 638302 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B1437353 : Blo 638302 1437353 := bstep (se 2 (by rfl) ⟨539007, by rfl⟩ : syracuseStep 1437353 = 1078015) B1078015
theorem B2913239 : Blo 638302 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B719167 : Blo 638302 719167 := bstep (se 1 (by rfl) ⟨539375, by rfl⟩ : syracuseStep 719167 = 1078751) B1078751
theorem B1441151 : Blo 638302 1441151 := bstep (se 1 (by rfl) ⟨1080863, by rfl⟩ : syracuseStep 1441151 = 2161727) B2161727
theorem B1539755 : Blo 638302 1539755 := bstep (se 1 (by rfl) ⟨1154816, by rfl⟩ : syracuseStep 1539755 = 2309633) B2309633
theorem B3637345 : Blo 638302 3637345 := bstep (se 2 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 3637345 = 2728009) B2728009
theorem B1081721 : Blo 638302 1081721 := bstep (se 2 (by rfl) ⟨405645, by rfl⟩ : syracuseStep 1081721 = 811291) B811291
theorem B11698931 : Blo 638302 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B5277737 : Blo 638302 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B4098347 : Blo 638302 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B1083719 : Blo 638302 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B13865215 : Blo 638302 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B3118817 : Blo 638302 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B3643703 : Blo 638302 3643703 := bstep (se 1 (by rfl) ⟨2732777, by rfl⟩ : syracuseStep 3643703 = 5465555) B5465555
theorem B958235 : Blo 638302 958235 := bstep (se 1 (by rfl) ⟨718676, by rfl⟩ : syracuseStep 958235 = 1437353) B1437353
theorem B10952495 : Blo 638302 10952495 := bstep (se 1 (by rfl) ⟨8214371, by rfl⟩ : syracuseStep 10952495 = 16428743) B16428743
theorem B958889 : Blo 638302 958889 := bstep (se 2 (by rfl) ⟨359583, by rfl⟩ : syracuseStep 958889 = 719167) B719167
theorem B1942159 : Blo 638302 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B960767 : Blo 638302 960767 := bstep (se 1 (by rfl) ⟨720575, by rfl⟩ : syracuseStep 960767 = 1441151) B1441151
theorem B1026503 : Blo 638302 1026503 := bstep (se 1 (by rfl) ⟨769877, by rfl⟩ : syracuseStep 1026503 = 1539755) B1539755
theorem B3648509 : Blo 638302 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B46869839 : Blo 638302 46869839 := bstep (se 1 (by rfl) ⟨35152379, by rfl⟩ : syracuseStep 46869839 = 70304759) B70304759
theorem B961895 : Blo 638302 961895 := bstep (se 1 (by rfl) ⟨721421, by rfl⟩ : syracuseStep 961895 = 1442843) B1442843
theorem B962075 : Blo 638302 962075 := bstep (se 1 (by rfl) ⟨721556, by rfl⟩ : syracuseStep 962075 = 1443113) B1443113
theorem B962537 : Blo 638302 962537 := bstep (se 2 (by rfl) ⟨360951, by rfl⟩ : syracuseStep 962537 = 721903) B721903
theorem B962591 : Blo 638302 962591 := bstep (se 1 (by rfl) ⟨721943, by rfl⟩ : syracuseStep 962591 = 1443887) B1443887
theorem B8204327 : Blo 638302 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B963449 : Blo 638302 963449 := bstep (se 2 (by rfl) ⟨361293, by rfl⟩ : syracuseStep 963449 = 722587) B722587
theorem B33208127 : Blo 638302 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B2603231 : Blo 638302 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B639423 : Blo 638302 639423 := bstep (se 1 (by rfl) ⟨479567, by rfl⟩ : syracuseStep 639423 = 959135) B959135
theorem B3424727 : Blo 638302 3424727 := bstep (se 1 (by rfl) ⟨2568545, by rfl⟩ : syracuseStep 3424727 = 5137091) B5137091
theorem B50579621 : Blo 638302 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B9881945 : Blo 638302 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B49761701 : Blo 638302 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B17488619 : Blo 638302 17488619 := bstep (se 1 (by rfl) ⟨13116464, by rfl⟩ : syracuseStep 17488619 = 26232929) B26232929
theorem B3234815 : Blo 638302 3234815 := bstep (se 1 (by rfl) ⟨2426111, by rfl⟩ : syracuseStep 3234815 = 4852223) B4852223
theorem B44326253 : Blo 638302 44326253 := bstep (se 3 (by rfl) ⟨8311172, by rfl⟩ : syracuseStep 44326253 = 16622345) B16622345
theorem B15621923 : Blo 638302 15621923 := bstep (se 1 (by rfl) ⟨11716442, by rfl⟩ : syracuseStep 15621923 = 23432885) B23432885
theorem B2154761 : Blo 638302 2154761 := bstep (se 2 (by rfl) ⟨808035, by rfl⟩ : syracuseStep 2154761 = 1616071) B1616071
theorem B8184847 : Blo 638302 8184847 := bstep (se 1 (by rfl) ⟨6138635, by rfl⟩ : syracuseStep 8184847 = 12277271) B12277271
theorem B4613203 : Blo 638302 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B6580075 : Blo 638302 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B4089811 : Blo 638302 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B1370857 : Blo 638302 1370857 := bstep (se 2 (by rfl) ⟨514071, by rfl⟩ : syracuseStep 1370857 = 1028143) B1028143
theorem B2158271 : Blo 638302 2158271 := bstep (se 1 (by rfl) ⟨1618703, by rfl⟩ : syracuseStep 2158271 = 3237407) B3237407
theorem B13334003 : Blo 638302 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B1078825 : Blo 638302 1078825 := bstep (se 2 (by rfl) ⟨404559, by rfl⟩ : syracuseStep 1078825 = 809119) B809119
theorem B31094765 : Blo 638302 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B1080263 : Blo 638302 1080263 := bstep (se 1 (by rfl) ⟨810197, by rfl⟩ : syracuseStep 1080263 = 1620395) B1620395
theorem B4849793 : Blo 638302 4849793 := bstep (se 2 (by rfl) ⟨1818672, by rfl⟩ : syracuseStep 4849793 = 3637345) B3637345
theorem B721147 : Blo 638302 721147 := bstep (se 1 (by rfl) ⟨540860, by rfl⟩ : syracuseStep 721147 = 1081721) B1081721
theorem B7799287 : Blo 638302 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B2589545 : Blo 638302 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B10913129 : Blo 638302 10913129 := bstep (se 2 (by rfl) ⟨4092423, by rfl⟩ : syracuseStep 10913129 = 8184847) B8184847
theorem B33719747 : Blo 638302 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B722479 : Blo 638302 722479 := bstep (se 1 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 722479 = 1083719) B1083719
theorem B6587963 : Blo 638302 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B2429135 : Blo 638302 2429135 := bstep (se 1 (by rfl) ⟨1821851, by rfl⟩ : syracuseStep 2429135 = 3643703) B3643703
theorem B18486953 : Blo 638302 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B2432339 : Blo 638302 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B8889335 : Blo 638302 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B3518491 : Blo 638302 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B2732231 : Blo 638302 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B33174467 : Blo 638302 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B5453081 : Blo 638302 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B2079211 : Blo 638302 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B638823 : Blo 638302 638823 := bstep (se 1 (by rfl) ⟨479117, by rfl⟩ : syracuseStep 638823 = 958235) B958235
theorem B639259 : Blo 638302 639259 := bstep (se 1 (by rfl) ⟨479444, by rfl⟩ : syracuseStep 639259 = 958889) B958889
theorem B640511 : Blo 638302 640511 := bstep (se 1 (by rfl) ⟨480383, by rfl⟩ : syracuseStep 640511 = 960767) B960767
theorem B31246559 : Blo 638302 31246559 := bstep (se 1 (by rfl) ⟨23434919, by rfl⟩ : syracuseStep 31246559 = 46869839) B46869839
theorem B641263 : Blo 638302 641263 := bstep (se 1 (by rfl) ⟨480947, by rfl⟩ : syracuseStep 641263 = 961895) B961895
theorem B641383 : Blo 638302 641383 := bstep (se 1 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 641383 = 962075) B962075
theorem B641691 : Blo 638302 641691 := bstep (se 1 (by rfl) ⟨481268, by rfl⟩ : syracuseStep 641691 = 962537) B962537
theorem B641727 : Blo 638302 641727 := bstep (se 1 (by rfl) ⟨481295, by rfl⟩ : syracuseStep 641727 = 962591) B962591
theorem B642299 : Blo 638302 642299 := bstep (se 1 (by rfl) ⟨481724, by rfl⟩ : syracuseStep 642299 = 963449) B963449
theorem B22138751 : Blo 638302 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B20729843 : Blo 638302 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B9132605 : Blo 638302 9132605 := bstep (se 3 (by rfl) ⟨1712363, by rfl⟩ : syracuseStep 9132605 = 3424727) B3424727
theorem B8773433 : Blo 638302 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B1827809 : Blo 638302 1827809 := bstep (se 2 (by rfl) ⟨685428, by rfl⟩ : syracuseStep 1827809 = 1370857) B1370857
theorem B11659079 : Blo 638302 11659079 := bstep (se 1 (by rfl) ⟨8744309, by rfl⟩ : syracuseStep 11659079 = 17488619) B17488619
theorem B2156543 : Blo 638302 2156543 := bstep (se 1 (by rfl) ⟨1617407, by rfl⟩ : syracuseStep 2156543 = 3234815) B3234815
theorem B29550835 : Blo 638302 29550835 := bstep (se 1 (by rfl) ⟨22163126, by rfl⟩ : syracuseStep 29550835 = 44326253) B44326253
theorem B10414615 : Blo 638302 10414615 := bstep (se 1 (by rfl) ⟨7810961, by rfl⟩ : syracuseStep 10414615 = 15621923) B15621923
theorem B7301663 : Blo 638302 7301663 := bstep (se 1 (by rfl) ⟨5476247, by rfl⟩ : syracuseStep 7301663 = 10952495) B10952495
theorem B1436507 : Blo 638302 1436507 := bstep (se 1 (by rfl) ⟨1077380, by rfl⟩ : syracuseStep 1436507 = 2154761) B2154761
theorem B24603749 : Blo 638302 24603749 := bstep (se 4 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 24603749 = 4613203) B4613203
theorem B684335 : Blo 638302 684335 := bstep (se 1 (by rfl) ⟨513251, by rfl⟩ : syracuseStep 684335 = 1026503) B1026503
theorem B1438433 : Blo 638302 1438433 := bstep (se 2 (by rfl) ⟨539412, by rfl⟩ : syracuseStep 1438433 = 1078825) B1078825
theorem B1438847 : Blo 638302 1438847 := bstep (se 1 (by rfl) ⟨1079135, by rfl⟩ : syracuseStep 1438847 = 2158271) B2158271
theorem B5469551 : Blo 638302 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B1735487 : Blo 638302 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B720175 : Blo 638302 720175 := bstep (se 1 (by rfl) ⟨540131, by rfl⟩ : syracuseStep 720175 = 1080263) B1080263
theorem B7275419 : Blo 638302 7275419 := bstep (se 1 (by rfl) ⟨5456564, by rfl⟩ : syracuseStep 7275419 = 10913129) B10913129
theorem B4391975 : Blo 638302 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B12324635 : Blo 638302 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B89919325 : Blo 638302 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B4691321 : Blo 638302 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B1218539 : Blo 638302 1218539 := bstep (se 1 (by rfl) ⟨913904, by rfl⟩ : syracuseStep 1218539 = 1827809) B1827809
theorem B7772719 : Blo 638302 7772719 := bstep (se 1 (by rfl) ⟨5829539, by rfl⟩ : syracuseStep 7772719 = 11659079) B11659079
theorem B957671 : Blo 638302 957671 := bstep (se 1 (by rfl) ⟨718253, by rfl⟩ : syracuseStep 957671 = 1436507) B1436507
theorem B958955 : Blo 638302 958955 := bstep (se 1 (by rfl) ⟨719216, by rfl⟩ : syracuseStep 958955 = 1438433) B1438433
theorem B959231 : Blo 638302 959231 := bstep (se 1 (by rfl) ⟨719423, by rfl⟩ : syracuseStep 959231 = 1438847) B1438847
theorem B3646367 : Blo 638302 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B960233 : Blo 638302 960233 := bstep (se 2 (by rfl) ⟨360087, by rfl⟩ : syracuseStep 960233 = 720175) B720175
theorem B961529 : Blo 638302 961529 := bstep (se 2 (by rfl) ⟨360573, by rfl⟩ : syracuseStep 961529 = 721147) B721147
theorem B10399049 : Blo 638302 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B963305 : Blo 638302 963305 := bstep (se 2 (by rfl) ⟨361239, by rfl⟩ : syracuseStep 963305 = 722479) B722479
theorem B14759167 : Blo 638302 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B1619423 : Blo 638302 1619423 := bstep (se 1 (by rfl) ⟨1214567, by rfl⟩ : syracuseStep 1619423 = 2429135) B2429135
theorem B39401113 : Blo 638302 39401113 := bstep (se 2 (by rfl) ⟨14775417, by rfl⟩ : syracuseStep 39401113 = 29550835) B29550835
theorem B1621559 : Blo 638302 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B5848955 : Blo 638302 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B4867775 : Blo 638302 4867775 := bstep (se 1 (by rfl) ⟨3650831, by rfl⟩ : syracuseStep 4867775 = 7301663) B7301663
theorem B16402499 : Blo 638302 16402499 := bstep (se 1 (by rfl) ⟨12301874, by rfl⟩ : syracuseStep 16402499 = 24603749) B24603749
theorem B1821487 : Blo 638302 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B2772281 : Blo 638302 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B3233195 : Blo 638302 3233195 := bstep (se 1 (by rfl) ⟨2424896, by rfl⟩ : syracuseStep 3233195 = 4849793) B4849793
theorem B1726363 : Blo 638302 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1824893 : Blo 638302 1824893 := bstep (se 3 (by rfl) ⟨342167, by rfl⟩ : syracuseStep 1824893 = 684335) B684335
theorem B20831039 : Blo 638302 20831039 := bstep (se 1 (by rfl) ⟨15623279, by rfl⟩ : syracuseStep 20831039 = 31246559) B31246559
theorem B13819895 : Blo 638302 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B13886153 : Blo 638302 13886153 := bstep (se 2 (by rfl) ⟨5207307, by rfl⟩ : syracuseStep 13886153 = 10414615) B10414615
theorem B6088403 : Blo 638302 6088403 := bstep (se 1 (by rfl) ⟨4566302, by rfl⟩ : syracuseStep 6088403 = 9132605) B9132605
theorem B5926223 : Blo 638302 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B1437695 : Blo 638302 1437695 := bstep (se 1 (by rfl) ⟨1078271, by rfl⟩ : syracuseStep 1437695 = 2156543) B2156543
theorem B22116311 : Blo 638302 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B18511861 : Blo 638302 18511861 := bstep (se 5 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 18511861 = 1735487) B1735487
theorem B3635387 : Blo 638302 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B4850279 : Blo 638302 4850279 := bstep (se 1 (by rfl) ⟨3637709, by rfl⟩ : syracuseStep 4850279 = 7275419) B7275419
theorem B3245183 : Blo 638302 3245183 := bstep (se 1 (by rfl) ⟨2433887, by rfl⟩ : syracuseStep 3245183 = 4867775) B4867775
theorem B2428649 : Blo 638302 2428649 := bstep (se 2 (by rfl) ⟨910743, by rfl⟩ : syracuseStep 2428649 = 1821487) B1821487
theorem B1216595 : Blo 638302 1216595 := bstep (se 1 (by rfl) ⟨912446, by rfl⟩ : syracuseStep 1216595 = 1824893) B1824893
theorem B9213263 : Blo 638302 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B2430911 : Blo 638302 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B52534817 : Blo 638302 52534817 := bstep (se 2 (by rfl) ⟨19700556, by rfl⟩ : syracuseStep 52534817 = 39401113) B39401113
theorem B24682481 : Blo 638302 24682481 := bstep (se 2 (by rfl) ⟨9255930, by rfl⟩ : syracuseStep 24682481 = 18511861) B18511861
theorem B958463 : Blo 638302 958463 := bstep (se 1 (by rfl) ⟨718847, by rfl⟩ : syracuseStep 958463 = 1437695) B1437695
theorem B10363625 : Blo 638302 10363625 := bstep (se 2 (by rfl) ⟨3886359, by rfl⟩ : syracuseStep 10363625 = 7772719) B7772719
theorem B479569733 : Blo 638302 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B2927983 : Blo 638302 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B1848187 : Blo 638302 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B3127547 : Blo 638302 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B16235741 : Blo 638302 16235741 := bstep (se 3 (by rfl) ⟨3044201, by rfl⟩ : syracuseStep 16235741 = 6088403) B6088403
theorem B638447 : Blo 638302 638447 := bstep (se 1 (by rfl) ⟨478835, by rfl⟩ : syracuseStep 638447 = 957671) B957671
theorem B639303 : Blo 638302 639303 := bstep (se 1 (by rfl) ⟨479477, by rfl⟩ : syracuseStep 639303 = 958955) B958955
theorem B9257435 : Blo 638302 9257435 := bstep (se 1 (by rfl) ⟨6943076, by rfl⟩ : syracuseStep 9257435 = 13886153) B13886153
theorem B639487 : Blo 638302 639487 := bstep (se 1 (by rfl) ⟨479615, by rfl⟩ : syracuseStep 639487 = 959231) B959231
theorem B640155 : Blo 638302 640155 := bstep (se 1 (by rfl) ⟨480116, by rfl⟩ : syracuseStep 640155 = 960233) B960233
theorem B19678889 : Blo 638302 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B641019 : Blo 638302 641019 := bstep (se 1 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 641019 = 961529) B961529
theorem B6932699 : Blo 638302 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B3950815 : Blo 638302 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B642203 : Blo 638302 642203 := bstep (se 1 (by rfl) ⟨481652, by rfl⟩ : syracuseStep 642203 = 963305) B963305
theorem B10934999 : Blo 638302 10934999 := bstep (se 1 (by rfl) ⟨8201249, by rfl⟩ : syracuseStep 10934999 = 16402499) B16402499
theorem B8216423 : Blo 638302 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B2155463 : Blo 638302 2155463 := bstep (se 1 (by rfl) ⟨1616597, by rfl⟩ : syracuseStep 2155463 = 3233195) B3233195
theorem B812359 : Blo 638302 812359 := bstep (se 1 (by rfl) ⟨609269, by rfl⟩ : syracuseStep 812359 = 1218539) B1218539
theorem B13887359 : Blo 638302 13887359 := bstep (se 1 (by rfl) ⟨10415519, by rfl⟩ : syracuseStep 13887359 = 20831039) B20831039
theorem B1079615 : Blo 638302 1079615 := bstep (se 1 (by rfl) ⟨809711, by rfl⟩ : syracuseStep 1079615 = 1619423) B1619423
theorem B14744207 : Blo 638302 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B2423591 : Blo 638302 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B9207269 : Blo 638302 9207269 := bstep (se 4 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 9207269 = 1726363) B1726363
theorem B1081039 : Blo 638302 1081039 := bstep (se 1 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 1081039 = 1621559) B1621559
theorem B3899303 : Blo 638302 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B2163455 : Blo 638302 2163455 := bstep (se 1 (by rfl) ⟨1622591, by rfl⟩ : syracuseStep 2163455 = 3245183) B3245183
theorem B4621799 : Blo 638302 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B1083145 : Blo 638302 1083145 := bstep (se 2 (by rfl) ⟨406179, by rfl⟩ : syracuseStep 1083145 = 812359) B812359
theorem B3903977 : Blo 638302 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B5477615 : Blo 638302 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B16454987 : Blo 638302 16454987 := bstep (se 1 (by rfl) ⟨12341240, by rfl⟩ : syracuseStep 16454987 = 24682481) B24682481
theorem B2464249 : Blo 638302 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B43295309 : Blo 638302 43295309 := bstep (se 3 (by rfl) ⟨8117870, by rfl⟩ : syracuseStep 43295309 = 16235741) B16235741
theorem B1615727 : Blo 638302 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B6138179 : Blo 638302 6138179 := bstep (se 1 (by rfl) ⟨4603634, by rfl⟩ : syracuseStep 6138179 = 9207269) B9207269
theorem B2599535 : Blo 638302 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B6171623 : Blo 638302 6171623 := bstep (se 1 (by rfl) ⟨4628717, by rfl⟩ : syracuseStep 6171623 = 9257435) B9257435
theorem B13119259 : Blo 638302 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B1619099 : Blo 638302 1619099 := bstep (se 1 (by rfl) ⟨1214324, by rfl⟩ : syracuseStep 1619099 = 2428649) B2428649
theorem B6142175 : Blo 638302 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B1620607 : Blo 638302 1620607 := bstep (se 1 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 1620607 = 2430911) B2430911
theorem B7289999 : Blo 638302 7289999 := bstep (se 1 (by rfl) ⟨5467499, by rfl⟩ : syracuseStep 7289999 = 10934999) B10934999
theorem B638975 : Blo 638302 638975 := bstep (se 1 (by rfl) ⟨479231, by rfl⟩ : syracuseStep 638975 = 958463) B958463
theorem B9258239 : Blo 638302 9258239 := bstep (se 1 (by rfl) ⟨6943679, by rfl⟩ : syracuseStep 9258239 = 13887359) B13887359
theorem B2085031 : Blo 638302 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B3233519 : Blo 638302 3233519 := bstep (se 1 (by rfl) ⟨2425139, by rfl⟩ : syracuseStep 3233519 = 4850279) B4850279
theorem B811063 : Blo 638302 811063 := bstep (se 1 (by rfl) ⟨608297, by rfl⟩ : syracuseStep 811063 = 1216595) B1216595
theorem B5267753 : Blo 638302 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B35023211 : Blo 638302 35023211 := bstep (se 1 (by rfl) ⟨26267408, by rfl⟩ : syracuseStep 35023211 = 52534817) B52534817
theorem B6909083 : Blo 638302 6909083 := bstep (se 1 (by rfl) ⟨5181812, by rfl⟩ : syracuseStep 6909083 = 10363625) B10363625
theorem B1436975 : Blo 638302 1436975 := bstep (se 1 (by rfl) ⟨1077731, by rfl⟩ : syracuseStep 1436975 = 2155463) B2155463
theorem B319713155 : Blo 638302 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B719743 : Blo 638302 719743 := bstep (se 1 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 719743 = 1079615) B1079615
theorem B9829471 : Blo 638302 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B1441385 : Blo 638302 1441385 := bstep (se 2 (by rfl) ⟨540519, by rfl⟩ : syracuseStep 1441385 = 1081039) B1081039
theorem B1081417 : Blo 638302 1081417 := bstep (se 2 (by rfl) ⟨405531, by rfl⟩ : syracuseStep 1081417 = 811063) B811063
theorem B1442303 : Blo 638302 1442303 := bstep (se 1 (by rfl) ⟨1081727, by rfl⟩ : syracuseStep 1442303 = 2163455) B2163455
theorem B3081199 : Blo 638302 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B1444193 : Blo 638302 1444193 := bstep (se 2 (by rfl) ⟨541572, by rfl⟩ : syracuseStep 1444193 = 1083145) B1083145
theorem B3511835 : Blo 638302 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B957983 : Blo 638302 957983 := bstep (se 1 (by rfl) ⟨718487, by rfl⟩ : syracuseStep 957983 = 1436975) B1436975
theorem B3285665 : Blo 638302 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B959657 : Blo 638302 959657 := bstep (se 2 (by rfl) ⟨359871, by rfl⟩ : syracuseStep 959657 = 719743) B719743
theorem B4859999 : Blo 638302 4859999 := bstep (se 1 (by rfl) ⟨3644999, by rfl⟩ : syracuseStep 4859999 = 7289999) B7289999
theorem B960923 : Blo 638302 960923 := bstep (se 1 (by rfl) ⟨720692, by rfl⟩ : syracuseStep 960923 = 1441385) B1441385
theorem B6172159 : Blo 638302 6172159 := bstep (se 1 (by rfl) ⟨4629119, by rfl⟩ : syracuseStep 6172159 = 9258239) B9258239
theorem B11120165 : Blo 638302 11120165 := bstep (se 4 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 11120165 = 2085031) B2085031
theorem B2602651 : Blo 638302 2602651 := bstep (se 1 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 2602651 = 3903977) B3903977
theorem B3651743 : Blo 638302 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B23348807 : Blo 638302 23348807 := bstep (se 1 (by rfl) ⟨17511605, by rfl⟩ : syracuseStep 23348807 = 35023211) B35023211
theorem B4114415 : Blo 638302 4114415 := bstep (se 1 (by rfl) ⟨3085811, by rfl⟩ : syracuseStep 4114415 = 6171623) B6171623
theorem B4606055 : Blo 638302 4606055 := bstep (se 1 (by rfl) ⟨3454541, by rfl⟩ : syracuseStep 4606055 = 6909083) B6909083
theorem B213142103 : Blo 638302 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B10969991 : Blo 638302 10969991 := bstep (se 1 (by rfl) ⟨8227493, by rfl⟩ : syracuseStep 10969991 = 16454987) B16454987
theorem B2155679 : Blo 638302 2155679 := bstep (se 1 (by rfl) ⟨1616759, by rfl⟩ : syracuseStep 2155679 = 3233519) B3233519
theorem B17492345 : Blo 638302 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B28863539 : Blo 638302 28863539 := bstep (se 1 (by rfl) ⟨21647654, by rfl⟩ : syracuseStep 28863539 = 43295309) B43295309
theorem B1077151 : Blo 638302 1077151 := bstep (se 1 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 1077151 = 1615727) B1615727
theorem B4092119 : Blo 638302 4092119 := bstep (se 1 (by rfl) ⟨3069089, by rfl⟩ : syracuseStep 4092119 = 6138179) B6138179
theorem B1733023 : Blo 638302 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B1079399 : Blo 638302 1079399 := bstep (se 1 (by rfl) ⟨809549, by rfl⟩ : syracuseStep 1079399 = 1619099) B1619099
theorem B2160809 : Blo 638302 2160809 := bstep (se 2 (by rfl) ⟨810303, by rfl⟩ : syracuseStep 2160809 = 1620607) B1620607
theorem B13105961 : Blo 638302 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B4094783 : Blo 638302 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B1441889 : Blo 638302 1441889 := bstep (se 2 (by rfl) ⟨540708, by rfl⟩ : syracuseStep 1441889 = 1081417) B1081417
theorem B15565871 : Blo 638302 15565871 := bstep (se 1 (by rfl) ⟨11674403, by rfl⟩ : syracuseStep 15565871 = 23348807) B23348807
theorem B8229545 : Blo 638302 8229545 := bstep (se 2 (by rfl) ⟨3086079, by rfl⟩ : syracuseStep 8229545 = 6172159) B6172159
theorem B7313327 : Blo 638302 7313327 := bstep (se 1 (by rfl) ⟨5484995, by rfl⟩ : syracuseStep 7313327 = 10969991) B10969991
theorem B19242359 : Blo 638302 19242359 := bstep (se 1 (by rfl) ⟨14431769, by rfl⟩ : syracuseStep 19242359 = 28863539) B28863539
theorem B7413443 : Blo 638302 7413443 := bstep (se 1 (by rfl) ⟨5560082, by rfl⟩ : syracuseStep 7413443 = 11120165) B11120165
theorem B2728079 : Blo 638302 2728079 := bstep (se 1 (by rfl) ⟨2046059, by rfl⟩ : syracuseStep 2728079 = 4092119) B4092119
theorem B2434495 : Blo 638302 2434495 := bstep (se 1 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 2434495 = 3651743) B3651743
theorem B2729855 : Blo 638302 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B961535 : Blo 638302 961535 := bstep (se 1 (by rfl) ⟨721151, by rfl⟩ : syracuseStep 961535 = 1442303) B1442303
theorem B4108265 : Blo 638302 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B962795 : Blo 638302 962795 := bstep (se 1 (by rfl) ⟨722096, by rfl⟩ : syracuseStep 962795 = 1444193) B1444193
theorem B142094735 : Blo 638302 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B2341223 : Blo 638302 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B638655 : Blo 638302 638655 := bstep (se 1 (by rfl) ⟨478991, by rfl⟩ : syracuseStep 638655 = 957983) B957983
theorem B2310697 : Blo 638302 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B639771 : Blo 638302 639771 := bstep (se 1 (by rfl) ⟨479828, by rfl⟩ : syracuseStep 639771 = 959657) B959657
theorem B640615 : Blo 638302 640615 := bstep (se 1 (by rfl) ⟨480461, by rfl⟩ : syracuseStep 640615 = 960923) B960923
theorem B8737307 : Blo 638302 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B2742943 : Blo 638302 2742943 := bstep (se 1 (by rfl) ⟨2057207, by rfl⟩ : syracuseStep 2742943 = 4114415) B4114415
theorem B3070703 : Blo 638302 3070703 := bstep (se 1 (by rfl) ⟨2303027, by rfl⟩ : syracuseStep 3070703 = 4606055) B4606055
theorem B1436201 : Blo 638302 1436201 := bstep (se 2 (by rfl) ⟨538575, by rfl⟩ : syracuseStep 1436201 = 1077151) B1077151
theorem B2190443 : Blo 638302 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B1437119 : Blo 638302 1437119 := bstep (se 1 (by rfl) ⟨1077839, by rfl⟩ : syracuseStep 1437119 = 2155679) B2155679
theorem B3239999 : Blo 638302 3239999 := bstep (se 1 (by rfl) ⟨2429999, by rfl⟩ : syracuseStep 3239999 = 4859999) B4859999
theorem B11661563 : Blo 638302 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B3470201 : Blo 638302 3470201 := bstep (se 2 (by rfl) ⟨1301325, by rfl⟩ : syracuseStep 3470201 = 2602651) B2602651
theorem B719599 : Blo 638302 719599 := bstep (se 1 (by rfl) ⟨539699, by rfl⟩ : syracuseStep 719599 = 1079399) B1079399
theorem B1440539 : Blo 638302 1440539 := bstep (se 1 (by rfl) ⟨1080404, by rfl⟩ : syracuseStep 1440539 = 2160809) B2160809
theorem B3080929 : Blo 638302 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B3245993 : Blo 638302 3245993 := bstep (se 2 (by rfl) ⟨1217247, by rfl⟩ : syracuseStep 3245993 = 2434495) B2434495
theorem B957467 : Blo 638302 957467 := bstep (se 1 (by rfl) ⟨718100, by rfl⟩ : syracuseStep 957467 = 1436201) B1436201
theorem B958079 : Blo 638302 958079 := bstep (se 1 (by rfl) ⟨718559, by rfl⟩ : syracuseStep 958079 = 1437119) B1437119
theorem B7774375 : Blo 638302 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B5841181 : Blo 638302 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B959465 : Blo 638302 959465 := bstep (se 2 (by rfl) ⟨359799, by rfl⟩ : syracuseStep 959465 = 719599) B719599
theorem B960359 : Blo 638302 960359 := bstep (se 1 (by rfl) ⟨720269, by rfl⟩ : syracuseStep 960359 = 1440539) B1440539
theorem B961259 : Blo 638302 961259 := bstep (se 1 (by rfl) ⟨720944, by rfl⟩ : syracuseStep 961259 = 1441889) B1441889
theorem B5486363 : Blo 638302 5486363 := bstep (se 1 (by rfl) ⟨4114772, by rfl⟩ : syracuseStep 5486363 = 8229545) B8229545
theorem B2047135 : Blo 638302 2047135 := bstep (se 1 (by rfl) ⟨1535351, by rfl⟩ : syracuseStep 2047135 = 3070703) B3070703
theorem B12828239 : Blo 638302 12828239 := bstep (se 1 (by rfl) ⟨9621179, by rfl⟩ : syracuseStep 12828239 = 19242359) B19242359
theorem B1818719 : Blo 638302 1818719 := bstep (se 1 (by rfl) ⟨1364039, by rfl⟩ : syracuseStep 1818719 = 2728079) B2728079
theorem B1819903 : Blo 638302 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B641023 : Blo 638302 641023 := bstep (se 1 (by rfl) ⟨480767, by rfl⟩ : syracuseStep 641023 = 961535) B961535
theorem B2738843 : Blo 638302 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B641863 : Blo 638302 641863 := bstep (se 1 (by rfl) ⟨481397, by rfl⟩ : syracuseStep 641863 = 962795) B962795
theorem B2313467 : Blo 638302 2313467 := bstep (se 1 (by rfl) ⟨1735100, by rfl⟩ : syracuseStep 2313467 = 3470201) B3470201
theorem B3657257 : Blo 638302 3657257 := bstep (se 2 (by rfl) ⟨1371471, by rfl⟩ : syracuseStep 3657257 = 2742943) B2742943
theorem B1560815 : Blo 638302 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B10377247 : Blo 638302 10377247 := bstep (se 1 (by rfl) ⟨7782935, by rfl⟩ : syracuseStep 10377247 = 15565871) B15565871
theorem B5824871 : Blo 638302 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B4875551 : Blo 638302 4875551 := bstep (se 1 (by rfl) ⟨3656663, by rfl⟩ : syracuseStep 4875551 = 7313327) B7313327
theorem B4942295 : Blo 638302 4942295 := bstep (se 1 (by rfl) ⟨3706721, by rfl⟩ : syracuseStep 4942295 = 7413443) B7413443
theorem B2159999 : Blo 638302 2159999 := bstep (se 1 (by rfl) ⟨1619999, by rfl⟩ : syracuseStep 2159999 = 3239999) B3239999
theorem B94729823 : Blo 638302 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B1212479 : Blo 638302 1212479 := bstep (se 1 (by rfl) ⟨909359, by rfl⟩ : syracuseStep 1212479 = 1818719) B1818719
theorem B2163995 : Blo 638302 2163995 := bstep (se 1 (by rfl) ⟨1622996, by rfl⟩ : syracuseStep 2163995 = 3245993) B3245993
theorem B2426537 : Blo 638302 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B1542311 : Blo 638302 1542311 := bstep (se 1 (by rfl) ⟨1156733, by rfl⟩ : syracuseStep 1542311 = 2313467) B2313467
theorem B3250367 : Blo 638302 3250367 := bstep (se 1 (by rfl) ⟨2437775, by rfl⟩ : syracuseStep 3250367 = 4875551) B4875551
theorem B13836329 : Blo 638302 13836329 := bstep (se 2 (by rfl) ⟨5188623, by rfl⟩ : syracuseStep 13836329 = 10377247) B10377247
theorem B63153215 : Blo 638302 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B2729513 : Blo 638302 2729513 := bstep (se 2 (by rfl) ⟨1023567, by rfl⟩ : syracuseStep 2729513 = 2047135) B2047135
theorem B10365833 : Blo 638302 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B4107905 : Blo 638302 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B2438171 : Blo 638302 2438171 := bstep (se 1 (by rfl) ⟨1828628, by rfl⟩ : syracuseStep 2438171 = 3657257) B3657257
theorem B638311 : Blo 638302 638311 := bstep (se 1 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 638311 = 957467) B957467
theorem B638719 : Blo 638302 638719 := bstep (se 1 (by rfl) ⟨479039, by rfl⟩ : syracuseStep 638719 = 958079) B958079
theorem B3883247 : Blo 638302 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B639643 : Blo 638302 639643 := bstep (se 1 (by rfl) ⟨479732, by rfl⟩ : syracuseStep 639643 = 959465) B959465
theorem B640239 : Blo 638302 640239 := bstep (se 1 (by rfl) ⟨480179, by rfl⟩ : syracuseStep 640239 = 960359) B960359
theorem B3294863 : Blo 638302 3294863 := bstep (se 1 (by rfl) ⟨2471147, by rfl⟩ : syracuseStep 3294863 = 4942295) B4942295
theorem B640839 : Blo 638302 640839 := bstep (se 1 (by rfl) ⟨480629, by rfl⟩ : syracuseStep 640839 = 961259) B961259
theorem B3657575 : Blo 638302 3657575 := bstep (se 1 (by rfl) ⟨2743181, by rfl⟩ : syracuseStep 3657575 = 5486363) B5486363
theorem B7788241 : Blo 638302 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B1825895 : Blo 638302 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B1040543 : Blo 638302 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B1439999 : Blo 638302 1439999 := bstep (se 1 (by rfl) ⟨1079999, by rfl⟩ : syracuseStep 1439999 = 2159999) B2159999
theorem B8552159 : Blo 638302 8552159 := bstep (se 1 (by rfl) ⟨6414119, by rfl⟩ : syracuseStep 8552159 = 12828239) B12828239
theorem B2588831 : Blo 638302 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B1442663 : Blo 638302 1442663 := bstep (se 1 (by rfl) ⟨1081997, by rfl⟩ : syracuseStep 1442663 = 2163995) B2163995
theorem B2196575 : Blo 638302 2196575 := bstep (se 1 (by rfl) ⟨1647431, by rfl⟩ : syracuseStep 2196575 = 3294863) B3294863
theorem B2166911 : Blo 638302 2166911 := bstep (se 1 (by rfl) ⟨1625183, by rfl⟩ : syracuseStep 2166911 = 3250367) B3250367
theorem B1217263 : Blo 638302 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B693695 : Blo 638302 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B959999 : Blo 638302 959999 := bstep (se 1 (by rfl) ⟨719999, by rfl⟩ : syracuseStep 959999 = 1439999) B1439999
theorem B1617691 : Blo 638302 1617691 := bstep (se 1 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 1617691 = 2426537) B2426537
theorem B1028207 : Blo 638302 1028207 := bstep (se 1 (by rfl) ⟨771155, by rfl⟩ : syracuseStep 1028207 = 1542311) B1542311
theorem B2438383 : Blo 638302 2438383 := bstep (se 1 (by rfl) ⟨1828787, by rfl⟩ : syracuseStep 2438383 = 3657575) B3657575
theorem B9224219 : Blo 638302 9224219 := bstep (se 1 (by rfl) ⟨6918164, by rfl⟩ : syracuseStep 9224219 = 13836329) B13836329
theorem B1819675 : Blo 638302 1819675 := bstep (se 1 (by rfl) ⟨1364756, by rfl⟩ : syracuseStep 1819675 = 2729513) B2729513
theorem B2738603 : Blo 638302 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B1625447 : Blo 638302 1625447 := bstep (se 1 (by rfl) ⟨1219085, by rfl⟩ : syracuseStep 1625447 = 2438171) B2438171
theorem B808319 : Blo 638302 808319 := bstep (se 1 (by rfl) ⟨606239, by rfl⟩ : syracuseStep 808319 = 1212479) B1212479
theorem B42102143 : Blo 638302 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B6910555 : Blo 638302 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B10384321 : Blo 638302 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B5701439 : Blo 638302 5701439 := bstep (se 1 (by rfl) ⟨4276079, by rfl⟩ : syracuseStep 5701439 = 8552159) B8552159
theorem B2426233 : Blo 638302 2426233 := bstep (se 2 (by rfl) ⟨909837, by rfl⟩ : syracuseStep 2426233 = 1819675) B1819675
theorem B1083631 : Blo 638302 1083631 := bstep (se 1 (by rfl) ⟨812723, by rfl⟩ : syracuseStep 1083631 = 1625447) B1625447
theorem B1444607 : Blo 638302 1444607 := bstep (se 1 (by rfl) ⟨1083455, by rfl⟩ : syracuseStep 1444607 = 2166911) B2166911
theorem B9214073 : Blo 638302 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B3251177 : Blo 638302 3251177 := bstep (se 2 (by rfl) ⟨1219191, by rfl⟩ : syracuseStep 3251177 = 2438383) B2438383
theorem B961775 : Blo 638302 961775 := bstep (se 1 (by rfl) ⟨721331, by rfl⟩ : syracuseStep 961775 = 1442663) B1442663
theorem B1849853 : Blo 638302 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B1623017 : Blo 638302 1623017 := bstep (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) B1217263
theorem B639999 : Blo 638302 639999 := bstep (se 1 (by rfl) ⟨479999, by rfl⟩ : syracuseStep 639999 = 959999) B959999
theorem B13845761 : Blo 638302 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B28068095 : Blo 638302 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B6149479 : Blo 638302 6149479 := bstep (se 1 (by rfl) ⟨4612109, by rfl⟩ : syracuseStep 6149479 = 9224219) B9224219
theorem B1725887 : Blo 638302 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B1464383 : Blo 638302 1464383 := bstep (se 1 (by rfl) ⟨1098287, by rfl⟩ : syracuseStep 1464383 = 2196575) B2196575
theorem B1825735 : Blo 638302 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B2155517 : Blo 638302 2155517 := bstep (se 3 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 2155517 = 808319) B808319
theorem B2156921 : Blo 638302 2156921 := bstep (se 2 (by rfl) ⟨808845, by rfl⟩ : syracuseStep 2156921 = 1617691) B1617691
theorem B685471 : Blo 638302 685471 := bstep (se 1 (by rfl) ⟨514103, by rfl⟩ : syracuseStep 685471 = 1028207) B1028207
theorem B15203837 : Blo 638302 15203837 := bstep (se 3 (by rfl) ⟨2850719, by rfl⟩ : syracuseStep 15203837 = 5701439) B5701439
theorem B1082011 : Blo 638302 1082011 := bstep (se 1 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 1082011 = 1623017) B1623017
theorem B18712063 : Blo 638302 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B1444841 : Blo 638302 1444841 := bstep (se 2 (by rfl) ⟨541815, by rfl⟩ : syracuseStep 1444841 = 1083631) B1083631
theorem B2167451 : Blo 638302 2167451 := bstep (se 1 (by rfl) ⟨1625588, by rfl⟩ : syracuseStep 2167451 = 3251177) B3251177
theorem B8199305 : Blo 638302 8199305 := bstep (se 2 (by rfl) ⟨3074739, by rfl⟩ : syracuseStep 8199305 = 6149479) B6149479
theorem B2434313 : Blo 638302 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B10135891 : Blo 638302 10135891 := bstep (se 1 (by rfl) ⟨7601918, by rfl⟩ : syracuseStep 10135891 = 15203837) B15203837
theorem B963071 : Blo 638302 963071 := bstep (se 1 (by rfl) ⟨722303, by rfl⟩ : syracuseStep 963071 = 1444607) B1444607
theorem B4602365 : Blo 638302 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B6142715 : Blo 638302 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B641183 : Blo 638302 641183 := bstep (se 1 (by rfl) ⟨480887, by rfl⟩ : syracuseStep 641183 = 961775) B961775
theorem B1233235 : Blo 638302 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B9230507 : Blo 638302 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B3234977 : Blo 638302 3234977 := bstep (se 2 (by rfl) ⟨1213116, by rfl⟩ : syracuseStep 3234977 = 2426233) B2426233
theorem B976255 : Blo 638302 976255 := bstep (se 1 (by rfl) ⟨732191, by rfl⟩ : syracuseStep 976255 = 1464383) B1464383
theorem B1437011 : Blo 638302 1437011 := bstep (se 1 (by rfl) ⟨1077758, by rfl⟩ : syracuseStep 1437011 = 2155517) B2155517
theorem B1437947 : Blo 638302 1437947 := bstep (se 1 (by rfl) ⟨1078460, by rfl⟩ : syracuseStep 1437947 = 2156921) B2156921
theorem B913961 : Blo 638302 913961 := bstep (se 2 (by rfl) ⟨342735, by rfl⟩ : syracuseStep 913961 = 685471) B685471
theorem B1442681 : Blo 638302 1442681 := bstep (se 2 (by rfl) ⟨541005, by rfl⟩ : syracuseStep 1442681 = 1082011) B1082011
theorem B1444967 : Blo 638302 1444967 := bstep (se 1 (by rfl) ⟨1083725, by rfl⟩ : syracuseStep 1444967 = 2167451) B2167451
theorem B1644313 : Blo 638302 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B958007 : Blo 638302 958007 := bstep (se 1 (by rfl) ⟨718505, by rfl⟩ : syracuseStep 958007 = 1437011) B1437011
theorem B958631 : Blo 638302 958631 := bstep (se 1 (by rfl) ⟨718973, by rfl⟩ : syracuseStep 958631 = 1437947) B1437947
theorem B2437229 : Blo 638302 2437229 := bstep (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) B913961
theorem B963227 : Blo 638302 963227 := bstep (se 1 (by rfl) ⟨722420, by rfl⟩ : syracuseStep 963227 = 1444841) B1444841
theorem B24949417 : Blo 638302 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B13514521 : Blo 638302 13514521 := bstep (se 2 (by rfl) ⟨5067945, by rfl⟩ : syracuseStep 13514521 = 10135891) B10135891
theorem B1622875 : Blo 638302 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B642047 : Blo 638302 642047 := bstep (se 1 (by rfl) ⟨481535, by rfl⟩ : syracuseStep 642047 = 963071) B963071
theorem B3068243 : Blo 638302 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B6153671 : Blo 638302 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B5466203 : Blo 638302 5466203 := bstep (se 1 (by rfl) ⟨4099652, by rfl⟩ : syracuseStep 5466203 = 8199305) B8199305
theorem B2156651 : Blo 638302 2156651 := bstep (se 1 (by rfl) ⟨1617488, by rfl⟩ : syracuseStep 2156651 = 3234977) B3234977
theorem B5206693 : Blo 638302 5206693 := bstep (se 4 (by rfl) ⟨488127, by rfl⟩ : syracuseStep 5206693 = 976255) B976255
theorem B4095143 : Blo 638302 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2163833 : Blo 638302 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B33265889 : Blo 638302 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B4102447 : Blo 638302 4102447 := bstep (se 1 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 4102447 = 6153671) B6153671
theorem B3644135 : Blo 638302 3644135 := bstep (se 1 (by rfl) ⟨2733101, by rfl⟩ : syracuseStep 3644135 = 5466203) B5466203
theorem B2730095 : Blo 638302 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B961787 : Blo 638302 961787 := bstep (se 1 (by rfl) ⟨721340, by rfl⟩ : syracuseStep 961787 = 1442681) B1442681
theorem B963311 : Blo 638302 963311 := bstep (se 1 (by rfl) ⟨722483, by rfl⟩ : syracuseStep 963311 = 1444967) B1444967
theorem B2045495 : Blo 638302 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B638671 : Blo 638302 638671 := bstep (se 1 (by rfl) ⟨479003, by rfl⟩ : syracuseStep 638671 = 958007) B958007
theorem B639087 : Blo 638302 639087 := bstep (se 1 (by rfl) ⟨479315, by rfl⟩ : syracuseStep 639087 = 958631) B958631
theorem B1624819 : Blo 638302 1624819 := bstep (se 1 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 1624819 = 2437229) B2437229
theorem B642151 : Blo 638302 642151 := bstep (se 1 (by rfl) ⟨481613, by rfl⟩ : syracuseStep 642151 = 963227) B963227
theorem B6942257 : Blo 638302 6942257 := bstep (se 2 (by rfl) ⟨2603346, by rfl⟩ : syracuseStep 6942257 = 5206693) B5206693
theorem B1437767 : Blo 638302 1437767 := bstep (se 1 (by rfl) ⟨1078325, by rfl⟩ : syracuseStep 1437767 = 2156651) B2156651
theorem B18019361 : Blo 638302 18019361 := bstep (se 2 (by rfl) ⟨6757260, by rfl⟩ : syracuseStep 18019361 = 13514521) B13514521
theorem B2192417 : Blo 638302 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B1442555 : Blo 638302 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B2166425 : Blo 638302 2166425 := bstep (se 2 (by rfl) ⟨812409, by rfl⟩ : syracuseStep 2166425 = 1624819) B1624819
theorem B2429423 : Blo 638302 2429423 := bstep (se 1 (by rfl) ⟨1822067, by rfl⟩ : syracuseStep 2429423 = 3644135) B3644135
theorem B4628171 : Blo 638302 4628171 := bstep (se 1 (by rfl) ⟨3471128, by rfl⟩ : syracuseStep 4628171 = 6942257) B6942257
theorem B958511 : Blo 638302 958511 := bstep (se 1 (by rfl) ⟨718883, by rfl⟩ : syracuseStep 958511 = 1437767) B1437767
theorem B1820063 : Blo 638302 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B641191 : Blo 638302 641191 := bstep (se 1 (by rfl) ⟨480893, by rfl⟩ : syracuseStep 641191 = 961787) B961787
theorem B642207 : Blo 638302 642207 := bstep (se 1 (by rfl) ⟨481655, by rfl⟩ : syracuseStep 642207 = 963311) B963311
theorem B12012907 : Blo 638302 12012907 := bstep (se 1 (by rfl) ⟨9009680, by rfl⟩ : syracuseStep 12012907 = 18019361) B18019361
theorem B1461611 : Blo 638302 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1363663 : Blo 638302 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B22177259 : Blo 638302 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B5469929 : Blo 638302 5469929 := bstep (se 2 (by rfl) ⟨2051223, by rfl⟩ : syracuseStep 5469929 = 4102447) B4102447
theorem B1213375 : Blo 638302 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B1444283 : Blo 638302 1444283 := bstep (se 1 (by rfl) ⟨1083212, by rfl⟩ : syracuseStep 1444283 = 2166425) B2166425
theorem B3085447 : Blo 638302 3085447 := bstep (se 1 (by rfl) ⟨2314085, by rfl⟩ : syracuseStep 3085447 = 4628171) B4628171
theorem B14784839 : Blo 638302 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B3646619 : Blo 638302 3646619 := bstep (se 1 (by rfl) ⟨2734964, by rfl⟩ : syracuseStep 3646619 = 5469929) B5469929
theorem B961703 : Blo 638302 961703 := bstep (se 1 (by rfl) ⟨721277, by rfl⟩ : syracuseStep 961703 = 1442555) B1442555
theorem B1619615 : Blo 638302 1619615 := bstep (se 1 (by rfl) ⟨1214711, by rfl⟩ : syracuseStep 1619615 = 2429423) B2429423
theorem B1818217 : Blo 638302 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B639007 : Blo 638302 639007 := bstep (se 1 (by rfl) ⟨479255, by rfl⟩ : syracuseStep 639007 = 958511) B958511
theorem B16017209 : Blo 638302 16017209 := bstep (se 2 (by rfl) ⟨6006453, by rfl⟩ : syracuseStep 16017209 = 12012907) B12012907
theorem B3897629 : Blo 638302 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B2431079 : Blo 638302 2431079 := bstep (se 1 (by rfl) ⟨1823309, by rfl⟩ : syracuseStep 2431079 = 3646619) B3646619
theorem B2598419 : Blo 638302 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B1617833 : Blo 638302 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B962855 : Blo 638302 962855 := bstep (se 1 (by rfl) ⟨722141, by rfl⟩ : syracuseStep 962855 = 1444283) B1444283
theorem B4113929 : Blo 638302 4113929 := bstep (se 2 (by rfl) ⟨1542723, by rfl⟩ : syracuseStep 4113929 = 3085447) B3085447
theorem B641135 : Blo 638302 641135 := bstep (se 1 (by rfl) ⟨480851, by rfl⟩ : syracuseStep 641135 = 961703) B961703
theorem B9856559 : Blo 638302 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B10678139 : Blo 638302 10678139 := bstep (se 1 (by rfl) ⟨8008604, by rfl⟩ : syracuseStep 10678139 = 16017209) B16017209
theorem B1079743 : Blo 638302 1079743 := bstep (se 1 (by rfl) ⟨809807, by rfl⟩ : syracuseStep 1079743 = 1619615) B1619615
theorem B2424289 : Blo 638302 2424289 := bstep (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) B1818217
theorem B7118759 : Blo 638302 7118759 := bstep (se 1 (by rfl) ⟨5339069, by rfl⟩ : syracuseStep 7118759 = 10678139) B10678139
theorem B1620719 : Blo 638302 1620719 := bstep (se 1 (by rfl) ⟨1215539, by rfl⟩ : syracuseStep 1620719 = 2431079) B2431079
theorem B6571039 : Blo 638302 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B641903 : Blo 638302 641903 := bstep (se 1 (by rfl) ⟨481427, by rfl⟩ : syracuseStep 641903 = 962855) B962855
theorem B3232385 : Blo 638302 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B2742619 : Blo 638302 2742619 := bstep (se 1 (by rfl) ⟨2056964, by rfl⟩ : syracuseStep 2742619 = 4113929) B4113929
theorem B1732279 : Blo 638302 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B1078555 : Blo 638302 1078555 := bstep (se 1 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 1078555 = 1617833) B1617833
theorem B1439657 : Blo 638302 1439657 := bstep (se 2 (by rfl) ⟨539871, by rfl⟩ : syracuseStep 1439657 = 1079743) B1079743
theorem B959771 : Blo 638302 959771 := bstep (se 1 (by rfl) ⟨719828, by rfl⟩ : syracuseStep 959771 = 1439657) B1439657
theorem B18983357 : Blo 638302 18983357 := bstep (se 3 (by rfl) ⟨3559379, by rfl⟩ : syracuseStep 18983357 = 7118759) B7118759
theorem B8761385 : Blo 638302 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B2309705 : Blo 638302 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B3656825 : Blo 638302 3656825 := bstep (se 2 (by rfl) ⟨1371309, by rfl⟩ : syracuseStep 3656825 = 2742619) B2742619
theorem B2154923 : Blo 638302 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B1438073 : Blo 638302 1438073 := bstep (se 2 (by rfl) ⟨539277, by rfl⟩ : syracuseStep 1438073 = 1078555) B1078555
theorem B1080479 : Blo 638302 1080479 := bstep (se 1 (by rfl) ⟨810359, by rfl⟩ : syracuseStep 1080479 = 1620719) B1620719
theorem B12655571 : Blo 638302 12655571 := bstep (se 1 (by rfl) ⟨9491678, by rfl⟩ : syracuseStep 12655571 = 18983357) B18983357
theorem B5840923 : Blo 638302 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B958715 : Blo 638302 958715 := bstep (se 1 (by rfl) ⟨719036, by rfl⟩ : syracuseStep 958715 = 1438073) B1438073
theorem B2437883 : Blo 638302 2437883 := bstep (se 1 (by rfl) ⟨1828412, by rfl⟩ : syracuseStep 2437883 = 3656825) B3656825
theorem B639847 : Blo 638302 639847 := bstep (se 1 (by rfl) ⟨479885, by rfl⟩ : syracuseStep 639847 = 959771) B959771
theorem B1436615 : Blo 638302 1436615 := bstep (se 1 (by rfl) ⟨1077461, by rfl⟩ : syracuseStep 1436615 = 2154923) B2154923
theorem B720319 : Blo 638302 720319 := bstep (se 1 (by rfl) ⟨540239, by rfl⟩ : syracuseStep 720319 = 1080479) B1080479
theorem B1539803 : Blo 638302 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B957743 : Blo 638302 957743 := bstep (se 1 (by rfl) ⟨718307, by rfl⟩ : syracuseStep 957743 = 1436615) B1436615
theorem B960425 : Blo 638302 960425 := bstep (se 2 (by rfl) ⟨360159, by rfl⟩ : syracuseStep 960425 = 720319) B720319
theorem B1026535 : Blo 638302 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B639143 : Blo 638302 639143 := bstep (se 1 (by rfl) ⟨479357, by rfl⟩ : syracuseStep 639143 = 958715) B958715
theorem B1625255 : Blo 638302 1625255 := bstep (se 1 (by rfl) ⟨1218941, by rfl⟩ : syracuseStep 1625255 = 2437883) B2437883
theorem B134992757 : Blo 638302 134992757 := bstep (se 5 (by rfl) ⟨6327785, by rfl⟩ : syracuseStep 134992757 = 12655571) B12655571
theorem B7787897 : Blo 638302 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B1083503 : Blo 638302 1083503 := bstep (se 1 (by rfl) ⟨812627, by rfl⟩ : syracuseStep 1083503 = 1625255) B1625255
theorem B89995171 : Blo 638302 89995171 := bstep (se 1 (by rfl) ⟨67496378, by rfl⟩ : syracuseStep 89995171 = 134992757) B134992757
theorem B5191931 : Blo 638302 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B638495 : Blo 638302 638495 := bstep (se 1 (by rfl) ⟨478871, by rfl⟩ : syracuseStep 638495 = 957743) B957743
theorem B640283 : Blo 638302 640283 := bstep (se 1 (by rfl) ⟨480212, by rfl⟩ : syracuseStep 640283 = 960425) B960425
theorem B1368713 : Blo 638302 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B722335 : Blo 638302 722335 := bstep (se 1 (by rfl) ⟨541751, by rfl⟩ : syracuseStep 722335 = 1083503) B1083503
theorem B3461287 : Blo 638302 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B912475 : Blo 638302 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B119993561 : Blo 638302 119993561 := bstep (se 2 (by rfl) ⟨44997585, by rfl⟩ : syracuseStep 119993561 = 89995171) B89995171
theorem B1216633 : Blo 638302 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B79995707 : Blo 638302 79995707 := bstep (se 1 (by rfl) ⟨59996780, by rfl⟩ : syracuseStep 79995707 = 119993561) B119993561
theorem B963113 : Blo 638302 963113 := bstep (se 2 (by rfl) ⟨361167, by rfl⟩ : syracuseStep 963113 = 722335) B722335
theorem B4615049 : Blo 638302 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B1622177 : Blo 638302 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B53330471 : Blo 638302 53330471 := bstep (se 1 (by rfl) ⟨39997853, by rfl⟩ : syracuseStep 53330471 = 79995707) B79995707
theorem B642075 : Blo 638302 642075 := bstep (se 1 (by rfl) ⟨481556, by rfl⟩ : syracuseStep 642075 = 963113) B963113
theorem B3076699 : Blo 638302 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B1081451 : Blo 638302 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B35553647 : Blo 638302 35553647 := bstep (se 1 (by rfl) ⟨26665235, by rfl⟩ : syracuseStep 35553647 = 53330471) B53330471
theorem B4102265 : Blo 638302 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B720967 : Blo 638302 720967 := bstep (se 1 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 720967 = 1081451) B1081451
theorem B23702431 : Blo 638302 23702431 := bstep (se 1 (by rfl) ⟨17776823, by rfl⟩ : syracuseStep 23702431 = 35553647) B35553647
theorem B10939373 : Blo 638302 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B961289 : Blo 638302 961289 := bstep (se 2 (by rfl) ⟨360483, by rfl⟩ : syracuseStep 961289 = 720967) B720967
theorem B31603241 : Blo 638302 31603241 := bstep (se 2 (by rfl) ⟨11851215, by rfl⟩ : syracuseStep 31603241 = 23702431) B23702431
theorem B7292915 : Blo 638302 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B4861943 : Blo 638302 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B640859 : Blo 638302 640859 := bstep (se 1 (by rfl) ⟨480644, by rfl⟩ : syracuseStep 640859 = 961289) B961289
theorem B84275309 : Blo 638302 84275309 := bstep (se 3 (by rfl) ⟨15801620, by rfl⟩ : syracuseStep 84275309 = 31603241) B31603241
theorem B56183539 : Blo 638302 56183539 := bstep (se 1 (by rfl) ⟨42137654, by rfl⟩ : syracuseStep 56183539 = 84275309) B84275309
theorem B3241295 : Blo 638302 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B74911385 : Blo 638302 74911385 := bstep (se 2 (by rfl) ⟨28091769, by rfl⟩ : syracuseStep 74911385 = 56183539) B56183539
theorem B2160863 : Blo 638302 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B49940923 : Blo 638302 49940923 := bstep (se 1 (by rfl) ⟨37455692, by rfl⟩ : syracuseStep 49940923 = 74911385) B74911385
theorem B1440575 : Blo 638302 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B66587897 : Blo 638302 66587897 := bstep (se 2 (by rfl) ⟨24970461, by rfl⟩ : syracuseStep 66587897 = 49940923) B49940923
theorem B960383 : Blo 638302 960383 := bstep (se 1 (by rfl) ⟨720287, by rfl⟩ : syracuseStep 960383 = 1440575) B1440575
theorem B640255 : Blo 638302 640255 := bstep (se 1 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 640255 = 960383) B960383
theorem B44391931 : Blo 638302 44391931 := bstep (se 1 (by rfl) ⟨33293948, by rfl⟩ : syracuseStep 44391931 = 66587897) B66587897
theorem B236756965 : Blo 638302 236756965 := bstep (se 4 (by rfl) ⟨22195965, by rfl⟩ : syracuseStep 236756965 = 44391931) B44391931
theorem B315675953 : Blo 638302 315675953 := bstep (se 2 (by rfl) ⟨118378482, by rfl⟩ : syracuseStep 315675953 = 236756965) B236756965
theorem B210450635 : Blo 638302 210450635 := bstep (se 1 (by rfl) ⟨157837976, by rfl⟩ : syracuseStep 210450635 = 315675953) B315675953
theorem B140300423 : Blo 638302 140300423 := bstep (se 1 (by rfl) ⟨105225317, by rfl⟩ : syracuseStep 140300423 = 210450635) B210450635
theorem B93533615 : Blo 638302 93533615 := bstep (se 1 (by rfl) ⟨70150211, by rfl⟩ : syracuseStep 93533615 = 140300423) B140300423
theorem B62355743 : Blo 638302 62355743 := bstep (se 1 (by rfl) ⟨46766807, by rfl⟩ : syracuseStep 62355743 = 93533615) B93533615
theorem B41570495 : Blo 638302 41570495 := bstep (se 1 (by rfl) ⟨31177871, by rfl⟩ : syracuseStep 41570495 = 62355743) B62355743
theorem B27713663 : Blo 638302 27713663 := bstep (se 1 (by rfl) ⟨20785247, by rfl⟩ : syracuseStep 27713663 = 41570495) B41570495
theorem B18475775 : Blo 638302 18475775 := bstep (se 1 (by rfl) ⟨13856831, by rfl⟩ : syracuseStep 18475775 = 27713663) B27713663
theorem B12317183 : Blo 638302 12317183 := bstep (se 1 (by rfl) ⟨9237887, by rfl⟩ : syracuseStep 12317183 = 18475775) B18475775
theorem B8211455 : Blo 638302 8211455 := bstep (se 1 (by rfl) ⟨6158591, by rfl⟩ : syracuseStep 8211455 = 12317183) B12317183
theorem B5474303 : Blo 638302 5474303 := bstep (se 1 (by rfl) ⟨4105727, by rfl⟩ : syracuseStep 5474303 = 8211455) B8211455
theorem B3649535 : Blo 638302 3649535 := bstep (se 1 (by rfl) ⟨2737151, by rfl⟩ : syracuseStep 3649535 = 5474303) B5474303
theorem B2433023 : Blo 638302 2433023 := bstep (se 1 (by rfl) ⟨1824767, by rfl⟩ : syracuseStep 2433023 = 3649535) B3649535
theorem B1622015 : Blo 638302 1622015 := bstep (se 1 (by rfl) ⟨1216511, by rfl⟩ : syracuseStep 1622015 = 2433023) B2433023
theorem B1081343 : Blo 638302 1081343 := bstep (se 1 (by rfl) ⟨811007, by rfl⟩ : syracuseStep 1081343 = 1622015) B1622015
theorem B720895 : Blo 638302 720895 := bstep (se 1 (by rfl) ⟨540671, by rfl⟩ : syracuseStep 720895 = 1081343) B1081343
theorem B961193 : Blo 638302 961193 := bstep (se 2 (by rfl) ⟨360447, by rfl⟩ : syracuseStep 961193 = 720895) B720895
theorem B640795 : Blo 638302 640795 := bstep (se 1 (by rfl) ⟨480596, by rfl⟩ : syracuseStep 640795 = 961193) B961193

theorem C0 (j : ℕ) (h1 : 159575 ≤ j) (h2 : j ≤ 160274) : Blo 638302 (4 * j + 3) := by
  interval_cases j
  · exact B638303
  · exact B638307
  · exact B638311
  · exact B638315
  · exact B638319
  · exact B638323
  · exact B638327
  · exact B638331
  · exact B638335
  · exact B638339
  · exact B638343
  · exact B638347
  · exact B638351
  · exact B638355
  · exact B638359
  · exact B638363
  · exact B638367
  · exact B638371
  · exact B638375
  · exact B638379
  · exact B638383
  · exact B638387
  · exact B638391
  · exact B638395
  · exact B638399
  · exact B638403
  · exact B638407
  · exact B638411
  · exact B638415
  · exact B638419
  · exact B638423
  · exact B638427
  · exact B638431
  · exact B638435
  · exact B638439
  · exact B638443
  · exact B638447
  · exact B638451
  · exact B638455
  · exact B638459
  · exact B638463
  · exact B638467
  · exact B638471
  · exact B638475
  · exact B638479
  · exact B638483
  · exact B638487
  · exact B638491
  · exact B638495
  · exact B638499
  · exact B638503
  · exact B638507
  · exact B638511
  · exact B638515
  · exact B638519
  · exact B638523
  · exact B638527
  · exact B638531
  · exact B638535
  · exact B638539
  · exact B638543
  · exact B638547
  · exact B638551
  · exact B638555
  · exact B638559
  · exact B638563
  · exact B638567
  · exact B638571
  · exact B638575
  · exact B638579
  · exact B638583
  · exact B638587
  · exact B638591
  · exact B638595
  · exact B638599
  · exact B638603
  · exact B638607
  · exact B638611
  · exact B638615
  · exact B638619
  · exact B638623
  · exact B638627
  · exact B638631
  · exact B638635
  · exact B638639
  · exact B638643
  · exact B638647
  · exact B638651
  · exact B638655
  · exact B638659
  · exact B638663
  · exact B638667
  · exact B638671
  · exact B638675
  · exact B638679
  · exact B638683
  · exact B638687
  · exact B638691
  · exact B638695
  · exact B638699
  · exact B638703
  · exact B638707
  · exact B638711
  · exact B638715
  · exact B638719
  · exact B638723
  · exact B638727
  · exact B638731
  · exact B638735
  · exact B638739
  · exact B638743
  · exact B638747
  · exact B638751
  · exact B638755
  · exact B638759
  · exact B638763
  · exact B638767
  · exact B638771
  · exact B638775
  · exact B638779
  · exact B638783
  · exact B638787
  · exact B638791
  · exact B638795
  · exact B638799
  · exact B638803
  · exact B638807
  · exact B638811
  · exact B638815
  · exact B638819
  · exact B638823
  · exact B638827
  · exact B638831
  · exact B638835
  · exact B638839
  · exact B638843
  · exact B638847
  · exact B638851
  · exact B638855
  · exact B638859
  · exact B638863
  · exact B638867
  · exact B638871
  · exact B638875
  · exact B638879
  · exact B638883
  · exact B638887
  · exact B638891
  · exact B638895
  · exact B638899
  · exact B638903
  · exact B638907
  · exact B638911
  · exact B638915
  · exact B638919
  · exact B638923
  · exact B638927
  · exact B638931
  · exact B638935
  · exact B638939
  · exact B638943
  · exact B638947
  · exact B638951
  · exact B638955
  · exact B638959
  · exact B638963
  · exact B638967
  · exact B638971
  · exact B638975
  · exact B638979
  · exact B638983
  · exact B638987
  · exact B638991
  · exact B638995
  · exact B638999
  · exact B639003
  · exact B639007
  · exact B639011
  · exact B639015
  · exact B639019
  · exact B639023
  · exact B639027
  · exact B639031
  · exact B639035
  · exact B639039
  · exact B639043
  · exact B639047
  · exact B639051
  · exact B639055
  · exact B639059
  · exact B639063
  · exact B639067
  · exact B639071
  · exact B639075
  · exact B639079
  · exact B639083
  · exact B639087
  · exact B639091
  · exact B639095
  · exact B639099
  · exact B639103
  · exact B639107
  · exact B639111
  · exact B639115
  · exact B639119
  · exact B639123
  · exact B639127
  · exact B639131
  · exact B639135
  · exact B639139
  · exact B639143
  · exact B639147
  · exact B639151
  · exact B639155
  · exact B639159
  · exact B639163
  · exact B639167
  · exact B639171
  · exact B639175
  · exact B639179
  · exact B639183
  · exact B639187
  · exact B639191
  · exact B639195
  · exact B639199
  · exact B639203
  · exact B639207
  · exact B639211
  · exact B639215
  · exact B639219
  · exact B639223
  · exact B639227
  · exact B639231
  · exact B639235
  · exact B639239
  · exact B639243
  · exact B639247
  · exact B639251
  · exact B639255
  · exact B639259
  · exact B639263
  · exact B639267
  · exact B639271
  · exact B639275
  · exact B639279
  · exact B639283
  · exact B639287
  · exact B639291
  · exact B639295
  · exact B639299
  · exact B639303
  · exact B639307
  · exact B639311
  · exact B639315
  · exact B639319
  · exact B639323
  · exact B639327
  · exact B639331
  · exact B639335
  · exact B639339
  · exact B639343
  · exact B639347
  · exact B639351
  · exact B639355
  · exact B639359
  · exact B639363
  · exact B639367
  · exact B639371
  · exact B639375
  · exact B639379
  · exact B639383
  · exact B639387
  · exact B639391
  · exact B639395
  · exact B639399
  · exact B639403
  · exact B639407
  · exact B639411
  · exact B639415
  · exact B639419
  · exact B639423
  · exact B639427
  · exact B639431
  · exact B639435
  · exact B639439
  · exact B639443
  · exact B639447
  · exact B639451
  · exact B639455
  · exact B639459
  · exact B639463
  · exact B639467
  · exact B639471
  · exact B639475
  · exact B639479
  · exact B639483
  · exact B639487
  · exact B639491
  · exact B639495
  · exact B639499
  · exact B639503
  · exact B639507
  · exact B639511
  · exact B639515
  · exact B639519
  · exact B639523
  · exact B639527
  · exact B639531
  · exact B639535
  · exact B639539
  · exact B639543
  · exact B639547
  · exact B639551
  · exact B639555
  · exact B639559
  · exact B639563
  · exact B639567
  · exact B639571
  · exact B639575
  · exact B639579
  · exact B639583
  · exact B639587
  · exact B639591
  · exact B639595
  · exact B639599
  · exact B639603
  · exact B639607
  · exact B639611
  · exact B639615
  · exact B639619
  · exact B639623
  · exact B639627
  · exact B639631
  · exact B639635
  · exact B639639
  · exact B639643
  · exact B639647
  · exact B639651
  · exact B639655
  · exact B639659
  · exact B639663
  · exact B639667
  · exact B639671
  · exact B639675
  · exact B639679
  · exact B639683
  · exact B639687
  · exact B639691
  · exact B639695
  · exact B639699
  · exact B639703
  · exact B639707
  · exact B639711
  · exact B639715
  · exact B639719
  · exact B639723
  · exact B639727
  · exact B639731
  · exact B639735
  · exact B639739
  · exact B639743
  · exact B639747
  · exact B639751
  · exact B639755
  · exact B639759
  · exact B639763
  · exact B639767
  · exact B639771
  · exact B639775
  · exact B639779
  · exact B639783
  · exact B639787
  · exact B639791
  · exact B639795
  · exact B639799
  · exact B639803
  · exact B639807
  · exact B639811
  · exact B639815
  · exact B639819
  · exact B639823
  · exact B639827
  · exact B639831
  · exact B639835
  · exact B639839
  · exact B639843
  · exact B639847
  · exact B639851
  · exact B639855
  · exact B639859
  · exact B639863
  · exact B639867
  · exact B639871
  · exact B639875
  · exact B639879
  · exact B639883
  · exact B639887
  · exact B639891
  · exact B639895
  · exact B639899
  · exact B639903
  · exact B639907
  · exact B639911
  · exact B639915
  · exact B639919
  · exact B639923
  · exact B639927
  · exact B639931
  · exact B639935
  · exact B639939
  · exact B639943
  · exact B639947
  · exact B639951
  · exact B639955
  · exact B639959
  · exact B639963
  · exact B639967
  · exact B639971
  · exact B639975
  · exact B639979
  · exact B639983
  · exact B639987
  · exact B639991
  · exact B639995
  · exact B639999
  · exact B640003
  · exact B640007
  · exact B640011
  · exact B640015
  · exact B640019
  · exact B640023
  · exact B640027
  · exact B640031
  · exact B640035
  · exact B640039
  · exact B640043
  · exact B640047
  · exact B640051
  · exact B640055
  · exact B640059
  · exact B640063
  · exact B640067
  · exact B640071
  · exact B640075
  · exact B640079
  · exact B640083
  · exact B640087
  · exact B640091
  · exact B640095
  · exact B640099
  · exact B640103
  · exact B640107
  · exact B640111
  · exact B640115
  · exact B640119
  · exact B640123
  · exact B640127
  · exact B640131
  · exact B640135
  · exact B640139
  · exact B640143
  · exact B640147
  · exact B640151
  · exact B640155
  · exact B640159
  · exact B640163
  · exact B640167
  · exact B640171
  · exact B640175
  · exact B640179
  · exact B640183
  · exact B640187
  · exact B640191
  · exact B640195
  · exact B640199
  · exact B640203
  · exact B640207
  · exact B640211
  · exact B640215
  · exact B640219
  · exact B640223
  · exact B640227
  · exact B640231
  · exact B640235
  · exact B640239
  · exact B640243
  · exact B640247
  · exact B640251
  · exact B640255
  · exact B640259
  · exact B640263
  · exact B640267
  · exact B640271
  · exact B640275
  · exact B640279
  · exact B640283
  · exact B640287
  · exact B640291
  · exact B640295
  · exact B640299
  · exact B640303
  · exact B640307
  · exact B640311
  · exact B640315
  · exact B640319
  · exact B640323
  · exact B640327
  · exact B640331
  · exact B640335
  · exact B640339
  · exact B640343
  · exact B640347
  · exact B640351
  · exact B640355
  · exact B640359
  · exact B640363
  · exact B640367
  · exact B640371
  · exact B640375
  · exact B640379
  · exact B640383
  · exact B640387
  · exact B640391
  · exact B640395
  · exact B640399
  · exact B640403
  · exact B640407
  · exact B640411
  · exact B640415
  · exact B640419
  · exact B640423
  · exact B640427
  · exact B640431
  · exact B640435
  · exact B640439
  · exact B640443
  · exact B640447
  · exact B640451
  · exact B640455
  · exact B640459
  · exact B640463
  · exact B640467
  · exact B640471
  · exact B640475
  · exact B640479
  · exact B640483
  · exact B640487
  · exact B640491
  · exact B640495
  · exact B640499
  · exact B640503
  · exact B640507
  · exact B640511
  · exact B640515
  · exact B640519
  · exact B640523
  · exact B640527
  · exact B640531
  · exact B640535
  · exact B640539
  · exact B640543
  · exact B640547
  · exact B640551
  · exact B640555
  · exact B640559
  · exact B640563
  · exact B640567
  · exact B640571
  · exact B640575
  · exact B640579
  · exact B640583
  · exact B640587
  · exact B640591
  · exact B640595
  · exact B640599
  · exact B640603
  · exact B640607
  · exact B640611
  · exact B640615
  · exact B640619
  · exact B640623
  · exact B640627
  · exact B640631
  · exact B640635
  · exact B640639
  · exact B640643
  · exact B640647
  · exact B640651
  · exact B640655
  · exact B640659
  · exact B640663
  · exact B640667
  · exact B640671
  · exact B640675
  · exact B640679
  · exact B640683
  · exact B640687
  · exact B640691
  · exact B640695
  · exact B640699
  · exact B640703
  · exact B640707
  · exact B640711
  · exact B640715
  · exact B640719
  · exact B640723
  · exact B640727
  · exact B640731
  · exact B640735
  · exact B640739
  · exact B640743
  · exact B640747
  · exact B640751
  · exact B640755
  · exact B640759
  · exact B640763
  · exact B640767
  · exact B640771
  · exact B640775
  · exact B640779
  · exact B640783
  · exact B640787
  · exact B640791
  · exact B640795
  · exact B640799
  · exact B640803
  · exact B640807
  · exact B640811
  · exact B640815
  · exact B640819
  · exact B640823
  · exact B640827
  · exact B640831
  · exact B640835
  · exact B640839
  · exact B640843
  · exact B640847
  · exact B640851
  · exact B640855
  · exact B640859
  · exact B640863
  · exact B640867
  · exact B640871
  · exact B640875
  · exact B640879
  · exact B640883
  · exact B640887
  · exact B640891
  · exact B640895
  · exact B640899
  · exact B640903
  · exact B640907
  · exact B640911
  · exact B640915
  · exact B640919
  · exact B640923
  · exact B640927
  · exact B640931
  · exact B640935
  · exact B640939
  · exact B640943
  · exact B640947
  · exact B640951
  · exact B640955
  · exact B640959
  · exact B640963
  · exact B640967
  · exact B640971
  · exact B640975
  · exact B640979
  · exact B640983
  · exact B640987
  · exact B640991
  · exact B640995
  · exact B640999
  · exact B641003
  · exact B641007
  · exact B641011
  · exact B641015
  · exact B641019
  · exact B641023
  · exact B641027
  · exact B641031
  · exact B641035
  · exact B641039
  · exact B641043
  · exact B641047
  · exact B641051
  · exact B641055
  · exact B641059
  · exact B641063
  · exact B641067
  · exact B641071
  · exact B641075
  · exact B641079
  · exact B641083
  · exact B641087
  · exact B641091
  · exact B641095
  · exact B641099

theorem C1 (j : ℕ) (h1 : 160275 ≤ j) (h2 : j ≤ 160574) : Blo 638302 (4 * j + 3) := by
  interval_cases j
  · exact B641103
  · exact B641107
  · exact B641111
  · exact B641115
  · exact B641119
  · exact B641123
  · exact B641127
  · exact B641131
  · exact B641135
  · exact B641139
  · exact B641143
  · exact B641147
  · exact B641151
  · exact B641155
  · exact B641159
  · exact B641163
  · exact B641167
  · exact B641171
  · exact B641175
  · exact B641179
  · exact B641183
  · exact B641187
  · exact B641191
  · exact B641195
  · exact B641199
  · exact B641203
  · exact B641207
  · exact B641211
  · exact B641215
  · exact B641219
  · exact B641223
  · exact B641227
  · exact B641231
  · exact B641235
  · exact B641239
  · exact B641243
  · exact B641247
  · exact B641251
  · exact B641255
  · exact B641259
  · exact B641263
  · exact B641267
  · exact B641271
  · exact B641275
  · exact B641279
  · exact B641283
  · exact B641287
  · exact B641291
  · exact B641295
  · exact B641299
  · exact B641303
  · exact B641307
  · exact B641311
  · exact B641315
  · exact B641319
  · exact B641323
  · exact B641327
  · exact B641331
  · exact B641335
  · exact B641339
  · exact B641343
  · exact B641347
  · exact B641351
  · exact B641355
  · exact B641359
  · exact B641363
  · exact B641367
  · exact B641371
  · exact B641375
  · exact B641379
  · exact B641383
  · exact B641387
  · exact B641391
  · exact B641395
  · exact B641399
  · exact B641403
  · exact B641407
  · exact B641411
  · exact B641415
  · exact B641419
  · exact B641423
  · exact B641427
  · exact B641431
  · exact B641435
  · exact B641439
  · exact B641443
  · exact B641447
  · exact B641451
  · exact B641455
  · exact B641459
  · exact B641463
  · exact B641467
  · exact B641471
  · exact B641475
  · exact B641479
  · exact B641483
  · exact B641487
  · exact B641491
  · exact B641495
  · exact B641499
  · exact B641503
  · exact B641507
  · exact B641511
  · exact B641515
  · exact B641519
  · exact B641523
  · exact B641527
  · exact B641531
  · exact B641535
  · exact B641539
  · exact B641543
  · exact B641547
  · exact B641551
  · exact B641555
  · exact B641559
  · exact B641563
  · exact B641567
  · exact B641571
  · exact B641575
  · exact B641579
  · exact B641583
  · exact B641587
  · exact B641591
  · exact B641595
  · exact B641599
  · exact B641603
  · exact B641607
  · exact B641611
  · exact B641615
  · exact B641619
  · exact B641623
  · exact B641627
  · exact B641631
  · exact B641635
  · exact B641639
  · exact B641643
  · exact B641647
  · exact B641651
  · exact B641655
  · exact B641659
  · exact B641663
  · exact B641667
  · exact B641671
  · exact B641675
  · exact B641679
  · exact B641683
  · exact B641687
  · exact B641691
  · exact B641695
  · exact B641699
  · exact B641703
  · exact B641707
  · exact B641711
  · exact B641715
  · exact B641719
  · exact B641723
  · exact B641727
  · exact B641731
  · exact B641735
  · exact B641739
  · exact B641743
  · exact B641747
  · exact B641751
  · exact B641755
  · exact B641759
  · exact B641763
  · exact B641767
  · exact B641771
  · exact B641775
  · exact B641779
  · exact B641783
  · exact B641787
  · exact B641791
  · exact B641795
  · exact B641799
  · exact B641803
  · exact B641807
  · exact B641811
  · exact B641815
  · exact B641819
  · exact B641823
  · exact B641827
  · exact B641831
  · exact B641835
  · exact B641839
  · exact B641843
  · exact B641847
  · exact B641851
  · exact B641855
  · exact B641859
  · exact B641863
  · exact B641867
  · exact B641871
  · exact B641875
  · exact B641879
  · exact B641883
  · exact B641887
  · exact B641891
  · exact B641895
  · exact B641899
  · exact B641903
  · exact B641907
  · exact B641911
  · exact B641915
  · exact B641919
  · exact B641923
  · exact B641927
  · exact B641931
  · exact B641935
  · exact B641939
  · exact B641943
  · exact B641947
  · exact B641951
  · exact B641955
  · exact B641959
  · exact B641963
  · exact B641967
  · exact B641971
  · exact B641975
  · exact B641979
  · exact B641983
  · exact B641987
  · exact B641991
  · exact B641995
  · exact B641999
  · exact B642003
  · exact B642007
  · exact B642011
  · exact B642015
  · exact B642019
  · exact B642023
  · exact B642027
  · exact B642031
  · exact B642035
  · exact B642039
  · exact B642043
  · exact B642047
  · exact B642051
  · exact B642055
  · exact B642059
  · exact B642063
  · exact B642067
  · exact B642071
  · exact B642075
  · exact B642079
  · exact B642083
  · exact B642087
  · exact B642091
  · exact B642095
  · exact B642099
  · exact B642103
  · exact B642107
  · exact B642111
  · exact B642115
  · exact B642119
  · exact B642123
  · exact B642127
  · exact B642131
  · exact B642135
  · exact B642139
  · exact B642143
  · exact B642147
  · exact B642151
  · exact B642155
  · exact B642159
  · exact B642163
  · exact B642167
  · exact B642171
  · exact B642175
  · exact B642179
  · exact B642183
  · exact B642187
  · exact B642191
  · exact B642195
  · exact B642199
  · exact B642203
  · exact B642207
  · exact B642211
  · exact B642215
  · exact B642219
  · exact B642223
  · exact B642227
  · exact B642231
  · exact B642235
  · exact B642239
  · exact B642243
  · exact B642247
  · exact B642251
  · exact B642255
  · exact B642259
  · exact B642263
  · exact B642267
  · exact B642271
  · exact B642275
  · exact B642279
  · exact B642283
  · exact B642287
  · exact B642291
  · exact B642295
  · exact B642299

theorem solution (m : ℕ) (hlo : 638302 ≤ m) (hhi : m ≤ 642302) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 159575 ≤ j := by omega
    have hj2 : j ≤ 160574 := by omega
    have hb : Blo 638302 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 160275 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
