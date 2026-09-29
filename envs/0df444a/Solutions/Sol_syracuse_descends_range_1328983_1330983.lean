-- Prove2me | solution 1 for syracuse_descends_range_1328983_1330983
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:39.521663+00:00
-- url     : https://prove2.me/submissions/f0f4d6f4-8198-404c-9726-2fd3c362cecc

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


theorem B3366917 : Blo 1328983 3366917 := bbase (se 4 (by rfl) ⟨315648, by rfl⟩ : syracuseStep 3366917 = 631297) (by norm_num)
theorem B2768933 : Blo 1328983 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B2244685 : Blo 1328983 2244685 := bbase (se 3 (by rfl) ⟨420878, by rfl⟩ : syracuseStep 2244685 = 841757) (by norm_num)
theorem B2523221 : Blo 1328983 2523221 := bbase (se 8 (by rfl) ⟨14784, by rfl⟩ : syracuseStep 2523221 = 29569) (by norm_num)
theorem B2130013 : Blo 1328983 2130013 := bbase (se 3 (by rfl) ⟨399377, by rfl⟩ : syracuseStep 2130013 = 798755) (by norm_num)
theorem B2990213 : Blo 1328983 2990213 := bbase (se 4 (by rfl) ⟨280332, by rfl⟩ : syracuseStep 2990213 = 560665) (by norm_num)
theorem B1597601 : Blo 1328983 1597601 := bbase (se 2 (by rfl) ⟨599100, by rfl⟩ : syracuseStep 1597601 = 1198201) (by norm_num)
theorem B2244773 : Blo 1328983 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B4489397 : Blo 1328983 4489397 := bbase (se 5 (by rfl) ⟨210440, by rfl⟩ : syracuseStep 4489397 = 420881) (by norm_num)
theorem B7594165 : Blo 1328983 7594165 := bbase (se 5 (by rfl) ⟨355976, by rfl⟩ : syracuseStep 7594165 = 711953) (by norm_num)
theorem B3367109 : Blo 1328983 3367109 := bbase (se 4 (by rfl) ⟨315666, by rfl⟩ : syracuseStep 3367109 = 631333) (by norm_num)
theorem B2990285 : Blo 1328983 2990285 := bbase (se 3 (by rfl) ⟨560678, by rfl⟩ : syracuseStep 2990285 = 1121357) (by norm_num)
theorem B1597649 : Blo 1328983 1597649 := bbase (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) (by norm_num)
theorem B11354357 : Blo 1328983 11354357 := bbase (se 5 (by rfl) ⟨532235, by rfl⟩ : syracuseStep 11354357 = 1064471) (by norm_num)
theorem B5046533 : Blo 1328983 5046533 := bbase (se 4 (by rfl) ⟨473112, by rfl⟩ : syracuseStep 5046533 = 946225) (by norm_num)
theorem B1515781 : Blo 1328983 1515781 := bbase (se 4 (by rfl) ⟨142104, by rfl⟩ : syracuseStep 1515781 = 284209) (by norm_num)
theorem B2990357 : Blo 1328983 2990357 := bbase (se 6 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 2990357 = 140173) (by norm_num)
theorem B3195173 : Blo 1328983 3195173 := bbase (se 4 (by rfl) ⟨299547, by rfl⟩ : syracuseStep 3195173 = 599095) (by norm_num)
theorem B2244901 : Blo 1328983 2244901 := bbase (se 4 (by rfl) ⟨210459, by rfl⟩ : syracuseStep 2244901 = 420919) (by norm_num)
theorem B6070565 : Blo 1328983 6070565 := bbase (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) (by norm_num)
theorem B1597745 : Blo 1328983 1597745 := bbase (se 2 (by rfl) ⟨599154, by rfl⟩ : syracuseStep 1597745 = 1198309) (by norm_num)
theorem B245637461 : Blo 1328983 245637461 := bbase (se 10 (by rfl) ⟨359820, by rfl⟩ : syracuseStep 245637461 = 719641) (by norm_num)
theorem B2990429 : Blo 1328983 2990429 := bbase (se 3 (by rfl) ⟨560705, by rfl⟩ : syracuseStep 2990429 = 1121411) (by norm_num)
theorem B2048357 : Blo 1328983 2048357 := bbase (se 4 (by rfl) ⟨192033, by rfl⟩ : syracuseStep 2048357 = 384067) (by norm_num)
theorem B2244989 : Blo 1328983 2244989 := bbase (se 3 (by rfl) ⟨420935, by rfl⟩ : syracuseStep 2244989 = 841871) (by norm_num)
theorem B2990501 : Blo 1328983 2990501 := bbase (se 4 (by rfl) ⟨280359, by rfl⟩ : syracuseStep 2990501 = 560719) (by norm_num)
theorem B7569845 : Blo 1328983 7569845 := bbase (se 5 (by rfl) ⟨354836, by rfl⟩ : syracuseStep 7569845 = 709673) (by norm_num)
theorem B1597909 : Blo 1328983 1597909 := bbase (se 7 (by rfl) ⟨18725, by rfl⟩ : syracuseStep 1597909 = 37451) (by norm_num)
theorem B2990573 : Blo 1328983 2990573 := bbase (se 3 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 2990573 = 1121465) (by norm_num)
theorem B2245117 : Blo 1328983 2245117 := bbase (se 3 (by rfl) ⟨420959, by rfl⟩ : syracuseStep 2245117 = 841919) (by norm_num)
theorem B5677573 : Blo 1328983 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B5677589 : Blo 1328983 5677589 := bbase (se 6 (by rfl) ⟨133068, by rfl⟩ : syracuseStep 5677589 = 266137) (by norm_num)
theorem B3367453 : Blo 1328983 3367453 := bbase (se 3 (by rfl) ⟨631397, by rfl⟩ : syracuseStep 3367453 = 1262795) (by norm_num)
theorem B2990645 : Blo 1328983 2990645 := bbase (se 5 (by rfl) ⟨140186, by rfl⟩ : syracuseStep 2990645 = 280373) (by norm_num)
theorem B1892917 : Blo 1328983 1892917 := bbase (se 5 (by rfl) ⟨88730, by rfl⟩ : syracuseStep 1892917 = 177461) (by norm_num)
theorem B2245205 : Blo 1328983 2245205 := bbase (se 8 (by rfl) ⟨13155, by rfl⟩ : syracuseStep 2245205 = 26311) (by norm_num)
theorem B4489829 : Blo 1328983 4489829 := bbase (se 4 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 4489829 = 841843) (by norm_num)
theorem B2990717 : Blo 1328983 2990717 := bbase (se 3 (by rfl) ⟨560759, by rfl⟩ : syracuseStep 2990717 = 1121519) (by norm_num)
theorem B3367565 : Blo 1328983 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B6734501 : Blo 1328983 6734501 := bbase (se 4 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 6734501 = 1262719) (by norm_num)
theorem B1598125 : Blo 1328983 1598125 := bbase (se 3 (by rfl) ⟨299648, by rfl⟩ : syracuseStep 1598125 = 599297) (by norm_num)
theorem B2990789 : Blo 1328983 2990789 := bbase (se 4 (by rfl) ⟨280386, by rfl⟩ : syracuseStep 2990789 = 560773) (by norm_num)
theorem B3785413 : Blo 1328983 3785413 := bbase (se 4 (by rfl) ⟨354882, by rfl⟩ : syracuseStep 3785413 = 709765) (by norm_num)
theorem B5186261 : Blo 1328983 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B8086229 : Blo 1328983 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B2245333 : Blo 1328983 2245333 := bbase (se 7 (by rfl) ⟨26312, by rfl⟩ : syracuseStep 2245333 = 52625) (by norm_num)
theorem B6390517 : Blo 1328983 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B2990861 : Blo 1328983 2990861 := bbase (se 3 (by rfl) ⟨560786, by rfl⟩ : syracuseStep 2990861 = 1121573) (by norm_num)
theorem B2245421 : Blo 1328983 2245421 := bbase (se 3 (by rfl) ⟨421016, by rfl⟩ : syracuseStep 2245421 = 842033) (by norm_num)
theorem B5391157 : Blo 1328983 5391157 := bbase (se 5 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 5391157 = 505421) (by norm_num)
theorem B2523973 : Blo 1328983 2523973 := bbase (se 4 (by rfl) ⟨236622, by rfl⟩ : syracuseStep 2523973 = 473245) (by norm_num)
theorem B3367757 : Blo 1328983 3367757 := bbase (se 3 (by rfl) ⟨631454, by rfl⟩ : syracuseStep 3367757 = 1262909) (by norm_num)
theorem B2990933 : Blo 1328983 2990933 := bbase (se 9 (by rfl) ⟨8762, by rfl⟩ : syracuseStep 2990933 = 17525) (by norm_num)
theorem B1598293 : Blo 1328983 1598293 := bbase (se 9 (by rfl) ⟨4682, by rfl⟩ : syracuseStep 1598293 = 9365) (by norm_num)
theorem B2991005 : Blo 1328983 2991005 := bbase (se 3 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 2991005 = 1121627) (by norm_num)
theorem B2245549 : Blo 1328983 2245549 := bbase (se 3 (by rfl) ⟨421040, by rfl⟩ : syracuseStep 2245549 = 842081) (by norm_num)
theorem B2524117 : Blo 1328983 2524117 := bbase (se 7 (by rfl) ⟨29579, by rfl⟩ : syracuseStep 2524117 = 59159) (by norm_num)
theorem B2991077 : Blo 1328983 2991077 := bbase (se 4 (by rfl) ⟨280413, by rfl⟩ : syracuseStep 2991077 = 560827) (by norm_num)
theorem B2245637 : Blo 1328983 2245637 := bbase (se 4 (by rfl) ⟨210528, by rfl⟩ : syracuseStep 2245637 = 421057) (by norm_num)
theorem B4490261 : Blo 1328983 4490261 := bbase (se 6 (by rfl) ⟨105240, by rfl⟩ : syracuseStep 4490261 = 210481) (by norm_num)
theorem B4793381 : Blo 1328983 4793381 := bbase (se 4 (by rfl) ⟨449379, by rfl⟩ : syracuseStep 4793381 = 898759) (by norm_num)
theorem B2991149 : Blo 1328983 2991149 := bbase (se 3 (by rfl) ⟨560840, by rfl⟩ : syracuseStep 2991149 = 1121681) (by norm_num)
theorem B2925629 : Blo 1328983 2925629 := bbase (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) (by norm_num)
theorem B2991221 : Blo 1328983 2991221 := bbase (se 5 (by rfl) ⟨140213, by rfl⟩ : syracuseStep 2991221 = 280427) (by norm_num)
theorem B2524277 : Blo 1328983 2524277 := bbase (se 5 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 2524277 = 236651) (by norm_num)
theorem B2245765 : Blo 1328983 2245765 := bbase (se 4 (by rfl) ⟨210540, by rfl⟩ : syracuseStep 2245765 = 421081) (by norm_num)
theorem B2696341 : Blo 1328983 2696341 := bbase (se 6 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 2696341 = 126391) (by norm_num)
theorem B3368101 : Blo 1328983 3368101 := bbase (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) (by norm_num)
theorem B4793525 : Blo 1328983 4793525 := bbase (se 5 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 4793525 = 449393) (by norm_num)
theorem B2991293 : Blo 1328983 2991293 := bbase (se 3 (by rfl) ⟨560867, by rfl⟩ : syracuseStep 2991293 = 1121735) (by norm_num)
theorem B2245853 : Blo 1328983 2245853 := bbase (se 3 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 2245853 = 842195) (by norm_num)
theorem B2991365 : Blo 1328983 2991365 := bbase (se 4 (by rfl) ⟨280440, by rfl⟩ : syracuseStep 2991365 = 560881) (by norm_num)
theorem B2524421 : Blo 1328983 2524421 := bbase (se 4 (by rfl) ⟨236664, by rfl⟩ : syracuseStep 2524421 = 473329) (by norm_num)
theorem B3368213 : Blo 1328983 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B2991437 : Blo 1328983 2991437 := bbase (se 3 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 2991437 = 1121789) (by norm_num)
theorem B1893709 : Blo 1328983 1893709 := bbase (se 3 (by rfl) ⟨355070, by rfl⟩ : syracuseStep 1893709 = 710141) (by norm_num)
theorem B2245981 : Blo 1328983 2245981 := bbase (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) (by norm_num)
theorem B1598821 : Blo 1328983 1598821 := bbase (se 4 (by rfl) ⟨149889, by rfl⟩ : syracuseStep 1598821 = 299779) (by norm_num)
theorem B2991509 : Blo 1328983 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B7194005 : Blo 1328983 7194005 := bbase (se 6 (by rfl) ⟨168609, by rfl⟩ : syracuseStep 7194005 = 337219) (by norm_num)
theorem B5047717 : Blo 1328983 5047717 := bbase (se 4 (by rfl) ⟨473223, by rfl⟩ : syracuseStep 5047717 = 946447) (by norm_num)
theorem B4490693 : Blo 1328983 4490693 := bbase (se 4 (by rfl) ⟨421002, by rfl⟩ : syracuseStep 4490693 = 842005) (by norm_num)
theorem B3368405 : Blo 1328983 3368405 := bbase (se 7 (by rfl) ⟨39473, by rfl⟩ : syracuseStep 3368405 = 78947) (by norm_num)
theorem B2991581 : Blo 1328983 2991581 := bbase (se 3 (by rfl) ⟨560921, by rfl⟩ : syracuseStep 2991581 = 1121843) (by norm_num)
theorem B2131429 : Blo 1328983 2131429 := bbase (se 4 (by rfl) ⟨199821, by rfl⟩ : syracuseStep 2131429 = 399643) (by norm_num)
theorem B2991653 : Blo 1328983 2991653 := bbase (se 4 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 2991653 = 560935) (by norm_num)
theorem B2524709 : Blo 1328983 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B7571029 : Blo 1328983 7571029 := bbase (se 8 (by rfl) ⟨44361, by rfl⟩ : syracuseStep 7571029 = 88723) (by norm_num)
theorem B2991725 : Blo 1328983 2991725 := bbase (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) (by norm_num)
theorem B1894045 : Blo 1328983 1894045 := bbase (se 3 (by rfl) ⟨355133, by rfl⟩ : syracuseStep 1894045 = 710267) (by norm_num)
theorem B2336429 : Blo 1328983 2336429 := bbase (se 3 (by rfl) ⟨438080, by rfl⟩ : syracuseStep 2336429 = 876161) (by norm_num)
theorem B2991797 : Blo 1328983 2991797 := bbase (se 5 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 2991797 = 280481) (by norm_num)
theorem B2524861 : Blo 1328983 2524861 := bbase (se 3 (by rfl) ⟨473411, by rfl⟩ : syracuseStep 2524861 = 946823) (by norm_num)
theorem B7186133 : Blo 1328983 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B5048021 : Blo 1328983 5048021 := bbase (se 7 (by rfl) ⟨59156, by rfl⟩ : syracuseStep 5048021 = 118313) (by norm_num)
theorem B4548325 : Blo 1328983 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B2131685 : Blo 1328983 2131685 := bbase (se 4 (by rfl) ⟨199845, by rfl⟩ : syracuseStep 2131685 = 399691) (by norm_num)
theorem B2991869 : Blo 1328983 2991869 := bbase (se 3 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 2991869 = 1121951) (by norm_num)
theorem B3786517 : Blo 1328983 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B3368749 : Blo 1328983 3368749 := bbase (se 3 (by rfl) ⟨631640, by rfl⟩ : syracuseStep 3368749 = 1263281) (by norm_num)
theorem B2991941 : Blo 1328983 2991941 := bbase (se 4 (by rfl) ⟨280494, by rfl⟩ : syracuseStep 2991941 = 560989) (by norm_num)
theorem B1894261 : Blo 1328983 1894261 := bbase (se 5 (by rfl) ⟨88793, by rfl⟩ : syracuseStep 1894261 = 177587) (by norm_num)
theorem B4491125 : Blo 1328983 4491125 := bbase (se 5 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 4491125 = 421043) (by norm_num)
theorem B1517449 : Blo 1328983 1517449 := bbase (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) (by norm_num)
theorem B2992013 : Blo 1328983 2992013 := bbase (se 3 (by rfl) ⟨561002, by rfl⟩ : syracuseStep 2992013 = 1122005) (by norm_num)
theorem B3368861 : Blo 1328983 3368861 := bbase (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) (by norm_num)
theorem B2131877 : Blo 1328983 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B6735797 : Blo 1328983 6735797 := bbase (se 5 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 6735797 = 631481) (by norm_num)
theorem B2992085 : Blo 1328983 2992085 := bbase (se 7 (by rfl) ⟨35063, by rfl⟩ : syracuseStep 2992085 = 70127) (by norm_num)
theorem B1705961 : Blo 1328983 1705961 := bbase (se 2 (by rfl) ⟨639735, by rfl⟩ : syracuseStep 1705961 = 1279471) (by norm_num)
theorem B2525165 : Blo 1328983 2525165 := bbase (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) (by norm_num)
theorem B4261909 : Blo 1328983 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B2992157 : Blo 1328983 2992157 := bbase (se 3 (by rfl) ⟨561029, by rfl⟩ : syracuseStep 2992157 = 1122059) (by norm_num)
theorem B6826037 : Blo 1328983 6826037 := bbase (se 5 (by rfl) ⟨319970, by rfl⟩ : syracuseStep 6826037 = 639941) (by norm_num)
theorem B1419329 : Blo 1328983 1419329 := bbase (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) (by norm_num)
theorem B3369053 : Blo 1328983 3369053 := bbase (se 3 (by rfl) ⟨631697, by rfl⟩ : syracuseStep 3369053 = 1263395) (by norm_num)
theorem B2992229 : Blo 1328983 2992229 := bbase (se 4 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 2992229 = 561043) (by norm_num)
theorem B1706141 : Blo 1328983 1706141 := bbase (se 3 (by rfl) ⟨319901, by rfl⟩ : syracuseStep 1706141 = 639803) (by norm_num)
theorem B2992301 : Blo 1328983 2992301 := bbase (se 3 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 2992301 = 1122113) (by norm_num)
theorem B1894637 : Blo 1328983 1894637 := bbase (se 3 (by rfl) ⟨355244, by rfl⟩ : syracuseStep 1894637 = 710489) (by norm_num)
theorem B1730797 : Blo 1328983 1730797 := bbase (se 3 (by rfl) ⟨324524, by rfl⟩ : syracuseStep 1730797 = 649049) (by norm_num)
theorem B2992373 : Blo 1328983 2992373 := bbase (se 5 (by rfl) ⟨140267, by rfl⟩ : syracuseStep 2992373 = 280535) (by norm_num)
theorem B7194869 : Blo 1328983 7194869 := bbase (se 5 (by rfl) ⟨337259, by rfl⟩ : syracuseStep 7194869 = 674519) (by norm_num)
theorem B4491557 : Blo 1328983 4491557 := bbase (se 4 (by rfl) ⟨421083, by rfl⟩ : syracuseStep 4491557 = 842167) (by norm_num)
theorem B2992445 : Blo 1328983 2992445 := bbase (se 3 (by rfl) ⟨561083, by rfl⟩ : syracuseStep 2992445 = 1122167) (by norm_num)
theorem B6728021 : Blo 1328983 6728021 := bbase (se 10 (by rfl) ⟨9855, by rfl⟩ : syracuseStep 6728021 = 19711) (by norm_num)
theorem B2992517 : Blo 1328983 2992517 := bbase (se 4 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 2992517 = 561097) (by norm_num)
theorem B2992589 : Blo 1328983 2992589 := bbase (se 3 (by rfl) ⟨561110, by rfl⟩ : syracuseStep 2992589 = 1122221) (by norm_num)
theorem B1419773 : Blo 1328983 1419773 := bbase (se 3 (by rfl) ⟨266207, by rfl⟩ : syracuseStep 1419773 = 532415) (by norm_num)
theorem B2992661 : Blo 1328983 2992661 := bbase (se 6 (by rfl) ⟨70140, by rfl⟩ : syracuseStep 2992661 = 140281) (by norm_num)
theorem B2992733 : Blo 1328983 2992733 := bbase (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) (by norm_num)
theorem B1682041 : Blo 1328983 1682041 := bbase (se 2 (by rfl) ⟨630765, by rfl⟩ : syracuseStep 1682041 = 1261531) (by norm_num)
theorem B2992805 : Blo 1328983 2992805 := bbase (se 4 (by rfl) ⟨280575, by rfl⟩ : syracuseStep 2992805 = 561151) (by norm_num)
theorem B4041397 : Blo 1328983 4041397 := bbase (se 5 (by rfl) ⟨189440, by rfl⟩ : syracuseStep 4041397 = 378881) (by norm_num)
theorem B8088245 : Blo 1328983 8088245 := bbase (se 5 (by rfl) ⟨379136, by rfl⟩ : syracuseStep 8088245 = 758273) (by norm_num)
theorem B4491989 : Blo 1328983 4491989 := bbase (se 7 (by rfl) ⟨52640, by rfl⟩ : syracuseStep 4491989 = 105281) (by norm_num)
theorem B1682137 : Blo 1328983 1682137 := bbase (se 2 (by rfl) ⟨630801, by rfl⟩ : syracuseStep 1682137 = 1261603) (by norm_num)
theorem B2525917 : Blo 1328983 2525917 := bbase (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) (by norm_num)
theorem B5679845 : Blo 1328983 5679845 := bbase (se 4 (by rfl) ⟨532485, by rfl⟩ : syracuseStep 5679845 = 1064971) (by norm_num)
theorem B2992877 : Blo 1328983 2992877 := bbase (se 3 (by rfl) ⟨561164, by rfl⟩ : syracuseStep 2992877 = 1122329) (by norm_num)
theorem B1420021 : Blo 1328983 1420021 := bbase (se 5 (by rfl) ⟨66563, by rfl⟩ : syracuseStep 1420021 = 133127) (by norm_num)
theorem B1993493 : Blo 1328983 1993493 := bbase (se 6 (by rfl) ⟨46722, by rfl⟩ : syracuseStep 1993493 = 93445) (by norm_num)
theorem B17042197 : Blo 1328983 17042197 := bbase (se 6 (by rfl) ⟨399426, by rfl⟩ : syracuseStep 17042197 = 798853) (by norm_num)
theorem B2394917 : Blo 1328983 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1993517 : Blo 1328983 1993517 := bbase (se 3 (by rfl) ⟨373784, by rfl⟩ : syracuseStep 1993517 = 747569) (by norm_num)
theorem B2992949 : Blo 1328983 2992949 := bbase (se 5 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 2992949 = 280589) (by norm_num)
theorem B1993541 : Blo 1328983 1993541 := bbase (se 4 (by rfl) ⟨186894, by rfl⟩ : syracuseStep 1993541 = 373789) (by norm_num)
theorem B1993565 : Blo 1328983 1993565 := bbase (se 3 (by rfl) ⟨373793, by rfl⟩ : syracuseStep 1993565 = 747587) (by norm_num)
theorem B2526061 : Blo 1328983 2526061 := bbase (se 3 (by rfl) ⟨473636, by rfl⟩ : syracuseStep 2526061 = 947273) (by norm_num)
theorem B1993589 : Blo 1328983 1993589 := bbase (se 5 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 1993589 = 186899) (by norm_num)
theorem B2993021 : Blo 1328983 2993021 := bbase (se 3 (by rfl) ⟨561191, by rfl⟩ : syracuseStep 2993021 = 1122383) (by norm_num)
theorem B1682309 : Blo 1328983 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B1993613 : Blo 1328983 1993613 := bbase (se 3 (by rfl) ⟨373802, by rfl⟩ : syracuseStep 1993613 = 747605) (by norm_num)
theorem B1993637 : Blo 1328983 1993637 := bbase (se 4 (by rfl) ⟨186903, by rfl⟩ : syracuseStep 1993637 = 373807) (by norm_num)
theorem B1993661 : Blo 1328983 1993661 := bbase (se 3 (by rfl) ⟨373811, by rfl⟩ : syracuseStep 1993661 = 747623) (by norm_num)
theorem B1682365 : Blo 1328983 1682365 := bbase (se 3 (by rfl) ⟨315443, by rfl⟩ : syracuseStep 1682365 = 630887) (by norm_num)
theorem B2993093 : Blo 1328983 2993093 := bbase (se 4 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 2993093 = 561205) (by norm_num)
theorem B1993685 : Blo 1328983 1993685 := bbase (se 7 (by rfl) ⟨23363, by rfl⟩ : syracuseStep 1993685 = 46727) (by norm_num)
theorem B2878429 : Blo 1328983 2878429 := bbase (se 3 (by rfl) ⟨539705, by rfl⟩ : syracuseStep 2878429 = 1079411) (by norm_num)
theorem B2698205 : Blo 1328983 2698205 := bbase (se 3 (by rfl) ⟨505913, by rfl⟩ : syracuseStep 2698205 = 1011827) (by norm_num)
theorem B1993709 : Blo 1328983 1993709 := bbase (se 3 (by rfl) ⟨373820, by rfl⟩ : syracuseStep 1993709 = 747641) (by norm_num)
theorem B1993733 : Blo 1328983 1993733 := bbase (se 4 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 1993733 = 373825) (by norm_num)
theorem B2993165 : Blo 1328983 2993165 := bbase (se 3 (by rfl) ⟨561218, by rfl⟩ : syracuseStep 2993165 = 1122437) (by norm_num)
theorem B2526221 : Blo 1328983 2526221 := bbase (se 3 (by rfl) ⟨473666, by rfl⟩ : syracuseStep 2526221 = 947333) (by norm_num)
theorem B1993757 : Blo 1328983 1993757 := bbase (se 3 (by rfl) ⟨373829, by rfl⟩ : syracuseStep 1993757 = 747659) (by norm_num)
theorem B1682461 : Blo 1328983 1682461 := bbase (se 3 (by rfl) ⟨315461, by rfl⟩ : syracuseStep 1682461 = 630923) (by norm_num)
theorem B1993781 : Blo 1328983 1993781 := bbase (se 5 (by rfl) ⟨93458, by rfl⟩ : syracuseStep 1993781 = 186917) (by norm_num)
theorem B1920061 : Blo 1328983 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B5762117 : Blo 1328983 5762117 := bbase (se 4 (by rfl) ⟨540198, by rfl⟩ : syracuseStep 5762117 = 1080397) (by norm_num)
theorem B1993805 : Blo 1328983 1993805 := bbase (se 3 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 1993805 = 747677) (by norm_num)
theorem B2993237 : Blo 1328983 2993237 := bbase (se 8 (by rfl) ⟨17538, by rfl⟩ : syracuseStep 2993237 = 35077) (by norm_num)
theorem B1993829 : Blo 1328983 1993829 := bbase (se 4 (by rfl) ⟨186921, by rfl⟩ : syracuseStep 1993829 = 373843) (by norm_num)
theorem B1993853 : Blo 1328983 1993853 := bbase (se 3 (by rfl) ⟨373847, by rfl⟩ : syracuseStep 1993853 = 747695) (by norm_num)
theorem B1993877 : Blo 1328983 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B11357333 : Blo 1328983 11357333 := bbase (se 6 (by rfl) ⟨266187, by rfl⟩ : syracuseStep 11357333 = 532375) (by norm_num)
theorem B4795541 : Blo 1328983 4795541 := bbase (se 6 (by rfl) ⟨112395, by rfl⟩ : syracuseStep 4795541 = 224791) (by norm_num)
theorem B4500629 : Blo 1328983 4500629 := bbase (se 6 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 4500629 = 210967) (by norm_num)
theorem B2993309 : Blo 1328983 2993309 := bbase (se 3 (by rfl) ⟨561245, by rfl⟩ : syracuseStep 2993309 = 1122491) (by norm_num)
theorem B2526365 : Blo 1328983 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B1420453 : Blo 1328983 1420453 := bbase (se 4 (by rfl) ⟨133167, by rfl⟩ : syracuseStep 1420453 = 266335) (by norm_num)
theorem B1993901 : Blo 1328983 1993901 := bbase (se 3 (by rfl) ⟨373856, by rfl⟩ : syracuseStep 1993901 = 747713) (by norm_num)
theorem B1993925 : Blo 1328983 1993925 := bbase (se 4 (by rfl) ⟨186930, by rfl⟩ : syracuseStep 1993925 = 373861) (by norm_num)
theorem B1682633 : Blo 1328983 1682633 := bbase (se 2 (by rfl) ⟨630987, by rfl⟩ : syracuseStep 1682633 = 1261975) (by norm_num)
theorem B6737093 : Blo 1328983 6737093 := bbase (se 4 (by rfl) ⟨631602, by rfl⟩ : syracuseStep 6737093 = 1263205) (by norm_num)
theorem B1993949 : Blo 1328983 1993949 := bbase (se 3 (by rfl) ⟨373865, by rfl⟩ : syracuseStep 1993949 = 747731) (by norm_num)
theorem B2993381 : Blo 1328983 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B1420525 : Blo 1328983 1420525 := bbase (se 3 (by rfl) ⟨266348, by rfl⟩ : syracuseStep 1420525 = 532697) (by norm_num)
theorem B1993973 : Blo 1328983 1993973 := bbase (se 5 (by rfl) ⟨93467, by rfl⟩ : syracuseStep 1993973 = 186935) (by norm_num)
theorem B3788021 : Blo 1328983 3788021 := bbase (se 5 (by rfl) ⟨177563, by rfl⟩ : syracuseStep 3788021 = 355127) (by norm_num)
theorem B1682689 : Blo 1328983 1682689 := bbase (se 2 (by rfl) ⟨631008, by rfl⟩ : syracuseStep 1682689 = 1262017) (by norm_num)
theorem B1993997 : Blo 1328983 1993997 := bbase (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) (by norm_num)
theorem B1994021 : Blo 1328983 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B2993453 : Blo 1328983 2993453 := bbase (se 3 (by rfl) ⟨561272, by rfl⟩ : syracuseStep 2993453 = 1122545) (by norm_num)
theorem B1994045 : Blo 1328983 1994045 := bbase (se 3 (by rfl) ⟨373883, by rfl⟩ : syracuseStep 1994045 = 747767) (by norm_num)
theorem B1994069 : Blo 1328983 1994069 := bbase (se 11 (by rfl) ⟨1460, by rfl⟩ : syracuseStep 1994069 = 2921) (by norm_num)
theorem B1682785 : Blo 1328983 1682785 := bbase (se 2 (by rfl) ⟨631044, by rfl⟩ : syracuseStep 1682785 = 1262089) (by norm_num)
theorem B1994093 : Blo 1328983 1994093 := bbase (se 3 (by rfl) ⟨373892, by rfl⟩ : syracuseStep 1994093 = 747785) (by norm_num)
theorem B2993525 : Blo 1328983 2993525 := bbase (se 5 (by rfl) ⟨140321, by rfl⟩ : syracuseStep 2993525 = 280643) (by norm_num)
theorem B1994117 : Blo 1328983 1994117 := bbase (se 4 (by rfl) ⟨186948, by rfl⟩ : syracuseStep 1994117 = 373897) (by norm_num)
theorem B1994141 : Blo 1328983 1994141 := bbase (se 3 (by rfl) ⟨373901, by rfl⟩ : syracuseStep 1994141 = 747803) (by norm_num)
theorem B1994165 : Blo 1328983 1994165 := bbase (se 5 (by rfl) ⟨93476, by rfl⟩ : syracuseStep 1994165 = 186953) (by norm_num)
theorem B6393269 : Blo 1328983 6393269 := bbase (se 5 (by rfl) ⟨299684, by rfl⟩ : syracuseStep 6393269 = 599369) (by norm_num)
theorem B2993597 : Blo 1328983 2993597 := bbase (se 3 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 2993597 = 1122599) (by norm_num)
theorem B2526653 : Blo 1328983 2526653 := bbase (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) (by norm_num)
theorem B1994189 : Blo 1328983 1994189 := bbase (se 3 (by rfl) ⟨373910, by rfl⟩ : syracuseStep 1994189 = 747821) (by norm_num)
theorem B1994213 : Blo 1328983 1994213 := bbase (se 4 (by rfl) ⟨186957, by rfl⟩ : syracuseStep 1994213 = 373915) (by norm_num)
theorem B2395637 : Blo 1328983 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B1994237 : Blo 1328983 1994237 := bbase (se 3 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 1994237 = 747839) (by norm_num)
theorem B2993669 : Blo 1328983 2993669 := bbase (se 4 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 2993669 = 561313) (by norm_num)
theorem B1682957 : Blo 1328983 1682957 := bbase (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) (by norm_num)
theorem B1994261 : Blo 1328983 1994261 := bbase (se 6 (by rfl) ⟨46740, by rfl⟩ : syracuseStep 1994261 = 93481) (by norm_num)
theorem B7573013 : Blo 1328983 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B1994285 : Blo 1328983 1994285 := bbase (se 3 (by rfl) ⟨373928, by rfl⟩ : syracuseStep 1994285 = 747857) (by norm_num)
theorem B1347121 : Blo 1328983 1347121 := bbase (se 2 (by rfl) ⟨505170, by rfl⟩ : syracuseStep 1347121 = 1010341) (by norm_num)
theorem B1994309 : Blo 1328983 1994309 := bbase (se 4 (by rfl) ⟨186966, by rfl⟩ : syracuseStep 1994309 = 373933) (by norm_num)
theorem B1683013 : Blo 1328983 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B2993741 : Blo 1328983 2993741 := bbase (se 3 (by rfl) ⟨561326, by rfl⟩ : syracuseStep 2993741 = 1122653) (by norm_num)
theorem B1994333 : Blo 1328983 1994333 := bbase (se 3 (by rfl) ⟨373937, by rfl⟩ : syracuseStep 1994333 = 747875) (by norm_num)
theorem B1420897 : Blo 1328983 1420897 := bbase (se 2 (by rfl) ⟨532836, by rfl⟩ : syracuseStep 1420897 = 1065673) (by norm_num)
theorem B6729317 : Blo 1328983 6729317 := bbase (se 4 (by rfl) ⟨630873, by rfl⟩ : syracuseStep 6729317 = 1261747) (by norm_num)
theorem B1994357 : Blo 1328983 1994357 := bbase (se 5 (by rfl) ⟨93485, by rfl⟩ : syracuseStep 1994357 = 186971) (by norm_num)
theorem B1994381 : Blo 1328983 1994381 := bbase (se 3 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 1994381 = 747893) (by norm_num)
theorem B12136085 : Blo 1328983 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B2993813 : Blo 1328983 2993813 := bbase (se 6 (by rfl) ⟨70167, by rfl⟩ : syracuseStep 2993813 = 140335) (by norm_num)
theorem B1994405 : Blo 1328983 1994405 := bbase (se 4 (by rfl) ⟨186975, by rfl⟩ : syracuseStep 1994405 = 373951) (by norm_num)
theorem B1683109 : Blo 1328983 1683109 := bbase (se 4 (by rfl) ⟨157791, by rfl⟩ : syracuseStep 1683109 = 315583) (by norm_num)
theorem B3239597 : Blo 1328983 3239597 := bbase (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) (by norm_num)
theorem B1994429 : Blo 1328983 1994429 := bbase (se 3 (by rfl) ⟨373955, by rfl⟩ : syracuseStep 1994429 = 747911) (by norm_num)
theorem B1994453 : Blo 1328983 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B2993885 : Blo 1328983 2993885 := bbase (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) (by norm_num)
theorem B1994477 : Blo 1328983 1994477 := bbase (se 3 (by rfl) ⟨373964, by rfl⟩ : syracuseStep 1994477 = 747929) (by norm_num)
theorem B12775157 : Blo 1328983 12775157 := bbase (se 5 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 12775157 = 1197671) (by norm_num)
theorem B1994501 : Blo 1328983 1994501 := bbase (se 4 (by rfl) ⟨186984, by rfl⟩ : syracuseStep 1994501 = 373969) (by norm_num)
theorem B5050133 : Blo 1328983 5050133 := bbase (se 6 (by rfl) ⟨118362, by rfl⟩ : syracuseStep 5050133 = 236725) (by norm_num)
theorem B1994525 : Blo 1328983 1994525 := bbase (se 3 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 1994525 = 747947) (by norm_num)
theorem B2993957 : Blo 1328983 2993957 := bbase (se 4 (by rfl) ⟨280683, by rfl⟩ : syracuseStep 2993957 = 561367) (by norm_num)
theorem B9711413 : Blo 1328983 9711413 := bbase (se 5 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 9711413 = 910445) (by norm_num)
theorem B1994549 : Blo 1328983 1994549 := bbase (se 5 (by rfl) ⟨93494, by rfl⟩ : syracuseStep 1994549 = 186989) (by norm_num)
theorem B1994573 : Blo 1328983 1994573 := bbase (se 3 (by rfl) ⟨373982, by rfl⟩ : syracuseStep 1994573 = 747965) (by norm_num)
theorem B1683281 : Blo 1328983 1683281 := bbase (se 2 (by rfl) ⟨631230, by rfl⟩ : syracuseStep 1683281 = 1262461) (by norm_num)
theorem B1994597 : Blo 1328983 1994597 := bbase (se 4 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 1994597 = 373987) (by norm_num)
theorem B2994029 : Blo 1328983 2994029 := bbase (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) (by norm_num)
theorem B1994621 : Blo 1328983 1994621 := bbase (se 3 (by rfl) ⟨373991, by rfl⟩ : syracuseStep 1994621 = 747983) (by norm_num)
theorem B1683337 : Blo 1328983 1683337 := bbase (se 2 (by rfl) ⟨631251, by rfl⟩ : syracuseStep 1683337 = 1262503) (by norm_num)
theorem B1994645 : Blo 1328983 1994645 := bbase (se 6 (by rfl) ⟨46749, by rfl⟩ : syracuseStep 1994645 = 93499) (by norm_num)
theorem B1994669 : Blo 1328983 1994669 := bbase (se 3 (by rfl) ⟨374000, by rfl⟩ : syracuseStep 1994669 = 748001) (by norm_num)
theorem B2994101 : Blo 1328983 2994101 := bbase (se 5 (by rfl) ⟨140348, by rfl⟩ : syracuseStep 2994101 = 280697) (by norm_num)
theorem B1994693 : Blo 1328983 1994693 := bbase (se 4 (by rfl) ⟨187002, by rfl⟩ : syracuseStep 1994693 = 374005) (by norm_num)
theorem B1421273 : Blo 1328983 1421273 := bbase (se 2 (by rfl) ⟨532977, by rfl⟩ : syracuseStep 1421273 = 1065955) (by norm_num)
theorem B1994717 : Blo 1328983 1994717 := bbase (se 3 (by rfl) ⟨374009, by rfl⟩ : syracuseStep 1994717 = 748019) (by norm_num)
theorem B1683433 : Blo 1328983 1683433 := bbase (se 2 (by rfl) ⟨631287, by rfl⟩ : syracuseStep 1683433 = 1262575) (by norm_num)
theorem B1994741 : Blo 1328983 1994741 := bbase (se 5 (by rfl) ⟨93503, by rfl⟩ : syracuseStep 1994741 = 187007) (by norm_num)
theorem B2994173 : Blo 1328983 2994173 := bbase (se 3 (by rfl) ⟨561407, by rfl⟩ : syracuseStep 2994173 = 1122815) (by norm_num)
theorem B1994765 : Blo 1328983 1994765 := bbase (se 3 (by rfl) ⟨374018, by rfl⟩ : syracuseStep 1994765 = 748037) (by norm_num)
theorem B5754901 : Blo 1328983 5754901 := bbase (se 6 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 5754901 = 269761) (by norm_num)
theorem B1994789 : Blo 1328983 1994789 := bbase (se 4 (by rfl) ⟨187011, by rfl⟩ : syracuseStep 1994789 = 374023) (by norm_num)
theorem B5050421 : Blo 1328983 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B1994813 : Blo 1328983 1994813 := bbase (se 3 (by rfl) ⟨374027, by rfl⟩ : syracuseStep 1994813 = 748055) (by norm_num)
theorem B2994245 : Blo 1328983 2994245 := bbase (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) (by norm_num)
theorem B1994837 : Blo 1328983 1994837 := bbase (se 8 (by rfl) ⟨11688, by rfl⟩ : syracuseStep 1994837 = 23377) (by norm_num)
theorem B1495129 : Blo 1328983 1495129 := bbase (se 2 (by rfl) ⟨560673, by rfl⟩ : syracuseStep 1495129 = 1121347) (by norm_num)
theorem B1994861 : Blo 1328983 1994861 := bbase (se 3 (by rfl) ⟨374036, by rfl⟩ : syracuseStep 1994861 = 748073) (by norm_num)
theorem B1495165 : Blo 1328983 1495165 := bbase (se 3 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 1495165 = 560687) (by norm_num)
theorem B1994885 : Blo 1328983 1994885 := bbase (se 4 (by rfl) ⟨187020, by rfl⟩ : syracuseStep 1994885 = 374041) (by norm_num)
theorem B2994317 : Blo 1328983 2994317 := bbase (se 3 (by rfl) ⟨561434, by rfl⟩ : syracuseStep 2994317 = 1122869) (by norm_num)
theorem B1683605 : Blo 1328983 1683605 := bbase (se 6 (by rfl) ⟨39459, by rfl⟩ : syracuseStep 1683605 = 78919) (by norm_num)
theorem B1994909 : Blo 1328983 1994909 := bbase (se 3 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 1994909 = 748091) (by norm_num)
theorem B1495201 : Blo 1328983 1495201 := bbase (se 2 (by rfl) ⟨560700, by rfl⟩ : syracuseStep 1495201 = 1121401) (by norm_num)
theorem B1994933 : Blo 1328983 1994933 := bbase (se 5 (by rfl) ⟨93512, by rfl⟩ : syracuseStep 1994933 = 187025) (by norm_num)
theorem B1347773 : Blo 1328983 1347773 := bbase (se 3 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 1347773 = 505415) (by norm_num)
theorem B1495237 : Blo 1328983 1495237 := bbase (se 4 (by rfl) ⟨140178, by rfl⟩ : syracuseStep 1495237 = 280357) (by norm_num)
theorem B2592965 : Blo 1328983 2592965 := bbase (se 4 (by rfl) ⟨243090, by rfl⟩ : syracuseStep 2592965 = 486181) (by norm_num)
theorem B1994957 : Blo 1328983 1994957 := bbase (se 3 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 1994957 = 748109) (by norm_num)
theorem B1683661 : Blo 1328983 1683661 := bbase (se 3 (by rfl) ⟨315686, by rfl⟩ : syracuseStep 1683661 = 631373) (by norm_num)
theorem B2994389 : Blo 1328983 2994389 := bbase (se 7 (by rfl) ⟨35090, by rfl⟩ : syracuseStep 2994389 = 70181) (by norm_num)
theorem B1994981 : Blo 1328983 1994981 := bbase (se 4 (by rfl) ⟨187029, by rfl⟩ : syracuseStep 1994981 = 374059) (by norm_num)
theorem B1495273 : Blo 1328983 1495273 := bbase (se 2 (by rfl) ⟨560727, by rfl⟩ : syracuseStep 1495273 = 1121455) (by norm_num)
theorem B1995005 : Blo 1328983 1995005 := bbase (se 3 (by rfl) ⟨374063, by rfl⟩ : syracuseStep 1995005 = 748127) (by norm_num)
theorem B1495309 : Blo 1328983 1495309 := bbase (se 3 (by rfl) ⟨280370, by rfl⟩ : syracuseStep 1495309 = 560741) (by norm_num)
theorem B1995029 : Blo 1328983 1995029 := bbase (se 6 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 1995029 = 93517) (by norm_num)
theorem B2994461 : Blo 1328983 2994461 := bbase (se 3 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 2994461 = 1122923) (by norm_num)
theorem B2838829 : Blo 1328983 2838829 := bbase (se 3 (by rfl) ⟨532280, by rfl⟩ : syracuseStep 2838829 = 1064561) (by norm_num)
theorem B1995053 : Blo 1328983 1995053 := bbase (se 3 (by rfl) ⟨374072, by rfl⟩ : syracuseStep 1995053 = 748145) (by norm_num)
theorem B1683757 : Blo 1328983 1683757 := bbase (se 3 (by rfl) ⟨315704, by rfl⟩ : syracuseStep 1683757 = 631409) (by norm_num)
theorem B1495345 : Blo 1328983 1495345 := bbase (se 2 (by rfl) ⟨560754, by rfl⟩ : syracuseStep 1495345 = 1121509) (by norm_num)
theorem B1995077 : Blo 1328983 1995077 := bbase (se 4 (by rfl) ⟨187038, by rfl⟩ : syracuseStep 1995077 = 374077) (by norm_num)
theorem B5394757 : Blo 1328983 5394757 := bbase (se 4 (by rfl) ⟨505758, by rfl⟩ : syracuseStep 5394757 = 1011517) (by norm_num)
theorem B1495381 : Blo 1328983 1495381 := bbase (se 10 (by rfl) ⟨2190, by rfl⟩ : syracuseStep 1495381 = 4381) (by norm_num)
theorem B1995101 : Blo 1328983 1995101 := bbase (se 3 (by rfl) ⟨374081, by rfl⟩ : syracuseStep 1995101 = 748163) (by norm_num)
theorem B2994533 : Blo 1328983 2994533 := bbase (se 4 (by rfl) ⟨280737, by rfl⟩ : syracuseStep 2994533 = 561475) (by norm_num)
theorem B4043125 : Blo 1328983 4043125 := bbase (se 5 (by rfl) ⟨189521, by rfl⟩ : syracuseStep 4043125 = 379043) (by norm_num)
theorem B1995125 : Blo 1328983 1995125 := bbase (se 5 (by rfl) ⟨93521, by rfl⟩ : syracuseStep 1995125 = 187043) (by norm_num)
theorem B1495417 : Blo 1328983 1495417 := bbase (se 2 (by rfl) ⟨560781, by rfl⟩ : syracuseStep 1495417 = 1121563) (by norm_num)
theorem B2429309 : Blo 1328983 2429309 := bbase (se 3 (by rfl) ⟨455495, by rfl⟩ : syracuseStep 2429309 = 910991) (by norm_num)
theorem B4485509 : Blo 1328983 4485509 := bbase (se 4 (by rfl) ⟨420516, by rfl⟩ : syracuseStep 4485509 = 841033) (by norm_num)
theorem B1995149 : Blo 1328983 1995149 := bbase (se 3 (by rfl) ⟨374090, by rfl⟩ : syracuseStep 1995149 = 748181) (by norm_num)
theorem B1495453 : Blo 1328983 1495453 := bbase (se 3 (by rfl) ⟨280397, by rfl⟩ : syracuseStep 1495453 = 560795) (by norm_num)
theorem B1995173 : Blo 1328983 1995173 := bbase (se 4 (by rfl) ⟨187047, by rfl⟩ : syracuseStep 1995173 = 374095) (by norm_num)
theorem B2994605 : Blo 1328983 2994605 := bbase (se 3 (by rfl) ⟨561488, by rfl⟩ : syracuseStep 2994605 = 1122977) (by norm_num)
theorem B1995197 : Blo 1328983 1995197 := bbase (se 3 (by rfl) ⟨374099, by rfl⟩ : syracuseStep 1995197 = 748199) (by norm_num)
theorem B1495489 : Blo 1328983 1495489 := bbase (se 2 (by rfl) ⟨560808, by rfl⟩ : syracuseStep 1495489 = 1121617) (by norm_num)
theorem B1348049 : Blo 1328983 1348049 := bbase (se 2 (by rfl) ⟨505518, by rfl⟩ : syracuseStep 1348049 = 1011037) (by norm_num)
theorem B1995221 : Blo 1328983 1995221 := bbase (se 7 (by rfl) ⟨23381, by rfl⟩ : syracuseStep 1995221 = 46763) (by norm_num)
theorem B1683929 : Blo 1328983 1683929 := bbase (se 2 (by rfl) ⟨631473, by rfl⟩ : syracuseStep 1683929 = 1262947) (by norm_num)
theorem B1495525 : Blo 1328983 1495525 := bbase (se 4 (by rfl) ⟨140205, by rfl⟩ : syracuseStep 1495525 = 280411) (by norm_num)
theorem B1995245 : Blo 1328983 1995245 := bbase (se 3 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 1995245 = 748217) (by norm_num)
theorem B2994677 : Blo 1328983 2994677 := bbase (se 5 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 2994677 = 280751) (by norm_num)
theorem B1995269 : Blo 1328983 1995269 := bbase (se 4 (by rfl) ⟨187056, by rfl⟩ : syracuseStep 1995269 = 374113) (by norm_num)
theorem B1495561 : Blo 1328983 1495561 := bbase (se 2 (by rfl) ⟨560835, by rfl⟩ : syracuseStep 1495561 = 1121671) (by norm_num)
theorem B1798669 : Blo 1328983 1798669 := bbase (se 3 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 1798669 = 674501) (by norm_num)
theorem B1683985 : Blo 1328983 1683985 := bbase (se 2 (by rfl) ⟨631494, by rfl⟩ : syracuseStep 1683985 = 1262989) (by norm_num)
theorem B1995293 : Blo 1328983 1995293 := bbase (se 3 (by rfl) ⟨374117, by rfl⟩ : syracuseStep 1995293 = 748235) (by norm_num)
theorem B1495597 : Blo 1328983 1495597 := bbase (se 3 (by rfl) ⟨280424, by rfl⟩ : syracuseStep 1495597 = 560849) (by norm_num)
theorem B1995317 : Blo 1328983 1995317 := bbase (se 5 (by rfl) ⟨93530, by rfl⟩ : syracuseStep 1995317 = 187061) (by norm_num)
theorem B10105397 : Blo 1328983 10105397 := bbase (se 5 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 10105397 = 947381) (by norm_num)
theorem B3330629 : Blo 1328983 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B1995341 : Blo 1328983 1995341 := bbase (se 3 (by rfl) ⟨374126, by rfl⟩ : syracuseStep 1995341 = 748253) (by norm_num)
theorem B1495633 : Blo 1328983 1495633 := bbase (se 2 (by rfl) ⟨560862, by rfl⟩ : syracuseStep 1495633 = 1121725) (by norm_num)
theorem B1995365 : Blo 1328983 1995365 := bbase (se 4 (by rfl) ⟨187065, by rfl⟩ : syracuseStep 1995365 = 374131) (by norm_num)
theorem B1684081 : Blo 1328983 1684081 := bbase (se 2 (by rfl) ⟨631530, by rfl⟩ : syracuseStep 1684081 = 1263061) (by norm_num)
theorem B1495669 : Blo 1328983 1495669 := bbase (se 5 (by rfl) ⟨70109, by rfl⟩ : syracuseStep 1495669 = 140219) (by norm_num)
theorem B1995389 : Blo 1328983 1995389 := bbase (se 3 (by rfl) ⟨374135, by rfl⟩ : syracuseStep 1995389 = 748271) (by norm_num)
theorem B1995413 : Blo 1328983 1995413 := bbase (se 6 (by rfl) ⟨46767, by rfl⟩ : syracuseStep 1995413 = 93535) (by norm_num)
theorem B1495705 : Blo 1328983 1495705 := bbase (se 2 (by rfl) ⟨560889, by rfl⟩ : syracuseStep 1495705 = 1121779) (by norm_num)
theorem B2839205 : Blo 1328983 2839205 := bbase (se 4 (by rfl) ⟨266175, by rfl⟩ : syracuseStep 2839205 = 532351) (by norm_num)
theorem B1995437 : Blo 1328983 1995437 := bbase (se 3 (by rfl) ⟨374144, by rfl⟩ : syracuseStep 1995437 = 748289) (by norm_num)
theorem B1495741 : Blo 1328983 1495741 := bbase (se 3 (by rfl) ⟨280451, by rfl⟩ : syracuseStep 1495741 = 560903) (by norm_num)
theorem B1995461 : Blo 1328983 1995461 := bbase (se 4 (by rfl) ⟨187074, by rfl⟩ : syracuseStep 1995461 = 374149) (by norm_num)
theorem B1995485 : Blo 1328983 1995485 := bbase (se 3 (by rfl) ⟨374153, by rfl⟩ : syracuseStep 1995485 = 748307) (by norm_num)
theorem B1495777 : Blo 1328983 1495777 := bbase (se 2 (by rfl) ⟨560916, by rfl⟩ : syracuseStep 1495777 = 1121833) (by norm_num)
theorem B1995509 : Blo 1328983 1995509 := bbase (se 5 (by rfl) ⟨93539, by rfl⟩ : syracuseStep 1995509 = 187079) (by norm_num)
theorem B1495813 : Blo 1328983 1495813 := bbase (se 4 (by rfl) ⟨140232, by rfl⟩ : syracuseStep 1495813 = 280465) (by norm_num)
theorem B1348357 : Blo 1328983 1348357 := bbase (se 4 (by rfl) ⟨126408, by rfl⟩ : syracuseStep 1348357 = 252817) (by norm_num)
theorem B1995533 : Blo 1328983 1995533 := bbase (se 3 (by rfl) ⟨374162, by rfl⟩ : syracuseStep 1995533 = 748325) (by norm_num)
theorem B1684253 : Blo 1328983 1684253 := bbase (se 3 (by rfl) ⟨315797, by rfl⟩ : syracuseStep 1684253 = 631595) (by norm_num)
theorem B1995557 : Blo 1328983 1995557 := bbase (se 4 (by rfl) ⟨187083, by rfl⟩ : syracuseStep 1995557 = 374167) (by norm_num)
theorem B3789605 : Blo 1328983 3789605 := bbase (se 4 (by rfl) ⟨355275, by rfl⟩ : syracuseStep 3789605 = 710551) (by norm_num)
theorem B1495849 : Blo 1328983 1495849 := bbase (se 2 (by rfl) ⟨560943, by rfl⟩ : syracuseStep 1495849 = 1121887) (by norm_num)
theorem B4485941 : Blo 1328983 4485941 := bbase (se 5 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 4485941 = 420557) (by norm_num)
theorem B1995581 : Blo 1328983 1995581 := bbase (se 3 (by rfl) ⟨374171, by rfl⟩ : syracuseStep 1995581 = 748343) (by norm_num)
theorem B1495885 : Blo 1328983 1495885 := bbase (se 3 (by rfl) ⟨280478, by rfl⟩ : syracuseStep 1495885 = 560957) (by norm_num)
theorem B3593045 : Blo 1328983 3593045 := bbase (se 9 (by rfl) ⟨10526, by rfl⟩ : syracuseStep 3593045 = 21053) (by norm_num)
theorem B1995605 : Blo 1328983 1995605 := bbase (se 9 (by rfl) ⟨5846, by rfl⟩ : syracuseStep 1995605 = 11693) (by norm_num)
theorem B1684309 : Blo 1328983 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B1995629 : Blo 1328983 1995629 := bbase (se 3 (by rfl) ⟨374180, by rfl⟩ : syracuseStep 1995629 = 748361) (by norm_num)
theorem B1495921 : Blo 1328983 1495921 := bbase (se 2 (by rfl) ⟨560970, by rfl⟩ : syracuseStep 1495921 = 1121941) (by norm_num)
theorem B6730613 : Blo 1328983 6730613 := bbase (se 5 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 6730613 = 630995) (by norm_num)
theorem B1995653 : Blo 1328983 1995653 := bbase (se 4 (by rfl) ⟨187092, by rfl⟩ : syracuseStep 1995653 = 374185) (by norm_num)
theorem B1495957 : Blo 1328983 1495957 := bbase (se 6 (by rfl) ⟨35061, by rfl⟩ : syracuseStep 1495957 = 70123) (by norm_num)
theorem B1995677 : Blo 1328983 1995677 := bbase (se 3 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 1995677 = 748379) (by norm_num)
theorem B1995701 : Blo 1328983 1995701 := bbase (se 5 (by rfl) ⟨93548, by rfl⟩ : syracuseStep 1995701 = 187097) (by norm_num)
theorem B1684405 : Blo 1328983 1684405 := bbase (se 5 (by rfl) ⟨78956, by rfl⟩ : syracuseStep 1684405 = 157913) (by norm_num)
theorem B1495993 : Blo 1328983 1495993 := bbase (se 2 (by rfl) ⟨560997, by rfl⟩ : syracuseStep 1495993 = 1121995) (by norm_num)
theorem B1995725 : Blo 1328983 1995725 := bbase (se 3 (by rfl) ⟨374198, by rfl⟩ : syracuseStep 1995725 = 748397) (by norm_num)
theorem B10097621 : Blo 1328983 10097621 := bbase (se 7 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 10097621 = 236663) (by norm_num)
theorem B1496029 : Blo 1328983 1496029 := bbase (se 3 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 1496029 = 561011) (by norm_num)
theorem B1995749 : Blo 1328983 1995749 := bbase (se 4 (by rfl) ⟨187101, by rfl⟩ : syracuseStep 1995749 = 374203) (by norm_num)
theorem B1995773 : Blo 1328983 1995773 := bbase (se 3 (by rfl) ⟨374207, by rfl⟩ : syracuseStep 1995773 = 748415) (by norm_num)
theorem B1496065 : Blo 1328983 1496065 := bbase (se 2 (by rfl) ⟨561024, by rfl⟩ : syracuseStep 1496065 = 1122049) (by norm_num)
theorem B1995797 : Blo 1328983 1995797 := bbase (se 6 (by rfl) ⟨46776, by rfl⟩ : syracuseStep 1995797 = 93553) (by norm_num)
theorem B1348633 : Blo 1328983 1348633 := bbase (se 2 (by rfl) ⟨505737, by rfl⟩ : syracuseStep 1348633 = 1011475) (by norm_num)
theorem B1496101 : Blo 1328983 1496101 := bbase (se 4 (by rfl) ⟨140259, by rfl⟩ : syracuseStep 1496101 = 280519) (by norm_num)
theorem B1995821 : Blo 1328983 1995821 := bbase (se 3 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 1995821 = 748433) (by norm_num)
theorem B1995845 : Blo 1328983 1995845 := bbase (se 4 (by rfl) ⟨187110, by rfl⟩ : syracuseStep 1995845 = 374221) (by norm_num)
theorem B1496137 : Blo 1328983 1496137 := bbase (se 2 (by rfl) ⟨561051, by rfl⟩ : syracuseStep 1496137 = 1122103) (by norm_num)
theorem B1995869 : Blo 1328983 1995869 := bbase (se 3 (by rfl) ⟨374225, by rfl⟩ : syracuseStep 1995869 = 748451) (by norm_num)
theorem B1496173 : Blo 1328983 1496173 := bbase (se 3 (by rfl) ⟨280532, by rfl⟩ : syracuseStep 1496173 = 561065) (by norm_num)
theorem B1995893 : Blo 1328983 1995893 := bbase (se 5 (by rfl) ⟨93557, by rfl⟩ : syracuseStep 1995893 = 187115) (by norm_num)
theorem B1995917 : Blo 1328983 1995917 := bbase (se 3 (by rfl) ⟨374234, by rfl⟩ : syracuseStep 1995917 = 748469) (by norm_num)
theorem B1496209 : Blo 1328983 1496209 := bbase (se 2 (by rfl) ⟨561078, by rfl⟩ : syracuseStep 1496209 = 1122157) (by norm_num)
theorem B1995941 : Blo 1328983 1995941 := bbase (se 4 (by rfl) ⟨187119, by rfl⟩ : syracuseStep 1995941 = 374239) (by norm_num)
theorem B1496245 : Blo 1328983 1496245 := bbase (se 5 (by rfl) ⟨70136, by rfl⟩ : syracuseStep 1496245 = 140273) (by norm_num)
theorem B1995965 : Blo 1328983 1995965 := bbase (se 3 (by rfl) ⟨374243, by rfl⟩ : syracuseStep 1995965 = 748487) (by norm_num)
theorem B2397397 : Blo 1328983 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B5051605 : Blo 1328983 5051605 := bbase (se 7 (by rfl) ⟨59198, by rfl⟩ : syracuseStep 5051605 = 118397) (by norm_num)
theorem B1995989 : Blo 1328983 1995989 := bbase (se 7 (by rfl) ⟨23390, by rfl⟩ : syracuseStep 1995989 = 46781) (by norm_num)
theorem B1496281 : Blo 1328983 1496281 := bbase (se 2 (by rfl) ⟨561105, by rfl⟩ : syracuseStep 1496281 = 1122211) (by norm_num)
theorem B4486373 : Blo 1328983 4486373 := bbase (se 4 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 4486373 = 841195) (by norm_num)
theorem B1996013 : Blo 1328983 1996013 := bbase (se 3 (by rfl) ⟨374252, by rfl⟩ : syracuseStep 1996013 = 748505) (by norm_num)
theorem B1496317 : Blo 1328983 1496317 := bbase (se 3 (by rfl) ⟨280559, by rfl⟩ : syracuseStep 1496317 = 561119) (by norm_num)
theorem B1996037 : Blo 1328983 1996037 := bbase (se 4 (by rfl) ⟨187128, by rfl⟩ : syracuseStep 1996037 = 374257) (by norm_num)
theorem B1996061 : Blo 1328983 1996061 := bbase (se 3 (by rfl) ⟨374261, by rfl⟩ : syracuseStep 1996061 = 748523) (by norm_num)
theorem B1496353 : Blo 1328983 1496353 := bbase (se 2 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 1496353 = 1122265) (by norm_num)
theorem B1996085 : Blo 1328983 1996085 := bbase (se 5 (by rfl) ⟨93566, by rfl⟩ : syracuseStep 1996085 = 187133) (by norm_num)
theorem B1496389 : Blo 1328983 1496389 := bbase (se 4 (by rfl) ⟨140286, by rfl⟩ : syracuseStep 1496389 = 280573) (by norm_num)
theorem B1996109 : Blo 1328983 1996109 := bbase (se 3 (by rfl) ⟨374270, by rfl⟩ : syracuseStep 1996109 = 748541) (by norm_num)
theorem B2397533 : Blo 1328983 2397533 := bbase (se 3 (by rfl) ⟨449537, by rfl⟩ : syracuseStep 2397533 = 899075) (by norm_num)
theorem B1996133 : Blo 1328983 1996133 := bbase (se 4 (by rfl) ⟨187137, by rfl⟩ : syracuseStep 1996133 = 374275) (by norm_num)
theorem B1496425 : Blo 1328983 1496425 := bbase (se 2 (by rfl) ⟨561159, by rfl⟩ : syracuseStep 1496425 = 1122319) (by norm_num)
theorem B3364213 : Blo 1328983 3364213 := bbase (se 5 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 3364213 = 315395) (by norm_num)
theorem B1996157 : Blo 1328983 1996157 := bbase (se 3 (by rfl) ⟨374279, by rfl⟩ : syracuseStep 1996157 = 748559) (by norm_num)
theorem B1496461 : Blo 1328983 1496461 := bbase (se 3 (by rfl) ⟨280586, by rfl⟩ : syracuseStep 1496461 = 561173) (by norm_num)
theorem B1996181 : Blo 1328983 1996181 := bbase (se 6 (by rfl) ⟨46785, by rfl⟩ : syracuseStep 1996181 = 93571) (by norm_num)
theorem B2397613 : Blo 1328983 2397613 := bbase (se 3 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 2397613 = 899105) (by norm_num)
theorem B1996205 : Blo 1328983 1996205 := bbase (se 3 (by rfl) ⟨374288, by rfl⟩ : syracuseStep 1996205 = 748577) (by norm_num)
theorem B1496497 : Blo 1328983 1496497 := bbase (se 2 (by rfl) ⟨561186, by rfl⟩ : syracuseStep 1496497 = 1122373) (by norm_num)
theorem B1996229 : Blo 1328983 1996229 := bbase (se 4 (by rfl) ⟨187146, by rfl⟩ : syracuseStep 1996229 = 374293) (by norm_num)
theorem B48534997 : Blo 1328983 48534997 := bbase (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) (by norm_num)
theorem B1496533 : Blo 1328983 1496533 := bbase (se 7 (by rfl) ⟨17537, by rfl⟩ : syracuseStep 1496533 = 35075) (by norm_num)
theorem B1996253 : Blo 1328983 1996253 := bbase (se 3 (by rfl) ⟨374297, by rfl⟩ : syracuseStep 1996253 = 748595) (by norm_num)
theorem B3364325 : Blo 1328983 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B1996277 : Blo 1328983 1996277 := bbase (se 5 (by rfl) ⟨93575, by rfl⟩ : syracuseStep 1996277 = 187151) (by norm_num)
theorem B1496569 : Blo 1328983 1496569 := bbase (se 2 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 1496569 = 1122427) (by norm_num)
theorem B5051909 : Blo 1328983 5051909 := bbase (se 4 (by rfl) ⟨473616, by rfl⟩ : syracuseStep 5051909 = 947233) (by norm_num)
theorem B1996301 : Blo 1328983 1996301 := bbase (se 3 (by rfl) ⟨374306, by rfl⟩ : syracuseStep 1996301 = 748613) (by norm_num)
theorem B6829589 : Blo 1328983 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B1496605 : Blo 1328983 1496605 := bbase (se 3 (by rfl) ⟨280613, by rfl⟩ : syracuseStep 1496605 = 561227) (by norm_num)
theorem B1996325 : Blo 1328983 1996325 := bbase (se 4 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 1996325 = 374311) (by norm_num)
theorem B1996349 : Blo 1328983 1996349 := bbase (se 3 (by rfl) ⟨374315, by rfl⟩ : syracuseStep 1996349 = 748631) (by norm_num)
theorem B1496641 : Blo 1328983 1496641 := bbase (se 2 (by rfl) ⟨561240, by rfl⟩ : syracuseStep 1496641 = 1122481) (by norm_num)
theorem B1996373 : Blo 1328983 1996373 := bbase (se 8 (by rfl) ⟨11697, by rfl⟩ : syracuseStep 1996373 = 23395) (by norm_num)
theorem B1496677 : Blo 1328983 1496677 := bbase (se 4 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 1496677 = 280627) (by norm_num)
theorem B1996397 : Blo 1328983 1996397 := bbase (se 3 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 1996397 = 748649) (by norm_num)
theorem B1996421 : Blo 1328983 1996421 := bbase (se 4 (by rfl) ⟨187164, by rfl⟩ : syracuseStep 1996421 = 374329) (by norm_num)
theorem B1496713 : Blo 1328983 1496713 := bbase (se 2 (by rfl) ⟨561267, by rfl⟩ : syracuseStep 1496713 = 1122535) (by norm_num)
theorem B4486805 : Blo 1328983 4486805 := bbase (se 6 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 4486805 = 210319) (by norm_num)
theorem B1996445 : Blo 1328983 1996445 := bbase (se 3 (by rfl) ⟨374333, by rfl⟩ : syracuseStep 1996445 = 748667) (by norm_num)
theorem B3364517 : Blo 1328983 3364517 := bbase (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) (by norm_num)
theorem B1496749 : Blo 1328983 1496749 := bbase (se 3 (by rfl) ⟨280640, by rfl⟩ : syracuseStep 1496749 = 561281) (by norm_num)
theorem B7575221 : Blo 1328983 7575221 := bbase (se 5 (by rfl) ⟨355088, by rfl⟩ : syracuseStep 7575221 = 710177) (by norm_num)
theorem B1996469 : Blo 1328983 1996469 := bbase (se 5 (by rfl) ⟨93584, by rfl⟩ : syracuseStep 1996469 = 187169) (by norm_num)
theorem B1496785 : Blo 1328983 1496785 := bbase (se 2 (by rfl) ⟨561294, by rfl⟩ : syracuseStep 1496785 = 1122589) (by norm_num)
theorem B1496821 : Blo 1328983 1496821 := bbase (se 5 (by rfl) ⟨70163, by rfl⟩ : syracuseStep 1496821 = 140327) (by norm_num)
theorem B6067973 : Blo 1328983 6067973 := bbase (se 4 (by rfl) ⟨568872, by rfl⟩ : syracuseStep 6067973 = 1137745) (by norm_num)
theorem B6395669 : Blo 1328983 6395669 := bbase (se 6 (by rfl) ⟨149898, by rfl⟩ : syracuseStep 6395669 = 299797) (by norm_num)
theorem B1496857 : Blo 1328983 1496857 := bbase (se 2 (by rfl) ⟨561321, by rfl⟩ : syracuseStep 1496857 = 1122643) (by norm_num)
theorem B1496893 : Blo 1328983 1496893 := bbase (se 3 (by rfl) ⟨280667, by rfl⟩ : syracuseStep 1496893 = 561335) (by norm_num)
theorem B1496929 : Blo 1328983 1496929 := bbase (se 2 (by rfl) ⟨561348, by rfl⟩ : syracuseStep 1496929 = 1122697) (by norm_num)
theorem B1496965 : Blo 1328983 1496965 := bbase (se 4 (by rfl) ⟨140340, by rfl⟩ : syracuseStep 1496965 = 280681) (by norm_num)
theorem B1497001 : Blo 1328983 1497001 := bbase (se 2 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 1497001 = 1122751) (by norm_num)
theorem B1497037 : Blo 1328983 1497037 := bbase (se 3 (by rfl) ⟨280694, by rfl⟩ : syracuseStep 1497037 = 561389) (by norm_num)
theorem B1497073 : Blo 1328983 1497073 := bbase (se 2 (by rfl) ⟨561402, by rfl⟩ : syracuseStep 1497073 = 1122805) (by norm_num)
theorem B3364861 : Blo 1328983 3364861 := bbase (se 3 (by rfl) ⟨630911, by rfl⟩ : syracuseStep 3364861 = 1261823) (by norm_num)
theorem B1497109 : Blo 1328983 1497109 := bbase (se 6 (by rfl) ⟨35088, by rfl⟩ : syracuseStep 1497109 = 70177) (by norm_num)
theorem B6387749 : Blo 1328983 6387749 := bbase (se 4 (by rfl) ⟨598851, by rfl⟩ : syracuseStep 6387749 = 1197703) (by norm_num)
theorem B2021429 : Blo 1328983 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B1497145 : Blo 1328983 1497145 := bbase (se 2 (by rfl) ⟨561429, by rfl⟩ : syracuseStep 1497145 = 1122859) (by norm_num)
theorem B4487237 : Blo 1328983 4487237 := bbase (se 4 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 4487237 = 841357) (by norm_num)
theorem B1497181 : Blo 1328983 1497181 := bbase (se 3 (by rfl) ⟨280721, by rfl⟩ : syracuseStep 1497181 = 561443) (by norm_num)
theorem B3364973 : Blo 1328983 3364973 := bbase (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) (by norm_num)
theorem B1497217 : Blo 1328983 1497217 := bbase (se 2 (by rfl) ⟨561456, by rfl⟩ : syracuseStep 1497217 = 1122913) (by norm_num)
theorem B6731909 : Blo 1328983 6731909 := bbase (se 4 (by rfl) ⟨631116, by rfl⟩ : syracuseStep 6731909 = 1262233) (by norm_num)
theorem B5462149 : Blo 1328983 5462149 := bbase (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) (by norm_num)
theorem B1620109 : Blo 1328983 1620109 := bbase (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) (by norm_num)
theorem B1497253 : Blo 1328983 1497253 := bbase (se 4 (by rfl) ⟨140367, by rfl⟩ : syracuseStep 1497253 = 280735) (by norm_num)
theorem B2242741 : Blo 1328983 2242741 := bbase (se 5 (by rfl) ⟨105128, by rfl⟩ : syracuseStep 2242741 = 210257) (by norm_num)
theorem B1497289 : Blo 1328983 1497289 := bbase (se 2 (by rfl) ⟨561483, by rfl⟩ : syracuseStep 1497289 = 1122967) (by norm_num)
theorem B2275565 : Blo 1328983 2275565 := bbase (se 3 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 2275565 = 853337) (by norm_num)
theorem B1497325 : Blo 1328983 1497325 := bbase (se 3 (by rfl) ⟨280748, by rfl⟩ : syracuseStep 1497325 = 561497) (by norm_num)
theorem B8091893 : Blo 1328983 8091893 := bbase (se 5 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 8091893 = 758615) (by norm_num)
theorem B2242829 : Blo 1328983 2242829 := bbase (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) (by norm_num)
theorem B2840845 : Blo 1328983 2840845 := bbase (se 3 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 2840845 = 1065317) (by norm_num)
theorem B3365165 : Blo 1328983 3365165 := bbase (se 3 (by rfl) ⟨630968, by rfl⟩ : syracuseStep 3365165 = 1261937) (by norm_num)
theorem B3594581 : Blo 1328983 3594581 := bbase (se 10 (by rfl) ⟨5265, by rfl⟩ : syracuseStep 3594581 = 10531) (by norm_num)
theorem B2242957 : Blo 1328983 2242957 := bbase (se 3 (by rfl) ⟨420554, by rfl⟩ : syracuseStep 2242957 = 841109) (by norm_num)
theorem B2243045 : Blo 1328983 2243045 := bbase (se 4 (by rfl) ⟨210285, by rfl⟩ : syracuseStep 2243045 = 420571) (by norm_num)
theorem B4487669 : Blo 1328983 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B3193357 : Blo 1328983 3193357 := bbase (se 3 (by rfl) ⟨598754, by rfl⟩ : syracuseStep 3193357 = 1197509) (by norm_num)
theorem B7191061 : Blo 1328983 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B6150725 : Blo 1328983 6150725 := bbase (se 4 (by rfl) ⟨576630, by rfl⟩ : syracuseStep 6150725 = 1153261) (by norm_num)
theorem B8518229 : Blo 1328983 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B2243173 : Blo 1328983 2243173 := bbase (se 4 (by rfl) ⟨210297, by rfl⟩ : syracuseStep 2243173 = 420595) (by norm_num)
theorem B3365509 : Blo 1328983 3365509 := bbase (se 4 (by rfl) ⟨315516, by rfl⟩ : syracuseStep 3365509 = 631033) (by norm_num)
theorem B5683877 : Blo 1328983 5683877 := bbase (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) (by norm_num)
theorem B2243261 : Blo 1328983 2243261 := bbase (se 3 (by rfl) ⟨420611, by rfl⟩ : syracuseStep 2243261 = 841223) (by norm_num)
theorem B3365621 : Blo 1328983 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B3595013 : Blo 1328983 3595013 := bbase (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) (by norm_num)
theorem B2243389 : Blo 1328983 2243389 := bbase (se 3 (by rfl) ⟨420635, by rfl⟩ : syracuseStep 2243389 = 841271) (by norm_num)
theorem B2243477 : Blo 1328983 2243477 := bbase (se 6 (by rfl) ⟨52581, by rfl⟩ : syracuseStep 2243477 = 105163) (by norm_num)
theorem B4488101 : Blo 1328983 4488101 := bbase (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) (by norm_num)
theorem B3365813 : Blo 1328983 3365813 := bbase (se 5 (by rfl) ⟨157772, by rfl⟩ : syracuseStep 3365813 = 315545) (by norm_num)
theorem B12139445 : Blo 1328983 12139445 := bbase (se 5 (by rfl) ⟨569036, by rfl⟩ : syracuseStep 12139445 = 1138073) (by norm_num)
theorem B4258757 : Blo 1328983 4258757 := bbase (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) (by norm_num)
theorem B2243605 : Blo 1328983 2243605 := bbase (se 6 (by rfl) ⟨52584, by rfl⟩ : syracuseStep 2243605 = 105169) (by norm_num)
theorem B2243693 : Blo 1328983 2243693 := bbase (se 3 (by rfl) ⟨420692, by rfl⟩ : syracuseStep 2243693 = 841385) (by norm_num)
theorem B2841733 : Blo 1328983 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B2243821 : Blo 1328983 2243821 := bbase (se 3 (by rfl) ⟨420716, by rfl⟩ : syracuseStep 2243821 = 841433) (by norm_num)
theorem B3366157 : Blo 1328983 3366157 := bbase (se 3 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 3366157 = 1262309) (by norm_num)
theorem B2243909 : Blo 1328983 2243909 := bbase (se 4 (by rfl) ⟨210366, by rfl⟩ : syracuseStep 2243909 = 420733) (by norm_num)
theorem B4488533 : Blo 1328983 4488533 := bbase (se 11 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 4488533 = 6575) (by norm_num)
theorem B3366269 : Blo 1328983 3366269 := bbase (se 3 (by rfl) ⟨631175, by rfl⟩ : syracuseStep 3366269 = 1262351) (by norm_num)
theorem B6733205 : Blo 1328983 6733205 := bbase (se 6 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 6733205 = 315619) (by norm_num)
theorem B2244037 : Blo 1328983 2244037 := bbase (se 4 (by rfl) ⟨210378, by rfl⟩ : syracuseStep 2244037 = 420757) (by norm_num)
theorem B2244125 : Blo 1328983 2244125 := bbase (se 3 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 2244125 = 841547) (by norm_num)
theorem B3366461 : Blo 1328983 3366461 := bbase (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) (by norm_num)
theorem B72818261 : Blo 1328983 72818261 := bbase (se 8 (by rfl) ⟨426669, by rfl⟩ : syracuseStep 72818261 = 853339) (by norm_num)
theorem B2842229 : Blo 1328983 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B2244253 : Blo 1328983 2244253 := bbase (se 3 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 2244253 = 841595) (by norm_num)
theorem B2244341 : Blo 1328983 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B4488965 : Blo 1328983 4488965 := bbase (se 4 (by rfl) ⟨420840, by rfl⟩ : syracuseStep 4488965 = 841681) (by norm_num)
theorem B6233861 : Blo 1328983 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B3194741 : Blo 1328983 3194741 := bbase (se 5 (by rfl) ⟨149753, by rfl⟩ : syracuseStep 3194741 = 299507) (by norm_num)
theorem B2244469 : Blo 1328983 2244469 := bbase (se 5 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 2244469 = 210419) (by norm_num)
theorem B2129789 : Blo 1328983 2129789 := bbase (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) (by norm_num)
theorem B2695045 : Blo 1328983 2695045 := bbase (se 4 (by rfl) ⟨252660, by rfl⟩ : syracuseStep 2695045 = 505321) (by norm_num)
theorem B2023309 : Blo 1328983 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B3366805 : Blo 1328983 3366805 := bbase (se 6 (by rfl) ⟨78909, by rfl⟩ : syracuseStep 3366805 = 157819) (by norm_num)
theorem B2244557 : Blo 1328983 2244557 := bbase (se 3 (by rfl) ⟨420854, by rfl⟩ : syracuseStep 2244557 = 841709) (by norm_num)
theorem B20742101 : Blo 1328983 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B5046245 : Blo 1328983 5046245 := bbase (se 4 (by rfl) ⟨473085, by rfl⟩ : syracuseStep 5046245 = 946171) (by norm_num)
theorem B6823925 : Blo 1328983 6823925 := bbase (se 5 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 6823925 = 639743) (by norm_num)
theorem B2244611 : Blo 1328983 2244611 := bstep (se 1 (by rfl) ⟨1683458, by rfl⟩ : syracuseStep 2244611 = 3366917) B3366917
theorem B3366947 : Blo 1328983 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B9592901 : Blo 1328983 9592901 := bstep (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) B1798669
theorem B2244739 : Blo 1328983 2244739 := bstep (se 1 (by rfl) ⟨1683554, by rfl⟩ : syracuseStep 2244739 = 3367109) B3367109
theorem B7192709 : Blo 1328983 7192709 := bstep (se 4 (by rfl) ⟨674316, by rfl⟩ : syracuseStep 7192709 = 1348633) B1348633
theorem B5390477 : Blo 1328983 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B7569571 : Blo 1328983 7569571 := bstep (se 1 (by rfl) ⟨5677178, by rfl⟩ : syracuseStep 7569571 = 11354357) B11354357
theorem B3784877 : Blo 1328983 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B7282865 : Blo 1328983 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B163758307 : Blo 1328983 163758307 := bstep (se 1 (by rfl) ⟨122818730, by rfl⟩ : syracuseStep 163758307 = 245637461) B245637461
theorem B2990321 : Blo 1328983 2990321 := bstep (se 2 (by rfl) ⟨1121370, by rfl⟩ : syracuseStep 2990321 = 2242741) B2242741
theorem B10125553 : Blo 1328983 10125553 := bstep (se 2 (by rfl) ⟨3797082, by rfl⟩ : syracuseStep 10125553 = 7594165) B7594165
theorem B2990339 : Blo 1328983 2990339 := bstep (se 1 (by rfl) ⟨2242754, by rfl⟩ : syracuseStep 2990339 = 4485509) B4485509
theorem B7184645 : Blo 1328983 7184645 := bstep (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) B1347121
theorem B2244881 : Blo 1328983 2244881 := bstep (se 2 (by rfl) ⟨841830, by rfl⟩ : syracuseStep 2244881 = 1683661) B1683661
theorem B5046563 : Blo 1328983 5046563 := bstep (se 1 (by rfl) ⟨3784922, by rfl⟩ : syracuseStep 5046563 = 7569845) B7569845
theorem B3785059 : Blo 1328983 3785059 := bstep (se 1 (by rfl) ⟨2838794, by rfl⟩ : syracuseStep 3785059 = 5677589) B5677589
theorem B2220419 : Blo 1328983 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B4489613 : Blo 1328983 4489613 := bstep (se 3 (by rfl) ⟨841802, by rfl⟩ : syracuseStep 4489613 = 1683605) B1683605
theorem B3785105 : Blo 1328983 3785105 := bstep (se 2 (by rfl) ⟨1419414, by rfl⟩ : syracuseStep 3785105 = 2838829) B2838829
theorem B2245009 : Blo 1328983 2245009 := bstep (se 2 (by rfl) ⟨841878, by rfl⟩ : syracuseStep 2245009 = 1683757) B1683757
theorem B4260269 : Blo 1328983 4260269 := bstep (se 3 (by rfl) ⟨798800, by rfl⟩ : syracuseStep 4260269 = 1597601) B1597601
theorem B7193009 : Blo 1328983 7193009 := bstep (se 2 (by rfl) ⟨2697378, by rfl⟩ : syracuseStep 7193009 = 5394757) B5394757
theorem B2245043 : Blo 1328983 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B1892803 : Blo 1328983 1892803 := bstep (se 1 (by rfl) ⟨1419602, by rfl⟩ : syracuseStep 1892803 = 2839205) B2839205
theorem B4489667 : Blo 1328983 4489667 := bstep (se 1 (by rfl) ⟨3367250, by rfl⟩ : syracuseStep 4489667 = 6734501) B6734501
theorem B3457507 : Blo 1328983 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B5390819 : Blo 1328983 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B5390833 : Blo 1328983 5390833 := bstep (se 2 (by rfl) ⟨2021562, by rfl⟩ : syracuseStep 5390833 = 4043125) B4043125
theorem B6914573 : Blo 1328983 6914573 := bstep (se 3 (by rfl) ⟨1296482, by rfl⟩ : syracuseStep 6914573 = 2592965) B2592965
theorem B2990609 : Blo 1328983 2990609 := bstep (se 2 (by rfl) ⟨1121478, by rfl⟩ : syracuseStep 2990609 = 2242957) B2242957
theorem B2990627 : Blo 1328983 2990627 := bstep (se 1 (by rfl) ⟨2242970, by rfl⟩ : syracuseStep 2990627 = 4485941) B4485941
theorem B4260397 : Blo 1328983 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B2245171 : Blo 1328983 2245171 := bstep (se 1 (by rfl) ⟨1683878, by rfl⟩ : syracuseStep 2245171 = 3367757) B3367757
theorem B72811061 : Blo 1328983 72811061 := bstep (se 5 (by rfl) ⟨3413018, by rfl⟩ : syracuseStep 72811061 = 6826037) B6826037
theorem B2130545 : Blo 1328983 2130545 := bstep (se 2 (by rfl) ⟨798954, by rfl⟩ : syracuseStep 2130545 = 1597909) B1597909
theorem B7570097 : Blo 1328983 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B2245313 : Blo 1328983 2245313 := bstep (se 2 (by rfl) ⟨841992, by rfl⟩ : syracuseStep 2245313 = 1683985) B1683985
theorem B3195587 : Blo 1328983 3195587 := bstep (se 1 (by rfl) ⟨2396690, by rfl⟩ : syracuseStep 3195587 = 4793381) B4793381
theorem B15155909 : Blo 1328983 15155909 := bstep (se 4 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 15155909 = 2841733) B2841733
theorem B4489937 : Blo 1328983 4489937 := bstep (se 2 (by rfl) ⟨1683726, by rfl⟩ : syracuseStep 4489937 = 3367453) B3367453
theorem B1950419 : Blo 1328983 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B2523889 : Blo 1328983 2523889 := bstep (se 2 (by rfl) ⟨946458, by rfl⟩ : syracuseStep 2523889 = 1892917) B1892917
theorem B8520461 : Blo 1328983 8520461 := bstep (se 3 (by rfl) ⟨1597586, by rfl⟩ : syracuseStep 8520461 = 3195173) B3195173
theorem B16188173 : Blo 1328983 16188173 := bstep (se 3 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 16188173 = 6070565) B6070565
theorem B3195683 : Blo 1328983 3195683 := bstep (se 1 (by rfl) ⟨2396762, by rfl⟩ : syracuseStep 3195683 = 4793525) B4793525
theorem B4260653 : Blo 1328983 4260653 := bstep (se 3 (by rfl) ⟨798872, by rfl⟩ : syracuseStep 4260653 = 1597745) B1597745
theorem B2990897 : Blo 1328983 2990897 := bstep (se 2 (by rfl) ⟨1121586, by rfl⟩ : syracuseStep 2990897 = 2243173) B2243173
theorem B2245441 : Blo 1328983 2245441 := bstep (se 2 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 2245441 = 1684081) B1684081
theorem B2990915 : Blo 1328983 2990915 := bstep (se 1 (by rfl) ⟨2243186, by rfl⟩ : syracuseStep 2990915 = 4486373) B4486373
theorem B2245475 : Blo 1328983 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B2130833 : Blo 1328983 2130833 := bstep (se 2 (by rfl) ⟨799062, by rfl⟩ : syracuseStep 2130833 = 1598125) B1598125
theorem B5047217 : Blo 1328983 5047217 := bstep (se 2 (by rfl) ⟨1892706, by rfl⟩ : syracuseStep 5047217 = 3785413) B3785413
theorem B3367889 : Blo 1328983 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B2245603 : Blo 1328983 2245603 := bstep (se 1 (by rfl) ⟨1684202, by rfl⟩ : syracuseStep 2245603 = 3368405) B3368405
theorem B8520689 : Blo 1328983 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B3367939 : Blo 1328983 3367939 := bstep (se 1 (by rfl) ⟨2525954, by rfl⟩ : syracuseStep 3367939 = 5051909) B5051909
theorem B2991185 : Blo 1328983 2991185 := bstep (se 2 (by rfl) ⟨1121694, by rfl⟩ : syracuseStep 2991185 = 2243389) B2243389
theorem B2991203 : Blo 1328983 2991203 := bstep (se 1 (by rfl) ⟨2243402, by rfl⟩ : syracuseStep 2991203 = 4486805) B4486805
theorem B2131057 : Blo 1328983 2131057 := bstep (se 2 (by rfl) ⟨799146, by rfl⟩ : syracuseStep 2131057 = 1598293) B1598293
theorem B2245745 : Blo 1328983 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B3368081 : Blo 1328983 3368081 := bstep (se 2 (by rfl) ⟨1263030, by rfl⟩ : syracuseStep 3368081 = 2526061) B2526061
theorem B4490477 : Blo 1328983 4490477 := bstep (se 3 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 4490477 = 1683929) B1683929
theorem B2245873 : Blo 1328983 2245873 := bstep (se 2 (by rfl) ⟨842202, by rfl⟩ : syracuseStep 2245873 = 1684405) B1684405
theorem B2245907 : Blo 1328983 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B4490531 : Blo 1328983 4490531 := bstep (se 1 (by rfl) ⟨3367898, by rfl⟩ : syracuseStep 4490531 = 6735797) B6735797
theorem B2991473 : Blo 1328983 2991473 := bstep (se 2 (by rfl) ⟨1121802, by rfl⟩ : syracuseStep 2991473 = 2243605) B2243605
theorem B2991491 : Blo 1328983 2991491 := bstep (se 1 (by rfl) ⟨2243618, by rfl⟩ : syracuseStep 2991491 = 4487237) B4487237
theorem B2246035 : Blo 1328983 2246035 := bstep (se 1 (by rfl) ⟨1684526, by rfl⟩ : syracuseStep 2246035 = 3369053) B3369053
theorem B1893937 : Blo 1328983 1893937 := bstep (se 2 (by rfl) ⟨710226, by rfl⟩ : syracuseStep 1893937 = 1420453) B1420453
theorem B4490801 : Blo 1328983 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B3196529 : Blo 1328983 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B6735473 : Blo 1328983 6735473 := bstep (se 2 (by rfl) ⟨2525802, by rfl⟩ : syracuseStep 6735473 = 5051605) B5051605
theorem B7579277 : Blo 1328983 7579277 := bstep (se 3 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 7579277 = 2842229) B2842229
theorem B2991761 : Blo 1328983 2991761 := bstep (se 2 (by rfl) ⟨1121910, by rfl⟩ : syracuseStep 2991761 = 2243821) B2243821
theorem B1894033 : Blo 1328983 1894033 := bstep (se 2 (by rfl) ⟨710262, by rfl⟩ : syracuseStep 1894033 = 1420525) B1420525
theorem B2991779 : Blo 1328983 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B5678819 : Blo 1328983 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B2524945 : Blo 1328983 2524945 := bstep (se 2 (by rfl) ⟨946854, by rfl⟩ : syracuseStep 2524945 = 1893709) B1893709
theorem B5392163 : Blo 1328983 5392163 := bstep (se 1 (by rfl) ⟨4044122, by rfl⟩ : syracuseStep 5392163 = 8088245) B8088245
theorem B3786563 : Blo 1328983 3786563 := bstep (se 1 (by rfl) ⟨2839922, by rfl⟩ : syracuseStep 3786563 = 5679845) B5679845
theorem B1328995 : Blo 1328983 1328995 := bstep (se 1 (by rfl) ⟨996746, by rfl⟩ : syracuseStep 1328995 = 1993493) B1993493
theorem B1329011 : Blo 1328983 1329011 := bstep (se 1 (by rfl) ⟨996758, by rfl⟩ : syracuseStep 1329011 = 1993517) B1993517
theorem B1329027 : Blo 1328983 1329027 := bstep (se 1 (by rfl) ⟨996770, by rfl⟩ : syracuseStep 1329027 = 1993541) B1993541
theorem B3196817 : Blo 1328983 3196817 := bstep (se 2 (by rfl) ⟨1198806, by rfl⟩ : syracuseStep 3196817 = 2397613) B2397613
theorem B1329043 : Blo 1328983 1329043 := bstep (se 1 (by rfl) ⟨996782, by rfl⟩ : syracuseStep 1329043 = 1993565) B1993565
theorem B1329059 : Blo 1328983 1329059 := bstep (se 1 (by rfl) ⟨996794, by rfl⟩ : syracuseStep 1329059 = 1993589) B1993589
theorem B2992049 : Blo 1328983 2992049 := bstep (se 2 (by rfl) ⟨1122018, by rfl⟩ : syracuseStep 2992049 = 2244037) B2244037
theorem B1329075 : Blo 1328983 1329075 := bstep (se 1 (by rfl) ⟨996806, by rfl⟩ : syracuseStep 1329075 = 1993613) B1993613
theorem B1329091 : Blo 1328983 1329091 := bstep (se 1 (by rfl) ⟨996818, by rfl⟩ : syracuseStep 1329091 = 1993637) B1993637
theorem B2992067 : Blo 1328983 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B1329107 : Blo 1328983 1329107 := bstep (se 1 (by rfl) ⟨996830, by rfl⟩ : syracuseStep 1329107 = 1993661) B1993661
theorem B1329123 : Blo 1328983 1329123 := bstep (se 1 (by rfl) ⟨996842, by rfl⟩ : syracuseStep 1329123 = 1993685) B1993685
theorem B1329139 : Blo 1328983 1329139 := bstep (se 1 (by rfl) ⟨996854, by rfl⟩ : syracuseStep 1329139 = 1993709) B1993709
theorem B1329155 : Blo 1328983 1329155 := bstep (se 1 (by rfl) ⟨996866, by rfl⟩ : syracuseStep 1329155 = 1993733) B1993733
theorem B1329171 : Blo 1328983 1329171 := bstep (se 1 (by rfl) ⟨996878, by rfl⟩ : syracuseStep 1329171 = 1993757) B1993757
theorem B1329187 : Blo 1328983 1329187 := bstep (se 1 (by rfl) ⟨996890, by rfl⟩ : syracuseStep 1329187 = 1993781) B1993781
theorem B1329203 : Blo 1328983 1329203 := bstep (se 1 (by rfl) ⟨996902, by rfl⟩ : syracuseStep 1329203 = 1993805) B1993805
theorem B1329219 : Blo 1328983 1329219 := bstep (se 1 (by rfl) ⟨996914, by rfl⟩ : syracuseStep 1329219 = 1993829) B1993829
theorem B4491341 : Blo 1328983 4491341 := bstep (se 3 (by rfl) ⟨842126, by rfl⟩ : syracuseStep 4491341 = 1684253) B1684253
theorem B1329235 : Blo 1328983 1329235 := bstep (se 1 (by rfl) ⟨996926, by rfl⟩ : syracuseStep 1329235 = 1993853) B1993853
theorem B1329251 : Blo 1328983 1329251 := bstep (se 1 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 1329251 = 1993877) B1993877
theorem B7571555 : Blo 1328983 7571555 := bstep (se 1 (by rfl) ⟨5678666, by rfl⟩ : syracuseStep 7571555 = 11357333) B11357333
theorem B3197027 : Blo 1328983 3197027 := bstep (se 1 (by rfl) ⟨2397770, by rfl⟩ : syracuseStep 3197027 = 4795541) B4795541
theorem B3000419 : Blo 1328983 3000419 := bstep (se 1 (by rfl) ⟨2250314, by rfl⟩ : syracuseStep 3000419 = 4500629) B4500629
theorem B10094705 : Blo 1328983 10094705 := bstep (se 2 (by rfl) ⟨3785514, by rfl⟩ : syracuseStep 10094705 = 7571029) B7571029
theorem B1329267 : Blo 1328983 1329267 := bstep (se 1 (by rfl) ⟨996950, by rfl⟩ : syracuseStep 1329267 = 1993901) B1993901
theorem B1894529 : Blo 1328983 1894529 := bstep (se 2 (by rfl) ⟨710448, by rfl⟩ : syracuseStep 1894529 = 1420897) B1420897
theorem B1329283 : Blo 1328983 1329283 := bstep (se 1 (by rfl) ⟨996962, by rfl⟩ : syracuseStep 1329283 = 1993925) B1993925
theorem B4491395 : Blo 1328983 4491395 := bstep (se 1 (by rfl) ⟨3368546, by rfl⟩ : syracuseStep 4491395 = 6737093) B6737093
theorem B1329299 : Blo 1328983 1329299 := bstep (se 1 (by rfl) ⟨996974, by rfl⟩ : syracuseStep 1329299 = 1993949) B1993949
theorem B1329315 : Blo 1328983 1329315 := bstep (se 1 (by rfl) ⟨996986, by rfl⟩ : syracuseStep 1329315 = 1993973) B1993973
theorem B2525347 : Blo 1328983 2525347 := bstep (se 1 (by rfl) ⟨1894010, by rfl⟩ : syracuseStep 2525347 = 3788021) B3788021
theorem B1329331 : Blo 1328983 1329331 := bstep (se 1 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 1329331 = 1993997) B1993997
theorem B1329347 : Blo 1328983 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B2992337 : Blo 1328983 2992337 := bstep (se 2 (by rfl) ⟨1122126, by rfl⟩ : syracuseStep 2992337 = 2244253) B2244253
theorem B2525393 : Blo 1328983 2525393 := bstep (se 2 (by rfl) ⟨947022, by rfl⟩ : syracuseStep 2525393 = 1894045) B1894045
theorem B1329363 : Blo 1328983 1329363 := bstep (se 1 (by rfl) ⟨997022, by rfl⟩ : syracuseStep 1329363 = 1994045) B1994045
theorem B1329379 : Blo 1328983 1329379 := bstep (se 1 (by rfl) ⟨997034, by rfl⟩ : syracuseStep 1329379 = 1994069) B1994069
theorem B2992355 : Blo 1328983 2992355 := bstep (se 1 (by rfl) ⟨2244266, by rfl⟩ : syracuseStep 2992355 = 4488533) B4488533
theorem B1329395 : Blo 1328983 1329395 := bstep (se 1 (by rfl) ⟨997046, by rfl⟩ : syracuseStep 1329395 = 1994093) B1994093
theorem B1329411 : Blo 1328983 1329411 := bstep (se 1 (by rfl) ⟨997058, by rfl⟩ : syracuseStep 1329411 = 1994117) B1994117
theorem B1329427 : Blo 1328983 1329427 := bstep (se 1 (by rfl) ⟨997070, by rfl⟩ : syracuseStep 1329427 = 1994141) B1994141
theorem B1329443 : Blo 1328983 1329443 := bstep (se 1 (by rfl) ⟨997082, by rfl⟩ : syracuseStep 1329443 = 1994165) B1994165
theorem B4262179 : Blo 1328983 4262179 := bstep (se 1 (by rfl) ⟨3196634, by rfl⟩ : syracuseStep 4262179 = 6393269) B6393269
theorem B6064433 : Blo 1328983 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B1329459 : Blo 1328983 1329459 := bstep (se 1 (by rfl) ⟨997094, by rfl⟩ : syracuseStep 1329459 = 1994189) B1994189
theorem B1329475 : Blo 1328983 1329475 := bstep (se 1 (by rfl) ⟨997106, by rfl⟩ : syracuseStep 1329475 = 1994213) B1994213
theorem B1329491 : Blo 1328983 1329491 := bstep (se 1 (by rfl) ⟨997118, by rfl⟩ : syracuseStep 1329491 = 1994237) B1994237
theorem B1329507 : Blo 1328983 1329507 := bstep (se 1 (by rfl) ⟨997130, by rfl⟩ : syracuseStep 1329507 = 1994261) B1994261
theorem B5048675 : Blo 1328983 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B5048689 : Blo 1328983 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B1329523 : Blo 1328983 1329523 := bstep (se 1 (by rfl) ⟨997142, by rfl⟩ : syracuseStep 1329523 = 1994285) B1994285
theorem B1329539 : Blo 1328983 1329539 := bstep (se 1 (by rfl) ⟨997154, by rfl⟩ : syracuseStep 1329539 = 1994309) B1994309
theorem B4491665 : Blo 1328983 4491665 := bstep (se 2 (by rfl) ⟨1684374, by rfl⟩ : syracuseStep 4491665 = 3368749) B3368749
theorem B1329555 : Blo 1328983 1329555 := bstep (se 1 (by rfl) ⟨997166, by rfl⟩ : syracuseStep 1329555 = 1994333) B1994333
theorem B1329571 : Blo 1328983 1329571 := bstep (se 1 (by rfl) ⟨997178, by rfl⟩ : syracuseStep 1329571 = 1994357) B1994357
theorem B1329587 : Blo 1328983 1329587 := bstep (se 1 (by rfl) ⟨997190, by rfl⟩ : syracuseStep 1329587 = 1994381) B1994381
theorem B1329603 : Blo 1328983 1329603 := bstep (se 1 (by rfl) ⟨997202, by rfl⟩ : syracuseStep 1329603 = 1994405) B1994405
theorem B1329619 : Blo 1328983 1329619 := bstep (se 1 (by rfl) ⟨997214, by rfl⟩ : syracuseStep 1329619 = 1994429) B1994429
theorem B1329635 : Blo 1328983 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B2992625 : Blo 1328983 2992625 := bstep (se 2 (by rfl) ⟨1122234, by rfl⟩ : syracuseStep 2992625 = 2244469) B2244469
theorem B2525681 : Blo 1328983 2525681 := bstep (se 2 (by rfl) ⟨947130, by rfl⟩ : syracuseStep 2525681 = 1894261) B1894261
theorem B1329651 : Blo 1328983 1329651 := bstep (se 1 (by rfl) ⟨997238, by rfl⟩ : syracuseStep 1329651 = 1994477) B1994477
theorem B1329667 : Blo 1328983 1329667 := bstep (se 1 (by rfl) ⟨997250, by rfl⟩ : syracuseStep 1329667 = 1994501) B1994501
theorem B2992643 : Blo 1328983 2992643 := bstep (se 1 (by rfl) ⟨2244482, by rfl⟩ : syracuseStep 2992643 = 4488965) B4488965
theorem B4155907 : Blo 1328983 4155907 := bstep (se 1 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 4155907 = 6233861) B6233861
theorem B2697745 : Blo 1328983 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B1329683 : Blo 1328983 1329683 := bstep (se 1 (by rfl) ⟨997262, by rfl⟩ : syracuseStep 1329683 = 1994525) B1994525
theorem B6474275 : Blo 1328983 6474275 := bstep (se 1 (by rfl) ⟨4855706, by rfl⟩ : syracuseStep 6474275 = 9711413) B9711413
theorem B1329699 : Blo 1328983 1329699 := bstep (se 1 (by rfl) ⟨997274, by rfl⟩ : syracuseStep 1329699 = 1994549) B1994549
theorem B1329715 : Blo 1328983 1329715 := bstep (se 1 (by rfl) ⟨997286, by rfl⟩ : syracuseStep 1329715 = 1994573) B1994573
theorem B1329731 : Blo 1328983 1329731 := bstep (se 1 (by rfl) ⟨997298, by rfl⟩ : syracuseStep 1329731 = 1994597) B1994597
theorem B7195213 : Blo 1328983 7195213 := bstep (se 3 (by rfl) ⟨1349102, by rfl⟩ : syracuseStep 7195213 = 2698205) B2698205
theorem B1419859 : Blo 1328983 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B1329747 : Blo 1328983 1329747 := bstep (se 1 (by rfl) ⟨997310, by rfl⟩ : syracuseStep 1329747 = 1994621) B1994621
theorem B1329763 : Blo 1328983 1329763 := bstep (se 1 (by rfl) ⟨997322, by rfl⟩ : syracuseStep 1329763 = 1994645) B1994645
theorem B4549229 : Blo 1328983 4549229 := bstep (se 3 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 4549229 = 1705961) B1705961
theorem B1329779 : Blo 1328983 1329779 := bstep (se 1 (by rfl) ⟨997334, by rfl⟩ : syracuseStep 1329779 = 1994669) B1994669
theorem B1329795 : Blo 1328983 1329795 := bstep (se 1 (by rfl) ⟨997346, by rfl⟩ : syracuseStep 1329795 = 1994693) B1994693
theorem B1329811 : Blo 1328983 1329811 := bstep (se 1 (by rfl) ⟨997358, by rfl⟩ : syracuseStep 1329811 = 1994717) B1994717
theorem B4549283 : Blo 1328983 4549283 := bstep (se 1 (by rfl) ⟨3411962, by rfl⟩ : syracuseStep 4549283 = 6823925) B6823925
theorem B1329827 : Blo 1328983 1329827 := bstep (se 1 (by rfl) ⟨997370, by rfl⟩ : syracuseStep 1329827 = 1994741) B1994741
theorem B1329843 : Blo 1328983 1329843 := bstep (se 1 (by rfl) ⟨997382, by rfl⟩ : syracuseStep 1329843 = 1994765) B1994765
theorem B1329859 : Blo 1328983 1329859 := bstep (se 1 (by rfl) ⟨997394, by rfl⟩ : syracuseStep 1329859 = 1994789) B1994789
theorem B1329875 : Blo 1328983 1329875 := bstep (se 1 (by rfl) ⟨997406, by rfl⟩ : syracuseStep 1329875 = 1994813) B1994813
theorem B1682147 : Blo 1328983 1682147 := bstep (se 1 (by rfl) ⟨1261610, by rfl⟩ : syracuseStep 1682147 = 2523221) B2523221
theorem B1329891 : Blo 1328983 1329891 := bstep (se 1 (by rfl) ⟨997418, by rfl⟩ : syracuseStep 1329891 = 1994837) B1994837
theorem B1329907 : Blo 1328983 1329907 := bstep (se 1 (by rfl) ⟨997430, by rfl⟩ : syracuseStep 1329907 = 1994861) B1994861
theorem B1993475 : Blo 1328983 1993475 := bstep (se 1 (by rfl) ⟨1495106, by rfl⟩ : syracuseStep 1993475 = 2990213) B2990213
theorem B1329923 : Blo 1328983 1329923 := bstep (se 1 (by rfl) ⟨997442, by rfl⟩ : syracuseStep 1329923 = 1994885) B1994885
theorem B7383821 : Blo 1328983 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B2992913 : Blo 1328983 2992913 := bstep (se 2 (by rfl) ⟨1122342, by rfl⟩ : syracuseStep 2992913 = 2244685) B2244685
theorem B1329939 : Blo 1328983 1329939 := bstep (se 1 (by rfl) ⟨997454, by rfl⟩ : syracuseStep 1329939 = 1994909) B1994909
theorem B1993505 : Blo 1328983 1993505 := bstep (se 2 (by rfl) ⟨747564, by rfl⟩ : syracuseStep 1993505 = 1495129) B1495129
theorem B1329955 : Blo 1328983 1329955 := bstep (se 1 (by rfl) ⟨997466, by rfl⟩ : syracuseStep 1329955 = 1994933) B1994933
theorem B2992931 : Blo 1328983 2992931 := bstep (se 1 (by rfl) ⟨2244698, by rfl⟩ : syracuseStep 2992931 = 4489397) B4489397
theorem B1993523 : Blo 1328983 1993523 := bstep (se 1 (by rfl) ⟨1495142, by rfl⟩ : syracuseStep 1993523 = 2990285) B2990285
theorem B1329971 : Blo 1328983 1329971 := bstep (se 1 (by rfl) ⟨997478, by rfl⟩ : syracuseStep 1329971 = 1994957) B1994957
theorem B1329987 : Blo 1328983 1329987 := bstep (se 1 (by rfl) ⟨997490, by rfl⟩ : syracuseStep 1329987 = 1994981) B1994981
theorem B1993553 : Blo 1328983 1993553 := bstep (se 2 (by rfl) ⟨747582, by rfl⟩ : syracuseStep 1993553 = 1495165) B1495165
theorem B1330003 : Blo 1328983 1330003 := bstep (se 1 (by rfl) ⟨997502, by rfl⟩ : syracuseStep 1330003 = 1995005) B1995005
theorem B1993571 : Blo 1328983 1993571 := bstep (se 1 (by rfl) ⟨1495178, by rfl⟩ : syracuseStep 1993571 = 2990357) B2990357
theorem B1330019 : Blo 1328983 1330019 := bstep (se 1 (by rfl) ⟨997514, by rfl⟩ : syracuseStep 1330019 = 1995029) B1995029
theorem B1330035 : Blo 1328983 1330035 := bstep (se 1 (by rfl) ⟨997526, by rfl⟩ : syracuseStep 1330035 = 1995053) B1995053
theorem B1993601 : Blo 1328983 1993601 := bstep (se 2 (by rfl) ⟨747600, by rfl⟩ : syracuseStep 1993601 = 1495201) B1495201
theorem B1330051 : Blo 1328983 1330051 := bstep (se 1 (by rfl) ⟨997538, by rfl⟩ : syracuseStep 1330051 = 1995077) B1995077
theorem B1993619 : Blo 1328983 1993619 := bstep (se 1 (by rfl) ⟨1495214, by rfl⟩ : syracuseStep 1993619 = 2990429) B2990429
theorem B1330067 : Blo 1328983 1330067 := bstep (se 1 (by rfl) ⟨997550, by rfl⟩ : syracuseStep 1330067 = 1995101) B1995101
theorem B1330083 : Blo 1328983 1330083 := bstep (se 1 (by rfl) ⟨997562, by rfl⟩ : syracuseStep 1330083 = 1995125) B1995125
theorem B1993649 : Blo 1328983 1993649 := bstep (se 2 (by rfl) ⟨747618, by rfl⟩ : syracuseStep 1993649 = 1495237) B1495237
theorem B1330099 : Blo 1328983 1330099 := bstep (se 1 (by rfl) ⟨997574, by rfl⟩ : syracuseStep 1330099 = 1995149) B1995149
theorem B1993667 : Blo 1328983 1993667 := bstep (se 1 (by rfl) ⟨1495250, by rfl⟩ : syracuseStep 1993667 = 2990501) B2990501
theorem B1330115 : Blo 1328983 1330115 := bstep (se 1 (by rfl) ⟨997586, by rfl⟩ : syracuseStep 1330115 = 1995173) B1995173
theorem B1330131 : Blo 1328983 1330131 := bstep (se 1 (by rfl) ⟨997598, by rfl⟩ : syracuseStep 1330131 = 1995197) B1995197
theorem B1993697 : Blo 1328983 1993697 := bstep (se 2 (by rfl) ⟨747636, by rfl⟩ : syracuseStep 1993697 = 1495273) B1495273
theorem B1330147 : Blo 1328983 1330147 := bstep (se 1 (by rfl) ⟨997610, by rfl⟩ : syracuseStep 1330147 = 1995221) B1995221
theorem B1993715 : Blo 1328983 1993715 := bstep (se 1 (by rfl) ⟨1495286, by rfl⟩ : syracuseStep 1993715 = 2990573) B2990573
theorem B1330163 : Blo 1328983 1330163 := bstep (se 1 (by rfl) ⟨997622, by rfl⟩ : syracuseStep 1330163 = 1995245) B1995245
theorem B1330179 : Blo 1328983 1330179 := bstep (se 1 (by rfl) ⟨997634, by rfl⟩ : syracuseStep 1330179 = 1995269) B1995269
theorem B1993745 : Blo 1328983 1993745 := bstep (se 2 (by rfl) ⟨747654, by rfl⟩ : syracuseStep 1993745 = 1495309) B1495309
theorem B3787793 : Blo 1328983 3787793 := bstep (se 2 (by rfl) ⟨1420422, by rfl⟩ : syracuseStep 3787793 = 2840845) B2840845
theorem B1330195 : Blo 1328983 1330195 := bstep (se 1 (by rfl) ⟨997646, by rfl⟩ : syracuseStep 1330195 = 1995293) B1995293
theorem B1993763 : Blo 1328983 1993763 := bstep (se 1 (by rfl) ⟨1495322, by rfl⟩ : syracuseStep 1993763 = 2990645) B2990645
theorem B1330211 : Blo 1328983 1330211 := bstep (se 1 (by rfl) ⟨997658, by rfl⟩ : syracuseStep 1330211 = 1995317) B1995317
theorem B6736931 : Blo 1328983 6736931 := bstep (se 1 (by rfl) ⟨5052698, by rfl⟩ : syracuseStep 6736931 = 10105397) B10105397
theorem B2993201 : Blo 1328983 2993201 := bstep (se 2 (by rfl) ⟨1122450, by rfl⟩ : syracuseStep 2993201 = 2244901) B2244901
theorem B1330227 : Blo 1328983 1330227 := bstep (se 1 (by rfl) ⟨997670, by rfl⟩ : syracuseStep 1330227 = 1995341) B1995341
theorem B1993793 : Blo 1328983 1993793 := bstep (se 2 (by rfl) ⟨747672, by rfl⟩ : syracuseStep 1993793 = 1495345) B1495345
theorem B1330243 : Blo 1328983 1330243 := bstep (se 1 (by rfl) ⟨997682, by rfl⟩ : syracuseStep 1330243 = 1995365) B1995365
theorem B2993219 : Blo 1328983 2993219 := bstep (se 1 (by rfl) ⟨2244914, by rfl⟩ : syracuseStep 2993219 = 4489829) B4489829
theorem B4549709 : Blo 1328983 4549709 := bstep (se 3 (by rfl) ⟨853070, by rfl⟩ : syracuseStep 4549709 = 1706141) B1706141
theorem B1993811 : Blo 1328983 1993811 := bstep (se 1 (by rfl) ⟨1495358, by rfl⟩ : syracuseStep 1993811 = 2990717) B2990717
theorem B1330259 : Blo 1328983 1330259 := bstep (se 1 (by rfl) ⟨997694, by rfl⟩ : syracuseStep 1330259 = 1995389) B1995389
theorem B1330275 : Blo 1328983 1330275 := bstep (se 1 (by rfl) ⟨997706, by rfl⟩ : syracuseStep 1330275 = 1995413) B1995413
theorem B1993841 : Blo 1328983 1993841 := bstep (se 2 (by rfl) ⟨747690, by rfl⟩ : syracuseStep 1993841 = 1495381) B1495381
theorem B1330291 : Blo 1328983 1330291 := bstep (se 1 (by rfl) ⟨997718, by rfl⟩ : syracuseStep 1330291 = 1995437) B1995437
theorem B1993859 : Blo 1328983 1993859 := bstep (se 1 (by rfl) ⟨1495394, by rfl⟩ : syracuseStep 1993859 = 2990789) B2990789
theorem B1330307 : Blo 1328983 1330307 := bstep (se 1 (by rfl) ⟨997730, by rfl⟩ : syracuseStep 1330307 = 1995461) B1995461
theorem B1330323 : Blo 1328983 1330323 := bstep (se 1 (by rfl) ⟨997742, by rfl⟩ : syracuseStep 1330323 = 1995485) B1995485
theorem B1993889 : Blo 1328983 1993889 := bstep (se 2 (by rfl) ⟨747708, by rfl⟩ : syracuseStep 1993889 = 1495417) B1495417
theorem B1330339 : Blo 1328983 1330339 := bstep (se 1 (by rfl) ⟨997754, by rfl⟩ : syracuseStep 1330339 = 1995509) B1995509
theorem B1993907 : Blo 1328983 1993907 := bstep (se 1 (by rfl) ⟨1495430, by rfl⟩ : syracuseStep 1993907 = 2990861) B2990861
theorem B1330355 : Blo 1328983 1330355 := bstep (se 1 (by rfl) ⟨997766, by rfl⟩ : syracuseStep 1330355 = 1995533) B1995533
theorem B1330371 : Blo 1328983 1330371 := bstep (se 1 (by rfl) ⟨997778, by rfl⟩ : syracuseStep 1330371 = 1995557) B1995557
theorem B2526403 : Blo 1328983 2526403 := bstep (se 1 (by rfl) ⟨1894802, by rfl⟩ : syracuseStep 2526403 = 3789605) B3789605
theorem B1993937 : Blo 1328983 1993937 := bstep (se 2 (by rfl) ⟨747726, by rfl⟩ : syracuseStep 1993937 = 1495453) B1495453
theorem B1330387 : Blo 1328983 1330387 := bstep (se 1 (by rfl) ⟨997790, by rfl⟩ : syracuseStep 1330387 = 1995581) B1995581
theorem B1993955 : Blo 1328983 1993955 := bstep (se 1 (by rfl) ⟨1495466, by rfl⟩ : syracuseStep 1993955 = 2990933) B2990933
theorem B1330403 : Blo 1328983 1330403 := bstep (se 1 (by rfl) ⟨997802, by rfl⟩ : syracuseStep 1330403 = 1995605) B1995605
theorem B1330419 : Blo 1328983 1330419 := bstep (se 1 (by rfl) ⟨997814, by rfl⟩ : syracuseStep 1330419 = 1995629) B1995629
theorem B1993985 : Blo 1328983 1993985 := bstep (se 2 (by rfl) ⟨747744, by rfl⟩ : syracuseStep 1993985 = 1495489) B1495489
theorem B1330435 : Blo 1328983 1330435 := bstep (se 1 (by rfl) ⟨997826, by rfl⟩ : syracuseStep 1330435 = 1995653) B1995653
theorem B1994003 : Blo 1328983 1994003 := bstep (se 1 (by rfl) ⟨1495502, by rfl⟩ : syracuseStep 1994003 = 2991005) B2991005
theorem B1330451 : Blo 1328983 1330451 := bstep (se 1 (by rfl) ⟨997838, by rfl⟩ : syracuseStep 1330451 = 1995677) B1995677
theorem B1330467 : Blo 1328983 1330467 := bstep (se 1 (by rfl) ⟨997850, by rfl⟩ : syracuseStep 1330467 = 1995701) B1995701
theorem B1994033 : Blo 1328983 1994033 := bstep (se 2 (by rfl) ⟨747762, by rfl⟩ : syracuseStep 1994033 = 1495525) B1495525
theorem B1330483 : Blo 1328983 1330483 := bstep (se 1 (by rfl) ⟨997862, by rfl⟩ : syracuseStep 1330483 = 1995725) B1995725
theorem B1994051 : Blo 1328983 1994051 := bstep (se 1 (by rfl) ⟨1495538, by rfl⟩ : syracuseStep 1994051 = 2991077) B2991077
theorem B1330499 : Blo 1328983 1330499 := bstep (se 1 (by rfl) ⟨997874, by rfl⟩ : syracuseStep 1330499 = 1995749) B1995749
theorem B2993489 : Blo 1328983 2993489 := bstep (se 2 (by rfl) ⟨1122558, by rfl⟩ : syracuseStep 2993489 = 2245117) B2245117
theorem B1330515 : Blo 1328983 1330515 := bstep (se 1 (by rfl) ⟨997886, by rfl⟩ : syracuseStep 1330515 = 1995773) B1995773
theorem B1994081 : Blo 1328983 1994081 := bstep (se 2 (by rfl) ⟨747780, by rfl⟩ : syracuseStep 1994081 = 1495561) B1495561
theorem B2993507 : Blo 1328983 2993507 := bstep (se 1 (by rfl) ⟨2245130, by rfl⟩ : syracuseStep 2993507 = 4490261) B4490261
theorem B1330531 : Blo 1328983 1330531 := bstep (se 1 (by rfl) ⟨997898, by rfl⟩ : syracuseStep 1330531 = 1995797) B1995797
theorem B1994099 : Blo 1328983 1994099 := bstep (se 1 (by rfl) ⟨1495574, by rfl⟩ : syracuseStep 1994099 = 2991149) B2991149
theorem B1330547 : Blo 1328983 1330547 := bstep (se 1 (by rfl) ⟨997910, by rfl⟩ : syracuseStep 1330547 = 1995821) B1995821
theorem B1330563 : Blo 1328983 1330563 := bstep (se 1 (by rfl) ⟨997922, by rfl⟩ : syracuseStep 1330563 = 1995845) B1995845
theorem B1994129 : Blo 1328983 1994129 := bstep (se 2 (by rfl) ⟨747798, by rfl⟩ : syracuseStep 1994129 = 1495597) B1495597
theorem B1330579 : Blo 1328983 1330579 := bstep (se 1 (by rfl) ⟨997934, by rfl⟩ : syracuseStep 1330579 = 1995869) B1995869
theorem B1994147 : Blo 1328983 1994147 := bstep (se 1 (by rfl) ⟨1495610, by rfl⟩ : syracuseStep 1994147 = 2991221) B2991221
theorem B1682851 : Blo 1328983 1682851 := bstep (se 1 (by rfl) ⟨1262138, by rfl⟩ : syracuseStep 1682851 = 2524277) B2524277
theorem B1330595 : Blo 1328983 1330595 := bstep (se 1 (by rfl) ⟨997946, by rfl⟩ : syracuseStep 1330595 = 1995893) B1995893
theorem B1330611 : Blo 1328983 1330611 := bstep (se 1 (by rfl) ⟨997958, by rfl⟩ : syracuseStep 1330611 = 1995917) B1995917
theorem B1994177 : Blo 1328983 1994177 := bstep (se 2 (by rfl) ⟨747816, by rfl⟩ : syracuseStep 1994177 = 1495633) B1495633
theorem B1330627 : Blo 1328983 1330627 := bstep (se 1 (by rfl) ⟨997970, by rfl⟩ : syracuseStep 1330627 = 1995941) B1995941
theorem B1994195 : Blo 1328983 1994195 := bstep (se 1 (by rfl) ⟨1495646, by rfl⟩ : syracuseStep 1994195 = 2991293) B2991293
theorem B1330643 : Blo 1328983 1330643 := bstep (se 1 (by rfl) ⟨997982, by rfl⟩ : syracuseStep 1330643 = 1995965) B1995965
theorem B1330659 : Blo 1328983 1330659 := bstep (se 1 (by rfl) ⟨997994, by rfl⟩ : syracuseStep 1330659 = 1995989) B1995989
theorem B1994225 : Blo 1328983 1994225 := bstep (se 2 (by rfl) ⟨747834, by rfl⟩ : syracuseStep 1994225 = 1495669) B1495669
theorem B1330675 : Blo 1328983 1330675 := bstep (se 1 (by rfl) ⟨998006, by rfl⟩ : syracuseStep 1330675 = 1996013) B1996013
theorem B1994243 : Blo 1328983 1994243 := bstep (se 1 (by rfl) ⟨1495682, by rfl⟩ : syracuseStep 1994243 = 2991365) B2991365
theorem B1682947 : Blo 1328983 1682947 := bstep (se 1 (by rfl) ⟨1262210, by rfl⟩ : syracuseStep 1682947 = 2524421) B2524421
theorem B1330691 : Blo 1328983 1330691 := bstep (se 1 (by rfl) ⟨998018, by rfl⟩ : syracuseStep 1330691 = 1996037) B1996037
theorem B1330707 : Blo 1328983 1330707 := bstep (se 1 (by rfl) ⟨998030, by rfl⟩ : syracuseStep 1330707 = 1996061) B1996061
theorem B1994273 : Blo 1328983 1994273 := bstep (se 2 (by rfl) ⟨747852, by rfl⟩ : syracuseStep 1994273 = 1495705) B1495705
theorem B1330723 : Blo 1328983 1330723 := bstep (se 1 (by rfl) ⟨998042, by rfl⟩ : syracuseStep 1330723 = 1996085) B1996085
theorem B1994291 : Blo 1328983 1994291 := bstep (se 1 (by rfl) ⟨1495718, by rfl⟩ : syracuseStep 1994291 = 2991437) B2991437
theorem B1330739 : Blo 1328983 1330739 := bstep (se 1 (by rfl) ⟨998054, by rfl⟩ : syracuseStep 1330739 = 1996109) B1996109
theorem B1330755 : Blo 1328983 1330755 := bstep (se 1 (by rfl) ⟨998066, by rfl⟩ : syracuseStep 1330755 = 1996133) B1996133
theorem B6393421 : Blo 1328983 6393421 := bstep (se 3 (by rfl) ⟨1198766, by rfl⟩ : syracuseStep 6393421 = 2397533) B2397533
theorem B1994321 : Blo 1328983 1994321 := bstep (se 2 (by rfl) ⟨747870, by rfl⟩ : syracuseStep 1994321 = 1495741) B1495741
theorem B1330771 : Blo 1328983 1330771 := bstep (se 1 (by rfl) ⟨998078, by rfl⟩ : syracuseStep 1330771 = 1996157) B1996157
theorem B1994339 : Blo 1328983 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B4796003 : Blo 1328983 4796003 := bstep (se 1 (by rfl) ⟨3597002, by rfl⟩ : syracuseStep 4796003 = 7194005) B7194005
theorem B1330787 : Blo 1328983 1330787 := bstep (se 1 (by rfl) ⟨998090, by rfl⟩ : syracuseStep 1330787 = 1996181) B1996181
theorem B2993777 : Blo 1328983 2993777 := bstep (se 2 (by rfl) ⟨1122666, by rfl⟩ : syracuseStep 2993777 = 2245333) B2245333
theorem B1330803 : Blo 1328983 1330803 := bstep (se 1 (by rfl) ⟨998102, by rfl⟩ : syracuseStep 1330803 = 1996205) B1996205
theorem B1994369 : Blo 1328983 1994369 := bstep (se 2 (by rfl) ⟨747888, by rfl⟩ : syracuseStep 1994369 = 1495777) B1495777
theorem B2993795 : Blo 1328983 2993795 := bstep (se 1 (by rfl) ⟨2245346, by rfl⟩ : syracuseStep 2993795 = 4490693) B4490693
theorem B1330819 : Blo 1328983 1330819 := bstep (se 1 (by rfl) ⟨998114, by rfl⟩ : syracuseStep 1330819 = 1996229) B1996229
theorem B1994387 : Blo 1328983 1994387 := bstep (se 1 (by rfl) ⟨1495790, by rfl⟩ : syracuseStep 1994387 = 2991581) B2991581
theorem B1330835 : Blo 1328983 1330835 := bstep (se 1 (by rfl) ⟨998126, by rfl⟩ : syracuseStep 1330835 = 1996253) B1996253
theorem B1330851 : Blo 1328983 1330851 := bstep (se 1 (by rfl) ⟨998138, by rfl⟩ : syracuseStep 1330851 = 1996277) B1996277
theorem B1994417 : Blo 1328983 1994417 := bstep (se 2 (by rfl) ⟨747906, by rfl⟩ : syracuseStep 1994417 = 1495813) B1495813
theorem B1797809 : Blo 1328983 1797809 := bstep (se 2 (by rfl) ⟨674178, by rfl⟩ : syracuseStep 1797809 = 1348357) B1348357
theorem B1330867 : Blo 1328983 1330867 := bstep (se 1 (by rfl) ⟨998150, by rfl⟩ : syracuseStep 1330867 = 1996301) B1996301
theorem B1994435 : Blo 1328983 1994435 := bstep (se 1 (by rfl) ⟨1495826, by rfl⟩ : syracuseStep 1994435 = 2991653) B2991653
theorem B1330883 : Blo 1328983 1330883 := bstep (se 1 (by rfl) ⟨998162, by rfl⟩ : syracuseStep 1330883 = 1996325) B1996325
theorem B1330899 : Blo 1328983 1330899 := bstep (se 1 (by rfl) ⟨998174, by rfl⟩ : syracuseStep 1330899 = 1996349) B1996349
theorem B1994465 : Blo 1328983 1994465 := bstep (se 2 (by rfl) ⟨747924, by rfl⟩ : syracuseStep 1994465 = 1495849) B1495849
theorem B1330915 : Blo 1328983 1330915 := bstep (se 1 (by rfl) ⟨998186, by rfl⟩ : syracuseStep 1330915 = 1996373) B1996373
theorem B7188209 : Blo 1328983 7188209 := bstep (se 2 (by rfl) ⟨2695578, by rfl⟩ : syracuseStep 7188209 = 5391157) B5391157
theorem B1994483 : Blo 1328983 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B1330931 : Blo 1328983 1330931 := bstep (se 1 (by rfl) ⟨998198, by rfl⟩ : syracuseStep 1330931 = 1996397) B1996397
theorem B1330947 : Blo 1328983 1330947 := bstep (se 1 (by rfl) ⟨998210, by rfl⟩ : syracuseStep 1330947 = 1996421) B1996421
theorem B1994513 : Blo 1328983 1994513 := bstep (se 2 (by rfl) ⟨747942, by rfl⟩ : syracuseStep 1994513 = 1495885) B1495885
theorem B1330963 : Blo 1328983 1330963 := bstep (se 1 (by rfl) ⟨998222, by rfl⟩ : syracuseStep 1330963 = 1996445) B1996445
theorem B1994531 : Blo 1328983 1994531 := bstep (se 1 (by rfl) ⟨1495898, by rfl⟩ : syracuseStep 1994531 = 2991797) B2991797
theorem B5050147 : Blo 1328983 5050147 := bstep (se 1 (by rfl) ⟨3787610, by rfl⟩ : syracuseStep 5050147 = 7575221) B7575221
theorem B1330979 : Blo 1328983 1330979 := bstep (se 1 (by rfl) ⟨998234, by rfl⟩ : syracuseStep 1330979 = 1996469) B1996469
theorem B1994561 : Blo 1328983 1994561 := bstep (se 2 (by rfl) ⟨747960, by rfl⟩ : syracuseStep 1994561 = 1495921) B1495921
theorem B1421123 : Blo 1328983 1421123 := bstep (se 1 (by rfl) ⟨1065842, by rfl⟩ : syracuseStep 1421123 = 2131685) B2131685
theorem B6737741 : Blo 1328983 6737741 := bstep (se 3 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 6737741 = 2526653) B2526653
theorem B1994579 : Blo 1328983 1994579 := bstep (se 1 (by rfl) ⟨1495934, by rfl⟩ : syracuseStep 1994579 = 2991869) B2991869
theorem B4263779 : Blo 1328983 4263779 := bstep (se 1 (by rfl) ⟨3197834, by rfl⟩ : syracuseStep 4263779 = 6395669) B6395669
theorem B1994609 : Blo 1328983 1994609 := bstep (se 2 (by rfl) ⟨747978, by rfl⟩ : syracuseStep 1994609 = 1495957) B1495957
theorem B1994627 : Blo 1328983 1994627 := bstep (se 1 (by rfl) ⟨1495970, by rfl⟩ : syracuseStep 1994627 = 2991941) B2991941
theorem B2994065 : Blo 1328983 2994065 := bstep (se 2 (by rfl) ⟨1122774, by rfl⟩ : syracuseStep 2994065 = 2245549) B2245549
theorem B1994657 : Blo 1328983 1994657 := bstep (se 2 (by rfl) ⟨747996, by rfl⟩ : syracuseStep 1994657 = 1495993) B1495993
theorem B2994083 : Blo 1328983 2994083 := bstep (se 1 (by rfl) ⟨2245562, by rfl⟩ : syracuseStep 2994083 = 4491125) B4491125
theorem B1994675 : Blo 1328983 1994675 := bstep (se 1 (by rfl) ⟨1496006, by rfl⟩ : syracuseStep 1994675 = 2992013) B2992013
theorem B7573445 : Blo 1328983 7573445 := bstep (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) B1420021
theorem B3837905 : Blo 1328983 3837905 := bstep (se 2 (by rfl) ⟨1439214, by rfl⟩ : syracuseStep 3837905 = 2878429) B2878429
theorem B1994705 : Blo 1328983 1994705 := bstep (se 2 (by rfl) ⟨748014, by rfl⟩ : syracuseStep 1994705 = 1496029) B1496029
theorem B1994723 : Blo 1328983 1994723 := bstep (se 1 (by rfl) ⟨1496042, by rfl⟩ : syracuseStep 1994723 = 2992085) B2992085
theorem B1683443 : Blo 1328983 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B1994753 : Blo 1328983 1994753 := bstep (se 2 (by rfl) ⟨748032, by rfl⟩ : syracuseStep 1994753 = 1496065) B1496065
theorem B1994771 : Blo 1328983 1994771 := bstep (se 1 (by rfl) ⟨1496078, by rfl⟩ : syracuseStep 1994771 = 2992157) B2992157
theorem B1994801 : Blo 1328983 1994801 := bstep (se 2 (by rfl) ⟨748050, by rfl⟩ : syracuseStep 1994801 = 1496101) B1496101
theorem B1994819 : Blo 1328983 1994819 := bstep (se 1 (by rfl) ⟨1496114, by rfl⟩ : syracuseStep 1994819 = 2992229) B2992229
theorem B2560081 : Blo 1328983 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B1994849 : Blo 1328983 1994849 := bstep (se 2 (by rfl) ⟨748068, by rfl⟩ : syracuseStep 1994849 = 1496137) B1496137
theorem B1994867 : Blo 1328983 1994867 := bstep (se 1 (by rfl) ⟨1496150, by rfl⟩ : syracuseStep 1994867 = 2992301) B2992301
theorem B1994897 : Blo 1328983 1994897 := bstep (se 2 (by rfl) ⟨748086, by rfl⟩ : syracuseStep 1994897 = 1496173) B1496173
theorem B1994915 : Blo 1328983 1994915 := bstep (se 1 (by rfl) ⟨1496186, by rfl⟩ : syracuseStep 1994915 = 2992373) B2992373
theorem B5394595 : Blo 1328983 5394595 := bstep (se 1 (by rfl) ⟨4045946, by rfl⟩ : syracuseStep 5394595 = 8091893) B8091893
theorem B4796579 : Blo 1328983 4796579 := bstep (se 1 (by rfl) ⟨3597434, by rfl⟩ : syracuseStep 4796579 = 7194869) B7194869
theorem B1495219 : Blo 1328983 1495219 := bstep (se 1 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 1495219 = 2242829) B2242829
theorem B2994353 : Blo 1328983 2994353 := bstep (se 2 (by rfl) ⟨1122882, by rfl⟩ : syracuseStep 2994353 = 2245765) B2245765
theorem B1994945 : Blo 1328983 1994945 := bstep (se 2 (by rfl) ⟨748104, by rfl⟩ : syracuseStep 1994945 = 1496209) B1496209
theorem B2994371 : Blo 1328983 2994371 := bstep (se 1 (by rfl) ⟨2245778, by rfl⟩ : syracuseStep 2994371 = 4491557) B4491557
theorem B1994963 : Blo 1328983 1994963 := bstep (se 1 (by rfl) ⟨1496222, by rfl⟩ : syracuseStep 1994963 = 2992445) B2992445
theorem B4485347 : Blo 1328983 4485347 := bstep (se 1 (by rfl) ⟨3364010, by rfl⟩ : syracuseStep 4485347 = 6728021) B6728021
theorem B2396387 : Blo 1328983 2396387 := bstep (se 1 (by rfl) ⟨1797290, by rfl⟩ : syracuseStep 2396387 = 3594581) B3594581
theorem B1994993 : Blo 1328983 1994993 := bstep (se 2 (by rfl) ⟨748122, by rfl⟩ : syracuseStep 1994993 = 1496245) B1496245
theorem B1995011 : Blo 1328983 1995011 := bstep (se 1 (by rfl) ⟨1496258, by rfl⟩ : syracuseStep 1995011 = 2992517) B2992517
theorem B1995041 : Blo 1328983 1995041 := bstep (se 2 (by rfl) ⟨748140, by rfl⟩ : syracuseStep 1995041 = 1496281) B1496281
theorem B1995059 : Blo 1328983 1995059 := bstep (se 1 (by rfl) ⟨1496294, by rfl⟩ : syracuseStep 1995059 = 2992589) B2992589
theorem B1495363 : Blo 1328983 1495363 := bstep (se 1 (by rfl) ⟨1121522, by rfl⟩ : syracuseStep 1495363 = 2243045) B2243045
theorem B1995089 : Blo 1328983 1995089 := bstep (se 2 (by rfl) ⟨748158, by rfl⟩ : syracuseStep 1995089 = 1496317) B1496317
theorem B1995107 : Blo 1328983 1995107 := bstep (se 1 (by rfl) ⟨1496330, by rfl⟩ : syracuseStep 1995107 = 2992661) B2992661
theorem B1995137 : Blo 1328983 1995137 := bstep (se 2 (by rfl) ⟨748176, by rfl⟩ : syracuseStep 1995137 = 1496353) B1496353
theorem B4100483 : Blo 1328983 4100483 := bstep (se 1 (by rfl) ⟨3075362, by rfl⟩ : syracuseStep 4100483 = 6150725) B6150725
theorem B1995155 : Blo 1328983 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B1995185 : Blo 1328983 1995185 := bstep (se 2 (by rfl) ⟨748194, by rfl⟩ : syracuseStep 1995185 = 1496389) B1496389
theorem B1995203 : Blo 1328983 1995203 := bstep (se 1 (by rfl) ⟨1496402, by rfl⟩ : syracuseStep 1995203 = 2992805) B2992805
theorem B3789251 : Blo 1328983 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B6230477 : Blo 1328983 6230477 := bstep (se 3 (by rfl) ⟨1168214, by rfl⟩ : syracuseStep 6230477 = 2336429) B2336429
theorem B2994641 : Blo 1328983 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B1495507 : Blo 1328983 1495507 := bstep (se 1 (by rfl) ⟨1121630, by rfl⟩ : syracuseStep 1495507 = 2243261) B2243261
theorem B1995233 : Blo 1328983 1995233 := bstep (se 2 (by rfl) ⟨748212, by rfl⟩ : syracuseStep 1995233 = 1496425) B1496425
theorem B2994659 : Blo 1328983 2994659 := bstep (se 1 (by rfl) ⟨2245994, by rfl⟩ : syracuseStep 2994659 = 4491989) B4491989
theorem B4485617 : Blo 1328983 4485617 := bstep (se 2 (by rfl) ⟨1682106, by rfl⟩ : syracuseStep 4485617 = 3364213) B3364213
theorem B1995251 : Blo 1328983 1995251 := bstep (se 1 (by rfl) ⟨1496438, by rfl⟩ : syracuseStep 1995251 = 2992877) B2992877
theorem B2396675 : Blo 1328983 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B1995281 : Blo 1328983 1995281 := bstep (se 2 (by rfl) ⟨748230, by rfl⟩ : syracuseStep 1995281 = 1496461) B1496461
theorem B1995299 : Blo 1328983 1995299 := bstep (se 1 (by rfl) ⟨1496474, by rfl⟩ : syracuseStep 1995299 = 2992949) B2992949
theorem B6730289 : Blo 1328983 6730289 := bstep (se 2 (by rfl) ⟨2523858, by rfl⟩ : syracuseStep 6730289 = 5047717) B5047717
theorem B1995329 : Blo 1328983 1995329 := bstep (se 2 (by rfl) ⟨748248, by rfl⟩ : syracuseStep 1995329 = 1496497) B1496497
theorem B1995347 : Blo 1328983 1995347 := bstep (se 1 (by rfl) ⟨1496510, by rfl⟩ : syracuseStep 1995347 = 2993021) B2993021
theorem B1495651 : Blo 1328983 1495651 := bstep (se 1 (by rfl) ⟨1121738, by rfl⟩ : syracuseStep 1495651 = 2243477) B2243477
theorem B64713329 : Blo 1328983 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B1995377 : Blo 1328983 1995377 := bstep (se 2 (by rfl) ⟨748266, by rfl⟩ : syracuseStep 1995377 = 1496533) B1496533
theorem B2839171 : Blo 1328983 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B1995395 : Blo 1328983 1995395 := bstep (se 1 (by rfl) ⟨1496546, by rfl⟩ : syracuseStep 1995395 = 2993093) B2993093
theorem B1995425 : Blo 1328983 1995425 := bstep (se 2 (by rfl) ⟨748284, by rfl⟩ : syracuseStep 1995425 = 1496569) B1496569
theorem B1995443 : Blo 1328983 1995443 := bstep (se 1 (by rfl) ⟨1496582, by rfl⟩ : syracuseStep 1995443 = 2993165) B2993165
theorem B1684147 : Blo 1328983 1684147 := bstep (se 1 (by rfl) ⟨1263110, by rfl⟩ : syracuseStep 1684147 = 2526221) B2526221
theorem B1995473 : Blo 1328983 1995473 := bstep (se 2 (by rfl) ⟨748302, by rfl⟩ : syracuseStep 1995473 = 1496605) B1496605
theorem B1995491 : Blo 1328983 1995491 := bstep (se 1 (by rfl) ⟨1496618, by rfl⟩ : syracuseStep 1995491 = 2993237) B2993237
theorem B1495795 : Blo 1328983 1495795 := bstep (se 1 (by rfl) ⟨1121846, by rfl⟩ : syracuseStep 1495795 = 2243693) B2243693
theorem B1995521 : Blo 1328983 1995521 := bstep (se 2 (by rfl) ⟨748320, by rfl⟩ : syracuseStep 1995521 = 1496641) B1496641
theorem B1995539 : Blo 1328983 1995539 := bstep (se 1 (by rfl) ⟨1496654, by rfl⟩ : syracuseStep 1995539 = 2993309) B2993309
theorem B1684243 : Blo 1328983 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B1995569 : Blo 1328983 1995569 := bstep (se 2 (by rfl) ⟨748338, by rfl⟩ : syracuseStep 1995569 = 1496677) B1496677
theorem B1995587 : Blo 1328983 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B1995617 : Blo 1328983 1995617 := bstep (se 2 (by rfl) ⟨748356, by rfl⟩ : syracuseStep 1995617 = 1496713) B1496713
theorem B1995635 : Blo 1328983 1995635 := bstep (se 1 (by rfl) ⟨1496726, by rfl⟩ : syracuseStep 1995635 = 2993453) B2993453
theorem B1495939 : Blo 1328983 1495939 := bstep (se 1 (by rfl) ⟨1121954, by rfl⟩ : syracuseStep 1495939 = 2243909) B2243909
theorem B9581453 : Blo 1328983 9581453 := bstep (se 3 (by rfl) ⟨1796522, by rfl⟩ : syracuseStep 9581453 = 3593045) B3593045
theorem B1995665 : Blo 1328983 1995665 := bstep (se 2 (by rfl) ⟨748374, by rfl⟩ : syracuseStep 1995665 = 1496749) B1496749
theorem B1995683 : Blo 1328983 1995683 := bstep (se 1 (by rfl) ⟨1496762, by rfl⟩ : syracuseStep 1995683 = 2993525) B2993525
theorem B1995713 : Blo 1328983 1995713 := bstep (se 2 (by rfl) ⟨748392, by rfl⟩ : syracuseStep 1995713 = 1496785) B1496785
theorem B1995731 : Blo 1328983 1995731 := bstep (se 1 (by rfl) ⟨1496798, by rfl⟩ : syracuseStep 1995731 = 2993597) B2993597
theorem B1995761 : Blo 1328983 1995761 := bstep (se 2 (by rfl) ⟨748410, by rfl⟩ : syracuseStep 1995761 = 1496821) B1496821
theorem B1995779 : Blo 1328983 1995779 := bstep (se 1 (by rfl) ⟨1496834, by rfl⟩ : syracuseStep 1995779 = 2993669) B2993669
theorem B4486157 : Blo 1328983 4486157 := bstep (se 3 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 4486157 = 1682309) B1682309
theorem B1496083 : Blo 1328983 1496083 := bstep (se 1 (by rfl) ⟨1122062, by rfl⟩ : syracuseStep 1496083 = 2244125) B2244125
theorem B1995809 : Blo 1328983 1995809 := bstep (se 2 (by rfl) ⟨748428, by rfl⟩ : syracuseStep 1995809 = 1496857) B1496857
theorem B1995827 : Blo 1328983 1995827 := bstep (se 1 (by rfl) ⟨1496870, by rfl⟩ : syracuseStep 1995827 = 2993741) B2993741
theorem B4486211 : Blo 1328983 4486211 := bstep (se 1 (by rfl) ⟨3364658, by rfl⟩ : syracuseStep 4486211 = 6729317) B6729317
theorem B1995857 : Blo 1328983 1995857 := bstep (se 2 (by rfl) ⟨748446, by rfl⟩ : syracuseStep 1995857 = 1496893) B1496893
theorem B8090723 : Blo 1328983 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B1995875 : Blo 1328983 1995875 := bstep (se 1 (by rfl) ⟨1496906, by rfl⟩ : syracuseStep 1995875 = 2993813) B2993813
theorem B2159731 : Blo 1328983 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B1995905 : Blo 1328983 1995905 := bstep (se 2 (by rfl) ⟨748464, by rfl⟩ : syracuseStep 1995905 = 1496929) B1496929
theorem B1995923 : Blo 1328983 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B8516771 : Blo 1328983 8516771 := bstep (se 1 (by rfl) ⟨6387578, by rfl⟩ : syracuseStep 8516771 = 12775157) B12775157
theorem B1496227 : Blo 1328983 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B3593393 : Blo 1328983 3593393 := bstep (se 2 (by rfl) ⟨1347522, by rfl⟩ : syracuseStep 3593393 = 2695045) B2695045
theorem B1995953 : Blo 1328983 1995953 := bstep (se 2 (by rfl) ⟨748482, by rfl⟩ : syracuseStep 1995953 = 1496965) B1496965
theorem B1995971 : Blo 1328983 1995971 := bstep (se 1 (by rfl) ⟨1496978, by rfl⟩ : syracuseStep 1995971 = 2993957) B2993957
theorem B1996001 : Blo 1328983 1996001 := bstep (se 2 (by rfl) ⟨748500, by rfl⟩ : syracuseStep 1996001 = 1497001) B1497001
theorem B3790061 : Blo 1328983 3790061 := bstep (se 3 (by rfl) ⟨710636, by rfl⟩ : syracuseStep 3790061 = 1421273) B1421273
theorem B1996019 : Blo 1328983 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B1996049 : Blo 1328983 1996049 := bstep (se 2 (by rfl) ⟨748518, by rfl⟩ : syracuseStep 1996049 = 1497037) B1497037
theorem B1996067 : Blo 1328983 1996067 := bstep (se 1 (by rfl) ⟨1497050, by rfl⟩ : syracuseStep 1996067 = 2994101) B2994101
theorem B1496371 : Blo 1328983 1496371 := bstep (se 1 (by rfl) ⟨1122278, by rfl⟩ : syracuseStep 1496371 = 2244557) B2244557
theorem B15144245 : Blo 1328983 15144245 := bstep (se 5 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 15144245 = 1419773) B1419773
theorem B1996097 : Blo 1328983 1996097 := bstep (se 2 (by rfl) ⟨748536, by rfl⟩ : syracuseStep 1996097 = 1497073) B1497073
theorem B3364163 : Blo 1328983 3364163 := bstep (se 1 (by rfl) ⟨2523122, by rfl⟩ : syracuseStep 3364163 = 5046245) B5046245
theorem B4486481 : Blo 1328983 4486481 := bstep (se 2 (by rfl) ⟨1682430, by rfl⟩ : syracuseStep 4486481 = 3364861) B3364861
theorem B1996115 : Blo 1328983 1996115 := bstep (se 1 (by rfl) ⟨1497086, by rfl⟩ : syracuseStep 1996115 = 2994173) B2994173
theorem B7673201 : Blo 1328983 7673201 := bstep (se 2 (by rfl) ⟨2877450, by rfl⟩ : syracuseStep 7673201 = 5754901) B5754901
theorem B5682545 : Blo 1328983 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B1996145 : Blo 1328983 1996145 := bstep (se 2 (by rfl) ⟨748554, by rfl⟩ : syracuseStep 1996145 = 1497109) B1497109
theorem B1996163 : Blo 1328983 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B1996193 : Blo 1328983 1996193 := bstep (se 2 (by rfl) ⟨748572, by rfl⟩ : syracuseStep 1996193 = 1497145) B1497145
theorem B1996211 : Blo 1328983 1996211 := bstep (se 1 (by rfl) ⟨1497158, by rfl⟩ : syracuseStep 1996211 = 2994317) B2994317
theorem B1496515 : Blo 1328983 1496515 := bstep (se 1 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 1496515 = 2244773) B2244773
theorem B38352325 : Blo 1328983 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B2840017 : Blo 1328983 2840017 := bstep (se 2 (by rfl) ⟨1065006, by rfl⟩ : syracuseStep 2840017 = 2130013) B2130013
theorem B1996241 : Blo 1328983 1996241 := bstep (se 2 (by rfl) ⟨748590, by rfl⟩ : syracuseStep 1996241 = 1497181) B1497181
theorem B1996259 : Blo 1328983 1996259 := bstep (se 1 (by rfl) ⟨1497194, by rfl⟩ : syracuseStep 1996259 = 2994389) B2994389
theorem B1996289 : Blo 1328983 1996289 := bstep (se 2 (by rfl) ⟨748608, by rfl⟩ : syracuseStep 1996289 = 1497217) B1497217
theorem B3364355 : Blo 1328983 3364355 := bstep (se 1 (by rfl) ⟨2523266, by rfl⟩ : syracuseStep 3364355 = 5046533) B5046533
theorem B15365645 : Blo 1328983 15365645 := bstep (se 3 (by rfl) ⟨2881058, by rfl⟩ : syracuseStep 15365645 = 5762117) B5762117
theorem B2160145 : Blo 1328983 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B1996307 : Blo 1328983 1996307 := bstep (se 1 (by rfl) ⟨1497230, by rfl⟩ : syracuseStep 1996307 = 2994461) B2994461
theorem B1996337 : Blo 1328983 1996337 := bstep (se 2 (by rfl) ⟨748626, by rfl⟩ : syracuseStep 1996337 = 1497253) B1497253
theorem B1365571 : Blo 1328983 1365571 := bstep (se 1 (by rfl) ⟨1024178, by rfl⟩ : syracuseStep 1365571 = 2048357) B2048357
theorem B1996355 : Blo 1328983 1996355 := bstep (se 1 (by rfl) ⟨1497266, by rfl⟩ : syracuseStep 1996355 = 2994533) B2994533
theorem B1619539 : Blo 1328983 1619539 := bstep (se 1 (by rfl) ⟨1214654, by rfl⟩ : syracuseStep 1619539 = 2429309) B2429309
theorem B1496659 : Blo 1328983 1496659 := bstep (se 1 (by rfl) ⟨1122494, by rfl⟩ : syracuseStep 1496659 = 2244989) B2244989
theorem B1996385 : Blo 1328983 1996385 := bstep (se 2 (by rfl) ⟨748644, by rfl⟩ : syracuseStep 1996385 = 1497289) B1497289
theorem B1996403 : Blo 1328983 1996403 := bstep (se 1 (by rfl) ⟨1497302, by rfl⟩ : syracuseStep 1996403 = 2994605) B2994605
theorem B1996433 : Blo 1328983 1996433 := bstep (se 2 (by rfl) ⟨748662, by rfl⟩ : syracuseStep 1996433 = 1497325) B1497325
theorem B1996451 : Blo 1328983 1996451 := bstep (se 1 (by rfl) ⟨1497338, by rfl⟩ : syracuseStep 1996451 = 2994677) B2994677
theorem B2021041 : Blo 1328983 2021041 := bstep (se 2 (by rfl) ⟨757890, by rfl⟩ : syracuseStep 2021041 = 1515781) B1515781
theorem B1496803 : Blo 1328983 1496803 := bstep (se 1 (by rfl) ⟨1122602, by rfl⟩ : syracuseStep 1496803 = 2245205) B2245205
theorem B3594061 : Blo 1328983 3594061 := bstep (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) B1347773
theorem B4487021 : Blo 1328983 4487021 := bstep (se 3 (by rfl) ⟨841316, by rfl⟩ : syracuseStep 4487021 = 1682633) B1682633
theorem B1496947 : Blo 1328983 1496947 := bstep (se 1 (by rfl) ⟨1122710, by rfl⟩ : syracuseStep 1496947 = 2245421) B2245421
theorem B4487075 : Blo 1328983 4487075 := bstep (se 1 (by rfl) ⟨3365306, by rfl⟩ : syracuseStep 4487075 = 6730613) B6730613
theorem B5052365 : Blo 1328983 5052365 := bstep (se 3 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 5052365 = 1894637) B1894637
theorem B6731747 : Blo 1328983 6731747 := bstep (se 1 (by rfl) ⟨5048810, by rfl⟩ : syracuseStep 6731747 = 10097621) B10097621
theorem B1497091 : Blo 1328983 1497091 := bstep (se 1 (by rfl) ⟨1122818, by rfl⟩ : syracuseStep 1497091 = 2245637) B2245637
theorem B4257809 : Blo 1328983 4257809 := bstep (se 2 (by rfl) ⟨1596678, by rfl⟩ : syracuseStep 4257809 = 3193357) B3193357
theorem B1497235 : Blo 1328983 1497235 := bstep (se 1 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 1497235 = 2245853) B2245853
theorem B2242721 : Blo 1328983 2242721 := bstep (se 2 (by rfl) ⟨841020, by rfl⟩ : syracuseStep 2242721 = 1682041) B1682041
theorem B4487345 : Blo 1328983 4487345 := bstep (se 2 (by rfl) ⟨1682754, by rfl⟩ : syracuseStep 4487345 = 3365509) B3365509
theorem B5388529 : Blo 1328983 5388529 := bstep (se 2 (by rfl) ⟨2020698, by rfl⟩ : syracuseStep 5388529 = 4041397) B4041397
theorem B2242849 : Blo 1328983 2242849 := bstep (se 2 (by rfl) ⟨841068, by rfl⟩ : syracuseStep 2242849 = 1682137) B1682137
theorem B2242883 : Blo 1328983 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B4553059 : Blo 1328983 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B22722929 : Blo 1328983 22722929 := bstep (se 2 (by rfl) ⟨8521098, by rfl⟩ : syracuseStep 22722929 = 17042197) B17042197
theorem B3365297 : Blo 1328983 3365297 := bstep (se 2 (by rfl) ⟨1261986, by rfl⟩ : syracuseStep 3365297 = 2523973) B2523973
theorem B2243011 : Blo 1328983 2243011 := bstep (se 1 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 2243011 = 3364517) B3364517
theorem B4790755 : Blo 1328983 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B3365347 : Blo 1328983 3365347 := bstep (se 1 (by rfl) ⟨2524010, by rfl⟩ : syracuseStep 3365347 = 5048021) B5048021
theorem B4045315 : Blo 1328983 4045315 := bstep (se 1 (by rfl) ⟨3033986, by rfl⟩ : syracuseStep 4045315 = 6067973) B6067973
theorem B3594797 : Blo 1328983 3594797 := bstep (se 3 (by rfl) ⟨674024, by rfl⟩ : syracuseStep 3594797 = 1348049) B1348049
theorem B9230917 : Blo 1328983 9230917 := bstep (se 4 (by rfl) ⟨865398, by rfl⟩ : syracuseStep 9230917 = 1730797) B1730797
theorem B2243153 : Blo 1328983 2243153 := bstep (se 2 (by rfl) ⟨841182, by rfl⟩ : syracuseStep 2243153 = 1682365) B1682365
theorem B3365489 : Blo 1328983 3365489 := bstep (se 2 (by rfl) ⟨1262058, by rfl⟩ : syracuseStep 3365489 = 2524117) B2524117
theorem B4258499 : Blo 1328983 4258499 := bstep (se 1 (by rfl) ⟨3193874, by rfl⟩ : syracuseStep 4258499 = 6387749) B6387749
theorem B4487885 : Blo 1328983 4487885 := bstep (se 3 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 4487885 = 1682957) B1682957
theorem B2243281 : Blo 1328983 2243281 := bstep (se 2 (by rfl) ⟨841230, by rfl⟩ : syracuseStep 2243281 = 1682461) B1682461
theorem B2243315 : Blo 1328983 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B4487939 : Blo 1328983 4487939 := bstep (se 1 (by rfl) ⟨3365954, by rfl⟩ : syracuseStep 4487939 = 6731909) B6731909
theorem B6732557 : Blo 1328983 6732557 := bstep (se 3 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 6732557 = 2524709) B2524709
theorem B3595121 : Blo 1328983 3595121 := bstep (se 2 (by rfl) ⟨1348170, by rfl⟩ : syracuseStep 3595121 = 2696341) B2696341
theorem B2243443 : Blo 1328983 2243443 := bstep (se 1 (by rfl) ⟨1682582, by rfl⟩ : syracuseStep 2243443 = 3365165) B3365165
theorem B2243585 : Blo 1328983 2243585 := bstep (se 2 (by rfl) ⟨841344, by rfl⟩ : syracuseStep 2243585 = 1682689) B1682689
theorem B4488209 : Blo 1328983 4488209 := bstep (se 2 (by rfl) ⟨1683078, by rfl⟩ : syracuseStep 4488209 = 3366157) B3366157
theorem B2243713 : Blo 1328983 2243713 := bstep (se 2 (by rfl) ⟨841392, by rfl⟩ : syracuseStep 2243713 = 1682785) B1682785
theorem B2243747 : Blo 1328983 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B1596611 : Blo 1328983 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B8527045 : Blo 1328983 8527045 := bstep (se 4 (by rfl) ⟨799410, by rfl⟩ : syracuseStep 8527045 = 1598821) B1598821
theorem B2243875 : Blo 1328983 2243875 := bstep (se 1 (by rfl) ⟨1682906, by rfl⟩ : syracuseStep 2243875 = 3365813) B3365813
theorem B8092963 : Blo 1328983 8092963 := bstep (se 1 (by rfl) ⟨6069722, by rfl⟩ : syracuseStep 8092963 = 12139445) B12139445
theorem B2841905 : Blo 1328983 2841905 := bstep (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) B2131429
theorem B2244017 : Blo 1328983 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B4488749 : Blo 1328983 4488749 := bstep (se 3 (by rfl) ⟨841640, by rfl⟩ : syracuseStep 4488749 = 1683281) B1683281
theorem B2244145 : Blo 1328983 2244145 := bstep (se 2 (by rfl) ⟨841554, by rfl⟩ : syracuseStep 2244145 = 1683109) B1683109
theorem B3366481 : Blo 1328983 3366481 := bstep (se 2 (by rfl) ⟨1262430, by rfl⟩ : syracuseStep 3366481 = 2524861) B2524861
theorem B2244179 : Blo 1328983 2244179 := bstep (se 1 (by rfl) ⟨1683134, by rfl⟩ : syracuseStep 2244179 = 3366269) B3366269
theorem B4488803 : Blo 1328983 4488803 := bstep (se 1 (by rfl) ⟨3366602, by rfl⟩ : syracuseStep 4488803 = 6733205) B6733205
theorem B1597091 : Blo 1328983 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B2244307 : Blo 1328983 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B48545507 : Blo 1328983 48545507 := bstep (se 1 (by rfl) ⟨36409130, by rfl⟩ : syracuseStep 48545507 = 72818261) B72818261
theorem B5685005 : Blo 1328983 5685005 := bstep (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) B2131877
theorem B24272693 : Blo 1328983 24272693 := bstep (se 5 (by rfl) ⟨1137782, by rfl⟩ : syracuseStep 24272693 = 2275565) B2275565
theorem B2244449 : Blo 1328983 2244449 := bstep (se 2 (by rfl) ⟨841668, by rfl⟩ : syracuseStep 2244449 = 1683337) B1683337
theorem B2023265 : Blo 1328983 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B3366755 : Blo 1328983 3366755 := bstep (se 1 (by rfl) ⟨2525066, by rfl⟩ : syracuseStep 3366755 = 5050133) B5050133
theorem B4489073 : Blo 1328983 4489073 := bstep (se 2 (by rfl) ⟨1683402, by rfl⟩ : syracuseStep 4489073 = 3366805) B3366805
theorem B2129827 : Blo 1328983 2129827 := bstep (se 1 (by rfl) ⟨1597370, by rfl⟩ : syracuseStep 2129827 = 3194741) B3194741
theorem B2244577 : Blo 1328983 2244577 := bstep (se 2 (by rfl) ⟨841716, by rfl⟩ : syracuseStep 2244577 = 1683433) B1683433
theorem B13828067 : Blo 1328983 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B2244631 : Blo 1328983 2244631 := bstep (se 1 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 2244631 = 3366947) B3366947
theorem B2523251 : Blo 1328983 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B2990231 : Blo 1328983 2990231 := bstep (se 1 (by rfl) ⟨2242673, by rfl⟩ : syracuseStep 2990231 = 4485347) B4485347
theorem B1597591 : Blo 1328983 1597591 := bstep (se 1 (by rfl) ⟨1198193, by rfl⟩ : syracuseStep 1597591 = 2396387) B2396387
theorem B10092761 : Blo 1328983 10092761 := bstep (se 2 (by rfl) ⟨3784785, by rfl⟩ : syracuseStep 10092761 = 7569571) B7569571
theorem B3367129 : Blo 1328983 3367129 := bstep (se 2 (by rfl) ⟨1262673, by rfl⟩ : syracuseStep 3367129 = 2525347) B2525347
theorem B7192793 : Blo 1328983 7192793 := bstep (se 2 (by rfl) ⟨2697297, by rfl⟩ : syracuseStep 7192793 = 5394595) B5394595
theorem B2523403 : Blo 1328983 2523403 := bstep (se 1 (by rfl) ⟨1892552, by rfl⟩ : syracuseStep 2523403 = 3785105) B3785105
theorem B7184705 : Blo 1328983 7184705 := bstep (se 2 (by rfl) ⟨2694264, by rfl⟩ : syracuseStep 7184705 = 5388529) B5388529
theorem B13500737 : Blo 1328983 13500737 := bstep (se 2 (by rfl) ⟨5062776, by rfl⟩ : syracuseStep 13500737 = 10125553) B10125553
theorem B2990411 : Blo 1328983 2990411 := bstep (se 1 (by rfl) ⟨2242808, by rfl⟩ : syracuseStep 2990411 = 4485617) B4485617
theorem B2990465 : Blo 1328983 2990465 := bstep (se 2 (by rfl) ⟨1121424, by rfl⟩ : syracuseStep 2990465 = 2242849) B2242849
theorem B5046731 : Blo 1328983 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B2130391 : Blo 1328983 2130391 := bstep (se 1 (by rfl) ⟨1597793, by rfl⟩ : syracuseStep 2130391 = 3195587) B3195587
theorem B5046745 : Blo 1328983 5046745 := bstep (se 2 (by rfl) ⟨1892529, by rfl⟩ : syracuseStep 5046745 = 3785059) B3785059
theorem B6070745 : Blo 1328983 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B2130455 : Blo 1328983 2130455 := bstep (se 1 (by rfl) ⟨1597841, by rfl⟩ : syracuseStep 2130455 = 3195683) B3195683
theorem B2990681 : Blo 1328983 2990681 := bstep (se 2 (by rfl) ⟨1121505, by rfl⟩ : syracuseStep 2990681 = 2243011) B2243011
theorem B2523737 : Blo 1328983 2523737 := bstep (se 2 (by rfl) ⟨946401, by rfl⟩ : syracuseStep 2523737 = 1892803) B1892803
theorem B2245259 : Blo 1328983 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B2990771 : Blo 1328983 2990771 := bstep (se 1 (by rfl) ⟨2243078, by rfl⟩ : syracuseStep 2990771 = 4486157) B4486157
theorem B3596993 : Blo 1328983 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B2990807 : Blo 1328983 2990807 := bstep (se 1 (by rfl) ⟨2243105, by rfl⟩ : syracuseStep 2990807 = 4486211) B4486211
theorem B10101509 : Blo 1328983 10101509 := bstep (se 4 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 10101509 = 1894033) B1894033
theorem B2245387 : Blo 1328983 2245387 := bstep (se 1 (by rfl) ⟨1684040, by rfl⟩ : syracuseStep 2245387 = 3368081) B3368081
theorem B5677847 : Blo 1328983 5677847 := bstep (se 1 (by rfl) ⟨4258385, by rfl⟩ : syracuseStep 5677847 = 8516771) B8516771
theorem B1893145 : Blo 1328983 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B3785561 : Blo 1328983 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B2990987 : Blo 1328983 2990987 := bstep (se 1 (by rfl) ⟨2243240, by rfl⟩ : syracuseStep 2990987 = 4486481) B4486481
theorem B2245529 : Blo 1328983 2245529 := bstep (se 2 (by rfl) ⟨842073, by rfl⟩ : syracuseStep 2245529 = 1684147) B1684147
theorem B2991041 : Blo 1328983 2991041 := bstep (se 2 (by rfl) ⟨1121640, by rfl⟩ : syracuseStep 2991041 = 2243281) B2243281
theorem B2245657 : Blo 1328983 2245657 := bstep (se 2 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 2245657 = 1684243) B1684243
theorem B2131019 : Blo 1328983 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B4490315 : Blo 1328983 4490315 := bstep (se 1 (by rfl) ⟨3367736, by rfl⟩ : syracuseStep 4490315 = 6735473) B6735473
theorem B3785879 : Blo 1328983 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B2991257 : Blo 1328983 2991257 := bstep (se 2 (by rfl) ⟨1121721, by rfl⟩ : syracuseStep 2991257 = 2243443) B2243443
theorem B16614605 : Blo 1328983 16614605 := bstep (se 3 (by rfl) ⟨3115238, by rfl⟩ : syracuseStep 16614605 = 6230477) B6230477
theorem B2524375 : Blo 1328983 2524375 := bstep (se 1 (by rfl) ⟨1893281, by rfl⟩ : syracuseStep 2524375 = 3786563) B3786563
theorem B2991347 : Blo 1328983 2991347 := bstep (se 1 (by rfl) ⟨2243510, by rfl⟩ : syracuseStep 2991347 = 4487021) B4487021
theorem B2131211 : Blo 1328983 2131211 := bstep (se 1 (by rfl) ⟨1598408, by rfl⟩ : syracuseStep 2131211 = 3196817) B3196817
theorem B2991383 : Blo 1328983 2991383 := bstep (se 1 (by rfl) ⟨2243537, by rfl⟩ : syracuseStep 2991383 = 4487075) B4487075
theorem B6735149 : Blo 1328983 6735149 := bstep (se 3 (by rfl) ⟨1262840, by rfl⟩ : syracuseStep 6735149 = 2525681) B2525681
theorem B3368243 : Blo 1328983 3368243 := bstep (se 1 (by rfl) ⟨2526182, by rfl⟩ : syracuseStep 3368243 = 5052365) B5052365
theorem B4490585 : Blo 1328983 4490585 := bstep (se 2 (by rfl) ⟨1683969, by rfl⟩ : syracuseStep 4490585 = 3367939) B3367939
theorem B6391133 : Blo 1328983 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B5047703 : Blo 1328983 5047703 := bstep (se 1 (by rfl) ⟨3785777, by rfl⟩ : syracuseStep 5047703 = 7571555) B7571555
theorem B2000279 : Blo 1328983 2000279 := bstep (se 1 (by rfl) ⟨1500209, by rfl⟩ : syracuseStep 2000279 = 3000419) B3000419
theorem B2991563 : Blo 1328983 2991563 := bstep (se 1 (by rfl) ⟨2243672, by rfl⟩ : syracuseStep 2991563 = 4487345) B4487345
theorem B276235733 : Blo 1328983 276235733 := bstep (se 7 (by rfl) ⟨3237137, by rfl⟩ : syracuseStep 276235733 = 6474275) B6474275
theorem B2991617 : Blo 1328983 2991617 := bstep (se 2 (by rfl) ⟨1121856, by rfl⟩ : syracuseStep 2991617 = 2243713) B2243713
theorem B15148619 : Blo 1328983 15148619 := bstep (se 1 (by rfl) ⟨11361464, by rfl⟩ : syracuseStep 15148619 = 22722929) B22722929
theorem B3368537 : Blo 1328983 3368537 := bstep (se 2 (by rfl) ⟨1263201, by rfl⟩ : syracuseStep 3368537 = 2526403) B2526403
theorem B2991833 : Blo 1328983 2991833 := bstep (se 2 (by rfl) ⟨1121937, by rfl⟩ : syracuseStep 2991833 = 2243875) B2243875
theorem B10790617 : Blo 1328983 10790617 := bstep (se 2 (by rfl) ⟨4046481, by rfl⟩ : syracuseStep 10790617 = 8092963) B8092963
theorem B3032819 : Blo 1328983 3032819 := bstep (se 1 (by rfl) ⟨2274614, by rfl⟩ : syracuseStep 3032819 = 4549229) B4549229
theorem B3032855 : Blo 1328983 3032855 := bstep (se 1 (by rfl) ⟨2274641, by rfl⟩ : syracuseStep 3032855 = 4549283) B4549283
theorem B4794157 : Blo 1328983 4794157 := bstep (se 3 (by rfl) ⟨898904, by rfl⟩ : syracuseStep 4794157 = 1797809) B1797809
theorem B2991923 : Blo 1328983 2991923 := bstep (se 1 (by rfl) ⟨2243942, by rfl⟩ : syracuseStep 2991923 = 4487885) B4487885
theorem B1328983 : Blo 1328983 1328983 := bstep (se 1 (by rfl) ⟨996737, by rfl⟩ : syracuseStep 1328983 = 1993475) B1993475
theorem B2991959 : Blo 1328983 2991959 := bstep (se 1 (by rfl) ⟨2243969, by rfl⟩ : syracuseStep 2991959 = 4487939) B4487939
theorem B11355997 : Blo 1328983 11355997 := bstep (se 3 (by rfl) ⟨2129249, by rfl⟩ : syracuseStep 11355997 = 4258499) B4258499
theorem B1329003 : Blo 1328983 1329003 := bstep (se 1 (by rfl) ⟨996752, by rfl⟩ : syracuseStep 1329003 = 1993505) B1993505
theorem B1329015 : Blo 1328983 1329015 := bstep (se 1 (by rfl) ⟨996761, by rfl⟩ : syracuseStep 1329015 = 1993523) B1993523
theorem B1329035 : Blo 1328983 1329035 := bstep (se 1 (by rfl) ⟨996776, by rfl⟩ : syracuseStep 1329035 = 1993553) B1993553
theorem B1329047 : Blo 1328983 1329047 := bstep (se 1 (by rfl) ⟨996785, by rfl⟩ : syracuseStep 1329047 = 1993571) B1993571
theorem B1329067 : Blo 1328983 1329067 := bstep (se 1 (by rfl) ⟨996800, by rfl⟩ : syracuseStep 1329067 = 1993601) B1993601
theorem B51136433 : Blo 1328983 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B1329079 : Blo 1328983 1329079 := bstep (se 1 (by rfl) ⟨996809, by rfl⟩ : syracuseStep 1329079 = 1993619) B1993619
theorem B3786689 : Blo 1328983 3786689 := bstep (se 2 (by rfl) ⟨1420008, by rfl⟩ : syracuseStep 3786689 = 2840017) B2840017
theorem B1329099 : Blo 1328983 1329099 := bstep (se 1 (by rfl) ⟨996824, by rfl⟩ : syracuseStep 1329099 = 1993649) B1993649
theorem B1329111 : Blo 1328983 1329111 := bstep (se 1 (by rfl) ⟨996833, by rfl⟩ : syracuseStep 1329111 = 1993667) B1993667
theorem B1329131 : Blo 1328983 1329131 := bstep (se 1 (by rfl) ⟨996848, by rfl⟩ : syracuseStep 1329131 = 1993697) B1993697
theorem B1329143 : Blo 1328983 1329143 := bstep (se 1 (by rfl) ⟨996857, by rfl⟩ : syracuseStep 1329143 = 1993715) B1993715
theorem B1329163 : Blo 1328983 1329163 := bstep (se 1 (by rfl) ⟨996872, by rfl⟩ : syracuseStep 1329163 = 1993745) B1993745
theorem B2992139 : Blo 1328983 2992139 := bstep (se 1 (by rfl) ⟨2244104, by rfl⟩ : syracuseStep 2992139 = 4488209) B4488209
theorem B2525195 : Blo 1328983 2525195 := bstep (se 1 (by rfl) ⟨1893896, by rfl⟩ : syracuseStep 2525195 = 3787793) B3787793
theorem B1329175 : Blo 1328983 1329175 := bstep (se 1 (by rfl) ⟨996881, by rfl⟩ : syracuseStep 1329175 = 1993763) B1993763
theorem B4491287 : Blo 1328983 4491287 := bstep (se 1 (by rfl) ⟨3368465, by rfl⟩ : syracuseStep 4491287 = 6736931) B6736931
theorem B1329195 : Blo 1328983 1329195 := bstep (se 1 (by rfl) ⟨996896, by rfl⟩ : syracuseStep 1329195 = 1993793) B1993793
theorem B3033139 : Blo 1328983 3033139 := bstep (se 1 (by rfl) ⟨2274854, by rfl⟩ : syracuseStep 3033139 = 4549709) B4549709
theorem B1329207 : Blo 1328983 1329207 := bstep (se 1 (by rfl) ⟨996905, by rfl⟩ : syracuseStep 1329207 = 1993811) B1993811
theorem B2992193 : Blo 1328983 2992193 := bstep (se 2 (by rfl) ⟨1122072, by rfl⟩ : syracuseStep 2992193 = 2244145) B2244145
theorem B2525249 : Blo 1328983 2525249 := bstep (se 2 (by rfl) ⟨946968, by rfl⟩ : syracuseStep 2525249 = 1893937) B1893937
theorem B1329227 : Blo 1328983 1329227 := bstep (se 1 (by rfl) ⟨996920, by rfl⟩ : syracuseStep 1329227 = 1993841) B1993841
theorem B1329239 : Blo 1328983 1329239 := bstep (se 1 (by rfl) ⟨996929, by rfl⟩ : syracuseStep 1329239 = 1993859) B1993859
theorem B1820761 : Blo 1328983 1820761 := bstep (se 2 (by rfl) ⟨682785, by rfl⟩ : syracuseStep 1820761 = 1365571) B1365571
theorem B1329259 : Blo 1328983 1329259 := bstep (se 1 (by rfl) ⟨996944, by rfl⟩ : syracuseStep 1329259 = 1993889) B1993889
theorem B1329271 : Blo 1328983 1329271 := bstep (se 1 (by rfl) ⟨996953, by rfl⟩ : syracuseStep 1329271 = 1993907) B1993907
theorem B1329291 : Blo 1328983 1329291 := bstep (se 1 (by rfl) ⟨996968, by rfl⟩ : syracuseStep 1329291 = 1993937) B1993937
theorem B1329303 : Blo 1328983 1329303 := bstep (se 1 (by rfl) ⟨996977, by rfl⟩ : syracuseStep 1329303 = 1993955) B1993955
theorem B1329323 : Blo 1328983 1329323 := bstep (se 1 (by rfl) ⟨996992, by rfl⟩ : syracuseStep 1329323 = 1993985) B1993985
theorem B1329335 : Blo 1328983 1329335 := bstep (se 1 (by rfl) ⟨997001, by rfl⟩ : syracuseStep 1329335 = 1994003) B1994003
theorem B1329355 : Blo 1328983 1329355 := bstep (se 1 (by rfl) ⟨997016, by rfl⟩ : syracuseStep 1329355 = 1994033) B1994033
theorem B1894603 : Blo 1328983 1894603 := bstep (se 1 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 1894603 = 2841905) B2841905
theorem B1329367 : Blo 1328983 1329367 := bstep (se 1 (by rfl) ⟨997025, by rfl⟩ : syracuseStep 1329367 = 1994051) B1994051
theorem B1329387 : Blo 1328983 1329387 := bstep (se 1 (by rfl) ⟨997040, by rfl⟩ : syracuseStep 1329387 = 1994081) B1994081
theorem B1329399 : Blo 1328983 1329399 := bstep (se 1 (by rfl) ⟨997049, by rfl⟩ : syracuseStep 1329399 = 1994099) B1994099
theorem B1329419 : Blo 1328983 1329419 := bstep (se 1 (by rfl) ⟨997064, by rfl⟩ : syracuseStep 1329419 = 1994129) B1994129
theorem B1329431 : Blo 1328983 1329431 := bstep (se 1 (by rfl) ⟨997073, by rfl⟩ : syracuseStep 1329431 = 1994147) B1994147
theorem B2992409 : Blo 1328983 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B1329451 : Blo 1328983 1329451 := bstep (se 1 (by rfl) ⟨997088, by rfl⟩ : syracuseStep 1329451 = 1994177) B1994177
theorem B1329463 : Blo 1328983 1329463 := bstep (se 1 (by rfl) ⟨997097, by rfl⟩ : syracuseStep 1329463 = 1994195) B1994195
theorem B1329483 : Blo 1328983 1329483 := bstep (se 1 (by rfl) ⟨997112, by rfl⟩ : syracuseStep 1329483 = 1994225) B1994225
theorem B1329495 : Blo 1328983 1329495 := bstep (se 1 (by rfl) ⟨997121, by rfl⟩ : syracuseStep 1329495 = 1994243) B1994243
theorem B1329515 : Blo 1328983 1329515 := bstep (se 1 (by rfl) ⟨997136, by rfl⟩ : syracuseStep 1329515 = 1994273) B1994273
theorem B2992499 : Blo 1328983 2992499 := bstep (se 1 (by rfl) ⟨2244374, by rfl⟩ : syracuseStep 2992499 = 4488749) B4488749
theorem B1329527 : Blo 1328983 1329527 := bstep (se 1 (by rfl) ⟨997145, by rfl⟩ : syracuseStep 1329527 = 1994291) B1994291
theorem B1329547 : Blo 1328983 1329547 := bstep (se 1 (by rfl) ⟨997160, by rfl⟩ : syracuseStep 1329547 = 1994321) B1994321
theorem B1329559 : Blo 1328983 1329559 := bstep (se 1 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 1329559 = 1994339) B1994339
theorem B2992535 : Blo 1328983 2992535 := bstep (se 1 (by rfl) ⟨2244401, by rfl⟩ : syracuseStep 2992535 = 4488803) B4488803
theorem B3197335 : Blo 1328983 3197335 := bstep (se 1 (by rfl) ⟨2398001, by rfl⟩ : syracuseStep 3197335 = 4796003) B4796003
theorem B1329579 : Blo 1328983 1329579 := bstep (se 1 (by rfl) ⟨997184, by rfl⟩ : syracuseStep 1329579 = 1994369) B1994369
theorem B1329591 : Blo 1328983 1329591 := bstep (se 1 (by rfl) ⟨997193, by rfl⟩ : syracuseStep 1329591 = 1994387) B1994387
theorem B1329611 : Blo 1328983 1329611 := bstep (se 1 (by rfl) ⟨997208, by rfl⟩ : syracuseStep 1329611 = 1994417) B1994417
theorem B1329623 : Blo 1328983 1329623 := bstep (se 1 (by rfl) ⟨997217, by rfl⟩ : syracuseStep 1329623 = 1994435) B1994435
theorem B1329643 : Blo 1328983 1329643 := bstep (se 1 (by rfl) ⟨997232, by rfl⟩ : syracuseStep 1329643 = 1994465) B1994465
theorem B1329655 : Blo 1328983 1329655 := bstep (se 1 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 1329655 = 1994483) B1994483
theorem B1329675 : Blo 1328983 1329675 := bstep (se 1 (by rfl) ⟨997256, by rfl⟩ : syracuseStep 1329675 = 1994513) B1994513
theorem B1329687 : Blo 1328983 1329687 := bstep (se 1 (by rfl) ⟨997265, by rfl⟩ : syracuseStep 1329687 = 1994531) B1994531
theorem B16181795 : Blo 1328983 16181795 := bstep (se 1 (by rfl) ⟨12136346, by rfl⟩ : syracuseStep 16181795 = 24272693) B24272693
theorem B1329707 : Blo 1328983 1329707 := bstep (se 1 (by rfl) ⟨997280, by rfl⟩ : syracuseStep 1329707 = 1994561) B1994561
theorem B4491827 : Blo 1328983 4491827 := bstep (se 1 (by rfl) ⟨3368870, by rfl⟩ : syracuseStep 4491827 = 6737741) B6737741
theorem B1329719 : Blo 1328983 1329719 := bstep (se 1 (by rfl) ⟨997289, by rfl⟩ : syracuseStep 1329719 = 1994579) B1994579
theorem B1329739 : Blo 1328983 1329739 := bstep (se 1 (by rfl) ⟨997304, by rfl⟩ : syracuseStep 1329739 = 1994609) B1994609
theorem B2992715 : Blo 1328983 2992715 := bstep (se 1 (by rfl) ⟨2244536, by rfl⟩ : syracuseStep 2992715 = 4489073) B4489073
theorem B1329751 : Blo 1328983 1329751 := bstep (se 1 (by rfl) ⟨997313, by rfl⟩ : syracuseStep 1329751 = 1994627) B1994627
theorem B1329771 : Blo 1328983 1329771 := bstep (se 1 (by rfl) ⟨997328, by rfl⟩ : syracuseStep 1329771 = 1994657) B1994657
theorem B1329783 : Blo 1328983 1329783 := bstep (se 1 (by rfl) ⟨997337, by rfl⟩ : syracuseStep 1329783 = 1994675) B1994675
theorem B2992769 : Blo 1328983 2992769 := bstep (se 2 (by rfl) ⟨1122288, by rfl⟩ : syracuseStep 2992769 = 2244577) B2244577
theorem B5048963 : Blo 1328983 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B2558603 : Blo 1328983 2558603 := bstep (se 1 (by rfl) ⟨1918952, by rfl⟩ : syracuseStep 2558603 = 3837905) B3837905
theorem B1329803 : Blo 1328983 1329803 := bstep (se 1 (by rfl) ⟨997352, by rfl⟩ : syracuseStep 1329803 = 1994705) B1994705
theorem B9218711 : Blo 1328983 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B1329815 : Blo 1328983 1329815 := bstep (se 1 (by rfl) ⟨997361, by rfl⟩ : syracuseStep 1329815 = 1994723) B1994723
theorem B1329835 : Blo 1328983 1329835 := bstep (se 1 (by rfl) ⟨997376, by rfl⟩ : syracuseStep 1329835 = 1994753) B1994753
theorem B1329847 : Blo 1328983 1329847 := bstep (se 1 (by rfl) ⟨997385, by rfl⟩ : syracuseStep 1329847 = 1994771) B1994771
theorem B1329867 : Blo 1328983 1329867 := bstep (se 1 (by rfl) ⟨997400, by rfl⟩ : syracuseStep 1329867 = 1994801) B1994801
theorem B1329879 : Blo 1328983 1329879 := bstep (se 1 (by rfl) ⟨997409, by rfl⟩ : syracuseStep 1329879 = 1994819) B1994819
theorem B1329899 : Blo 1328983 1329899 := bstep (se 1 (by rfl) ⟨997424, by rfl⟩ : syracuseStep 1329899 = 1994849) B1994849
theorem B1329911 : Blo 1328983 1329911 := bstep (se 1 (by rfl) ⟨997433, by rfl⟩ : syracuseStep 1329911 = 1994867) B1994867
theorem B4795139 : Blo 1328983 4795139 := bstep (se 1 (by rfl) ⟨3596354, by rfl⟩ : syracuseStep 4795139 = 7192709) B7192709
theorem B1329931 : Blo 1328983 1329931 := bstep (se 1 (by rfl) ⟨997448, by rfl⟩ : syracuseStep 1329931 = 1994897) B1994897
theorem B1329943 : Blo 1328983 1329943 := bstep (se 1 (by rfl) ⟨997457, by rfl⟩ : syracuseStep 1329943 = 1994915) B1994915
theorem B3197719 : Blo 1328983 3197719 := bstep (se 1 (by rfl) ⟨2398289, by rfl⟩ : syracuseStep 3197719 = 4796579) B4796579
theorem B1329963 : Blo 1328983 1329963 := bstep (se 1 (by rfl) ⟨997472, by rfl⟩ : syracuseStep 1329963 = 1994945) B1994945
theorem B1329975 : Blo 1328983 1329975 := bstep (se 1 (by rfl) ⟨997481, by rfl⟩ : syracuseStep 1329975 = 1994963) B1994963
theorem B1993547 : Blo 1328983 1993547 := bstep (se 1 (by rfl) ⟨1495160, by rfl⟩ : syracuseStep 1993547 = 2990321) B2990321
theorem B1329995 : Blo 1328983 1329995 := bstep (se 1 (by rfl) ⟨997496, by rfl⟩ : syracuseStep 1329995 = 1994993) B1994993
theorem B1993559 : Blo 1328983 1993559 := bstep (se 1 (by rfl) ⟨1495169, by rfl⟩ : syracuseStep 1993559 = 2990339) B2990339
theorem B1330007 : Blo 1328983 1330007 := bstep (se 1 (by rfl) ⟨997505, by rfl⟩ : syracuseStep 1330007 = 1995011) B1995011
theorem B2992985 : Blo 1328983 2992985 := bstep (se 2 (by rfl) ⟨1122369, by rfl⟩ : syracuseStep 2992985 = 2244739) B2244739
theorem B1330027 : Blo 1328983 1330027 := bstep (se 1 (by rfl) ⟨997520, by rfl⟩ : syracuseStep 1330027 = 1995041) B1995041
theorem B1330039 : Blo 1328983 1330039 := bstep (se 1 (by rfl) ⟨997529, by rfl⟩ : syracuseStep 1330039 = 1995059) B1995059
theorem B1330059 : Blo 1328983 1330059 := bstep (se 1 (by rfl) ⟨997544, by rfl⟩ : syracuseStep 1330059 = 1995089) B1995089
theorem B1330071 : Blo 1328983 1330071 := bstep (se 1 (by rfl) ⟨997553, by rfl⟩ : syracuseStep 1330071 = 1995107) B1995107
theorem B1993625 : Blo 1328983 1993625 := bstep (se 2 (by rfl) ⟨747609, by rfl⟩ : syracuseStep 1993625 = 1495219) B1495219
theorem B1330091 : Blo 1328983 1330091 := bstep (se 1 (by rfl) ⟨997568, by rfl⟩ : syracuseStep 1330091 = 1995137) B1995137
theorem B2993075 : Blo 1328983 2993075 := bstep (se 1 (by rfl) ⟨2244806, by rfl⟩ : syracuseStep 2993075 = 4489613) B4489613
theorem B1330103 : Blo 1328983 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B1330123 : Blo 1328983 1330123 := bstep (se 1 (by rfl) ⟨997592, by rfl⟩ : syracuseStep 1330123 = 1995185) B1995185
theorem B1330135 : Blo 1328983 1330135 := bstep (se 1 (by rfl) ⟨997601, by rfl⟩ : syracuseStep 1330135 = 1995203) B1995203
theorem B2993111 : Blo 1328983 2993111 := bstep (se 1 (by rfl) ⟨2244833, by rfl⟩ : syracuseStep 2993111 = 4489667) B4489667
theorem B218344409 : Blo 1328983 218344409 := bstep (se 2 (by rfl) ⟨81879153, by rfl⟩ : syracuseStep 218344409 = 163758307) B163758307
theorem B2526167 : Blo 1328983 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B1330155 : Blo 1328983 1330155 := bstep (se 1 (by rfl) ⟨997616, by rfl⟩ : syracuseStep 1330155 = 1995233) B1995233
theorem B1330167 : Blo 1328983 1330167 := bstep (se 1 (by rfl) ⟨997625, by rfl⟩ : syracuseStep 1330167 = 1995251) B1995251
theorem B1993739 : Blo 1328983 1993739 := bstep (se 1 (by rfl) ⟨1495304, by rfl⟩ : syracuseStep 1993739 = 2990609) B2990609
theorem B1330187 : Blo 1328983 1330187 := bstep (se 1 (by rfl) ⟨997640, by rfl⟩ : syracuseStep 1330187 = 1995281) B1995281
theorem B1993751 : Blo 1328983 1993751 := bstep (se 1 (by rfl) ⟨1495313, by rfl⟩ : syracuseStep 1993751 = 2990627) B2990627
theorem B1330199 : Blo 1328983 1330199 := bstep (se 1 (by rfl) ⟨997649, by rfl⟩ : syracuseStep 1330199 = 1995299) B1995299
theorem B48540707 : Blo 1328983 48540707 := bstep (se 1 (by rfl) ⟨36405530, by rfl⟩ : syracuseStep 48540707 = 72811061) B72811061
theorem B1330219 : Blo 1328983 1330219 := bstep (se 1 (by rfl) ⟨997664, by rfl⟩ : syracuseStep 1330219 = 1995329) B1995329
theorem B1330231 : Blo 1328983 1330231 := bstep (se 1 (by rfl) ⟨997673, by rfl⟩ : syracuseStep 1330231 = 1995347) B1995347
theorem B38374469 : Blo 1328983 38374469 := bstep (se 4 (by rfl) ⟨3597606, by rfl⟩ : syracuseStep 38374469 = 7195213) B7195213
theorem B43142219 : Blo 1328983 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B1420363 : Blo 1328983 1420363 := bstep (se 1 (by rfl) ⟨1065272, by rfl⟩ : syracuseStep 1420363 = 2130545) B2130545
theorem B1330251 : Blo 1328983 1330251 := bstep (se 1 (by rfl) ⟨997688, by rfl⟩ : syracuseStep 1330251 = 1995377) B1995377
theorem B1330263 : Blo 1328983 1330263 := bstep (se 1 (by rfl) ⟨997697, by rfl⟩ : syracuseStep 1330263 = 1995395) B1995395
theorem B1993817 : Blo 1328983 1993817 := bstep (se 2 (by rfl) ⟨747681, by rfl⟩ : syracuseStep 1993817 = 1495363) B1495363
theorem B1330283 : Blo 1328983 1330283 := bstep (se 1 (by rfl) ⟨997712, by rfl⟩ : syracuseStep 1330283 = 1995425) B1995425
theorem B1330295 : Blo 1328983 1330295 := bstep (se 1 (by rfl) ⟨997721, by rfl⟩ : syracuseStep 1330295 = 1995443) B1995443
theorem B1330315 : Blo 1328983 1330315 := bstep (se 1 (by rfl) ⟨997736, by rfl⟩ : syracuseStep 1330315 = 1995473) B1995473
theorem B2993291 : Blo 1328983 2993291 := bstep (se 1 (by rfl) ⟨2244968, by rfl⟩ : syracuseStep 2993291 = 4489937) B4489937
theorem B1330327 : Blo 1328983 1330327 := bstep (se 1 (by rfl) ⟨997745, by rfl⟩ : syracuseStep 1330327 = 1995491) B1995491
theorem B1330347 : Blo 1328983 1330347 := bstep (se 1 (by rfl) ⟨997760, by rfl⟩ : syracuseStep 1330347 = 1995521) B1995521
theorem B5680307 : Blo 1328983 5680307 := bstep (se 1 (by rfl) ⟨4260230, by rfl⟩ : syracuseStep 5680307 = 8520461) B8520461
theorem B1330359 : Blo 1328983 1330359 := bstep (se 1 (by rfl) ⟨997769, by rfl⟩ : syracuseStep 1330359 = 1995539) B1995539
theorem B10792115 : Blo 1328983 10792115 := bstep (se 1 (by rfl) ⟨8094086, by rfl⟩ : syracuseStep 10792115 = 16188173) B16188173
theorem B2993345 : Blo 1328983 2993345 := bstep (se 2 (by rfl) ⟨1122504, by rfl⟩ : syracuseStep 2993345 = 2245009) B2245009
theorem B1993931 : Blo 1328983 1993931 := bstep (se 1 (by rfl) ⟨1495448, by rfl⟩ : syracuseStep 1993931 = 2990897) B2990897
theorem B1330379 : Blo 1328983 1330379 := bstep (se 1 (by rfl) ⟨997784, by rfl⟩ : syracuseStep 1330379 = 1995569) B1995569
theorem B1993943 : Blo 1328983 1993943 := bstep (se 1 (by rfl) ⟨1495457, by rfl⟩ : syracuseStep 1993943 = 2990915) B2990915
theorem B1330391 : Blo 1328983 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B1330411 : Blo 1328983 1330411 := bstep (se 1 (by rfl) ⟨997808, by rfl⟩ : syracuseStep 1330411 = 1995617) B1995617
theorem B1330423 : Blo 1328983 1330423 := bstep (se 1 (by rfl) ⟨997817, by rfl⟩ : syracuseStep 1330423 = 1995635) B1995635
theorem B1330443 : Blo 1328983 1330443 := bstep (se 1 (by rfl) ⟨997832, by rfl⟩ : syracuseStep 1330443 = 1995665) B1995665
theorem B1330455 : Blo 1328983 1330455 := bstep (se 1 (by rfl) ⟨997841, by rfl⟩ : syracuseStep 1330455 = 1995683) B1995683
theorem B1994009 : Blo 1328983 1994009 := bstep (se 2 (by rfl) ⟨747753, by rfl⟩ : syracuseStep 1994009 = 1495507) B1495507
theorem B1330475 : Blo 1328983 1330475 := bstep (se 1 (by rfl) ⟨997856, by rfl⟩ : syracuseStep 1330475 = 1995713) B1995713
theorem B1330487 : Blo 1328983 1330487 := bstep (se 1 (by rfl) ⟨997865, by rfl⟩ : syracuseStep 1330487 = 1995731) B1995731
theorem B7187777 : Blo 1328983 7187777 := bstep (se 2 (by rfl) ⟨2695416, by rfl⟩ : syracuseStep 7187777 = 5390833) B5390833
theorem B5680459 : Blo 1328983 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B1330507 : Blo 1328983 1330507 := bstep (se 1 (by rfl) ⟨997880, by rfl⟩ : syracuseStep 1330507 = 1995761) B1995761
theorem B1330519 : Blo 1328983 1330519 := bstep (se 1 (by rfl) ⟨997889, by rfl⟩ : syracuseStep 1330519 = 1995779) B1995779
theorem B5541209 : Blo 1328983 5541209 := bstep (se 2 (by rfl) ⟨2077953, by rfl⟩ : syracuseStep 5541209 = 4155907) B4155907
theorem B5393753 : Blo 1328983 5393753 := bstep (se 2 (by rfl) ⟨2022657, by rfl⟩ : syracuseStep 5393753 = 4045315) B4045315
theorem B1330539 : Blo 1328983 1330539 := bstep (se 1 (by rfl) ⟨997904, by rfl⟩ : syracuseStep 1330539 = 1995809) B1995809
theorem B1330551 : Blo 1328983 1330551 := bstep (se 1 (by rfl) ⟨997913, by rfl⟩ : syracuseStep 1330551 = 1995827) B1995827
theorem B1994123 : Blo 1328983 1994123 := bstep (se 1 (by rfl) ⟨1495592, by rfl⟩ : syracuseStep 1994123 = 2991185) B2991185
theorem B1330571 : Blo 1328983 1330571 := bstep (se 1 (by rfl) ⟨997928, by rfl⟩ : syracuseStep 1330571 = 1995857) B1995857
theorem B5680529 : Blo 1328983 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B1994135 : Blo 1328983 1994135 := bstep (se 1 (by rfl) ⟨1495601, by rfl⟩ : syracuseStep 1994135 = 2991203) B2991203
theorem B1330583 : Blo 1328983 1330583 := bstep (se 1 (by rfl) ⟨997937, by rfl⟩ : syracuseStep 1330583 = 1995875) B1995875
theorem B2993561 : Blo 1328983 2993561 := bstep (se 2 (by rfl) ⟨1122585, by rfl⟩ : syracuseStep 2993561 = 2245171) B2245171
theorem B1330603 : Blo 1328983 1330603 := bstep (se 1 (by rfl) ⟨997952, by rfl⟩ : syracuseStep 1330603 = 1995905) B1995905
theorem B12307889 : Blo 1328983 12307889 := bstep (se 2 (by rfl) ⟨4615458, by rfl⟩ : syracuseStep 12307889 = 9230917) B9230917
theorem B1330615 : Blo 1328983 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B2395595 : Blo 1328983 2395595 := bstep (se 1 (by rfl) ⟨1796696, by rfl⟩ : syracuseStep 2395595 = 3593393) B3593393
theorem B1330635 : Blo 1328983 1330635 := bstep (se 1 (by rfl) ⟨997976, by rfl⟩ : syracuseStep 1330635 = 1995953) B1995953
theorem B1330647 : Blo 1328983 1330647 := bstep (se 1 (by rfl) ⟨997985, by rfl⟩ : syracuseStep 1330647 = 1995971) B1995971
theorem B1994201 : Blo 1328983 1994201 := bstep (se 2 (by rfl) ⟨747825, by rfl⟩ : syracuseStep 1994201 = 1495651) B1495651
theorem B1330667 : Blo 1328983 1330667 := bstep (se 1 (by rfl) ⟨998000, by rfl⟩ : syracuseStep 1330667 = 1996001) B1996001
theorem B2993651 : Blo 1328983 2993651 := bstep (se 1 (by rfl) ⟨2245238, by rfl⟩ : syracuseStep 2993651 = 4490477) B4490477
theorem B1330679 : Blo 1328983 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B2526707 : Blo 1328983 2526707 := bstep (se 1 (by rfl) ⟨1895030, by rfl⟩ : syracuseStep 2526707 = 3790061) B3790061
theorem B1330699 : Blo 1328983 1330699 := bstep (se 1 (by rfl) ⟨998024, by rfl⟩ : syracuseStep 1330699 = 1996049) B1996049
theorem B2993687 : Blo 1328983 2993687 := bstep (se 1 (by rfl) ⟨2245265, by rfl⟩ : syracuseStep 2993687 = 4490531) B4490531
theorem B1330711 : Blo 1328983 1330711 := bstep (se 1 (by rfl) ⟨998033, by rfl⟩ : syracuseStep 1330711 = 1996067) B1996067
theorem B10096163 : Blo 1328983 10096163 := bstep (se 1 (by rfl) ⟨7572122, by rfl⟩ : syracuseStep 10096163 = 15144245) B15144245
theorem B1330731 : Blo 1328983 1330731 := bstep (se 1 (by rfl) ⟨998048, by rfl⟩ : syracuseStep 1330731 = 1996097) B1996097
theorem B1330743 : Blo 1328983 1330743 := bstep (se 1 (by rfl) ⟨998057, by rfl⟩ : syracuseStep 1330743 = 1996115) B1996115
theorem B5115467 : Blo 1328983 5115467 := bstep (se 1 (by rfl) ⟨3836600, by rfl⟩ : syracuseStep 5115467 = 7673201) B7673201
theorem B1994315 : Blo 1328983 1994315 := bstep (se 1 (by rfl) ⟨1495736, by rfl⟩ : syracuseStep 1994315 = 2991473) B2991473
theorem B3788363 : Blo 1328983 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B1330763 : Blo 1328983 1330763 := bstep (se 1 (by rfl) ⟨998072, by rfl⟩ : syracuseStep 1330763 = 1996145) B1996145
theorem B1994327 : Blo 1328983 1994327 := bstep (se 1 (by rfl) ⟨1495745, by rfl⟩ : syracuseStep 1994327 = 2991491) B2991491
theorem B1330775 : Blo 1328983 1330775 := bstep (se 1 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 1330775 = 1996163) B1996163
theorem B1330795 : Blo 1328983 1330795 := bstep (se 1 (by rfl) ⟨998096, by rfl⟩ : syracuseStep 1330795 = 1996193) B1996193
theorem B1330807 : Blo 1328983 1330807 := bstep (se 1 (by rfl) ⟨998105, by rfl⟩ : syracuseStep 1330807 = 1996211) B1996211
theorem B1330827 : Blo 1328983 1330827 := bstep (se 1 (by rfl) ⟨998120, by rfl⟩ : syracuseStep 1330827 = 1996241) B1996241
theorem B1330839 : Blo 1328983 1330839 := bstep (se 1 (by rfl) ⟨998129, by rfl⟩ : syracuseStep 1330839 = 1996259) B1996259
theorem B1994393 : Blo 1328983 1994393 := bstep (se 2 (by rfl) ⟨747897, by rfl⟩ : syracuseStep 1994393 = 1495795) B1495795
theorem B1330859 : Blo 1328983 1330859 := bstep (se 1 (by rfl) ⟨998144, by rfl⟩ : syracuseStep 1330859 = 1996289) B1996289
theorem B10243763 : Blo 1328983 10243763 := bstep (se 1 (by rfl) ⟨7682822, by rfl⟩ : syracuseStep 10243763 = 15365645) B15365645
theorem B1330871 : Blo 1328983 1330871 := bstep (se 1 (by rfl) ⟨998153, by rfl⟩ : syracuseStep 1330871 = 1996307) B1996307
theorem B2993867 : Blo 1328983 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B1330891 : Blo 1328983 1330891 := bstep (se 1 (by rfl) ⟨998168, by rfl⟩ : syracuseStep 1330891 = 1996337) B1996337
theorem B1330903 : Blo 1328983 1330903 := bstep (se 1 (by rfl) ⟨998177, by rfl⟩ : syracuseStep 1330903 = 1996355) B1996355
theorem B1330923 : Blo 1328983 1330923 := bstep (se 1 (by rfl) ⟨998192, by rfl⟩ : syracuseStep 1330923 = 1996385) B1996385
theorem B1330935 : Blo 1328983 1330935 := bstep (se 1 (by rfl) ⟨998201, by rfl⟩ : syracuseStep 1330935 = 1996403) B1996403
theorem B2993921 : Blo 1328983 2993921 := bstep (se 2 (by rfl) ⟨1122720, by rfl⟩ : syracuseStep 2993921 = 2245441) B2245441
theorem B1994507 : Blo 1328983 1994507 := bstep (se 1 (by rfl) ⟨1495880, by rfl⟩ : syracuseStep 1994507 = 2991761) B2991761
theorem B1330955 : Blo 1328983 1330955 := bstep (se 1 (by rfl) ⟨998216, by rfl⟩ : syracuseStep 1330955 = 1996433) B1996433
theorem B1994519 : Blo 1328983 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B1330967 : Blo 1328983 1330967 := bstep (se 1 (by rfl) ⟨998225, by rfl⟩ : syracuseStep 1330967 = 1996451) B1996451
theorem B19181357 : Blo 1328983 19181357 := bstep (se 3 (by rfl) ⟨3596504, by rfl⟩ : syracuseStep 19181357 = 7193009) B7193009
theorem B1994585 : Blo 1328983 1994585 := bstep (se 2 (by rfl) ⟨747969, by rfl⟩ : syracuseStep 1994585 = 1495939) B1495939
theorem B1994699 : Blo 1328983 1994699 := bstep (se 1 (by rfl) ⟨1496024, by rfl⟩ : syracuseStep 1994699 = 2992049) B2992049
theorem B1994711 : Blo 1328983 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B2994137 : Blo 1328983 2994137 := bstep (se 2 (by rfl) ⟨1122801, by rfl⟩ : syracuseStep 2994137 = 2245603) B2245603
theorem B10103939 : Blo 1328983 10103939 := bstep (se 1 (by rfl) ⟨7577954, by rfl⟩ : syracuseStep 10103939 = 15155909) B15155909
theorem B2838539 : Blo 1328983 2838539 := bstep (se 1 (by rfl) ⟨2128904, by rfl⟩ : syracuseStep 2838539 = 4257809) B4257809
theorem B1994777 : Blo 1328983 1994777 := bstep (se 2 (by rfl) ⟨748041, by rfl⟩ : syracuseStep 1994777 = 1496083) B1496083
theorem B2994227 : Blo 1328983 2994227 := bstep (se 1 (by rfl) ⟨2245670, by rfl⟩ : syracuseStep 2994227 = 4491341) B4491341
theorem B6729803 : Blo 1328983 6729803 := bstep (se 1 (by rfl) ⟨5047352, by rfl⟩ : syracuseStep 6729803 = 10094705) B10094705
theorem B2994263 : Blo 1328983 2994263 := bstep (se 1 (by rfl) ⟨2245697, by rfl⟩ : syracuseStep 2994263 = 4491395) B4491395
theorem B1495147 : Blo 1328983 1495147 := bstep (se 1 (by rfl) ⟨1121360, by rfl⟩ : syracuseStep 1495147 = 2242721) B2242721
theorem B1994891 : Blo 1328983 1994891 := bstep (se 1 (by rfl) ⟨1496168, by rfl⟩ : syracuseStep 1994891 = 2992337) B2992337
theorem B1683595 : Blo 1328983 1683595 := bstep (se 1 (by rfl) ⟨1262696, by rfl⟩ : syracuseStep 1683595 = 2525393) B2525393
theorem B1994903 : Blo 1328983 1994903 := bstep (se 1 (by rfl) ⟨1496177, by rfl⟩ : syracuseStep 1994903 = 2992355) B2992355
theorem B2879641 : Blo 1328983 2879641 := bstep (se 2 (by rfl) ⟨1079865, by rfl⟩ : syracuseStep 2879641 = 2159731) B2159731
theorem B4042955 : Blo 1328983 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B1495255 : Blo 1328983 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1994969 : Blo 1328983 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B2994443 : Blo 1328983 2994443 := bstep (se 1 (by rfl) ⟨2245832, by rfl⟩ : syracuseStep 2994443 = 4491665) B4491665
theorem B2994497 : Blo 1328983 2994497 := bstep (se 2 (by rfl) ⟨1122936, by rfl⟩ : syracuseStep 2994497 = 2245873) B2245873
theorem B1995083 : Blo 1328983 1995083 := bstep (se 1 (by rfl) ⟨1496312, by rfl⟩ : syracuseStep 1995083 = 2992625) B2992625
theorem B1995095 : Blo 1328983 1995095 := bstep (se 1 (by rfl) ⟨1496321, by rfl⟩ : syracuseStep 1995095 = 2992643) B2992643
theorem B2396531 : Blo 1328983 2396531 := bstep (se 1 (by rfl) ⟨1797398, by rfl⟩ : syracuseStep 2396531 = 3594797) B3594797
theorem B1495435 : Blo 1328983 1495435 := bstep (se 1 (by rfl) ⟨1121576, by rfl⟩ : syracuseStep 1495435 = 2243153) B2243153
theorem B34550165 : Blo 1328983 34550165 := bstep (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) B1619539
theorem B1995161 : Blo 1328983 1995161 := bstep (se 2 (by rfl) ⟨748185, by rfl⟩ : syracuseStep 1995161 = 1496371) B1496371
theorem B1495543 : Blo 1328983 1495543 := bstep (se 1 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 1495543 = 2243315) B2243315
theorem B1995275 : Blo 1328983 1995275 := bstep (se 1 (by rfl) ⟨1496456, by rfl⟩ : syracuseStep 1995275 = 2992913) B2992913
theorem B1995287 : Blo 1328983 1995287 := bstep (se 1 (by rfl) ⟨1496465, by rfl⟩ : syracuseStep 1995287 = 2992931) B2992931
theorem B2994713 : Blo 1328983 2994713 := bstep (se 2 (by rfl) ⟨1123017, by rfl⟩ : syracuseStep 2994713 = 2246035) B2246035
theorem B2396747 : Blo 1328983 2396747 := bstep (se 1 (by rfl) ⟨1797560, by rfl⟩ : syracuseStep 2396747 = 3595121) B3595121
theorem B1995353 : Blo 1328983 1995353 := bstep (se 2 (by rfl) ⟨748257, by rfl⟩ : syracuseStep 1995353 = 1496515) B1496515
theorem B4485725 : Blo 1328983 4485725 := bstep (se 3 (by rfl) ⟨841073, by rfl⟩ : syracuseStep 4485725 = 1682147) B1682147
theorem B1495723 : Blo 1328983 1495723 := bstep (se 1 (by rfl) ⟨1121792, by rfl⟩ : syracuseStep 1495723 = 2243585) B2243585
theorem B2880193 : Blo 1328983 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B1995467 : Blo 1328983 1995467 := bstep (se 1 (by rfl) ⟨1496600, by rfl⟩ : syracuseStep 1995467 = 2993201) B2993201
theorem B19690189 : Blo 1328983 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B1995479 : Blo 1328983 1995479 := bstep (se 1 (by rfl) ⟨1496609, by rfl⟩ : syracuseStep 1995479 = 2993219) B2993219
theorem B8524561 : Blo 1328983 8524561 := bstep (se 2 (by rfl) ⟨3196710, by rfl⟩ : syracuseStep 8524561 = 6393421) B6393421
theorem B1495831 : Blo 1328983 1495831 := bstep (se 1 (by rfl) ⟨1121873, by rfl⟩ : syracuseStep 1495831 = 2243747) B2243747
theorem B1995545 : Blo 1328983 1995545 := bstep (se 2 (by rfl) ⟨748329, by rfl⟩ : syracuseStep 1995545 = 1496659) B1496659
theorem B3789661 : Blo 1328983 3789661 := bstep (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) B1421123
theorem B1995659 : Blo 1328983 1995659 := bstep (se 1 (by rfl) ⟨1496744, by rfl⟩ : syracuseStep 1995659 = 2993489) B2993489
theorem B1995671 : Blo 1328983 1995671 := bstep (se 1 (by rfl) ⟨1496753, by rfl⟩ : syracuseStep 1995671 = 2993507) B2993507
theorem B5395373 : Blo 1328983 5395373 := bstep (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) B2023265
theorem B1496011 : Blo 1328983 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B1995737 : Blo 1328983 1995737 := bstep (se 2 (by rfl) ⟨748401, by rfl⟩ : syracuseStep 1995737 = 1496803) B1496803
theorem B5682221 : Blo 1328983 5682221 := bstep (se 3 (by rfl) ⟨1065416, by rfl⟩ : syracuseStep 5682221 = 2130833) B2130833
theorem B1496119 : Blo 1328983 1496119 := bstep (se 1 (by rfl) ⟨1122089, by rfl⟩ : syracuseStep 1496119 = 2244179) B2244179
theorem B1995851 : Blo 1328983 1995851 := bstep (se 1 (by rfl) ⟨1496888, by rfl⟩ : syracuseStep 1995851 = 2993777) B2993777
theorem B1995863 : Blo 1328983 1995863 := bstep (se 1 (by rfl) ⟨1496897, by rfl⟩ : syracuseStep 1995863 = 2993795) B2993795
theorem B32363671 : Blo 1328983 32363671 := bstep (se 1 (by rfl) ⟨24272753, by rfl⟩ : syracuseStep 32363671 = 48545507) B48545507
theorem B1995929 : Blo 1328983 1995929 := bstep (se 2 (by rfl) ⟨748473, by rfl⟩ : syracuseStep 1995929 = 1496947) B1496947
theorem B3790003 : Blo 1328983 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B2839769 : Blo 1328983 2839769 := bstep (se 2 (by rfl) ⟨1064913, by rfl⟩ : syracuseStep 2839769 = 2129827) B2129827
theorem B1496299 : Blo 1328983 1496299 := bstep (se 1 (by rfl) ⟨1122224, by rfl⟩ : syracuseStep 1496299 = 2244449) B2244449
theorem B1996043 : Blo 1328983 1996043 := bstep (se 1 (by rfl) ⟨1497032, by rfl⟩ : syracuseStep 1996043 = 2994065) B2994065
theorem B1996055 : Blo 1328983 1996055 := bstep (se 1 (by rfl) ⟨1497041, by rfl⟩ : syracuseStep 1996055 = 2994083) B2994083
theorem B1496407 : Blo 1328983 1496407 := bstep (se 1 (by rfl) ⟨1122305, by rfl⟩ : syracuseStep 1496407 = 2244611) B2244611
theorem B1996121 : Blo 1328983 1996121 := bstep (se 2 (by rfl) ⟨748545, by rfl⟩ : syracuseStep 1996121 = 1497091) B1497091
theorem B6395267 : Blo 1328983 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B3593651 : Blo 1328983 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B3413441 : Blo 1328983 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B4855243 : Blo 1328983 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B1996235 : Blo 1328983 1996235 := bstep (se 1 (by rfl) ⟨1497176, by rfl⟩ : syracuseStep 1996235 = 2994353) B2994353
theorem B1996247 : Blo 1328983 1996247 := bstep (se 1 (by rfl) ⟨1497185, by rfl⟩ : syracuseStep 1996247 = 2994371) B2994371
theorem B4789763 : Blo 1328983 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B1496587 : Blo 1328983 1496587 := bstep (se 1 (by rfl) ⟨1122440, by rfl⟩ : syracuseStep 1496587 = 2244881) B2244881
theorem B3364375 : Blo 1328983 3364375 := bstep (se 1 (by rfl) ⟨2523281, by rfl⟩ : syracuseStep 3364375 = 5046563) B5046563
theorem B1996313 : Blo 1328983 1996313 := bstep (se 2 (by rfl) ⟨748617, by rfl⟩ : syracuseStep 1996313 = 1497235) B1497235
theorem B1480279 : Blo 1328983 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B21575261 : Blo 1328983 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B8525405 : Blo 1328983 8525405 := bstep (se 3 (by rfl) ⟨1598513, by rfl⟩ : syracuseStep 8525405 = 3197027) B3197027
theorem B2840179 : Blo 1328983 2840179 := bstep (se 1 (by rfl) ⟨2130134, by rfl⟩ : syracuseStep 2840179 = 4260269) B4260269
theorem B1496695 : Blo 1328983 1496695 := bstep (se 1 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 1496695 = 2245043) B2245043
theorem B1996427 : Blo 1328983 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B3593879 : Blo 1328983 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B1996439 : Blo 1328983 1996439 := bstep (se 1 (by rfl) ⟨1497329, by rfl⟩ : syracuseStep 1996439 = 2994659) B2994659
theorem B5052077 : Blo 1328983 5052077 := bstep (se 3 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 5052077 = 1894529) B1894529
theorem B4609715 : Blo 1328983 4609715 := bstep (se 1 (by rfl) ⟨3457286, by rfl⟩ : syracuseStep 4609715 = 6914573) B6914573
theorem B4486859 : Blo 1328983 4486859 := bstep (se 1 (by rfl) ⟨3365144, by rfl⟩ : syracuseStep 4486859 = 6730289) B6730289
theorem B5682905 : Blo 1328983 5682905 := bstep (se 2 (by rfl) ⟨2131089, by rfl⟩ : syracuseStep 5682905 = 4262179) B4262179
theorem B1496875 : Blo 1328983 1496875 := bstep (se 1 (by rfl) ⟨1122656, by rfl⟩ : syracuseStep 1496875 = 2245313) B2245313
theorem B6731585 : Blo 1328983 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B4257629 : Blo 1328983 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B2840435 : Blo 1328983 2840435 := bstep (se 1 (by rfl) ⟨2130326, by rfl⟩ : syracuseStep 2840435 = 4260653) B4260653
theorem B1496983 : Blo 1328983 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B6387635 : Blo 1328983 6387635 := bstep (se 1 (by rfl) ⟨4790726, by rfl⟩ : syracuseStep 6387635 = 9581453) B9581453
theorem B3364811 : Blo 1328983 3364811 := bstep (se 1 (by rfl) ⟨2523608, by rfl⟩ : syracuseStep 3364811 = 5047217) B5047217
theorem B6387673 : Blo 1328983 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B4610009 : Blo 1328983 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B4487129 : Blo 1328983 4487129 := bstep (se 2 (by rfl) ⟨1682673, by rfl⟩ : syracuseStep 4487129 = 3365347) B3365347
theorem B1497163 : Blo 1328983 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B1497271 : Blo 1328983 1497271 := bstep (se 1 (by rfl) ⟨1122953, by rfl⟩ : syracuseStep 1497271 = 2245907) B2245907
theorem B2242775 : Blo 1328983 2242775 := bstep (se 1 (by rfl) ⟨1682081, by rfl⟩ : syracuseStep 2242775 = 3364163) B3364163
theorem B3365185 : Blo 1328983 3365185 := bstep (se 2 (by rfl) ⟨1261944, by rfl⟩ : syracuseStep 3365185 = 2523889) B2523889
theorem B2242903 : Blo 1328983 2242903 := bstep (se 1 (by rfl) ⟨1682177, by rfl⟩ : syracuseStep 2242903 = 3364355) B3364355
theorem B10934621 : Blo 1328983 10934621 := bstep (se 3 (by rfl) ⟨2050241, by rfl⟩ : syracuseStep 10934621 = 4100483) B4100483
theorem B5052851 : Blo 1328983 5052851 := bstep (se 1 (by rfl) ⟨3789638, by rfl⟩ : syracuseStep 5052851 = 7579277) B7579277
theorem B3594775 : Blo 1328983 3594775 := bstep (se 1 (by rfl) ⟨2696081, by rfl⟩ : syracuseStep 3594775 = 5392163) B5392163
theorem B4487831 : Blo 1328983 4487831 := bstep (se 1 (by rfl) ⟨3365873, by rfl⟩ : syracuseStep 4487831 = 6731747) B6731747
theorem B2841409 : Blo 1328983 2841409 := bstep (se 2 (by rfl) ⟨1065528, by rfl⟩ : syracuseStep 2841409 = 2131057) B2131057
theorem B3365783 : Blo 1328983 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B11369393 : Blo 1328983 11369393 := bstep (se 2 (by rfl) ⟨4263522, by rfl⟩ : syracuseStep 11369393 = 8527045) B8527045
theorem B2243531 : Blo 1328983 2243531 := bstep (se 1 (by rfl) ⟨1682648, by rfl⟩ : syracuseStep 2243531 = 3365297) B3365297
theorem B19168325 : Blo 1328983 19168325 := bstep (se 4 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 19168325 = 3594061) B3594061
theorem B2243659 : Blo 1328983 2243659 := bstep (se 1 (by rfl) ⟨1682744, by rfl⟩ : syracuseStep 2243659 = 3365489) B3365489
theorem B4258909 : Blo 1328983 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B4488371 : Blo 1328983 4488371 := bstep (se 1 (by rfl) ⟨3366278, by rfl⟩ : syracuseStep 4488371 = 6732557) B6732557
theorem B2243801 : Blo 1328983 2243801 := bstep (se 2 (by rfl) ⟨841425, by rfl⟩ : syracuseStep 2243801 = 1682851) B1682851
theorem B5201117 : Blo 1328983 5201117 := bstep (se 3 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 5201117 = 1950419) B1950419
theorem B2243929 : Blo 1328983 2243929 := bstep (se 2 (by rfl) ⟨841473, by rfl⟩ : syracuseStep 2243929 = 1682947) B1682947
theorem B4488641 : Blo 1328983 4488641 := bstep (se 2 (by rfl) ⟨1683240, by rfl⟩ : syracuseStep 4488641 = 3366481) B3366481
theorem B2694721 : Blo 1328983 2694721 := bstep (se 2 (by rfl) ⟨1010520, by rfl⟩ : syracuseStep 2694721 = 2021041) B2021041
theorem B11370077 : Blo 1328983 11370077 := bstep (se 3 (by rfl) ⟨2131889, by rfl⟩ : syracuseStep 11370077 = 4263779) B4263779
theorem B3366593 : Blo 1328983 3366593 := bstep (se 2 (by rfl) ⟨1262472, by rfl⟩ : syracuseStep 3366593 = 2524945) B2524945
theorem B6733529 : Blo 1328983 6733529 := bstep (se 2 (by rfl) ⟨2525073, by rfl⟩ : syracuseStep 6733529 = 5050147) B5050147
theorem B4792139 : Blo 1328983 4792139 := bstep (se 1 (by rfl) ⟨3594104, by rfl⟩ : syracuseStep 4792139 = 7188209) B7188209
theorem B2244503 : Blo 1328983 2244503 := bstep (se 1 (by rfl) ⟨1683377, by rfl⟩ : syracuseStep 2244503 = 3366755) B3366755
theorem B4489181 : Blo 1328983 4489181 := bstep (se 3 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 4489181 = 1683443) B1683443
theorem B1892359 : Blo 1328983 1892359 := bstep (se 1 (by rfl) ⟨1419269, by rfl⟩ : syracuseStep 1892359 = 2838539) B2838539
theorem B6733853 : Blo 1328983 6733853 := bstep (se 3 (by rfl) ⟨1262597, by rfl⟩ : syracuseStep 6733853 = 2525195) B2525195
theorem B2695303 : Blo 1328983 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B2244793 : Blo 1328983 2244793 := bstep (se 2 (by rfl) ⟨841797, by rfl⟩ : syracuseStep 2244793 = 1683595) B1683595
theorem B2130121 : Blo 1328983 2130121 := bstep (se 2 (by rfl) ⟨798795, by rfl⟩ : syracuseStep 2130121 = 1597591) B1597591
theorem B1597687 : Blo 1328983 1597687 := bstep (se 1 (by rfl) ⟨1198265, by rfl⟩ : syracuseStep 1597687 = 2396531) B2396531
theorem B4489505 : Blo 1328983 4489505 := bstep (se 2 (by rfl) ⟨1683564, by rfl⟩ : syracuseStep 4489505 = 3367129) B3367129
theorem B2990483 : Blo 1328983 2990483 := bstep (se 1 (by rfl) ⟨2242862, by rfl⟩ : syracuseStep 2990483 = 4485725) B4485725
theorem B2990537 : Blo 1328983 2990537 := bstep (se 2 (by rfl) ⟨1121451, by rfl⟩ : syracuseStep 2990537 = 2242903) B2242903
theorem B6734339 : Blo 1328983 6734339 := bstep (se 1 (by rfl) ⟨5050754, by rfl⟩ : syracuseStep 6734339 = 10101509) B10101509
theorem B3785231 : Blo 1328983 3785231 := bstep (se 1 (by rfl) ⟨2838923, by rfl⟩ : syracuseStep 3785231 = 5677847) B5677847
theorem B2523707 : Blo 1328983 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B3596915 : Blo 1328983 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B4793033 : Blo 1328983 4793033 := bstep (se 2 (by rfl) ⟨1797387, by rfl⟩ : syracuseStep 4793033 = 3594775) B3594775
theorem B1893179 : Blo 1328983 1893179 := bstep (se 1 (by rfl) ⟨1419884, by rfl⟩ : syracuseStep 1893179 = 2839769) B2839769
theorem B4490099 : Blo 1328983 4490099 := bstep (se 1 (by rfl) ⟨3367574, by rfl⟩ : syracuseStep 4490099 = 6735149) B6735149
theorem B2245495 : Blo 1328983 2245495 := bstep (se 1 (by rfl) ⟨1684121, by rfl⟩ : syracuseStep 2245495 = 3368243) B3368243
theorem B4260755 : Blo 1328983 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B184157155 : Blo 1328983 184157155 := bstep (se 1 (by rfl) ⟨138117866, by rfl⟩ : syracuseStep 184157155 = 276235733) B276235733
theorem B2524193 : Blo 1328983 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B2245691 : Blo 1328983 2245691 := bstep (se 1 (by rfl) ⟨1684268, by rfl⟩ : syracuseStep 2245691 = 3368537) B3368537
theorem B105014341 : Blo 1328983 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B3368051 : Blo 1328983 3368051 := bstep (se 1 (by rfl) ⟨2526038, by rfl⟩ : syracuseStep 3368051 = 5052077) B5052077
theorem B2991239 : Blo 1328983 2991239 := bstep (se 1 (by rfl) ⟨2243429, by rfl⟩ : syracuseStep 2991239 = 4486859) B4486859
theorem B16188653 : Blo 1328983 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B1893623 : Blo 1328983 1893623 := bstep (se 1 (by rfl) ⟨1420217, by rfl⟩ : syracuseStep 1893623 = 2840435) B2840435
theorem B2524459 : Blo 1328983 2524459 := bstep (se 1 (by rfl) ⟨1893344, by rfl⟩ : syracuseStep 2524459 = 3786689) B3786689
theorem B3073339 : Blo 1328983 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B2991419 : Blo 1328983 2991419 := bstep (se 1 (by rfl) ⟨2243564, by rfl⟩ : syracuseStep 2991419 = 4487129) B4487129
theorem B2991545 : Blo 1328983 2991545 := bstep (se 2 (by rfl) ⟨1121829, by rfl⟩ : syracuseStep 2991545 = 2243659) B2243659
theorem B1893817 : Blo 1328983 1893817 := bstep (se 2 (by rfl) ⟨710181, by rfl⟩ : syracuseStep 1893817 = 1420363) B1420363
theorem B6391325 : Blo 1328983 6391325 := bstep (se 3 (by rfl) ⟨1198373, by rfl⟩ : syracuseStep 6391325 = 2396747) B2396747
theorem B3368567 : Blo 1328983 3368567 := bstep (se 1 (by rfl) ⟨2526425, by rfl⟩ : syracuseStep 3368567 = 5052851) B5052851
theorem B1705735 : Blo 1328983 1705735 := bstep (se 1 (by rfl) ⟨1279301, by rfl⟩ : syracuseStep 1705735 = 2558603) B2558603
theorem B6145807 : Blo 1328983 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B2991887 : Blo 1328983 2991887 := bstep (se 1 (by rfl) ⟨2243915, by rfl⟩ : syracuseStep 2991887 = 4487831) B4487831
theorem B2991905 : Blo 1328983 2991905 := bstep (se 2 (by rfl) ⟨1121964, by rfl⟩ : syracuseStep 2991905 = 2243929) B2243929
theorem B3196759 : Blo 1328983 3196759 := bstep (se 1 (by rfl) ⟨2397569, by rfl⟩ : syracuseStep 3196759 = 4795139) B4795139
theorem B1329031 : Blo 1328983 1329031 := bstep (se 1 (by rfl) ⟨996773, by rfl⟩ : syracuseStep 1329031 = 1993547) B1993547
theorem B1329039 : Blo 1328983 1329039 := bstep (se 1 (by rfl) ⟨996779, by rfl⟩ : syracuseStep 1329039 = 1993559) B1993559
theorem B6473657 : Blo 1328983 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B1329083 : Blo 1328983 1329083 := bstep (se 1 (by rfl) ⟨996812, by rfl⟩ : syracuseStep 1329083 = 1993625) B1993625
theorem B7579595 : Blo 1328983 7579595 := bstep (se 1 (by rfl) ⟨5684696, by rfl⟩ : syracuseStep 7579595 = 11369393) B11369393
theorem B1329159 : Blo 1328983 1329159 := bstep (se 1 (by rfl) ⟨996869, by rfl⟩ : syracuseStep 1329159 = 1993739) B1993739
theorem B1329167 : Blo 1328983 1329167 := bstep (se 1 (by rfl) ⟨996875, by rfl⟩ : syracuseStep 1329167 = 1993751) B1993751
theorem B32360471 : Blo 1328983 32360471 := bstep (se 1 (by rfl) ⟨24270353, by rfl⟩ : syracuseStep 32360471 = 48540707) B48540707
theorem B1329211 : Blo 1328983 1329211 := bstep (se 1 (by rfl) ⟨996908, by rfl⟩ : syracuseStep 1329211 = 1993817) B1993817
theorem B6735959 : Blo 1328983 6735959 := bstep (se 1 (by rfl) ⟨5051969, by rfl⟩ : syracuseStep 6735959 = 10103939) B10103939
theorem B3786871 : Blo 1328983 3786871 := bstep (se 1 (by rfl) ⟨2840153, by rfl⟩ : syracuseStep 3786871 = 5680307) B5680307
theorem B2992247 : Blo 1328983 2992247 := bstep (se 1 (by rfl) ⟨2244185, by rfl⟩ : syracuseStep 2992247 = 4488371) B4488371
theorem B7194743 : Blo 1328983 7194743 := bstep (se 1 (by rfl) ⟨5396057, by rfl⟩ : syracuseStep 7194743 = 10792115) B10792115
theorem B1329287 : Blo 1328983 1329287 := bstep (se 1 (by rfl) ⟨996965, by rfl⟩ : syracuseStep 1329287 = 1993931) B1993931
theorem B1329295 : Blo 1328983 1329295 := bstep (se 1 (by rfl) ⟨996971, by rfl⟩ : syracuseStep 1329295 = 1993943) B1993943
theorem B3467411 : Blo 1328983 3467411 := bstep (se 1 (by rfl) ⟨2600558, by rfl⟩ : syracuseStep 3467411 = 5201117) B5201117
theorem B3786905 : Blo 1328983 3786905 := bstep (se 2 (by rfl) ⟨1420089, by rfl⟩ : syracuseStep 3786905 = 2840179) B2840179
theorem B1329339 : Blo 1328983 1329339 := bstep (se 1 (by rfl) ⟨997004, by rfl⟩ : syracuseStep 1329339 = 1994009) B1994009
theorem B1329415 : Blo 1328983 1329415 := bstep (se 1 (by rfl) ⟨997061, by rfl⟩ : syracuseStep 1329415 = 1994123) B1994123
theorem B3787019 : Blo 1328983 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B1329423 : Blo 1328983 1329423 := bstep (se 1 (by rfl) ⟨997067, by rfl⟩ : syracuseStep 1329423 = 1994135) B1994135
theorem B14387489 : Blo 1328983 14387489 := bstep (se 2 (by rfl) ⟨5395308, by rfl⟩ : syracuseStep 14387489 = 10790617) B10790617
theorem B2992427 : Blo 1328983 2992427 := bstep (se 1 (by rfl) ⟨2244320, by rfl⟩ : syracuseStep 2992427 = 4488641) B4488641
theorem B1329467 : Blo 1328983 1329467 := bstep (se 1 (by rfl) ⟨997100, by rfl⟩ : syracuseStep 1329467 = 1994201) B1994201
theorem B3410311 : Blo 1328983 3410311 := bstep (se 1 (by rfl) ⟨2557733, by rfl⟩ : syracuseStep 3410311 = 5115467) B5115467
theorem B1329543 : Blo 1328983 1329543 := bstep (se 1 (by rfl) ⟨997157, by rfl⟩ : syracuseStep 1329543 = 1994315) B1994315
theorem B2525575 : Blo 1328983 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B1329551 : Blo 1328983 1329551 := bstep (se 1 (by rfl) ⟨997163, by rfl⟩ : syracuseStep 1329551 = 1994327) B1994327
theorem B6392209 : Blo 1328983 6392209 := bstep (se 2 (by rfl) ⟨2397078, by rfl⟩ : syracuseStep 6392209 = 4794157) B4794157
theorem B7580051 : Blo 1328983 7580051 := bstep (se 1 (by rfl) ⟨5685038, by rfl⟩ : syracuseStep 7580051 = 11370077) B11370077
theorem B1329595 : Blo 1328983 1329595 := bstep (se 1 (by rfl) ⟨997196, by rfl⟩ : syracuseStep 1329595 = 1994393) B1994393
theorem B15141329 : Blo 1328983 15141329 := bstep (se 2 (by rfl) ⟨5677998, by rfl⟩ : syracuseStep 15141329 = 11355997) B11355997
theorem B1329671 : Blo 1328983 1329671 := bstep (se 1 (by rfl) ⟨997253, by rfl⟩ : syracuseStep 1329671 = 1994507) B1994507
theorem B1329679 : Blo 1328983 1329679 := bstep (se 1 (by rfl) ⟨997259, by rfl⟩ : syracuseStep 1329679 = 1994519) B1994519
theorem B1329723 : Blo 1328983 1329723 := bstep (se 1 (by rfl) ⟨997292, by rfl⟩ : syracuseStep 1329723 = 1994585) B1994585
theorem B6736445 : Blo 1328983 6736445 := bstep (se 3 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 6736445 = 2526167) B2526167
theorem B1329799 : Blo 1328983 1329799 := bstep (se 1 (by rfl) ⟨997349, by rfl⟩ : syracuseStep 1329799 = 1994699) B1994699
theorem B1329807 : Blo 1328983 1329807 := bstep (se 1 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 1329807 = 1994711) B1994711
theorem B2992787 : Blo 1328983 2992787 := bstep (se 1 (by rfl) ⟨2244590, by rfl⟩ : syracuseStep 2992787 = 4489181) B4489181
theorem B1329851 : Blo 1328983 1329851 := bstep (se 1 (by rfl) ⟨997388, by rfl⟩ : syracuseStep 1329851 = 1994777) B1994777
theorem B2992841 : Blo 1328983 2992841 := bstep (se 2 (by rfl) ⟨1122315, by rfl⟩ : syracuseStep 2992841 = 2244631) B2244631
theorem B1329927 : Blo 1328983 1329927 := bstep (se 1 (by rfl) ⟨997445, by rfl⟩ : syracuseStep 1329927 = 1994891) B1994891
theorem B1993487 : Blo 1328983 1993487 := bstep (se 1 (by rfl) ⟨1495115, by rfl⟩ : syracuseStep 1993487 = 2990231) B2990231
theorem B1329935 : Blo 1328983 1329935 := bstep (se 1 (by rfl) ⟨997451, by rfl⟩ : syracuseStep 1329935 = 1994903) B1994903
theorem B1993529 : Blo 1328983 1993529 := bstep (se 2 (by rfl) ⟨747573, by rfl⟩ : syracuseStep 1993529 = 1495147) B1495147
theorem B6728507 : Blo 1328983 6728507 := bstep (se 1 (by rfl) ⟨5046380, by rfl⟩ : syracuseStep 6728507 = 10092761) B10092761
theorem B1329979 : Blo 1328983 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B4795195 : Blo 1328983 4795195 := bstep (se 1 (by rfl) ⟨3596396, by rfl⟩ : syracuseStep 4795195 = 7192793) B7192793
theorem B1993607 : Blo 1328983 1993607 := bstep (se 1 (by rfl) ⟨1495205, by rfl⟩ : syracuseStep 1993607 = 2990411) B2990411
theorem B1330055 : Blo 1328983 1330055 := bstep (se 1 (by rfl) ⟨997541, by rfl⟩ : syracuseStep 1330055 = 1995083) B1995083
theorem B1330063 : Blo 1328983 1330063 := bstep (se 1 (by rfl) ⟨997547, by rfl⟩ : syracuseStep 1330063 = 1995095) B1995095
theorem B1993643 : Blo 1328983 1993643 := bstep (se 1 (by rfl) ⟨1495232, by rfl⟩ : syracuseStep 1993643 = 2990465) B2990465
theorem B2526137 : Blo 1328983 2526137 := bstep (se 2 (by rfl) ⟨947301, by rfl⟩ : syracuseStep 2526137 = 1894603) B1894603
theorem B1330107 : Blo 1328983 1330107 := bstep (se 1 (by rfl) ⟨997580, by rfl⟩ : syracuseStep 1330107 = 1995161) B1995161
theorem B1993673 : Blo 1328983 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B6728669 : Blo 1328983 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B1330183 : Blo 1328983 1330183 := bstep (se 1 (by rfl) ⟨997637, by rfl⟩ : syracuseStep 1330183 = 1995275) B1995275
theorem B1420303 : Blo 1328983 1420303 := bstep (se 1 (by rfl) ⟨1065227, by rfl⟩ : syracuseStep 1420303 = 2130455) B2130455
theorem B1330191 : Blo 1328983 1330191 := bstep (se 1 (by rfl) ⟨997643, by rfl⟩ : syracuseStep 1330191 = 1995287) B1995287
theorem B1993787 : Blo 1328983 1993787 := bstep (se 1 (by rfl) ⟨1495340, by rfl⟩ : syracuseStep 1993787 = 2990681) B2990681
theorem B1330235 : Blo 1328983 1330235 := bstep (se 1 (by rfl) ⟨997676, by rfl⟩ : syracuseStep 1330235 = 1995353) B1995353
theorem B10095677 : Blo 1328983 10095677 := bstep (se 3 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 10095677 = 3785879) B3785879
theorem B1993847 : Blo 1328983 1993847 := bstep (se 1 (by rfl) ⟨1495385, by rfl⟩ : syracuseStep 1993847 = 2990771) B2990771
theorem B9710725 : Blo 1328983 9710725 := bstep (se 4 (by rfl) ⟨910380, by rfl⟩ : syracuseStep 9710725 = 1820761) B1820761
theorem B1330311 : Blo 1328983 1330311 := bstep (se 1 (by rfl) ⟨997733, by rfl⟩ : syracuseStep 1330311 = 1995467) B1995467
theorem B1993871 : Blo 1328983 1993871 := bstep (se 1 (by rfl) ⟨1495403, by rfl⟩ : syracuseStep 1993871 = 2990807) B2990807
theorem B1330319 : Blo 1328983 1330319 := bstep (se 1 (by rfl) ⟨997739, by rfl⟩ : syracuseStep 1330319 = 1995479) B1995479
theorem B1993913 : Blo 1328983 1993913 := bstep (se 2 (by rfl) ⟨747717, by rfl⟩ : syracuseStep 1993913 = 1495435) B1495435
theorem B1330363 : Blo 1328983 1330363 := bstep (se 1 (by rfl) ⟨997772, by rfl⟩ : syracuseStep 1330363 = 1995545) B1995545
theorem B4263113 : Blo 1328983 4263113 := bstep (se 2 (by rfl) ⟨1598667, by rfl⟩ : syracuseStep 4263113 = 3197335) B3197335
theorem B44305613 : Blo 1328983 44305613 := bstep (se 3 (by rfl) ⟨8307302, by rfl⟩ : syracuseStep 44305613 = 16614605) B16614605
theorem B1993991 : Blo 1328983 1993991 := bstep (se 1 (by rfl) ⟨1495493, by rfl⟩ : syracuseStep 1993991 = 2990987) B2990987
theorem B1330439 : Blo 1328983 1330439 := bstep (se 1 (by rfl) ⟨997829, by rfl⟩ : syracuseStep 1330439 = 1995659) B1995659
theorem B1330447 : Blo 1328983 1330447 := bstep (se 1 (by rfl) ⟨997835, by rfl⟩ : syracuseStep 1330447 = 1995671) B1995671
theorem B6728993 : Blo 1328983 6728993 := bstep (se 2 (by rfl) ⟨2523372, by rfl⟩ : syracuseStep 6728993 = 5046745) B5046745
theorem B1994027 : Blo 1328983 1994027 := bstep (se 1 (by rfl) ⟨1495520, by rfl⟩ : syracuseStep 1994027 = 2991041) B2991041
theorem B1330491 : Blo 1328983 1330491 := bstep (se 1 (by rfl) ⟨997868, by rfl⟩ : syracuseStep 1330491 = 1995737) B1995737
theorem B1994057 : Blo 1328983 1994057 := bstep (se 2 (by rfl) ⟨747771, by rfl⟩ : syracuseStep 1994057 = 1495543) B1495543
theorem B3788147 : Blo 1328983 3788147 := bstep (se 1 (by rfl) ⟨2841110, by rfl⟩ : syracuseStep 3788147 = 5682221) B5682221
theorem B1420679 : Blo 1328983 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B2993543 : Blo 1328983 2993543 := bstep (se 1 (by rfl) ⟨2245157, by rfl⟩ : syracuseStep 2993543 = 4490315) B4490315
theorem B1330567 : Blo 1328983 1330567 := bstep (se 1 (by rfl) ⟨997925, by rfl⟩ : syracuseStep 1330567 = 1995851) B1995851
theorem B1330575 : Blo 1328983 1330575 := bstep (se 1 (by rfl) ⟨997931, by rfl⟩ : syracuseStep 1330575 = 1995863) B1995863
theorem B1994171 : Blo 1328983 1994171 := bstep (se 1 (by rfl) ⟨1495628, by rfl⟩ : syracuseStep 1994171 = 2991257) B2991257
theorem B1330619 : Blo 1328983 1330619 := bstep (se 1 (by rfl) ⟨997964, by rfl⟩ : syracuseStep 1330619 = 1995929) B1995929
theorem B1994231 : Blo 1328983 1994231 := bstep (se 1 (by rfl) ⟨1495673, by rfl⟩ : syracuseStep 1994231 = 2991347) B2991347
theorem B1330695 : Blo 1328983 1330695 := bstep (se 1 (by rfl) ⟨998021, by rfl⟩ : syracuseStep 1330695 = 1996043) B1996043
theorem B1994255 : Blo 1328983 1994255 := bstep (se 1 (by rfl) ⟨1495691, by rfl⟩ : syracuseStep 1994255 = 2991383) B2991383
theorem B1330703 : Blo 1328983 1330703 := bstep (se 1 (by rfl) ⟨998027, by rfl⟩ : syracuseStep 1330703 = 1996055) B1996055
theorem B1994297 : Blo 1328983 1994297 := bstep (se 2 (by rfl) ⟨747861, by rfl⟩ : syracuseStep 1994297 = 1495723) B1495723
theorem B2993723 : Blo 1328983 2993723 := bstep (se 1 (by rfl) ⟨2245292, by rfl⟩ : syracuseStep 2993723 = 4490585) B4490585
theorem B1330747 : Blo 1328983 1330747 := bstep (se 1 (by rfl) ⟨998060, by rfl⟩ : syracuseStep 1330747 = 1996121) B1996121
theorem B4263511 : Blo 1328983 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B1994375 : Blo 1328983 1994375 := bstep (se 1 (by rfl) ⟨1495781, by rfl⟩ : syracuseStep 1994375 = 2991563) B2991563
theorem B1330823 : Blo 1328983 1330823 := bstep (se 1 (by rfl) ⟨998117, by rfl⟩ : syracuseStep 1330823 = 1996235) B1996235
theorem B1330831 : Blo 1328983 1330831 := bstep (se 1 (by rfl) ⟨998123, by rfl⟩ : syracuseStep 1330831 = 1996247) B1996247
theorem B1994411 : Blo 1328983 1994411 := bstep (se 1 (by rfl) ⟨1495808, by rfl⟩ : syracuseStep 1994411 = 2991617) B2991617
theorem B2993849 : Blo 1328983 2993849 := bstep (se 2 (by rfl) ⟨1122693, by rfl⟩ : syracuseStep 2993849 = 2245387) B2245387
theorem B1330875 : Blo 1328983 1330875 := bstep (se 1 (by rfl) ⟨998156, by rfl⟩ : syracuseStep 1330875 = 1996313) B1996313
theorem B11366081 : Blo 1328983 11366081 := bstep (se 2 (by rfl) ⟨4262280, by rfl⟩ : syracuseStep 11366081 = 8524561) B8524561
theorem B1994441 : Blo 1328983 1994441 := bstep (se 2 (by rfl) ⟨747915, by rfl⟩ : syracuseStep 1994441 = 1495831) B1495831
theorem B4263625 : Blo 1328983 4263625 := bstep (se 2 (by rfl) ⟨1598859, by rfl⟩ : syracuseStep 4263625 = 3197719) B3197719
theorem B3788545 : Blo 1328983 3788545 := bstep (se 2 (by rfl) ⟨1420704, by rfl⟩ : syracuseStep 3788545 = 2841409) B2841409
theorem B1330951 : Blo 1328983 1330951 := bstep (se 1 (by rfl) ⟨998213, by rfl⟩ : syracuseStep 1330951 = 1996427) B1996427
theorem B2395919 : Blo 1328983 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B1330959 : Blo 1328983 1330959 := bstep (se 1 (by rfl) ⟨998219, by rfl⟩ : syracuseStep 1330959 = 1996439) B1996439
theorem B1994555 : Blo 1328983 1994555 := bstep (se 1 (by rfl) ⟨1495916, by rfl⟩ : syracuseStep 1994555 = 2991833) B2991833
theorem B3788603 : Blo 1328983 3788603 := bstep (se 1 (by rfl) ⟨2841452, by rfl⟩ : syracuseStep 3788603 = 5682905) B5682905
theorem B1994615 : Blo 1328983 1994615 := bstep (se 1 (by rfl) ⟨1495961, by rfl⟩ : syracuseStep 1994615 = 2991923) B2991923
theorem B1994639 : Blo 1328983 1994639 := bstep (se 1 (by rfl) ⟨1495979, by rfl⟩ : syracuseStep 1994639 = 2991959) B2991959
theorem B2838419 : Blo 1328983 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B1994681 : Blo 1328983 1994681 := bstep (se 2 (by rfl) ⟨748005, by rfl⟩ : syracuseStep 1994681 = 1496011) B1496011
theorem B34090955 : Blo 1328983 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B1994759 : Blo 1328983 1994759 := bstep (se 1 (by rfl) ⟨1496069, by rfl⟩ : syracuseStep 1994759 = 2992139) B2992139
theorem B2994191 : Blo 1328983 2994191 := bstep (se 1 (by rfl) ⟨2245643, by rfl⟩ : syracuseStep 2994191 = 4491287) B4491287
theorem B2994209 : Blo 1328983 2994209 := bstep (se 2 (by rfl) ⟨1122828, by rfl⟩ : syracuseStep 2994209 = 2245657) B2245657
theorem B1994795 : Blo 1328983 1994795 := bstep (se 1 (by rfl) ⟨1496096, by rfl⟩ : syracuseStep 1994795 = 2992193) B2992193
theorem B1683499 : Blo 1328983 1683499 := bstep (se 1 (by rfl) ⟨1262624, by rfl⟩ : syracuseStep 1683499 = 2525249) B2525249
theorem B1994825 : Blo 1328983 1994825 := bstep (se 2 (by rfl) ⟨748059, by rfl⟩ : syracuseStep 1994825 = 1496119) B1496119
theorem B1495183 : Blo 1328983 1495183 := bstep (se 1 (by rfl) ⟨1121387, by rfl⟩ : syracuseStep 1495183 = 2242775) B2242775
theorem B1994939 : Blo 1328983 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B43151561 : Blo 1328983 43151561 := bstep (se 2 (by rfl) ⟨16181835, by rfl⟩ : syracuseStep 43151561 = 32363671) B32363671
theorem B6729965 : Blo 1328983 6729965 := bstep (se 3 (by rfl) ⟨1261868, by rfl⟩ : syracuseStep 6729965 = 2523737) B2523737
theorem B1994999 : Blo 1328983 1994999 := bstep (se 1 (by rfl) ⟨1496249, by rfl⟩ : syracuseStep 1994999 = 2992499) B2992499
theorem B1995023 : Blo 1328983 1995023 := bstep (se 1 (by rfl) ⟨1496267, by rfl⟩ : syracuseStep 1995023 = 2992535) B2992535
theorem B1995065 : Blo 1328983 1995065 := bstep (se 2 (by rfl) ⟨748149, by rfl⟩ : syracuseStep 1995065 = 1496299) B1496299
theorem B2994551 : Blo 1328983 2994551 := bstep (se 1 (by rfl) ⟨2245913, by rfl⟩ : syracuseStep 2994551 = 4491827) B4491827
theorem B1995143 : Blo 1328983 1995143 := bstep (se 1 (by rfl) ⟨1496357, by rfl⟩ : syracuseStep 1995143 = 2992715) B2992715
theorem B1995179 : Blo 1328983 1995179 := bstep (se 1 (by rfl) ⟨1496384, by rfl⟩ : syracuseStep 1995179 = 2992769) B2992769
theorem B7573945 : Blo 1328983 7573945 := bstep (se 2 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 7573945 = 5680459) B5680459
theorem B1995209 : Blo 1328983 1995209 := bstep (se 2 (by rfl) ⟨748203, by rfl⟩ : syracuseStep 1995209 = 1496407) B1496407
theorem B12292573 : Blo 1328983 12292573 := bstep (se 3 (by rfl) ⟨2304857, by rfl⟩ : syracuseStep 12292573 = 4609715) B4609715
theorem B1995323 : Blo 1328983 1995323 := bstep (se 1 (by rfl) ⟨1496492, by rfl⟩ : syracuseStep 1995323 = 2992985) B2992985
theorem B1995383 : Blo 1328983 1995383 := bstep (se 1 (by rfl) ⟨1496537, by rfl⟩ : syracuseStep 1995383 = 2993075) B2993075
theorem B1495687 : Blo 1328983 1495687 := bstep (se 1 (by rfl) ⟨1121765, by rfl⟩ : syracuseStep 1495687 = 2243531) B2243531
theorem B1995407 : Blo 1328983 1995407 := bstep (se 1 (by rfl) ⟨1496555, by rfl⟩ : syracuseStep 1995407 = 2993111) B2993111
theorem B1995449 : Blo 1328983 1995449 := bstep (se 2 (by rfl) ⟨748293, by rfl⟩ : syracuseStep 1995449 = 1496587) B1496587
theorem B4485833 : Blo 1328983 4485833 := bstep (se 2 (by rfl) ⟨1682187, by rfl⟩ : syracuseStep 4485833 = 3364375) B3364375
theorem B3592961 : Blo 1328983 3592961 := bstep (se 2 (by rfl) ⟨1347360, by rfl⟩ : syracuseStep 3592961 = 2694721) B2694721
theorem B1995527 : Blo 1328983 1995527 := bstep (se 1 (by rfl) ⟨1496645, by rfl⟩ : syracuseStep 1995527 = 2993291) B2993291
theorem B1995563 : Blo 1328983 1995563 := bstep (se 1 (by rfl) ⟨1496672, by rfl⟩ : syracuseStep 1995563 = 2993345) B2993345
theorem B1495867 : Blo 1328983 1495867 := bstep (se 1 (by rfl) ⟨1121900, by rfl⟩ : syracuseStep 1495867 = 2243801) B2243801
theorem B1995593 : Blo 1328983 1995593 := bstep (se 2 (by rfl) ⟨748347, by rfl⟩ : syracuseStep 1995593 = 1496695) B1496695
theorem B1995707 : Blo 1328983 1995707 := bstep (se 1 (by rfl) ⟨1496780, by rfl⟩ : syracuseStep 1995707 = 2993561) B2993561
theorem B8205259 : Blo 1328983 8205259 := bstep (se 1 (by rfl) ⟨6153944, by rfl⟩ : syracuseStep 8205259 = 12307889) B12307889
theorem B1995767 : Blo 1328983 1995767 := bstep (se 1 (by rfl) ⟨1496825, by rfl⟩ : syracuseStep 1995767 = 2993651) B2993651
theorem B1684471 : Blo 1328983 1684471 := bstep (se 1 (by rfl) ⟨1263353, by rfl⟩ : syracuseStep 1684471 = 2526707) B2526707
theorem B1995791 : Blo 1328983 1995791 := bstep (se 1 (by rfl) ⟨1496843, by rfl⟩ : syracuseStep 1995791 = 2993687) B2993687
theorem B6730775 : Blo 1328983 6730775 := bstep (se 1 (by rfl) ⟨5048081, by rfl⟩ : syracuseStep 6730775 = 10096163) B10096163
theorem B1995833 : Blo 1328983 1995833 := bstep (se 2 (by rfl) ⟨748437, by rfl⟩ : syracuseStep 1995833 = 1496875) B1496875
theorem B6829175 : Blo 1328983 6829175 := bstep (se 1 (by rfl) ⟨5121881, by rfl⟩ : syracuseStep 6829175 = 10243763) B10243763
theorem B1995911 : Blo 1328983 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B1995947 : Blo 1328983 1995947 := bstep (se 1 (by rfl) ⟨1496960, by rfl⟩ : syracuseStep 1995947 = 2993921) B2993921
theorem B1995977 : Blo 1328983 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B1496335 : Blo 1328983 1496335 := bstep (se 1 (by rfl) ⟨1122251, by rfl⟩ : syracuseStep 1496335 = 2244503) B2244503
theorem B8516897 : Blo 1328983 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1996091 : Blo 1328983 1996091 := bstep (se 1 (by rfl) ⟨1497068, by rfl⟩ : syracuseStep 1996091 = 2994137) B2994137
theorem B1996151 : Blo 1328983 1996151 := bstep (se 1 (by rfl) ⟨1497113, by rfl⟩ : syracuseStep 1996151 = 2994227) B2994227
theorem B4486535 : Blo 1328983 4486535 := bstep (se 1 (by rfl) ⟨3364901, by rfl⟩ : syracuseStep 4486535 = 6729803) B6729803
theorem B1996175 : Blo 1328983 1996175 := bstep (se 1 (by rfl) ⟨1497131, by rfl⟩ : syracuseStep 1996175 = 2994263) B2994263
theorem B4044185 : Blo 1328983 4044185 := bstep (se 2 (by rfl) ⟨1516569, by rfl⟩ : syracuseStep 4044185 = 3033139) B3033139
theorem B1996217 : Blo 1328983 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B1996295 : Blo 1328983 1996295 := bstep (se 1 (by rfl) ⟨1497221, by rfl⟩ : syracuseStep 1996295 = 2994443) B2994443
theorem B3839521 : Blo 1328983 3839521 := bstep (se 2 (by rfl) ⟨1439820, by rfl⟩ : syracuseStep 3839521 = 2879641) B2879641
theorem B9000491 : Blo 1328983 9000491 := bstep (se 1 (by rfl) ⟨6750368, by rfl⟩ : syracuseStep 9000491 = 13500737) B13500737
theorem B1996331 : Blo 1328983 1996331 := bstep (se 1 (by rfl) ⟨1497248, by rfl⟩ : syracuseStep 1996331 = 2994497) B2994497
theorem B1996361 : Blo 1328983 1996361 := bstep (se 2 (by rfl) ⟨748635, by rfl⟩ : syracuseStep 1996361 = 1497271) B1497271
theorem B23033443 : Blo 1328983 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B3364487 : Blo 1328983 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B3364537 : Blo 1328983 3364537 := bstep (se 2 (by rfl) ⟨1261701, by rfl⟩ : syracuseStep 3364537 = 2523403) B2523403
theorem B1996475 : Blo 1328983 1996475 := bstep (se 1 (by rfl) ⟨1497356, by rfl⟩ : syracuseStep 1996475 = 2994713) B2994713
theorem B4486913 : Blo 1328983 4486913 := bstep (se 2 (by rfl) ⟨1682592, by rfl⟩ : syracuseStep 4486913 = 3365185) B3365185
theorem B1496839 : Blo 1328983 1496839 := bstep (se 1 (by rfl) ⟨1122629, by rfl⟩ : syracuseStep 1496839 = 2245259) B2245259
theorem B2397995 : Blo 1328983 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B22714181 : Blo 1328983 22714181 := bstep (se 4 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 22714181 = 4258909) B4258909
theorem B1497019 : Blo 1328983 1497019 := bstep (se 1 (by rfl) ⟨1122764, by rfl⟩ : syracuseStep 1497019 = 2245529) B2245529
theorem B2840521 : Blo 1328983 2840521 := bstep (se 2 (by rfl) ⟨1065195, by rfl⟩ : syracuseStep 2840521 = 2130391) B2130391
theorem B5683229 : Blo 1328983 5683229 := bstep (se 3 (by rfl) ⟨1065605, by rfl⟩ : syracuseStep 5683229 = 2131211) B2131211
theorem B19159213 : Blo 1328983 19159213 := bstep (se 3 (by rfl) ⟨3592352, by rfl⟩ : syracuseStep 19159213 = 7184705) B7184705
theorem B3840257 : Blo 1328983 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B3365135 : Blo 1328983 3365135 := bstep (se 1 (by rfl) ⟨2523851, by rfl⟩ : syracuseStep 3365135 = 5047703) B5047703
theorem B1333519 : Blo 1328983 1333519 := bstep (se 1 (by rfl) ⟨1000139, by rfl⟩ : syracuseStep 1333519 = 2000279) B2000279
theorem B2275627 : Blo 1328983 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B3193175 : Blo 1328983 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B10099079 : Blo 1328983 10099079 := bstep (se 1 (by rfl) ⟨7574309, by rfl⟩ : syracuseStep 10099079 = 15148619) B15148619
theorem B14383507 : Blo 1328983 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B5683603 : Blo 1328983 5683603 := bstep (se 1 (by rfl) ⟨4262702, by rfl⟩ : syracuseStep 5683603 = 8525405) B8525405
theorem B5052881 : Blo 1328983 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B9583069 : Blo 1328983 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B2021879 : Blo 1328983 2021879 := bstep (se 1 (by rfl) ⟨1516409, by rfl⟩ : syracuseStep 2021879 = 3032819) B3032819
theorem B2021903 : Blo 1328983 2021903 := bstep (se 1 (by rfl) ⟨1516427, by rfl⟩ : syracuseStep 2021903 = 3032855) B3032855
theorem B4487723 : Blo 1328983 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B4258423 : Blo 1328983 4258423 := bstep (se 1 (by rfl) ⟨3193817, by rfl⟩ : syracuseStep 4258423 = 6387635) B6387635
theorem B2243207 : Blo 1328983 2243207 := bstep (se 1 (by rfl) ⟨1682405, by rfl⟩ : syracuseStep 2243207 = 3364811) B3364811
theorem B7289747 : Blo 1328983 7289747 := bstep (se 1 (by rfl) ⟨5467310, by rfl⟩ : syracuseStep 7289747 = 10934621) B10934621
theorem B5053337 : Blo 1328983 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B3365833 : Blo 1328983 3365833 := bstep (se 2 (by rfl) ⟨1262187, by rfl⟩ : syracuseStep 3365833 = 2524375) B2524375
theorem B10787863 : Blo 1328983 10787863 := bstep (se 1 (by rfl) ⟨8090897, by rfl⟩ : syracuseStep 10787863 = 16181795) B16181795
theorem B3365975 : Blo 1328983 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B2243855 : Blo 1328983 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B145562939 : Blo 1328983 145562939 := bstep (se 1 (by rfl) ⟨109172204, by rfl⟩ : syracuseStep 145562939 = 218344409) B218344409
theorem B12778883 : Blo 1328983 12778883 := bstep (se 1 (by rfl) ⟨9584162, by rfl⟩ : syracuseStep 12778883 = 19168325) B19168325
theorem B25582979 : Blo 1328983 25582979 := bstep (se 1 (by rfl) ⟨19187234, by rfl⟩ : syracuseStep 25582979 = 38374469) B38374469
theorem B28761479 : Blo 1328983 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1973705 : Blo 1328983 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B4791851 : Blo 1328983 4791851 := bstep (se 1 (by rfl) ⟨3593888, by rfl⟩ : syracuseStep 4791851 = 7187777) B7187777
theorem B3694139 : Blo 1328983 3694139 := bstep (se 1 (by rfl) ⟨2770604, by rfl⟩ : syracuseStep 3694139 = 5541209) B5541209
theorem B3595835 : Blo 1328983 3595835 := bstep (se 1 (by rfl) ⟨2696876, by rfl⟩ : syracuseStep 3595835 = 5393753) B5393753
theorem B1597063 : Blo 1328983 1597063 := bstep (se 1 (by rfl) ⟨1197797, by rfl⟩ : syracuseStep 1597063 = 2395595) B2395595
theorem B2244395 : Blo 1328983 2244395 := bstep (se 1 (by rfl) ⟨1683296, by rfl⟩ : syracuseStep 2244395 = 3366593) B3366593
theorem B4489019 : Blo 1328983 4489019 := bstep (se 1 (by rfl) ⟨3366764, by rfl⟩ : syracuseStep 4489019 = 6733529) B6733529
theorem B12787571 : Blo 1328983 12787571 := bstep (se 1 (by rfl) ⟨9590678, by rfl⟩ : syracuseStep 12787571 = 19181357) B19181357
theorem B3194759 : Blo 1328983 3194759 := bstep (se 1 (by rfl) ⟨2396069, by rfl⟩ : syracuseStep 3194759 = 4792139) B4792139
theorem B2523145 : Blo 1328983 2523145 := bstep (se 2 (by rfl) ⟨946179, by rfl⟩ : syracuseStep 2523145 = 1892359) B1892359
theorem B4489235 : Blo 1328983 4489235 := bstep (se 1 (by rfl) ⟨3366926, by rfl⟩ : syracuseStep 4489235 = 6733853) B6733853
theorem B2244665 : Blo 1328983 2244665 := bstep (se 2 (by rfl) ⟨841749, by rfl⟩ : syracuseStep 2244665 = 1683499) B1683499
theorem B4489559 : Blo 1328983 4489559 := bstep (se 1 (by rfl) ⟨3367169, by rfl⟩ : syracuseStep 4489559 = 6734339) B6734339
theorem B2523487 : Blo 1328983 2523487 := bstep (se 1 (by rfl) ⟨1892615, by rfl⟩ : syracuseStep 2523487 = 3785231) B3785231
theorem B2990555 : Blo 1328983 2990555 := bstep (se 1 (by rfl) ⟨2242916, by rfl⟩ : syracuseStep 2990555 = 4485833) B4485833
theorem B4547081 : Blo 1328983 4547081 := bstep (se 2 (by rfl) ⟨1705155, by rfl⟩ : syracuseStep 4547081 = 3410311) B3410311
theorem B3367433 : Blo 1328983 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B19178009 : Blo 1328983 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B7578137 : Blo 1328983 7578137 := bstep (se 2 (by rfl) ⟨2841801, by rfl⟩ : syracuseStep 7578137 = 5683603) B5683603
theorem B10240685 : Blo 1328983 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B2245367 : Blo 1328983 2245367 := bstep (se 1 (by rfl) ⟨1684025, by rfl⟩ : syracuseStep 2245367 = 3368051) B3368051
theorem B5677897 : Blo 1328983 5677897 := bstep (se 2 (by rfl) ⟨2129211, by rfl⟩ : syracuseStep 5677897 = 4258423) B4258423
theorem B5677931 : Blo 1328983 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B2991023 : Blo 1328983 2991023 := bstep (se 1 (by rfl) ⟨2243267, by rfl⟩ : syracuseStep 2991023 = 4486535) B4486535
theorem B2696123 : Blo 1328983 2696123 := bstep (se 1 (by rfl) ⟨2022092, by rfl⟩ : syracuseStep 2696123 = 4044185) B4044185
theorem B2245711 : Blo 1328983 2245711 := bstep (se 1 (by rfl) ⟨1684283, by rfl⟩ : syracuseStep 2245711 = 3368567) B3368567
theorem B2991275 : Blo 1328983 2991275 := bstep (se 1 (by rfl) ⟨2243456, by rfl⟩ : syracuseStep 2991275 = 4486913) B4486913
theorem B1598663 : Blo 1328983 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B8520997 : Blo 1328983 8520997 := bstep (se 4 (by rfl) ⟨798843, by rfl⟩ : syracuseStep 8520997 = 1597687) B1597687
theorem B5391677 : Blo 1328983 5391677 := bstep (se 3 (by rfl) ⟨1010939, by rfl⟩ : syracuseStep 5391677 = 2021879) B2021879
theorem B2245961 : Blo 1328983 2245961 := bstep (se 2 (by rfl) ⟨842235, by rfl⟩ : syracuseStep 2245961 = 1684471) B1684471
theorem B1893737 : Blo 1328983 1893737 := bstep (se 2 (by rfl) ⟨710151, by rfl⟩ : syracuseStep 1893737 = 1420303) B1420303
theorem B4490639 : Blo 1328983 4490639 := bstep (se 1 (by rfl) ⟨3367979, by rfl⟩ : syracuseStep 4490639 = 6735959) B6735959
theorem B140019121 : Blo 1328983 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B2311607 : Blo 1328983 2311607 := bstep (se 1 (by rfl) ⟨1733705, by rfl⟩ : syracuseStep 2311607 = 3467411) B3467411
theorem B2524603 : Blo 1328983 2524603 := bstep (se 1 (by rfl) ⟨1893452, by rfl⟩ : syracuseStep 2524603 = 3786905) B3786905
theorem B2524679 : Blo 1328983 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B10094219 : Blo 1328983 10094219 := bstep (se 1 (by rfl) ⟨7570664, by rfl⟩ : syracuseStep 10094219 = 15141329) B15141329
theorem B3368587 : Blo 1328983 3368587 := bstep (se 1 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 3368587 = 5052881) B5052881
theorem B2991815 : Blo 1328983 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B4490963 : Blo 1328983 4490963 := bstep (se 1 (by rfl) ⟨3368222, by rfl⟩ : syracuseStep 4490963 = 6736445) B6736445
theorem B4097785 : Blo 1328983 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B1328991 : Blo 1328983 1328991 := bstep (se 1 (by rfl) ⟨996743, by rfl⟩ : syracuseStep 1328991 = 1993487) B1993487
theorem B12781421 : Blo 1328983 12781421 := bstep (se 3 (by rfl) ⟨2396516, by rfl⟩ : syracuseStep 12781421 = 4793033) B4793033
theorem B1329019 : Blo 1328983 1329019 := bstep (se 1 (by rfl) ⟨996764, by rfl⟩ : syracuseStep 1329019 = 1993529) B1993529
theorem B2525089 : Blo 1328983 2525089 := bstep (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) B1893817
theorem B1329071 : Blo 1328983 1329071 := bstep (se 1 (by rfl) ⟨996803, by rfl⟩ : syracuseStep 1329071 = 1993607) B1993607
theorem B4859831 : Blo 1328983 4859831 := bstep (se 1 (by rfl) ⟨3644873, by rfl⟩ : syracuseStep 4859831 = 7289747) B7289747
theorem B3368891 : Blo 1328983 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B1329095 : Blo 1328983 1329095 := bstep (se 1 (by rfl) ⟨996821, by rfl⟩ : syracuseStep 1329095 = 1993643) B1993643
theorem B1329115 : Blo 1328983 1329115 := bstep (se 1 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 1329115 = 1993673) B1993673
theorem B1329191 : Blo 1328983 1329191 := bstep (se 1 (by rfl) ⟨996893, by rfl⟩ : syracuseStep 1329191 = 1993787) B1993787
theorem B1329231 : Blo 1328983 1329231 := bstep (se 1 (by rfl) ⟨996923, by rfl⟩ : syracuseStep 1329231 = 1993847) B1993847
theorem B1329247 : Blo 1328983 1329247 := bstep (se 1 (by rfl) ⟨996935, by rfl⟩ : syracuseStep 1329247 = 1993871) B1993871
theorem B1329275 : Blo 1328983 1329275 := bstep (se 1 (by rfl) ⟨996956, by rfl⟩ : syracuseStep 1329275 = 1993913) B1993913
theorem B5048477 : Blo 1328983 5048477 := bstep (se 3 (by rfl) ⟨946589, by rfl⟩ : syracuseStep 5048477 = 1893179) B1893179
theorem B1329327 : Blo 1328983 1329327 := bstep (se 1 (by rfl) ⟨996995, by rfl⟩ : syracuseStep 1329327 = 1993991) B1993991
theorem B1329351 : Blo 1328983 1329351 := bstep (se 1 (by rfl) ⟨997013, by rfl⟩ : syracuseStep 1329351 = 1994027) B1994027
theorem B1329371 : Blo 1328983 1329371 := bstep (se 1 (by rfl) ⟨997028, by rfl⟩ : syracuseStep 1329371 = 1994057) B1994057
theorem B2525431 : Blo 1328983 2525431 := bstep (se 1 (by rfl) ⟨1894073, by rfl⟩ : syracuseStep 2525431 = 3788147) B3788147
theorem B1329447 : Blo 1328983 1329447 := bstep (se 1 (by rfl) ⟨997085, by rfl⟩ : syracuseStep 1329447 = 1994171) B1994171
theorem B1329487 : Blo 1328983 1329487 := bstep (se 1 (by rfl) ⟨997115, by rfl⟩ : syracuseStep 1329487 = 1994231) B1994231
theorem B1329503 : Blo 1328983 1329503 := bstep (se 1 (by rfl) ⟨997127, by rfl⟩ : syracuseStep 1329503 = 1994255) B1994255
theorem B8194409 : Blo 1328983 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B1329531 : Blo 1328983 1329531 := bstep (se 1 (by rfl) ⟨997148, by rfl⟩ : syracuseStep 1329531 = 1994297) B1994297
theorem B1329583 : Blo 1328983 1329583 := bstep (se 1 (by rfl) ⟨997187, by rfl⟩ : syracuseStep 1329583 = 1994375) B1994375
theorem B1329607 : Blo 1328983 1329607 := bstep (se 1 (by rfl) ⟨997205, by rfl⟩ : syracuseStep 1329607 = 1994411) B1994411
theorem B4262345 : Blo 1328983 4262345 := bstep (se 2 (by rfl) ⟨1598379, by rfl⟩ : syracuseStep 4262345 = 3196759) B3196759
theorem B1329627 : Blo 1328983 1329627 := bstep (se 1 (by rfl) ⟨997220, by rfl⟩ : syracuseStep 1329627 = 1994441) B1994441
theorem B1329703 : Blo 1328983 1329703 := bstep (se 1 (by rfl) ⟨997277, by rfl⟩ : syracuseStep 1329703 = 1994555) B1994555
theorem B2992679 : Blo 1328983 2992679 := bstep (se 1 (by rfl) ⟨2244509, by rfl⟩ : syracuseStep 2992679 = 4489019) B4489019
theorem B2525735 : Blo 1328983 2525735 := bstep (se 1 (by rfl) ⟨1894301, by rfl⟩ : syracuseStep 2525735 = 3788603) B3788603
theorem B1329743 : Blo 1328983 1329743 := bstep (se 1 (by rfl) ⟨997307, by rfl⟩ : syracuseStep 1329743 = 1994615) B1994615
theorem B1329759 : Blo 1328983 1329759 := bstep (se 1 (by rfl) ⟨997319, by rfl⟩ : syracuseStep 1329759 = 1994639) B1994639
theorem B3787361 : Blo 1328983 3787361 := bstep (se 2 (by rfl) ⟨1420260, by rfl⟩ : syracuseStep 3787361 = 2840521) B2840521
theorem B1329787 : Blo 1328983 1329787 := bstep (se 1 (by rfl) ⟨997340, by rfl⟩ : syracuseStep 1329787 = 1994681) B1994681
theorem B22727303 : Blo 1328983 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B1329839 : Blo 1328983 1329839 := bstep (se 1 (by rfl) ⟨997379, by rfl⟩ : syracuseStep 1329839 = 1994759) B1994759
theorem B1329863 : Blo 1328983 1329863 := bstep (se 1 (by rfl) ⟨997397, by rfl⟩ : syracuseStep 1329863 = 1994795) B1994795
theorem B1329883 : Blo 1328983 1329883 := bstep (se 1 (by rfl) ⟨997412, by rfl⟩ : syracuseStep 1329883 = 1994825) B1994825
theorem B1329959 : Blo 1328983 1329959 := bstep (se 1 (by rfl) ⟨997469, by rfl⟩ : syracuseStep 1329959 = 1994939) B1994939
theorem B5049161 : Blo 1328983 5049161 := bstep (se 2 (by rfl) ⟨1893435, by rfl⟩ : syracuseStep 5049161 = 3786871) B3786871
theorem B1329999 : Blo 1328983 1329999 := bstep (se 1 (by rfl) ⟨997499, by rfl⟩ : syracuseStep 1329999 = 1994999) B1994999
theorem B1330015 : Blo 1328983 1330015 := bstep (se 1 (by rfl) ⟨997511, by rfl⟩ : syracuseStep 1330015 = 1995023) B1995023
theorem B1993577 : Blo 1328983 1993577 := bstep (se 2 (by rfl) ⟨747591, by rfl⟩ : syracuseStep 1993577 = 1495183) B1495183
theorem B2993003 : Blo 1328983 2993003 := bstep (se 1 (by rfl) ⟨2244752, by rfl⟩ : syracuseStep 2993003 = 4489505) B4489505
theorem B1330043 : Blo 1328983 1330043 := bstep (se 1 (by rfl) ⟨997532, by rfl⟩ : syracuseStep 1330043 = 1995065) B1995065
theorem B25545617 : Blo 1328983 25545617 := bstep (se 2 (by rfl) ⟨9579606, by rfl⟩ : syracuseStep 25545617 = 19159213) B19159213
theorem B2993057 : Blo 1328983 2993057 := bstep (se 2 (by rfl) ⟨1122396, by rfl⟩ : syracuseStep 2993057 = 2244793) B2244793
theorem B1330095 : Blo 1328983 1330095 := bstep (se 1 (by rfl) ⟨997571, by rfl⟩ : syracuseStep 1330095 = 1995143) B1995143
theorem B1993655 : Blo 1328983 1993655 := bstep (se 1 (by rfl) ⟨1495241, by rfl⟩ : syracuseStep 1993655 = 2990483) B2990483
theorem B1330119 : Blo 1328983 1330119 := bstep (se 1 (by rfl) ⟨997589, by rfl⟩ : syracuseStep 1330119 = 1995179) B1995179
theorem B1993691 : Blo 1328983 1993691 := bstep (se 1 (by rfl) ⟨1495268, by rfl⟩ : syracuseStep 1993691 = 2990537) B2990537
theorem B1330139 : Blo 1328983 1330139 := bstep (se 1 (by rfl) ⟨997604, by rfl⟩ : syracuseStep 1330139 = 1995209) B1995209
theorem B1682471 : Blo 1328983 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B1330215 : Blo 1328983 1330215 := bstep (se 1 (by rfl) ⟨997661, by rfl⟩ : syracuseStep 1330215 = 1995323) B1995323
theorem B3034169 : Blo 1328983 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B1330255 : Blo 1328983 1330255 := bstep (se 1 (by rfl) ⟨997691, by rfl⟩ : syracuseStep 1330255 = 1995383) B1995383
theorem B1330271 : Blo 1328983 1330271 := bstep (se 1 (by rfl) ⟨997703, by rfl⟩ : syracuseStep 1330271 = 1995407) B1995407
theorem B1330299 : Blo 1328983 1330299 := bstep (se 1 (by rfl) ⟨997724, by rfl⟩ : syracuseStep 1330299 = 1995449) B1995449
theorem B2395307 : Blo 1328983 2395307 := bstep (se 1 (by rfl) ⟨1796480, by rfl⟩ : syracuseStep 2395307 = 3592961) B3592961
theorem B1330351 : Blo 1328983 1330351 := bstep (se 1 (by rfl) ⟨997763, by rfl⟩ : syracuseStep 1330351 = 1995527) B1995527
theorem B8522945 : Blo 1328983 8522945 := bstep (se 2 (by rfl) ⟨3196104, by rfl⟩ : syracuseStep 8522945 = 6392209) B6392209
theorem B1330375 : Blo 1328983 1330375 := bstep (se 1 (by rfl) ⟨997781, by rfl⟩ : syracuseStep 1330375 = 1995563) B1995563
theorem B1330395 : Blo 1328983 1330395 := bstep (se 1 (by rfl) ⟨997796, by rfl⟩ : syracuseStep 1330395 = 1995593) B1995593
theorem B2993399 : Blo 1328983 2993399 := bstep (se 1 (by rfl) ⟨2245049, by rfl⟩ : syracuseStep 2993399 = 4490099) B4490099
theorem B1330471 : Blo 1328983 1330471 := bstep (se 1 (by rfl) ⟨997853, by rfl⟩ : syracuseStep 1330471 = 1995707) B1995707
theorem B5049661 : Blo 1328983 5049661 := bstep (se 3 (by rfl) ⟨946811, by rfl⟩ : syracuseStep 5049661 = 1893623) B1893623
theorem B1330511 : Blo 1328983 1330511 := bstep (se 1 (by rfl) ⟨997883, by rfl⟩ : syracuseStep 1330511 = 1995767) B1995767
theorem B1330527 : Blo 1328983 1330527 := bstep (se 1 (by rfl) ⟨997895, by rfl⟩ : syracuseStep 1330527 = 1995791) B1995791
theorem B1682795 : Blo 1328983 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B1330555 : Blo 1328983 1330555 := bstep (se 1 (by rfl) ⟨997916, by rfl⟩ : syracuseStep 1330555 = 1995833) B1995833
theorem B1994159 : Blo 1328983 1994159 := bstep (se 1 (by rfl) ⟨1495619, by rfl⟩ : syracuseStep 1994159 = 2991239) B2991239
theorem B1330607 : Blo 1328983 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B1330631 : Blo 1328983 1330631 := bstep (se 1 (by rfl) ⟨997973, by rfl⟩ : syracuseStep 1330631 = 1995947) B1995947
theorem B1330651 : Blo 1328983 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B10792435 : Blo 1328983 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B1994249 : Blo 1328983 1994249 := bstep (se 2 (by rfl) ⟨747843, by rfl⟩ : syracuseStep 1994249 = 1495687) B1495687
theorem B1994279 : Blo 1328983 1994279 := bstep (se 1 (by rfl) ⟨1495709, by rfl⟩ : syracuseStep 1994279 = 2991419) B2991419
theorem B1330727 : Blo 1328983 1330727 := bstep (se 1 (by rfl) ⟨998045, by rfl⟩ : syracuseStep 1330727 = 1996091) B1996091
theorem B1330767 : Blo 1328983 1330767 := bstep (se 1 (by rfl) ⟨998075, by rfl⟩ : syracuseStep 1330767 = 1996151) B1996151
theorem B1330783 : Blo 1328983 1330783 := bstep (se 1 (by rfl) ⟨998087, by rfl⟩ : syracuseStep 1330783 = 1996175) B1996175
theorem B1994363 : Blo 1328983 1994363 := bstep (se 1 (by rfl) ⟨1495772, by rfl⟩ : syracuseStep 1994363 = 2991545) B2991545
theorem B1330811 : Blo 1328983 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B1330863 : Blo 1328983 1330863 := bstep (se 1 (by rfl) ⟨998147, by rfl⟩ : syracuseStep 1330863 = 1996295) B1996295
theorem B3788477 : Blo 1328983 3788477 := bstep (se 3 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 3788477 = 1420679) B1420679
theorem B1330887 : Blo 1328983 1330887 := bstep (se 1 (by rfl) ⟨998165, by rfl⟩ : syracuseStep 1330887 = 1996331) B1996331
theorem B1330907 : Blo 1328983 1330907 := bstep (se 1 (by rfl) ⟨998180, by rfl⟩ : syracuseStep 1330907 = 1996361) B1996361
theorem B1994489 : Blo 1328983 1994489 := bstep (se 2 (by rfl) ⟨747933, by rfl⟩ : syracuseStep 1994489 = 1495867) B1495867
theorem B6393593 : Blo 1328983 6393593 := bstep (se 2 (by rfl) ⟨2397597, by rfl⟩ : syracuseStep 6393593 = 4795195) B4795195
theorem B1330983 : Blo 1328983 1330983 := bstep (se 1 (by rfl) ⟨998237, by rfl⟩ : syracuseStep 1330983 = 1996475) B1996475
theorem B2993993 : Blo 1328983 2993993 := bstep (se 2 (by rfl) ⟨1122747, by rfl⟩ : syracuseStep 2993993 = 2245495) B2245495
theorem B1994591 : Blo 1328983 1994591 := bstep (se 1 (by rfl) ⟨1495943, by rfl⟩ : syracuseStep 1994591 = 2991887) B2991887
theorem B1994603 : Blo 1328983 1994603 := bstep (se 1 (by rfl) ⟨1495952, by rfl⟩ : syracuseStep 1994603 = 2991905) B2991905
theorem B15142787 : Blo 1328983 15142787 := bstep (se 1 (by rfl) ⟨11357090, by rfl⟩ : syracuseStep 15142787 = 22714181) B22714181
theorem B10940345 : Blo 1328983 10940345 := bstep (se 2 (by rfl) ⟨4102629, by rfl⟩ : syracuseStep 10940345 = 8205259) B8205259
theorem B245542873 : Blo 1328983 245542873 := bstep (se 2 (by rfl) ⟨92078577, by rfl⟩ : syracuseStep 245542873 = 184157155) B184157155
theorem B21573647 : Blo 1328983 21573647 := bstep (se 1 (by rfl) ⟨16180235, by rfl⟩ : syracuseStep 21573647 = 32360471) B32360471
theorem B3788819 : Blo 1328983 3788819 := bstep (se 1 (by rfl) ⟨2841614, by rfl⟩ : syracuseStep 3788819 = 5683229) B5683229
theorem B17043533 : Blo 1328983 17043533 := bstep (se 3 (by rfl) ⟨3195662, by rfl⟩ : syracuseStep 17043533 = 6391325) B6391325
theorem B1994831 : Blo 1328983 1994831 := bstep (se 1 (by rfl) ⟨1496123, by rfl⟩ : syracuseStep 1994831 = 2992247) B2992247
theorem B4796495 : Blo 1328983 4796495 := bstep (se 1 (by rfl) ⟨3597371, by rfl⟩ : syracuseStep 4796495 = 7194743) B7194743
theorem B12947633 : Blo 1328983 12947633 := bstep (se 2 (by rfl) ⟨4855362, by rfl⟩ : syracuseStep 12947633 = 9710725) B9710725
theorem B1994951 : Blo 1328983 1994951 := bstep (se 1 (by rfl) ⟨1496213, by rfl⟩ : syracuseStep 1994951 = 2992427) B2992427
theorem B1347935 : Blo 1328983 1347935 := bstep (se 1 (by rfl) ⟨1010951, by rfl⟩ : syracuseStep 1347935 = 2021903) B2021903
theorem B1995113 : Blo 1328983 1995113 := bstep (se 2 (by rfl) ⟨748167, by rfl⟩ : syracuseStep 1995113 = 1496335) B1496335
theorem B1495471 : Blo 1328983 1495471 := bstep (se 1 (by rfl) ⟨1121603, by rfl⟩ : syracuseStep 1495471 = 2243207) B2243207
theorem B1995191 : Blo 1328983 1995191 := bstep (se 1 (by rfl) ⟨1496393, by rfl⟩ : syracuseStep 1995191 = 2992787) B2992787
theorem B1995227 : Blo 1328983 1995227 := bstep (se 1 (by rfl) ⟨1496420, by rfl⟩ : syracuseStep 1995227 = 2992841) B2992841
theorem B4485671 : Blo 1328983 4485671 := bstep (se 1 (by rfl) ⟨3364253, by rfl⟩ : syracuseStep 4485671 = 6728507) B6728507
theorem B1684091 : Blo 1328983 1684091 := bstep (se 1 (by rfl) ⟨1263068, by rfl⟩ : syracuseStep 1684091 = 2526137) B2526137
theorem B4485779 : Blo 1328983 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B6730451 : Blo 1328983 6730451 := bstep (se 1 (by rfl) ⟨5047838, by rfl⟩ : syracuseStep 6730451 = 10095677) B10095677
theorem B29537075 : Blo 1328983 29537075 := bstep (se 1 (by rfl) ⟨22152806, by rfl⟩ : syracuseStep 29537075 = 44305613) B44305613
theorem B1495903 : Blo 1328983 1495903 := bstep (se 1 (by rfl) ⟨1121927, by rfl⟩ : syracuseStep 1495903 = 2243855) B2243855
theorem B4485995 : Blo 1328983 4485995 := bstep (se 1 (by rfl) ⟨3364496, by rfl⟩ : syracuseStep 4485995 = 6728993) B6728993
theorem B4486049 : Blo 1328983 4486049 := bstep (se 2 (by rfl) ⟨1682268, by rfl⟩ : syracuseStep 4486049 = 3364537) B3364537
theorem B19174319 : Blo 1328983 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B1995695 : Blo 1328983 1995695 := bstep (se 1 (by rfl) ⟨1496771, by rfl⟩ : syracuseStep 1995695 = 2993543) B2993543
theorem B5051393 : Blo 1328983 5051393 := bstep (se 2 (by rfl) ⟨1894272, by rfl⟩ : syracuseStep 5051393 = 3788545) B3788545
theorem B2274313 : Blo 1328983 2274313 := bstep (se 2 (by rfl) ⟨852867, by rfl⟩ : syracuseStep 2274313 = 1705735) B1705735
theorem B1995785 : Blo 1328983 1995785 := bstep (se 2 (by rfl) ⟨748419, by rfl⟩ : syracuseStep 1995785 = 1496839) B1496839
theorem B2462759 : Blo 1328983 2462759 := bstep (se 1 (by rfl) ⟨1847069, by rfl⟩ : syracuseStep 2462759 = 3694139) B3694139
theorem B2397223 : Blo 1328983 2397223 := bstep (se 1 (by rfl) ⟨1797917, by rfl⟩ : syracuseStep 2397223 = 3595835) B3595835
theorem B1995815 : Blo 1328983 1995815 := bstep (se 1 (by rfl) ⟨1496861, by rfl⟩ : syracuseStep 1995815 = 2993723) B2993723
theorem B1995899 : Blo 1328983 1995899 := bstep (se 1 (by rfl) ⟨1496924, by rfl⟩ : syracuseStep 1995899 = 2993849) B2993849
theorem B1496263 : Blo 1328983 1496263 := bstep (se 1 (by rfl) ⟨1122197, by rfl⟩ : syracuseStep 1496263 = 2244395) B2244395
theorem B8525047 : Blo 1328983 8525047 := bstep (se 1 (by rfl) ⟨6393785, by rfl⟩ : syracuseStep 8525047 = 12787571) B12787571
theorem B1996025 : Blo 1328983 1996025 := bstep (se 2 (by rfl) ⟨748509, by rfl⟩ : syracuseStep 1996025 = 1497019) B1497019
theorem B1996127 : Blo 1328983 1996127 := bstep (se 1 (by rfl) ⟨1497095, by rfl⟩ : syracuseStep 1996127 = 2994191) B2994191
theorem B1996139 : Blo 1328983 1996139 := bstep (se 1 (by rfl) ⟨1497104, by rfl⟩ : syracuseStep 1996139 = 2994209) B2994209
theorem B28767707 : Blo 1328983 28767707 := bstep (se 1 (by rfl) ⟨21575780, by rfl⟩ : syracuseStep 28767707 = 43151561) B43151561
theorem B4486643 : Blo 1328983 4486643 := bstep (se 1 (by rfl) ⟨3364982, by rfl⟩ : syracuseStep 4486643 = 6729965) B6729965
theorem B3593737 : Blo 1328983 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B1996367 : Blo 1328983 1996367 := bstep (se 1 (by rfl) ⟨1497275, by rfl⟩ : syracuseStep 1996367 = 2994551) B2994551
theorem B28448405 : Blo 1328983 28448405 := bstep (se 6 (by rfl) ⟨666759, by rfl⟩ : syracuseStep 28448405 = 1333519) B1333519
theorem B2397943 : Blo 1328983 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B10098593 : Blo 1328983 10098593 := bstep (se 2 (by rfl) ⟨3786972, by rfl⟩ : syracuseStep 10098593 = 7573945) B7573945
theorem B2840503 : Blo 1328983 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B16390097 : Blo 1328983 16390097 := bstep (se 2 (by rfl) ⟨6146286, by rfl⟩ : syracuseStep 16390097 = 12292573) B12292573
theorem B12777425 : Blo 1328983 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B4487183 : Blo 1328983 4487183 := bstep (se 1 (by rfl) ⟨3365387, by rfl⟩ : syracuseStep 4487183 = 6730775) B6730775
theorem B1497127 : Blo 1328983 1497127 := bstep (se 1 (by rfl) ⟨1122845, by rfl⟩ : syracuseStep 1497127 = 2245691) B2245691
theorem B4552783 : Blo 1328983 4552783 := bstep (se 1 (by rfl) ⟨3414587, by rfl⟩ : syracuseStep 4552783 = 6829175) B6829175
theorem B11360645 : Blo 1328983 11360645 := bstep (se 4 (by rfl) ⟨1065060, by rfl⟩ : syracuseStep 11360645 = 2130121) B2130121
theorem B2242991 : Blo 1328983 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B4487777 : Blo 1328983 4487777 := bstep (se 2 (by rfl) ⟨1682916, by rfl⟩ : syracuseStep 4487777 = 3365833) B3365833
theorem B4315771 : Blo 1328983 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B5053063 : Blo 1328983 5053063 := bstep (se 1 (by rfl) ⟨3789797, by rfl⟩ : syracuseStep 5053063 = 7579595) B7579595
theorem B14383817 : Blo 1328983 14383817 := bstep (se 2 (by rfl) ⟨5393931, by rfl⟩ : syracuseStep 14383817 = 10787863) B10787863
theorem B2243423 : Blo 1328983 2243423 := bstep (se 1 (by rfl) ⟨1682567, by rfl⟩ : syracuseStep 2243423 = 3365135) B3365135
theorem B9591659 : Blo 1328983 9591659 := bstep (se 1 (by rfl) ⟨7193744, by rfl⟩ : syracuseStep 9591659 = 14387489) B14387489
theorem B2128783 : Blo 1328983 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B6732719 : Blo 1328983 6732719 := bstep (se 1 (by rfl) ⟨5049539, by rfl⟩ : syracuseStep 6732719 = 10099079) B10099079
theorem B5053367 : Blo 1328983 5053367 := bstep (se 1 (by rfl) ⟨3790025, by rfl⟩ : syracuseStep 5053367 = 7580051) B7580051
theorem B3365945 : Blo 1328983 3365945 := bstep (se 2 (by rfl) ⟨1262229, by rfl⟩ : syracuseStep 3365945 = 2524459) B2524459
theorem B6144335189 : Blo 1328983 6144335189 := bstep (se 11 (by rfl) ⟨4500245, by rfl⟩ : syracuseStep 6144335189 = 9000491) B9000491
theorem B6389117 : Blo 1328983 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B5119361 : Blo 1328983 5119361 := bstep (se 2 (by rfl) ⟨1919760, by rfl⟩ : syracuseStep 5119361 = 3839521) B3839521
theorem B2243983 : Blo 1328983 2243983 := bstep (se 1 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 2243983 = 3365975) B3365975
theorem B21052853 : Blo 1328983 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B5684681 : Blo 1328983 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B30711257 : Blo 1328983 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B2842075 : Blo 1328983 2842075 := bstep (se 1 (by rfl) ⟨2131556, by rfl⟩ : syracuseStep 2842075 = 4263113) B4263113
theorem B2129417 : Blo 1328983 2129417 := bstep (se 2 (by rfl) ⟨798531, by rfl⟩ : syracuseStep 2129417 = 1597063) B1597063
theorem B97041959 : Blo 1328983 97041959 := bstep (se 1 (by rfl) ⟨72781469, by rfl⟩ : syracuseStep 97041959 = 145562939) B145562939
theorem B8519255 : Blo 1328983 8519255 := bstep (se 1 (by rfl) ⟨6389441, by rfl⟩ : syracuseStep 8519255 = 12778883) B12778883
theorem B17055319 : Blo 1328983 17055319 := bstep (se 1 (by rfl) ⟨12791489, by rfl⟩ : syracuseStep 17055319 = 25582979) B25582979
theorem B5684833 : Blo 1328983 5684833 := bstep (se 2 (by rfl) ⟨2131812, by rfl⟩ : syracuseStep 5684833 = 4263625) B4263625
theorem B8519357 : Blo 1328983 8519357 := bstep (se 3 (by rfl) ⟨1597379, by rfl⟩ : syracuseStep 8519357 = 3194759) B3194759
theorem B3194567 : Blo 1328983 3194567 := bstep (se 1 (by rfl) ⟨2395925, by rfl⟩ : syracuseStep 3194567 = 4791851) B4791851
theorem B7577387 : Blo 1328983 7577387 := bstep (se 1 (by rfl) ⟨5683040, by rfl⟩ : syracuseStep 7577387 = 11366081) B11366081
theorem B1892279 : Blo 1328983 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B11362355 : Blo 1328983 11362355 := bstep (se 1 (by rfl) ⟨8521766, by rfl⟩ : syracuseStep 11362355 = 17043533) B17043533
theorem B3367241 : Blo 1328983 3367241 := bstep (se 2 (by rfl) ⟨1262715, by rfl⟩ : syracuseStep 3367241 = 2525431) B2525431
theorem B3031387 : Blo 1328983 3031387 := bstep (se 1 (by rfl) ⟨2273540, by rfl⟩ : syracuseStep 3031387 = 4547081) B4547081
theorem B2244955 : Blo 1328983 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B2990447 : Blo 1328983 2990447 := bstep (se 1 (by rfl) ⟨2242835, by rfl⟩ : syracuseStep 2990447 = 4485671) B4485671
theorem B2990519 : Blo 1328983 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B2990663 : Blo 1328983 2990663 := bstep (se 1 (by rfl) ⟨2242997, by rfl⟩ : syracuseStep 2990663 = 4485995) B4485995
theorem B3785287 : Blo 1328983 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B2990699 : Blo 1328983 2990699 := bstep (se 1 (by rfl) ⟨2243024, by rfl⟩ : syracuseStep 2990699 = 4486049) B4486049
theorem B3367595 : Blo 1328983 3367595 := bstep (se 1 (by rfl) ⟨2525696, by rfl⟩ : syracuseStep 3367595 = 5051393) B5051393
theorem B1541071 : Blo 1328983 1541071 := bstep (se 1 (by rfl) ⟨1155803, by rfl⟩ : syracuseStep 1541071 = 2311607) B2311607
theorem B19178471 : Blo 1328983 19178471 := bstep (se 1 (by rfl) ⟨14383853, by rfl⟩ : syracuseStep 19178471 = 28767707) B28767707
theorem B2991095 : Blo 1328983 2991095 := bstep (se 1 (by rfl) ⟨2243321, by rfl⟩ : syracuseStep 2991095 = 4486643) B4486643
theorem B7570529 : Blo 1328983 7570529 := bstep (se 2 (by rfl) ⟨2838948, by rfl⟩ : syracuseStep 7570529 = 5677897) B5677897
theorem B18965603 : Blo 1328983 18965603 := bstep (se 1 (by rfl) ⟨14224202, by rfl⟩ : syracuseStep 18965603 = 28448405) B28448405
theorem B8520947 : Blo 1328983 8520947 := bstep (se 1 (by rfl) ⟨6390710, by rfl⟩ : syracuseStep 8520947 = 12781421) B12781421
theorem B12789029 : Blo 1328983 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B2245927 : Blo 1328983 2245927 := bstep (se 1 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 2245927 = 3368891) B3368891
theorem B2991455 : Blo 1328983 2991455 := bstep (se 1 (by rfl) ⟨2243591, by rfl⟩ : syracuseStep 2991455 = 4487183) B4487183
theorem B3032417 : Blo 1328983 3032417 := bstep (se 2 (by rfl) ⟨1137156, by rfl⟩ : syracuseStep 3032417 = 2274313) B2274313
theorem B3196297 : Blo 1328983 3196297 := bstep (se 2 (by rfl) ⟨1198611, by rfl⟩ : syracuseStep 3196297 = 2397223) B2397223
theorem B97126037 : Blo 1328983 97126037 := bstep (se 6 (by rfl) ⟨2276391, by rfl⟩ : syracuseStep 97126037 = 4552783) B4552783
theorem B4490909 : Blo 1328983 4490909 := bstep (se 3 (by rfl) ⟨842045, by rfl⟩ : syracuseStep 4490909 = 1684091) B1684091
theorem B2991851 : Blo 1328983 2991851 := bstep (se 1 (by rfl) ⟨2243888, by rfl⟩ : syracuseStep 2991851 = 4487777) B4487777
theorem B2524907 : Blo 1328983 2524907 := bstep (se 1 (by rfl) ⟨1893680, by rfl⟩ : syracuseStep 2524907 = 3787361) B3787361
theorem B2991977 : Blo 1328983 2991977 := bstep (se 2 (by rfl) ⟨1121991, by rfl⟩ : syracuseStep 2991977 = 2243983) B2243983
theorem B1329051 : Blo 1328983 1329051 := bstep (se 1 (by rfl) ⟨996788, by rfl⟩ : syracuseStep 1329051 = 1993577) B1993577
theorem B1329103 : Blo 1328983 1329103 := bstep (se 1 (by rfl) ⟨996827, by rfl⟩ : syracuseStep 1329103 = 1993655) B1993655
theorem B3368911 : Blo 1328983 3368911 := bstep (se 1 (by rfl) ⟨2526683, by rfl⟩ : syracuseStep 3368911 = 5053367) B5053367
theorem B1329127 : Blo 1328983 1329127 := bstep (se 1 (by rfl) ⟨996845, by rfl⟩ : syracuseStep 1329127 = 1993691) B1993691
theorem B7579777 : Blo 1328983 7579777 := bstep (se 2 (by rfl) ⟨2842416, by rfl⟩ : syracuseStep 7579777 = 5684833) B5684833
theorem B4491449 : Blo 1328983 4491449 := bstep (se 2 (by rfl) ⟨1684293, by rfl⟩ : syracuseStep 4491449 = 3368587) B3368587
theorem B4096223459 : Blo 1328983 4096223459 := bstep (se 1 (by rfl) ⟨3072167594, by rfl⟩ : syracuseStep 4096223459 = 6144335189) B6144335189
theorem B746768645 : Blo 1328983 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B1329439 : Blo 1328983 1329439 := bstep (se 1 (by rfl) ⟨997079, by rfl⟩ : syracuseStep 1329439 = 1994159) B1994159
theorem B14035235 : Blo 1328983 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B20474171 : Blo 1328983 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B1419611 : Blo 1328983 1419611 := bstep (se 1 (by rfl) ⟨1064708, by rfl⟩ : syracuseStep 1419611 = 2129417) B2129417
theorem B1329499 : Blo 1328983 1329499 := bstep (se 1 (by rfl) ⟨997124, by rfl⟩ : syracuseStep 1329499 = 1994249) B1994249
theorem B1329519 : Blo 1328983 1329519 := bstep (se 1 (by rfl) ⟨997139, by rfl⟩ : syracuseStep 1329519 = 1994279) B1994279
theorem B64694639 : Blo 1328983 64694639 := bstep (se 1 (by rfl) ⟨48520979, by rfl⟩ : syracuseStep 64694639 = 97041959) B97041959
theorem B5679503 : Blo 1328983 5679503 := bstep (se 1 (by rfl) ⟨4259627, by rfl⟩ : syracuseStep 5679503 = 8519255) B8519255
theorem B1329575 : Blo 1328983 1329575 := bstep (se 1 (by rfl) ⟨997181, by rfl⟩ : syracuseStep 1329575 = 1994363) B1994363
theorem B5679571 : Blo 1328983 5679571 := bstep (se 1 (by rfl) ⟨4259678, by rfl⟩ : syracuseStep 5679571 = 8519357) B8519357
theorem B2525651 : Blo 1328983 2525651 := bstep (se 1 (by rfl) ⟨1894238, by rfl⟩ : syracuseStep 2525651 = 3788477) B3788477
theorem B1329659 : Blo 1328983 1329659 := bstep (se 1 (by rfl) ⟨997244, by rfl⟩ : syracuseStep 1329659 = 1994489) B1994489
theorem B4262395 : Blo 1328983 4262395 := bstep (se 1 (by rfl) ⟨3196796, by rfl⟩ : syracuseStep 4262395 = 6393593) B6393593
theorem B1329727 : Blo 1328983 1329727 := bstep (se 1 (by rfl) ⟨997295, by rfl⟩ : syracuseStep 1329727 = 1994591) B1994591
theorem B1329735 : Blo 1328983 1329735 := bstep (se 1 (by rfl) ⟨997301, by rfl⟩ : syracuseStep 1329735 = 1994603) B1994603
theorem B3787337 : Blo 1328983 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B10095191 : Blo 1328983 10095191 := bstep (se 1 (by rfl) ⟨7571393, by rfl⟩ : syracuseStep 10095191 = 15142787) B15142787
theorem B7293563 : Blo 1328983 7293563 := bstep (se 1 (by rfl) ⟨5470172, by rfl⟩ : syracuseStep 7293563 = 10940345) B10940345
theorem B2992823 : Blo 1328983 2992823 := bstep (se 1 (by rfl) ⟨2244617, by rfl⟩ : syracuseStep 2992823 = 4489235) B4489235
theorem B2525879 : Blo 1328983 2525879 := bstep (se 1 (by rfl) ⟨1894409, by rfl⟩ : syracuseStep 2525879 = 3788819) B3788819
theorem B1329887 : Blo 1328983 1329887 := bstep (se 1 (by rfl) ⟨997415, by rfl⟩ : syracuseStep 1329887 = 1994831) B1994831
theorem B3197663 : Blo 1328983 3197663 := bstep (se 1 (by rfl) ⟨2398247, by rfl⟩ : syracuseStep 3197663 = 4796495) B4796495
theorem B1329967 : Blo 1328983 1329967 := bstep (se 1 (by rfl) ⟨997475, by rfl⟩ : syracuseStep 1329967 = 1994951) B1994951
theorem B2993039 : Blo 1328983 2993039 := bstep (se 1 (by rfl) ⟨2244779, by rfl⟩ : syracuseStep 2993039 = 4489559) B4489559
theorem B1330075 : Blo 1328983 1330075 := bstep (se 1 (by rfl) ⟨997556, by rfl⟩ : syracuseStep 1330075 = 1995113) B1995113
theorem B1330127 : Blo 1328983 1330127 := bstep (se 1 (by rfl) ⟨997595, by rfl⟩ : syracuseStep 1330127 = 1995191) B1995191
theorem B1993703 : Blo 1328983 1993703 := bstep (se 1 (by rfl) ⟨1495277, by rfl⟩ : syracuseStep 1993703 = 2990555) B2990555
theorem B1330151 : Blo 1328983 1330151 := bstep (se 1 (by rfl) ⟨997613, by rfl⟩ : syracuseStep 1330151 = 1995227) B1995227
theorem B6827123 : Blo 1328983 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B4263101 : Blo 1328983 4263101 := bstep (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) B1598663
theorem B1993961 : Blo 1328983 1993961 := bstep (se 2 (by rfl) ⟨747735, by rfl⟩ : syracuseStep 1993961 = 1495471) B1495471
theorem B1994015 : Blo 1328983 1994015 := bstep (se 1 (by rfl) ⟨1495511, by rfl⟩ : syracuseStep 1994015 = 2991023) B2991023
theorem B12782879 : Blo 1328983 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B1330463 : Blo 1328983 1330463 := bstep (se 1 (by rfl) ⟨997847, by rfl⟩ : syracuseStep 1330463 = 1995695) B1995695
theorem B1330523 : Blo 1328983 1330523 := bstep (se 1 (by rfl) ⟨997892, by rfl⟩ : syracuseStep 1330523 = 1995785) B1995785
theorem B1641839 : Blo 1328983 1641839 := bstep (se 1 (by rfl) ⟨1231379, by rfl⟩ : syracuseStep 1641839 = 2462759) B2462759
theorem B1330543 : Blo 1328983 1330543 := bstep (se 1 (by rfl) ⟨997907, by rfl⟩ : syracuseStep 1330543 = 1995815) B1995815
theorem B1330599 : Blo 1328983 1330599 := bstep (se 1 (by rfl) ⟨997949, by rfl⟩ : syracuseStep 1330599 = 1995899) B1995899
theorem B1994183 : Blo 1328983 1994183 := bstep (se 1 (by rfl) ⟨1495637, by rfl⟩ : syracuseStep 1994183 = 2991275) B2991275
theorem B1330683 : Blo 1328983 1330683 := bstep (se 1 (by rfl) ⟨998012, by rfl⟩ : syracuseStep 1330683 = 1996025) B1996025
theorem B6737417 : Blo 1328983 6737417 := bstep (se 2 (by rfl) ⟨2526531, by rfl⟩ : syracuseStep 6737417 = 5053063) B5053063
theorem B1330751 : Blo 1328983 1330751 := bstep (se 1 (by rfl) ⟨998063, by rfl⟩ : syracuseStep 1330751 = 1996127) B1996127
theorem B1330759 : Blo 1328983 1330759 := bstep (se 1 (by rfl) ⟨998069, by rfl⟩ : syracuseStep 1330759 = 1996139) B1996139
theorem B2993759 : Blo 1328983 2993759 := bstep (se 1 (by rfl) ⟨2245319, by rfl⟩ : syracuseStep 2993759 = 4490639) B4490639
theorem B5049965 : Blo 1328983 5049965 := bstep (se 3 (by rfl) ⟨946868, by rfl⟩ : syracuseStep 5049965 = 1893737) B1893737
theorem B1683119 : Blo 1328983 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B1330911 : Blo 1328983 1330911 := bstep (se 1 (by rfl) ⟨998183, by rfl⟩ : syracuseStep 1330911 = 1996367) B1996367
theorem B6729479 : Blo 1328983 6729479 := bstep (se 1 (by rfl) ⟨5047109, by rfl⟩ : syracuseStep 6729479 = 10094219) B10094219
theorem B1994537 : Blo 1328983 1994537 := bstep (se 2 (by rfl) ⟨747951, by rfl⟩ : syracuseStep 1994537 = 1495903) B1495903
theorem B1994543 : Blo 1328983 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B2993975 : Blo 1328983 2993975 := bstep (se 1 (by rfl) ⟨2245481, by rfl⟩ : syracuseStep 2993975 = 4490963) B4490963
theorem B2838377 : Blo 1328983 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B3239887 : Blo 1328983 3239887 := bstep (se 1 (by rfl) ⟨2429915, by rfl⟩ : syracuseStep 3239887 = 4859831) B4859831
theorem B2994281 : Blo 1328983 2994281 := bstep (se 2 (by rfl) ⟨1122855, by rfl⟩ : syracuseStep 2994281 = 2245711) B2245711
theorem B7573763 : Blo 1328983 7573763 := bstep (se 1 (by rfl) ⟨5680322, by rfl⟩ : syracuseStep 7573763 = 11360645) B11360645
theorem B1995017 : Blo 1328983 1995017 := bstep (se 2 (by rfl) ⟨748131, by rfl⟩ : syracuseStep 1995017 = 1496263) B1496263
theorem B1495327 : Blo 1328983 1495327 := bstep (se 1 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 1495327 = 2242991) B2242991
theorem B11366729 : Blo 1328983 11366729 := bstep (se 2 (by rfl) ⟨4262523, by rfl⟩ : syracuseStep 11366729 = 8525047) B8525047
theorem B1995119 : Blo 1328983 1995119 := bstep (se 1 (by rfl) ⟨1496339, by rfl⟩ : syracuseStep 1995119 = 2992679) B2992679
theorem B1683823 : Blo 1328983 1683823 := bstep (se 1 (by rfl) ⟨1262867, by rfl⟩ : syracuseStep 1683823 = 2525735) B2525735
theorem B15151535 : Blo 1328983 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B9589211 : Blo 1328983 9589211 := bstep (se 1 (by rfl) ⟨7191908, by rfl⟩ : syracuseStep 9589211 = 14383817) B14383817
theorem B1495615 : Blo 1328983 1495615 := bstep (se 1 (by rfl) ⟨1121711, by rfl⟩ : syracuseStep 1495615 = 2243423) B2243423
theorem B1995335 : Blo 1328983 1995335 := bstep (se 1 (by rfl) ⟨1496501, by rfl⟩ : syracuseStep 1995335 = 2993003) B2993003
theorem B6394439 : Blo 1328983 6394439 := bstep (se 1 (by rfl) ⟨4795829, by rfl⟩ : syracuseStep 6394439 = 9591659) B9591659
theorem B1995371 : Blo 1328983 1995371 := bstep (se 1 (by rfl) ⟨1496528, by rfl⟩ : syracuseStep 1995371 = 2993057) B2993057
theorem B3789433 : Blo 1328983 3789433 := bstep (se 2 (by rfl) ⟨1421037, by rfl⟩ : syracuseStep 3789433 = 2842075) B2842075
theorem B14389913 : Blo 1328983 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B5681963 : Blo 1328983 5681963 := bstep (se 1 (by rfl) ⟨4261472, by rfl⟩ : syracuseStep 5681963 = 8522945) B8522945
theorem B1995599 : Blo 1328983 1995599 := bstep (se 1 (by rfl) ⟨1496699, by rfl⟩ : syracuseStep 1995599 = 2993399) B2993399
theorem B3412907 : Blo 1328983 3412907 := bstep (se 1 (by rfl) ⟨2559680, by rfl⟩ : syracuseStep 3412907 = 5119361) B5119361
theorem B3789787 : Blo 1328983 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B7189661 : Blo 1328983 7189661 := bstep (se 3 (by rfl) ⟨1348061, by rfl⟩ : syracuseStep 7189661 = 2696123) B2696123
theorem B5051591 : Blo 1328983 5051591 := bstep (se 1 (by rfl) ⟨3788693, by rfl⟩ : syracuseStep 5051591 = 7577387) B7577387
theorem B1995995 : Blo 1328983 1995995 := bstep (se 1 (by rfl) ⟨1496996, by rfl⟩ : syracuseStep 1995995 = 2993993) B2993993
theorem B327390497 : Blo 1328983 327390497 := bstep (se 2 (by rfl) ⟨122771436, by rfl⟩ : syracuseStep 327390497 = 245542873) B245542873
theorem B14382431 : Blo 1328983 14382431 := bstep (se 1 (by rfl) ⟨10786823, by rfl⟩ : syracuseStep 14382431 = 21573647) B21573647
theorem B3364193 : Blo 1328983 3364193 := bstep (se 2 (by rfl) ⟨1261572, by rfl⟩ : syracuseStep 3364193 = 2523145) B2523145
theorem B1496443 : Blo 1328983 1496443 := bstep (se 1 (by rfl) ⟨1122332, by rfl⟩ : syracuseStep 1496443 = 2244665) B2244665
theorem B1996169 : Blo 1328983 1996169 := bstep (se 2 (by rfl) ⟨748563, by rfl⟩ : syracuseStep 1996169 = 1497127) B1497127
theorem B4486589 : Blo 1328983 4486589 := bstep (se 3 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 4486589 = 1682471) B1682471
theorem B8631755 : Blo 1328983 8631755 := bstep (se 1 (by rfl) ⟨6473816, by rfl⟩ : syracuseStep 8631755 = 12947633) B12947633
theorem B12785339 : Blo 1328983 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B5052091 : Blo 1328983 5052091 := bstep (se 1 (by rfl) ⟨3789068, by rfl⟩ : syracuseStep 5052091 = 7578137) B7578137
theorem B3364649 : Blo 1328983 3364649 := bstep (se 2 (by rfl) ⟨1261743, by rfl⟩ : syracuseStep 3364649 = 2523487) B2523487
theorem B4486967 : Blo 1328983 4486967 := bstep (se 1 (by rfl) ⟨3365225, by rfl⟩ : syracuseStep 4486967 = 6730451) B6730451
theorem B1496911 : Blo 1328983 1496911 := bstep (se 1 (by rfl) ⟨1122683, by rfl⟩ : syracuseStep 1496911 = 2245367) B2245367
theorem B19691383 : Blo 1328983 19691383 := bstep (se 1 (by rfl) ⟨14768537, by rfl⟩ : syracuseStep 19691383 = 29537075) B29537075
theorem B23017445 : Blo 1328983 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B3594451 : Blo 1328983 3594451 := bstep (se 1 (by rfl) ⟨2695838, by rfl⟩ : syracuseStep 3594451 = 5391677) B5391677
theorem B1497307 : Blo 1328983 1497307 := bstep (se 1 (by rfl) ⟨1122980, by rfl⟩ : syracuseStep 1497307 = 2245961) B2245961
theorem B3594493 : Blo 1328983 3594493 := bstep (se 3 (by rfl) ⟨673967, by rfl⟩ : syracuseStep 3594493 = 1347935) B1347935
theorem B4487453 : Blo 1328983 4487453 := bstep (se 3 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 4487453 = 1682795) B1682795
theorem B6732395 : Blo 1328983 6732395 := bstep (se 1 (by rfl) ⟨5049296, by rfl⟩ : syracuseStep 6732395 = 10098593) B10098593
theorem B10926731 : Blo 1328983 10926731 := bstep (se 1 (by rfl) ⟨8195048, by rfl⟩ : syracuseStep 10926731 = 16390097) B16390097
theorem B8518283 : Blo 1328983 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B3365651 : Blo 1328983 3365651 := bstep (se 1 (by rfl) ⟨2524238, by rfl⟩ : syracuseStep 3365651 = 5048477) B5048477
theorem B5462939 : Blo 1328983 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B2841563 : Blo 1328983 2841563 := bstep (se 1 (by rfl) ⟨2131172, by rfl⟩ : syracuseStep 2841563 = 4262345) B4262345
theorem B11361329 : Blo 1328983 11361329 := bstep (se 2 (by rfl) ⟨4260498, by rfl⟩ : syracuseStep 11361329 = 8520997) B8520997
theorem B6732881 : Blo 1328983 6732881 := bstep (se 2 (by rfl) ⟨2524830, by rfl⟩ : syracuseStep 6732881 = 5049661) B5049661
theorem B3366107 : Blo 1328983 3366107 := bstep (se 1 (by rfl) ⟨2524580, by rfl⟩ : syracuseStep 3366107 = 5049161) B5049161
theorem B3366137 : Blo 1328983 3366137 := bstep (se 2 (by rfl) ⟨1262301, by rfl⟩ : syracuseStep 3366137 = 2524603) B2524603
theorem B17030411 : Blo 1328983 17030411 := bstep (se 1 (by rfl) ⟨12772808, by rfl⟩ : syracuseStep 17030411 = 25545617) B25545617
theorem B4488479 : Blo 1328983 4488479 := bstep (se 1 (by rfl) ⟨3366359, by rfl⟩ : syracuseStep 4488479 = 6732719) B6732719
theorem B4791649 : Blo 1328983 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B2243963 : Blo 1328983 2243963 := bstep (se 1 (by rfl) ⟨1682972, by rfl⟩ : syracuseStep 2243963 = 3365945) B3365945
theorem B2022779 : Blo 1328983 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B1596871 : Blo 1328983 1596871 := bstep (se 1 (by rfl) ⟨1197653, by rfl⟩ : syracuseStep 1596871 = 2395307) B2395307
theorem B22740425 : Blo 1328983 22740425 := bstep (se 2 (by rfl) ⟨8527659, by rfl⟩ : syracuseStep 22740425 = 17055319) B17055319
theorem B4259411 : Blo 1328983 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B5463713 : Blo 1328983 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B2129711 : Blo 1328983 2129711 := bstep (se 1 (by rfl) ⟨1597283, by rfl⟩ : syracuseStep 2129711 = 3194567) B3194567
theorem B5046077 : Blo 1328983 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B3366785 : Blo 1328983 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B2244827 : Blo 1328983 2244827 := bstep (se 1 (by rfl) ⟨1683620, by rfl⟩ : syracuseStep 2244827 = 3367241) B3367241
theorem B7577819 : Blo 1328983 7577819 := bstep (se 1 (by rfl) ⟨5683364, by rfl⟩ : syracuseStep 7577819 = 11366729) B11366729
theorem B4792601 : Blo 1328983 4792601 := bstep (se 2 (by rfl) ⟨1797225, by rfl⟩ : syracuseStep 4792601 = 3594451) B3594451
theorem B10101023 : Blo 1328983 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B4792657 : Blo 1328983 4792657 := bstep (se 2 (by rfl) ⟨1797246, by rfl⟩ : syracuseStep 4792657 = 3594493) B3594493
theorem B9593275 : Blo 1328983 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B2245063 : Blo 1328983 2245063 := bstep (se 1 (by rfl) ⟨1683797, by rfl⟩ : syracuseStep 2245063 = 3367595) B3367595
theorem B2245097 : Blo 1328983 2245097 := bstep (se 2 (by rfl) ⟨841911, by rfl⟩ : syracuseStep 2245097 = 1683823) B1683823
theorem B5047019 : Blo 1328983 5047019 := bstep (se 1 (by rfl) ⟨3785264, by rfl⟩ : syracuseStep 5047019 = 7570529) B7570529
theorem B5047049 : Blo 1328983 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B34104077 : Blo 1328983 34104077 := bstep (se 3 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 34104077 = 12789029) B12789029
theorem B4793107 : Blo 1328983 4793107 := bstep (se 1 (by rfl) ⟨3594830, by rfl⟩ : syracuseStep 4793107 = 7189661) B7189661
theorem B3367727 : Blo 1328983 3367727 := bstep (se 1 (by rfl) ⟨2525795, by rfl⟩ : syracuseStep 3367727 = 5051591) B5051591
theorem B218260331 : Blo 1328983 218260331 := bstep (se 1 (by rfl) ⟨163695248, by rfl⟩ : syracuseStep 218260331 = 327390497) B327390497
theorem B3785629 : Blo 1328983 3785629 := bstep (se 3 (by rfl) ⟨709805, by rfl⟩ : syracuseStep 3785629 = 1419611) B1419611
theorem B2991059 : Blo 1328983 2991059 := bstep (se 1 (by rfl) ⟨2243294, by rfl⟩ : syracuseStep 2991059 = 4486589) B4486589
theorem B64750691 : Blo 1328983 64750691 := bstep (se 1 (by rfl) ⟨48563018, by rfl⟩ : syracuseStep 64750691 = 97126037) B97126037
theorem B2991311 : Blo 1328983 2991311 := bstep (se 1 (by rfl) ⟨2243483, by rfl⟩ : syracuseStep 2991311 = 4486967) B4486967
theorem B15344963 : Blo 1328983 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B497845763 : Blo 1328983 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B2991635 : Blo 1328983 2991635 := bstep (se 1 (by rfl) ⟨2243726, by rfl⟩ : syracuseStep 2991635 = 4487453) B4487453
theorem B13649447 : Blo 1328983 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B3786335 : Blo 1328983 3786335 := bstep (se 1 (by rfl) ⟨2839751, by rfl⟩ : syracuseStep 3786335 = 5679503) B5679503
theorem B7284487 : Blo 1328983 7284487 := bstep (se 1 (by rfl) ⟨5463365, by rfl⟩ : syracuseStep 7284487 = 10926731) B10926731
theorem B5678855 : Blo 1328983 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B2131775 : Blo 1328983 2131775 := bstep (se 1 (by rfl) ⟨1598831, by rfl⟩ : syracuseStep 2131775 = 3197663) B3197663
theorem B4261729 : Blo 1328983 4261729 := bstep (se 2 (by rfl) ⟨1598148, by rfl⟩ : syracuseStep 4261729 = 3196297) B3196297
theorem B1894375 : Blo 1328983 1894375 := bstep (se 1 (by rfl) ⟨1420781, by rfl⟩ : syracuseStep 1894375 = 2841563) B2841563
theorem B1329135 : Blo 1328983 1329135 := bstep (se 1 (by rfl) ⟨996851, by rfl⟩ : syracuseStep 1329135 = 1993703) B1993703
theorem B5679229 : Blo 1328983 5679229 := bstep (se 3 (by rfl) ⟨1064855, by rfl⟩ : syracuseStep 5679229 = 2129711) B2129711
theorem B1329307 : Blo 1328983 1329307 := bstep (se 1 (by rfl) ⟨996980, by rfl⟩ : syracuseStep 1329307 = 1993961) B1993961
theorem B1329343 : Blo 1328983 1329343 := bstep (se 1 (by rfl) ⟨997007, by rfl⟩ : syracuseStep 1329343 = 1994015) B1994015
theorem B2992319 : Blo 1328983 2992319 := bstep (se 1 (by rfl) ⟨2244239, by rfl⟩ : syracuseStep 2992319 = 4488479) B4488479
theorem B8521919 : Blo 1328983 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B6736121 : Blo 1328983 6736121 := bstep (se 2 (by rfl) ⟨2526045, by rfl⟩ : syracuseStep 6736121 = 5052091) B5052091
theorem B1329455 : Blo 1328983 1329455 := bstep (se 1 (by rfl) ⟨997091, by rfl⟩ : syracuseStep 1329455 = 1994183) B1994183
theorem B4491611 : Blo 1328983 4491611 := bstep (se 1 (by rfl) ⟨3368708, by rfl⟩ : syracuseStep 4491611 = 6737417) B6737417
theorem B8219045 : Blo 1328983 8219045 := bstep (se 4 (by rfl) ⟨770535, by rfl⟩ : syracuseStep 8219045 = 1541071) B1541071
theorem B1329691 : Blo 1328983 1329691 := bstep (se 1 (by rfl) ⟨997268, by rfl⟩ : syracuseStep 1329691 = 1994537) B1994537
theorem B1329695 : Blo 1328983 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B4319849 : Blo 1328983 4319849 := bstep (se 2 (by rfl) ⟨1619943, by rfl⟩ : syracuseStep 4319849 = 3239887) B3239887
theorem B4491881 : Blo 1328983 4491881 := bstep (se 2 (by rfl) ⟨1684455, by rfl⟩ : syracuseStep 4491881 = 3368911) B3368911
theorem B5049175 : Blo 1328983 5049175 := bstep (se 1 (by rfl) ⟨3786881, by rfl⟩ : syracuseStep 5049175 = 7573763) B7573763
theorem B1330011 : Blo 1328983 1330011 := bstep (se 1 (by rfl) ⟨997508, by rfl⟩ : syracuseStep 1330011 = 1995017) B1995017
theorem B1993631 : Blo 1328983 1993631 := bstep (se 1 (by rfl) ⟨1495223, by rfl⟩ : syracuseStep 1993631 = 2990447) B2990447
theorem B1330079 : Blo 1328983 1330079 := bstep (se 1 (by rfl) ⟨997559, by rfl⟩ : syracuseStep 1330079 = 1995119) B1995119
theorem B1993679 : Blo 1328983 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B18205661 : Blo 1328983 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B6392807 : Blo 1328983 6392807 := bstep (se 1 (by rfl) ⟨4794605, by rfl⟩ : syracuseStep 6392807 = 9589211) B9589211
theorem B1993769 : Blo 1328983 1993769 := bstep (se 2 (by rfl) ⟨747663, by rfl⟩ : syracuseStep 1993769 = 1495327) B1495327
theorem B1993775 : Blo 1328983 1993775 := bstep (se 1 (by rfl) ⟨1495331, by rfl⟩ : syracuseStep 1993775 = 2990663) B2990663
theorem B1330223 : Blo 1328983 1330223 := bstep (se 1 (by rfl) ⟨997667, by rfl⟩ : syracuseStep 1330223 = 1995335) B1995335
theorem B4262959 : Blo 1328983 4262959 := bstep (se 1 (by rfl) ⟨3197219, by rfl⟩ : syracuseStep 4262959 = 6394439) B6394439
theorem B1993799 : Blo 1328983 1993799 := bstep (se 1 (by rfl) ⟨1495349, by rfl⟩ : syracuseStep 1993799 = 2990699) B2990699
theorem B1330247 : Blo 1328983 1330247 := bstep (se 1 (by rfl) ⟨997685, by rfl⟩ : syracuseStep 1330247 = 1995371) B1995371
theorem B2993273 : Blo 1328983 2993273 := bstep (se 2 (by rfl) ⟨1122477, by rfl⟩ : syracuseStep 2993273 = 2244955) B2244955
theorem B3787975 : Blo 1328983 3787975 := bstep (se 1 (by rfl) ⟨2840981, by rfl⟩ : syracuseStep 3787975 = 5681963) B5681963
theorem B1330399 : Blo 1328983 1330399 := bstep (se 1 (by rfl) ⟨997799, by rfl⟩ : syracuseStep 1330399 = 1995599) B1995599
theorem B7572761 : Blo 1328983 7572761 := bstep (se 2 (by rfl) ⟨2839785, by rfl⟩ : syracuseStep 7572761 = 5679571) B5679571
theorem B1994063 : Blo 1328983 1994063 := bstep (se 1 (by rfl) ⟨1495547, by rfl⟩ : syracuseStep 1994063 = 2991095) B2991095
theorem B12643735 : Blo 1328983 12643735 := bstep (se 1 (by rfl) ⟨9482801, by rfl⟩ : syracuseStep 12643735 = 18965603) B18965603
theorem B1994153 : Blo 1328983 1994153 := bstep (se 2 (by rfl) ⟨747807, by rfl⟩ : syracuseStep 1994153 = 1495615) B1495615
theorem B1330663 : Blo 1328983 1330663 := bstep (se 1 (by rfl) ⟨997997, by rfl⟩ : syracuseStep 1330663 = 1995995) B1995995
theorem B5680631 : Blo 1328983 5680631 := bstep (se 1 (by rfl) ⟨4260473, by rfl⟩ : syracuseStep 5680631 = 8520947) B8520947
theorem B1994303 : Blo 1328983 1994303 := bstep (se 1 (by rfl) ⟨1495727, by rfl⟩ : syracuseStep 1994303 = 2991455) B2991455
theorem B9588287 : Blo 1328983 9588287 := bstep (se 1 (by rfl) ⟨7191215, by rfl⟩ : syracuseStep 9588287 = 14382431) B14382431
theorem B1330779 : Blo 1328983 1330779 := bstep (se 1 (by rfl) ⟨998084, by rfl⟩ : syracuseStep 1330779 = 1996169) B1996169
theorem B5754503 : Blo 1328983 5754503 := bstep (se 1 (by rfl) ⟨4315877, by rfl⟩ : syracuseStep 5754503 = 8631755) B8631755
theorem B5394077 : Blo 1328983 5394077 := bstep (se 3 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 5394077 = 2022779) B2022779
theorem B2993939 : Blo 1328983 2993939 := bstep (se 1 (by rfl) ⟨2245454, by rfl⟩ : syracuseStep 2993939 = 4490909) B4490909
theorem B8523559 : Blo 1328983 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1994567 : Blo 1328983 1994567 := bstep (se 1 (by rfl) ⟨1495925, by rfl⟩ : syracuseStep 1994567 = 2991851) B2991851
theorem B1683271 : Blo 1328983 1683271 := bstep (se 1 (by rfl) ⟨1262453, by rfl⟩ : syracuseStep 1683271 = 2524907) B2524907
theorem B1994651 : Blo 1328983 1994651 := bstep (se 1 (by rfl) ⟨1495988, by rfl⟩ : syracuseStep 1994651 = 2991977) B2991977
theorem B2994299 : Blo 1328983 2994299 := bstep (se 1 (by rfl) ⟨2245724, by rfl⟩ : syracuseStep 2994299 = 4491449) B4491449
theorem B2730815639 : Blo 1328983 2730815639 := bstep (se 1 (by rfl) ⟨2048111729, by rfl⟩ : syracuseStep 2730815639 = 4096223459) B4096223459
theorem B1683767 : Blo 1328983 1683767 := bstep (se 1 (by rfl) ⟨1262825, by rfl⟩ : syracuseStep 1683767 = 2525651) B2525651
theorem B2994569 : Blo 1328983 2994569 := bstep (se 2 (by rfl) ⟨1122963, by rfl⟩ : syracuseStep 2994569 = 2245927) B2245927
theorem B6730127 : Blo 1328983 6730127 := bstep (se 1 (by rfl) ⟨5047595, by rfl⟩ : syracuseStep 6730127 = 10095191) B10095191
theorem B4862375 : Blo 1328983 4862375 := bstep (se 1 (by rfl) ⟨3646781, by rfl⟩ : syracuseStep 4862375 = 7293563) B7293563
theorem B14569901 : Blo 1328983 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B1995215 : Blo 1328983 1995215 := bstep (se 1 (by rfl) ⟨1496411, by rfl⟩ : syracuseStep 1995215 = 2992823) B2992823
theorem B1683919 : Blo 1328983 1683919 := bstep (se 1 (by rfl) ⟨1262939, by rfl⟩ : syracuseStep 1683919 = 2525879) B2525879
theorem B16167397 : Blo 1328983 16167397 := bstep (se 4 (by rfl) ⟨1515693, by rfl⟩ : syracuseStep 16167397 = 3031387) B3031387
theorem B1995257 : Blo 1328983 1995257 := bstep (se 2 (by rfl) ⟨748221, by rfl⟩ : syracuseStep 1995257 = 1496443) B1496443
theorem B1995359 : Blo 1328983 1995359 := bstep (se 1 (by rfl) ⟨1496519, by rfl⟩ : syracuseStep 1995359 = 2993039) B2993039
theorem B3641959 : Blo 1328983 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B7574219 : Blo 1328983 7574219 := bstep (se 1 (by rfl) ⟨5680664, by rfl⟩ : syracuseStep 7574219 = 11361329) B11361329
theorem B1495975 : Blo 1328983 1495975 := bstep (se 1 (by rfl) ⟨1121981, by rfl⟩ : syracuseStep 1495975 = 2243963) B2243963
theorem B15160283 : Blo 1328983 15160283 := bstep (se 1 (by rfl) ⟨11370212, by rfl⟩ : syracuseStep 15160283 = 22740425) B22740425
theorem B2839607 : Blo 1328983 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B1995839 : Blo 1328983 1995839 := bstep (se 1 (by rfl) ⟨1496879, by rfl⟩ : syracuseStep 1995839 = 2993759) B2993759
theorem B1995881 : Blo 1328983 1995881 := bstep (se 2 (by rfl) ⟨748455, by rfl⟩ : syracuseStep 1995881 = 1496911) B1496911
theorem B4486319 : Blo 1328983 4486319 := bstep (se 1 (by rfl) ⟨3364739, by rfl⟩ : syracuseStep 4486319 = 6729479) B6729479
theorem B1995983 : Blo 1328983 1995983 := bstep (se 1 (by rfl) ⟨1496987, by rfl⟩ : syracuseStep 1995983 = 2993975) B2993975
theorem B3364051 : Blo 1328983 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B7574903 : Blo 1328983 7574903 := bstep (se 1 (by rfl) ⟨5681177, by rfl⟩ : syracuseStep 7574903 = 11362355) B11362355
theorem B1996187 : Blo 1328983 1996187 := bstep (se 1 (by rfl) ⟨1497140, by rfl⟩ : syracuseStep 1996187 = 2994281) B2994281
theorem B10106369 : Blo 1328983 10106369 := bstep (se 2 (by rfl) ⟨3789888, by rfl⟩ : syracuseStep 10106369 = 7579777) B7579777
theorem B1996409 : Blo 1328983 1996409 := bstep (se 2 (by rfl) ⟨748653, by rfl⟩ : syracuseStep 1996409 = 1497307) B1497307
theorem B2275271 : Blo 1328983 2275271 := bstep (se 1 (by rfl) ⟨1706453, by rfl⟩ : syracuseStep 2275271 = 3412907) B3412907
theorem B12785647 : Blo 1328983 12785647 := bstep (se 1 (by rfl) ⟨9589235, by rfl⟩ : syracuseStep 12785647 = 19178471) B19178471
theorem B5683193 : Blo 1328983 5683193 := bstep (se 2 (by rfl) ⟨2131197, by rfl⟩ : syracuseStep 5683193 = 4262395) B4262395
theorem B37427293 : Blo 1328983 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B5052577 : Blo 1328983 5052577 := bstep (se 2 (by rfl) ⟨1894716, by rfl⟩ : syracuseStep 5052577 = 3789433) B3789433
theorem B2242795 : Blo 1328983 2242795 := bstep (se 1 (by rfl) ⟨1682096, by rfl⟩ : syracuseStep 2242795 = 3364193) B3364193
theorem B2021611 : Blo 1328983 2021611 := bstep (se 1 (by rfl) ⟨1516208, by rfl⟩ : syracuseStep 2021611 = 3032417) B3032417
theorem B17512949 : Blo 1328983 17512949 := bstep (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) B1641839
theorem B2243099 : Blo 1328983 2243099 := bstep (se 1 (by rfl) ⟨1682324, by rfl⟩ : syracuseStep 2243099 = 3364649) B3364649
theorem B5053049 : Blo 1328983 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B10099565 : Blo 1328983 10099565 := bstep (se 3 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 10099565 = 3787337) B3787337
theorem B43129759 : Blo 1328983 43129759 := bstep (se 1 (by rfl) ⟨32347319, by rfl⟩ : syracuseStep 43129759 = 64694639) B64694639
theorem B4488263 : Blo 1328983 4488263 := bstep (se 1 (by rfl) ⟨3366197, by rfl⟩ : syracuseStep 4488263 = 6732395) B6732395
theorem B4488317 : Blo 1328983 4488317 := bstep (se 3 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 4488317 = 1683119) B1683119
theorem B6388865 : Blo 1328983 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B2243767 : Blo 1328983 2243767 := bstep (se 1 (by rfl) ⟨1682825, by rfl⟩ : syracuseStep 2243767 = 3365651) B3365651
theorem B2129161 : Blo 1328983 2129161 := bstep (se 2 (by rfl) ⟨798435, by rfl⟩ : syracuseStep 2129161 = 1596871) B1596871
theorem B4488587 : Blo 1328983 4488587 := bstep (se 1 (by rfl) ⟨3366440, by rfl⟩ : syracuseStep 4488587 = 6732881) B6732881
theorem B2842067 : Blo 1328983 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B2244071 : Blo 1328983 2244071 := bstep (se 1 (by rfl) ⟨1683053, by rfl⟩ : syracuseStep 2244071 = 3366107) B3366107
theorem B2244091 : Blo 1328983 2244091 := bstep (se 1 (by rfl) ⟨1683068, by rfl⟩ : syracuseStep 2244091 = 3366137) B3366137
theorem B11353607 : Blo 1328983 11353607 := bstep (se 1 (by rfl) ⟨8515205, by rfl⟩ : syracuseStep 11353607 = 17030411) B17030411
theorem B3366643 : Blo 1328983 3366643 := bstep (se 1 (by rfl) ⟨2524982, by rfl⟩ : syracuseStep 3366643 = 5049965) B5049965
theorem B26255177 : Blo 1328983 26255177 := bstep (se 2 (by rfl) ⟨9845691, by rfl⟩ : syracuseStep 26255177 = 19691383) B19691383
theorem B1892251 : Blo 1328983 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B2244523 : Blo 1328983 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B3195067 : Blo 1328983 3195067 := bstep (se 1 (by rfl) ⟨2396300, by rfl⟩ : syracuseStep 3195067 = 4792601) B4792601
theorem B6734015 : Blo 1328983 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B2990393 : Blo 1328983 2990393 := bstep (se 2 (by rfl) ⟨1121397, by rfl⟩ : syracuseStep 2990393 = 2242795) B2242795
theorem B2695481 : Blo 1328983 2695481 := bstep (se 2 (by rfl) ⟨1010805, by rfl⟩ : syracuseStep 2695481 = 2021611) B2021611
theorem B6390209 : Blo 1328983 6390209 := bstep (se 2 (by rfl) ⟨2396328, by rfl⟩ : syracuseStep 6390209 = 4792657) B4792657
theorem B2245151 : Blo 1328983 2245151 := bstep (se 1 (by rfl) ⟨1683863, by rfl⟩ : syracuseStep 2245151 = 3367727) B3367727
theorem B145506887 : Blo 1328983 145506887 := bstep (se 1 (by rfl) ⟨109130165, by rfl⟩ : syracuseStep 145506887 = 218260331) B218260331
theorem B2245225 : Blo 1328983 2245225 := bstep (se 2 (by rfl) ⟨841959, by rfl⟩ : syracuseStep 2245225 = 1683919) B1683919
theorem B1893071 : Blo 1328983 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B2990879 : Blo 1328983 2990879 := bstep (se 1 (by rfl) ⟨2243159, by rfl⟩ : syracuseStep 2990879 = 4486319) B4486319
theorem B4490045 : Blo 1328983 4490045 := bstep (se 3 (by rfl) ⟨841883, by rfl⟩ : syracuseStep 4490045 = 1683767) B1683767
theorem B6390809 : Blo 1328983 6390809 := bstep (se 2 (by rfl) ⟨2396553, by rfl⟩ : syracuseStep 6390809 = 4793107) B4793107
theorem B2524223 : Blo 1328983 2524223 := bstep (se 1 (by rfl) ⟨1893167, by rfl⟩ : syracuseStep 2524223 = 3786335) B3786335
theorem B3785903 : Blo 1328983 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B5047505 : Blo 1328983 5047505 := bstep (se 2 (by rfl) ⟨1892814, by rfl⟩ : syracuseStep 5047505 = 3785629) B3785629
theorem B7578845 : Blo 1328983 7578845 := bstep (se 3 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 7578845 = 2842067) B2842067
theorem B1516847 : Blo 1328983 1516847 := bstep (se 1 (by rfl) ⟨1137635, by rfl⟩ : syracuseStep 1516847 = 2275271) B2275271
theorem B4490747 : Blo 1328983 4490747 := bstep (se 1 (by rfl) ⟨3368060, by rfl⟩ : syracuseStep 4490747 = 6736121) B6736121
theorem B2991689 : Blo 1328983 2991689 := bstep (se 2 (by rfl) ⟨1121883, by rfl⟩ : syracuseStep 2991689 = 2243767) B2243767
theorem B11519597 : Blo 1328983 11519597 := bstep (se 3 (by rfl) ⟨2159924, by rfl⟩ : syracuseStep 11519597 = 4319849) B4319849
theorem B3368699 : Blo 1328983 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B1329087 : Blo 1328983 1329087 := bstep (se 1 (by rfl) ⟨996815, by rfl⟩ : syracuseStep 1329087 = 1993631) B1993631
theorem B1329119 : Blo 1328983 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B4261871 : Blo 1328983 4261871 := bstep (se 1 (by rfl) ⟨3196403, by rfl⟩ : syracuseStep 4261871 = 6392807) B6392807
theorem B2992121 : Blo 1328983 2992121 := bstep (se 2 (by rfl) ⟨1122045, by rfl⟩ : syracuseStep 2992121 = 2244091) B2244091
theorem B1329179 : Blo 1328983 1329179 := bstep (se 1 (by rfl) ⟨996884, by rfl⟩ : syracuseStep 1329179 = 1993769) B1993769
theorem B1329183 : Blo 1328983 1329183 := bstep (se 1 (by rfl) ⟨996887, by rfl⟩ : syracuseStep 1329183 = 1993775) B1993775
theorem B1329199 : Blo 1328983 1329199 := bstep (se 1 (by rfl) ⟨996899, by rfl⟩ : syracuseStep 1329199 = 1993799) B1993799
theorem B2992175 : Blo 1328983 2992175 := bstep (se 1 (by rfl) ⟨2244131, by rfl⟩ : syracuseStep 2992175 = 4488263) B4488263
theorem B2992211 : Blo 1328983 2992211 := bstep (se 1 (by rfl) ⟨2244158, by rfl⟩ : syracuseStep 2992211 = 4488317) B4488317
theorem B5048507 : Blo 1328983 5048507 := bstep (se 1 (by rfl) ⟨3786380, by rfl⟩ : syracuseStep 5048507 = 7572761) B7572761
theorem B1329375 : Blo 1328983 1329375 := bstep (se 1 (by rfl) ⟨997031, by rfl⟩ : syracuseStep 1329375 = 1994063) B1994063
theorem B2992391 : Blo 1328983 2992391 := bstep (se 1 (by rfl) ⟨2244293, by rfl⟩ : syracuseStep 2992391 = 4488587) B4488587
theorem B1329435 : Blo 1328983 1329435 := bstep (se 1 (by rfl) ⟨997076, by rfl⟩ : syracuseStep 1329435 = 1994153) B1994153
theorem B3787087 : Blo 1328983 3787087 := bstep (se 1 (by rfl) ⟨2840315, by rfl⟩ : syracuseStep 3787087 = 5680631) B5680631
theorem B1329535 : Blo 1328983 1329535 := bstep (se 1 (by rfl) ⟨997151, by rfl⟩ : syracuseStep 1329535 = 1994303) B1994303
theorem B6392191 : Blo 1328983 6392191 := bstep (se 1 (by rfl) ⟨4794143, by rfl⟩ : syracuseStep 6392191 = 9588287) B9588287
theorem B11364745 : Blo 1328983 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B3836335 : Blo 1328983 3836335 := bstep (se 1 (by rfl) ⟨2877251, by rfl⟩ : syracuseStep 3836335 = 5754503) B5754503
theorem B1329711 : Blo 1328983 1329711 := bstep (se 1 (by rfl) ⟨997283, by rfl⟩ : syracuseStep 1329711 = 1994567) B1994567
theorem B2992697 : Blo 1328983 2992697 := bstep (se 2 (by rfl) ⟨1122261, by rfl⟩ : syracuseStep 2992697 = 2244523) B2244523
theorem B48548429 : Blo 1328983 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B1329767 : Blo 1328983 1329767 := bstep (se 1 (by rfl) ⟨997325, by rfl⟩ : syracuseStep 1329767 = 1994651) B1994651
theorem B2525833 : Blo 1328983 2525833 := bstep (se 2 (by rfl) ⟨947187, by rfl⟩ : syracuseStep 2525833 = 1894375) B1894375
theorem B1820543759 : Blo 1328983 1820543759 := bstep (se 1 (by rfl) ⟨1365407819, by rfl⟩ : syracuseStep 1820543759 = 2730815639) B2730815639
theorem B7572305 : Blo 1328983 7572305 := bstep (se 2 (by rfl) ⟨2839614, by rfl⟩ : syracuseStep 7572305 = 5679229) B5679229
theorem B6736769 : Blo 1328983 6736769 := bstep (se 2 (by rfl) ⟨2526288, by rfl⟩ : syracuseStep 6736769 = 5052577) B5052577
theorem B1330143 : Blo 1328983 1330143 := bstep (se 1 (by rfl) ⟨997607, by rfl⟩ : syracuseStep 1330143 = 1995215) B1995215
theorem B1330171 : Blo 1328983 1330171 := bstep (se 1 (by rfl) ⟨997628, by rfl⟩ : syracuseStep 1330171 = 1995257) B1995257
theorem B1330239 : Blo 1328983 1330239 := bstep (se 1 (by rfl) ⟨997679, by rfl⟩ : syracuseStep 1330239 = 1995359) B1995359
theorem B5049479 : Blo 1328983 5049479 := bstep (se 1 (by rfl) ⟨3787109, by rfl⟩ : syracuseStep 5049479 = 7574219) B7574219
theorem B22736051 : Blo 1328983 22736051 := bstep (se 1 (by rfl) ⟨17052038, by rfl⟩ : syracuseStep 22736051 = 34104077) B34104077
theorem B12791033 : Blo 1328983 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B2993417 : Blo 1328983 2993417 := bstep (se 2 (by rfl) ⟨1122531, by rfl⟩ : syracuseStep 2993417 = 2245063) B2245063
theorem B21556529 : Blo 1328983 21556529 := bstep (se 2 (by rfl) ⟨8083698, by rfl⟩ : syracuseStep 21556529 = 16167397) B16167397
theorem B1994039 : Blo 1328983 1994039 := bstep (se 1 (by rfl) ⟨1495529, by rfl⟩ : syracuseStep 1994039 = 2991059) B2991059
theorem B1330559 : Blo 1328983 1330559 := bstep (se 1 (by rfl) ⟨997919, by rfl⟩ : syracuseStep 1330559 = 1995839) B1995839
theorem B1330587 : Blo 1328983 1330587 := bstep (se 1 (by rfl) ⟨997940, by rfl⟩ : syracuseStep 1330587 = 1995881) B1995881
theorem B43167127 : Blo 1328983 43167127 := bstep (se 1 (by rfl) ⟨32375345, by rfl⟩ : syracuseStep 43167127 = 64750691) B64750691
theorem B1994207 : Blo 1328983 1994207 := bstep (se 1 (by rfl) ⟨1495655, by rfl⟩ : syracuseStep 1994207 = 2991311) B2991311
theorem B1330655 : Blo 1328983 1330655 := bstep (se 1 (by rfl) ⟨997991, by rfl⟩ : syracuseStep 1330655 = 1995983) B1995983
theorem B5049935 : Blo 1328983 5049935 := bstep (se 1 (by rfl) ⟨3787451, by rfl⟩ : syracuseStep 5049935 = 7574903) B7574903
theorem B1330791 : Blo 1328983 1330791 := bstep (se 1 (by rfl) ⟨998093, by rfl⟩ : syracuseStep 1330791 = 1996187) B1996187
theorem B6737579 : Blo 1328983 6737579 := bstep (se 1 (by rfl) ⟨5053184, by rfl⟩ : syracuseStep 6737579 = 10106369) B10106369
theorem B1994423 : Blo 1328983 1994423 := bstep (se 1 (by rfl) ⟨1495817, by rfl⟩ : syracuseStep 1994423 = 2991635) B2991635
theorem B1330939 : Blo 1328983 1330939 := bstep (se 1 (by rfl) ⟨998204, by rfl⟩ : syracuseStep 1330939 = 1996409) B1996409
theorem B1421183 : Blo 1328983 1421183 := bstep (se 1 (by rfl) ⟨1065887, by rfl⟩ : syracuseStep 1421183 = 2131775) B2131775
theorem B1994633 : Blo 1328983 1994633 := bstep (se 2 (by rfl) ⟨747987, by rfl⟩ : syracuseStep 1994633 = 1495975) B1495975
theorem B3788795 : Blo 1328983 3788795 := bstep (se 1 (by rfl) ⟨2841596, by rfl⟩ : syracuseStep 3788795 = 5683193) B5683193
theorem B1994879 : Blo 1328983 1994879 := bstep (se 1 (by rfl) ⟨1496159, by rfl⟩ : syracuseStep 1994879 = 2992319) B2992319
theorem B5681279 : Blo 1328983 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B2994407 : Blo 1328983 2994407 := bstep (se 1 (by rfl) ⟨2245805, by rfl⟩ : syracuseStep 2994407 = 4491611) B4491611
theorem B5050633 : Blo 1328983 5050633 := bstep (se 2 (by rfl) ⟨1893987, by rfl⟩ : syracuseStep 5050633 = 3787975) B3787975
theorem B4485401 : Blo 1328983 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B2838881 : Blo 1328983 2838881 := bstep (se 2 (by rfl) ⟨1064580, by rfl⟩ : syracuseStep 2838881 = 2129161) B2129161
theorem B1495399 : Blo 1328983 1495399 := bstep (se 1 (by rfl) ⟨1121549, by rfl⟩ : syracuseStep 1495399 = 2243099) B2243099
theorem B2994587 : Blo 1328983 2994587 := bstep (se 1 (by rfl) ⟨2245940, by rfl⟩ : syracuseStep 2994587 = 4491881) B4491881
theorem B1995515 : Blo 1328983 1995515 := bstep (se 1 (by rfl) ⟨1496636, by rfl⟩ : syracuseStep 1995515 = 2993273) B2993273
theorem B1496047 : Blo 1328983 1496047 := bstep (se 1 (by rfl) ⟨1122035, by rfl⟩ : syracuseStep 1496047 = 2244071) B2244071
theorem B9712649 : Blo 1328983 9712649 := bstep (se 2 (by rfl) ⟨3642243, by rfl⟩ : syracuseStep 9712649 = 7284487) B7284487
theorem B5682305 : Blo 1328983 5682305 := bstep (se 2 (by rfl) ⟨2130864, by rfl⟩ : syracuseStep 5682305 = 4261729) B4261729
theorem B1995959 : Blo 1328983 1995959 := bstep (se 1 (by rfl) ⟨1496969, by rfl⟩ : syracuseStep 1995959 = 2993939) B2993939
theorem B17503451 : Blo 1328983 17503451 := bstep (se 1 (by rfl) ⟨13127588, by rfl⟩ : syracuseStep 17503451 = 26255177) B26255177
theorem B1996199 : Blo 1328983 1996199 := bstep (se 1 (by rfl) ⟨1497149, by rfl⟩ : syracuseStep 1996199 = 2994299) B2994299
theorem B49903057 : Blo 1328983 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B1496551 : Blo 1328983 1496551 := bstep (se 1 (by rfl) ⟨1122413, by rfl⟩ : syracuseStep 1496551 = 2244827) B2244827
theorem B5051879 : Blo 1328983 5051879 := bstep (se 1 (by rfl) ⟨3788909, by rfl⟩ : syracuseStep 5051879 = 7577819) B7577819
theorem B1996379 : Blo 1328983 1996379 := bstep (se 1 (by rfl) ⟨1497284, by rfl⟩ : syracuseStep 1996379 = 2994569) B2994569
theorem B4486751 : Blo 1328983 4486751 := bstep (se 1 (by rfl) ⟨3365063, by rfl⟩ : syracuseStep 4486751 = 6730127) B6730127
theorem B3241583 : Blo 1328983 3241583 := bstep (se 1 (by rfl) ⟨2431187, by rfl⟩ : syracuseStep 3241583 = 4862375) B4862375
theorem B9713267 : Blo 1328983 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B1496731 : Blo 1328983 1496731 := bstep (se 1 (by rfl) ⟨1122548, by rfl⟩ : syracuseStep 1496731 = 2245097) B2245097
theorem B3364679 : Blo 1328983 3364679 := bstep (se 1 (by rfl) ⟨2523509, by rfl⟩ : syracuseStep 3364679 = 5047019) B5047019
theorem B3364699 : Blo 1328983 3364699 := bstep (se 1 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 3364699 = 5047049) B5047049
theorem B10106855 : Blo 1328983 10106855 := bstep (se 1 (by rfl) ⟨7580141, by rfl⟩ : syracuseStep 10106855 = 15160283) B15160283
theorem B4855945 : Blo 1328983 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B10229975 : Blo 1328983 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B331897175 : Blo 1328983 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B9099631 : Blo 1328983 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B6732233 : Blo 1328983 6732233 := bstep (se 2 (by rfl) ⟨2524587, by rfl⟩ : syracuseStep 6732233 = 5049175) B5049175
theorem B57506345 : Blo 1328983 57506345 := bstep (se 2 (by rfl) ⟨21564879, by rfl⟩ : syracuseStep 57506345 = 43129759) B43129759
theorem B46701197 : Blo 1328983 46701197 := bstep (se 3 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 46701197 = 17512949) B17512949
theorem B5683945 : Blo 1328983 5683945 := bstep (se 2 (by rfl) ⟨2131479, by rfl⟩ : syracuseStep 5683945 = 4262959) B4262959
theorem B5479363 : Blo 1328983 5479363 := bstep (se 1 (by rfl) ⟨4109522, by rfl⟩ : syracuseStep 5479363 = 8219045) B8219045
theorem B16858313 : Blo 1328983 16858313 := bstep (se 2 (by rfl) ⟨6321867, by rfl⟩ : syracuseStep 16858313 = 12643735) B12643735
theorem B6733043 : Blo 1328983 6733043 := bstep (se 1 (by rfl) ⟨5049782, by rfl⟩ : syracuseStep 6733043 = 10099565) B10099565
theorem B4259243 : Blo 1328983 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B4488857 : Blo 1328983 4488857 := bstep (se 2 (by rfl) ⟨1683321, by rfl⟩ : syracuseStep 4488857 = 3366643) B3366643
theorem B7569071 : Blo 1328983 7569071 := bstep (se 1 (by rfl) ⟨5676803, by rfl⟩ : syracuseStep 7569071 = 11353607) B11353607
theorem B2244361 : Blo 1328983 2244361 := bstep (se 2 (by rfl) ⟨841635, by rfl⟩ : syracuseStep 2244361 = 1683271) B1683271
theorem B3596051 : Blo 1328983 3596051 := bstep (se 1 (by rfl) ⟨2697038, by rfl⟩ : syracuseStep 3596051 = 5394077) B5394077
theorem B2523001 : Blo 1328983 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B17047529 : Blo 1328983 17047529 := bstep (se 2 (by rfl) ⟨6392823, by rfl⟩ : syracuseStep 17047529 = 12785647) B12785647
theorem B4489343 : Blo 1328983 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B2990267 : Blo 1328983 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B1892587 : Blo 1328983 1892587 := bstep (se 1 (by rfl) ⟨1419440, by rfl⟩ : syracuseStep 1892587 = 2838881) B2838881
theorem B4260089 : Blo 1328983 4260089 := bstep (se 2 (by rfl) ⟨1597533, by rfl⟩ : syracuseStep 4260089 = 3195067) B3195067
theorem B6734177 : Blo 1328983 6734177 := bstep (se 2 (by rfl) ⟨2525316, by rfl⟩ : syracuseStep 6734177 = 5050633) B5050633
theorem B12132841 : Blo 1328983 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B4260539 : Blo 1328983 4260539 := bstep (se 1 (by rfl) ⟨3195404, by rfl⟩ : syracuseStep 4260539 = 6390809) B6390809
theorem B2523935 : Blo 1328983 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B3367777 : Blo 1328983 3367777 := bstep (se 2 (by rfl) ⟨1262916, by rfl⟩ : syracuseStep 3367777 = 2525833) B2525833
theorem B7578593 : Blo 1328983 7578593 := bstep (se 2 (by rfl) ⟨2841972, by rfl⟩ : syracuseStep 7578593 = 5683945) B5683945
theorem B3367919 : Blo 1328983 3367919 := bstep (se 1 (by rfl) ⟨2525939, by rfl⟩ : syracuseStep 3367919 = 5051879) B5051879
theorem B2991167 : Blo 1328983 2991167 := bstep (se 1 (by rfl) ⟨2243375, by rfl⟩ : syracuseStep 2991167 = 4486751) B4486751
theorem B2245799 : Blo 1328983 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B17040557 : Blo 1328983 17040557 := bstep (se 3 (by rfl) ⟨3195104, by rfl⟩ : syracuseStep 17040557 = 6390209) B6390209
theorem B1213695839 : Blo 1328983 1213695839 := bstep (se 1 (by rfl) ⟨910271879, by rfl⟩ : syracuseStep 1213695839 = 1820543759) B1820543759
theorem B5048189 : Blo 1328983 5048189 := bstep (se 3 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 5048189 = 1893071) B1893071
theorem B5048203 : Blo 1328983 5048203 := bstep (se 1 (by rfl) ⟨3786152, by rfl⟩ : syracuseStep 5048203 = 7572305) B7572305
theorem B4491179 : Blo 1328983 4491179 := bstep (se 1 (by rfl) ⟨3368384, by rfl⟩ : syracuseStep 4491179 = 6736769) B6736769
theorem B66537409 : Blo 1328983 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B15157367 : Blo 1328983 15157367 := bstep (se 1 (by rfl) ⟨11368025, by rfl⟩ : syracuseStep 15157367 = 22736051) B22736051
theorem B14371019 : Blo 1328983 14371019 := bstep (se 1 (by rfl) ⟨10778264, by rfl⟩ : syracuseStep 14371019 = 21556529) B21556529
theorem B1329359 : Blo 1328983 1329359 := bstep (se 1 (by rfl) ⟨997019, by rfl⟩ : syracuseStep 1329359 = 1994039) B1994039
theorem B1329471 : Blo 1328983 1329471 := bstep (se 1 (by rfl) ⟨997103, by rfl⟩ : syracuseStep 1329471 = 1994207) B1994207
theorem B2992481 : Blo 1328983 2992481 := bstep (se 2 (by rfl) ⟨1122180, by rfl⟩ : syracuseStep 2992481 = 2244361) B2244361
theorem B2992571 : Blo 1328983 2992571 := bstep (se 1 (by rfl) ⟨2244428, by rfl⟩ : syracuseStep 2992571 = 4488857) B4488857
theorem B4491719 : Blo 1328983 4491719 := bstep (se 1 (by rfl) ⟨3368789, by rfl⟩ : syracuseStep 4491719 = 6737579) B6737579
theorem B1329615 : Blo 1328983 1329615 := bstep (se 1 (by rfl) ⟨997211, by rfl⟩ : syracuseStep 1329615 = 1994423) B1994423
theorem B1329755 : Blo 1328983 1329755 := bstep (se 1 (by rfl) ⟨997316, by rfl⟩ : syracuseStep 1329755 = 1994633) B1994633
theorem B11365019 : Blo 1328983 11365019 := bstep (se 1 (by rfl) ⟨8523764, by rfl⟩ : syracuseStep 11365019 = 17047529) B17047529
theorem B10103453 : Blo 1328983 10103453 := bstep (se 3 (by rfl) ⟨1894397, by rfl⟩ : syracuseStep 10103453 = 3788795) B3788795
theorem B1329919 : Blo 1328983 1329919 := bstep (se 1 (by rfl) ⟨997439, by rfl⟩ : syracuseStep 1329919 = 1994879) B1994879
theorem B6474593 : Blo 1328983 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B1993595 : Blo 1328983 1993595 := bstep (se 1 (by rfl) ⟨1495196, by rfl⟩ : syracuseStep 1993595 = 2990393) B2990393
theorem B1796987 : Blo 1328983 1796987 := bstep (se 1 (by rfl) ⟨1347740, by rfl⟩ : syracuseStep 1796987 = 2695481) B2695481
theorem B15150077 : Blo 1328983 15150077 := bstep (se 3 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 15150077 = 5681279) B5681279
theorem B97004591 : Blo 1328983 97004591 := bstep (se 1 (by rfl) ⟨72753443, by rfl⟩ : syracuseStep 97004591 = 145506887) B145506887
theorem B5049449 : Blo 1328983 5049449 := bstep (se 2 (by rfl) ⟨1893543, by rfl⟩ : syracuseStep 5049449 = 3787087) B3787087
theorem B1993865 : Blo 1328983 1993865 := bstep (se 2 (by rfl) ⟨747699, by rfl⟩ : syracuseStep 1993865 = 1495399) B1495399
theorem B8522921 : Blo 1328983 8522921 := bstep (se 2 (by rfl) ⟨3196095, by rfl⟩ : syracuseStep 8522921 = 6392191) B6392191
theorem B1330343 : Blo 1328983 1330343 := bstep (se 1 (by rfl) ⟨997757, by rfl⟩ : syracuseStep 1330343 = 1995515) B1995515
theorem B1993919 : Blo 1328983 1993919 := bstep (se 1 (by rfl) ⟨1495439, by rfl⟩ : syracuseStep 1993919 = 2990879) B2990879
theorem B2993363 : Blo 1328983 2993363 := bstep (se 1 (by rfl) ⟨2245022, by rfl⟩ : syracuseStep 2993363 = 4490045) B4490045
theorem B5115113 : Blo 1328983 5115113 := bstep (se 2 (by rfl) ⟨1918167, by rfl⟩ : syracuseStep 5115113 = 3836335) B3836335
theorem B6475099 : Blo 1328983 6475099 := bstep (se 1 (by rfl) ⟨4856324, by rfl⟩ : syracuseStep 6475099 = 9712649) B9712649
theorem B3788203 : Blo 1328983 3788203 := bstep (se 1 (by rfl) ⟨2841152, by rfl⟩ : syracuseStep 3788203 = 5682305) B5682305
theorem B1330639 : Blo 1328983 1330639 := bstep (se 1 (by rfl) ⟨997979, by rfl⟩ : syracuseStep 1330639 = 1995959) B1995959
theorem B2993633 : Blo 1328983 2993633 := bstep (se 2 (by rfl) ⟨1122612, by rfl⟩ : syracuseStep 2993633 = 2245225) B2245225
theorem B11668967 : Blo 1328983 11668967 := bstep (se 1 (by rfl) ⟨8751725, by rfl⟩ : syracuseStep 11668967 = 17503451) B17503451
theorem B1330799 : Blo 1328983 1330799 := bstep (se 1 (by rfl) ⟨998099, by rfl⟩ : syracuseStep 1330799 = 1996199) B1996199
theorem B2993831 : Blo 1328983 2993831 := bstep (se 1 (by rfl) ⟨2245373, by rfl⟩ : syracuseStep 2993831 = 4490747) B4490747
theorem B1994459 : Blo 1328983 1994459 := bstep (se 1 (by rfl) ⟨1495844, by rfl⟩ : syracuseStep 1994459 = 2991689) B2991689
theorem B1330919 : Blo 1328983 1330919 := bstep (se 1 (by rfl) ⟨998189, by rfl⟩ : syracuseStep 1330919 = 1996379) B1996379
theorem B7679731 : Blo 1328983 7679731 := bstep (se 1 (by rfl) ⟨5759798, by rfl⟩ : syracuseStep 7679731 = 11519597) B11519597
theorem B6475511 : Blo 1328983 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B11357981 : Blo 1328983 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B1994729 : Blo 1328983 1994729 := bstep (se 2 (by rfl) ⟨748023, by rfl⟩ : syracuseStep 1994729 = 1496047) B1496047
theorem B6737903 : Blo 1328983 6737903 := bstep (se 1 (by rfl) ⟨5053427, by rfl⟩ : syracuseStep 6737903 = 10106855) B10106855
theorem B1994747 : Blo 1328983 1994747 := bstep (se 1 (by rfl) ⟨1496060, by rfl⟩ : syracuseStep 1994747 = 2992121) B2992121
theorem B1994783 : Blo 1328983 1994783 := bstep (se 1 (by rfl) ⟨1496087, by rfl⟩ : syracuseStep 1994783 = 2992175) B2992175
theorem B1994807 : Blo 1328983 1994807 := bstep (se 1 (by rfl) ⟨1496105, by rfl⟩ : syracuseStep 1994807 = 2992211) B2992211
theorem B6819983 : Blo 1328983 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B1994927 : Blo 1328983 1994927 := bstep (se 1 (by rfl) ⟨1496195, by rfl⟩ : syracuseStep 1994927 = 2992391) B2992391
theorem B1995131 : Blo 1328983 1995131 := bstep (se 1 (by rfl) ⟨1496348, by rfl⟩ : syracuseStep 1995131 = 2992697) B2992697
theorem B31134131 : Blo 1328983 31134131 := bstep (se 1 (by rfl) ⟨23350598, by rfl⟩ : syracuseStep 31134131 = 46701197) B46701197
theorem B1995401 : Blo 1328983 1995401 := bstep (se 2 (by rfl) ⟨748275, by rfl⟩ : syracuseStep 1995401 = 1496551) B1496551
theorem B1995611 : Blo 1328983 1995611 := bstep (se 1 (by rfl) ⟨1496708, by rfl⟩ : syracuseStep 1995611 = 2993417) B2993417
theorem B1995641 : Blo 1328983 1995641 := bstep (se 2 (by rfl) ⟨748365, by rfl⟩ : syracuseStep 1995641 = 1496731) B1496731
theorem B3789821 : Blo 1328983 3789821 := bstep (se 3 (by rfl) ⟨710591, by rfl⟩ : syracuseStep 3789821 = 1421183) B1421183
theorem B4486265 : Blo 1328983 4486265 := bstep (se 2 (by rfl) ⟨1682349, by rfl⟩ : syracuseStep 4486265 = 3364699) B3364699
theorem B3364001 : Blo 1328983 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B2397367 : Blo 1328983 2397367 := bstep (se 1 (by rfl) ⟨1798025, by rfl⟩ : syracuseStep 2397367 = 3596051) B3596051
theorem B1996271 : Blo 1328983 1996271 := bstep (se 1 (by rfl) ⟨1497203, by rfl⟩ : syracuseStep 1996271 = 2994407) B2994407
theorem B6731261 : Blo 1328983 6731261 := bstep (se 3 (by rfl) ⟨1262111, by rfl⟩ : syracuseStep 6731261 = 2524223) B2524223
theorem B1996391 : Blo 1328983 1996391 := bstep (se 1 (by rfl) ⟨1497293, by rfl⟩ : syracuseStep 1996391 = 2994587) B2994587
theorem B1496767 : Blo 1328983 1496767 := bstep (se 1 (by rfl) ⟨1122575, by rfl⟩ : syracuseStep 1496767 = 2245151) B2245151
theorem B15152993 : Blo 1328983 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B4044925 : Blo 1328983 4044925 := bstep (se 3 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 4044925 = 1516847) B1516847
theorem B3365003 : Blo 1328983 3365003 := bstep (se 1 (by rfl) ⟨2523752, by rfl⟩ : syracuseStep 3365003 = 5047505) B5047505
theorem B5052563 : Blo 1328983 5052563 := bstep (se 1 (by rfl) ⟨3789422, by rfl⟩ : syracuseStep 5052563 = 7578845) B7578845
theorem B2161055 : Blo 1328983 2161055 := bstep (se 1 (by rfl) ⟨1620791, by rfl⟩ : syracuseStep 2161055 = 3241583) B3241583
theorem B2243119 : Blo 1328983 2243119 := bstep (se 1 (by rfl) ⟨1682339, by rfl⟩ : syracuseStep 2243119 = 3364679) B3364679
theorem B7305817 : Blo 1328983 7305817 := bstep (se 2 (by rfl) ⟨2739681, by rfl⟩ : syracuseStep 7305817 = 5479363) B5479363
theorem B2841247 : Blo 1328983 2841247 := bstep (se 1 (by rfl) ⟨2130935, by rfl⟩ : syracuseStep 2841247 = 4261871) B4261871
theorem B3365671 : Blo 1328983 3365671 := bstep (se 1 (by rfl) ⟨2524253, by rfl⟩ : syracuseStep 3365671 = 5048507) B5048507
theorem B221264783 : Blo 1328983 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B4488155 : Blo 1328983 4488155 := bstep (se 1 (by rfl) ⟨3366116, by rfl⟩ : syracuseStep 4488155 = 6732233) B6732233
theorem B38337563 : Blo 1328983 38337563 := bstep (se 1 (by rfl) ⟨28753172, by rfl⟩ : syracuseStep 38337563 = 57506345) B57506345
theorem B32365619 : Blo 1328983 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B57556169 : Blo 1328983 57556169 := bstep (se 2 (by rfl) ⟨21583563, by rfl⟩ : syracuseStep 57556169 = 43167127) B43167127
theorem B3366319 : Blo 1328983 3366319 := bstep (se 1 (by rfl) ⟨2524739, by rfl⟩ : syracuseStep 3366319 = 5049479) B5049479
theorem B11238875 : Blo 1328983 11238875 := bstep (se 1 (by rfl) ⟨8429156, by rfl⟩ : syracuseStep 11238875 = 16858313) B16858313
theorem B4488695 : Blo 1328983 4488695 := bstep (se 1 (by rfl) ⟨3366521, by rfl⟩ : syracuseStep 4488695 = 6733043) B6733043
theorem B8527355 : Blo 1328983 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B3366623 : Blo 1328983 3366623 := bstep (se 1 (by rfl) ⟨2524967, by rfl⟩ : syracuseStep 3366623 = 5049935) B5049935
theorem B5046047 : Blo 1328983 5046047 := bstep (se 1 (by rfl) ⟨3784535, by rfl⟩ : syracuseStep 5046047 = 7569071) B7569071
theorem B4546655 : Blo 1328983 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B4489451 : Blo 1328983 4489451 := bstep (se 1 (by rfl) ⟨3367088, by rfl⟩ : syracuseStep 4489451 = 6734177) B6734177
theorem B2523449 : Blo 1328983 2523449 := bstep (se 2 (by rfl) ⟨946293, by rfl⟩ : syracuseStep 2523449 = 1892587) B1892587
theorem B2245279 : Blo 1328983 2245279 := bstep (se 1 (by rfl) ⟨1683959, by rfl⟩ : syracuseStep 2245279 = 3367919) B3367919
theorem B2990825 : Blo 1328983 2990825 := bstep (se 2 (by rfl) ⟨1121559, by rfl⟩ : syracuseStep 2990825 = 2243119) B2243119
theorem B2990843 : Blo 1328983 2990843 := bstep (se 1 (by rfl) ⟨2243132, by rfl⟩ : syracuseStep 2990843 = 4486265) B4486265
theorem B9741089 : Blo 1328983 9741089 := bstep (se 2 (by rfl) ⟨3652908, by rfl⟩ : syracuseStep 9741089 = 7305817) B7305817
theorem B4490369 : Blo 1328983 4490369 := bstep (se 2 (by rfl) ⟨1683888, by rfl⟩ : syracuseStep 4490369 = 3367777) B3367777
theorem B10101995 : Blo 1328983 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B3368375 : Blo 1328983 3368375 := bstep (se 1 (by rfl) ⟨2526281, by rfl⟩ : syracuseStep 3368375 = 5052563) B5052563
theorem B3196489 : Blo 1328983 3196489 := bstep (se 2 (by rfl) ⟨1198683, by rfl⟩ : syracuseStep 3196489 = 2397367) B2397367
theorem B6735635 : Blo 1328983 6735635 := bstep (se 1 (by rfl) ⟨5051726, by rfl⟩ : syracuseStep 6735635 = 10103453) B10103453
theorem B1329063 : Blo 1328983 1329063 := bstep (se 1 (by rfl) ⟨996797, by rfl⟩ : syracuseStep 1329063 = 1993595) B1993595
theorem B2992103 : Blo 1328983 2992103 := bstep (se 1 (by rfl) ⟨2244077, by rfl⟩ : syracuseStep 2992103 = 4488155) B4488155
theorem B64669727 : Blo 1328983 64669727 := bstep (se 1 (by rfl) ⟨48502295, by rfl⟩ : syracuseStep 64669727 = 97004591) B97004591
theorem B1329243 : Blo 1328983 1329243 := bstep (se 1 (by rfl) ⟨996932, by rfl⟩ : syracuseStep 1329243 = 1993865) B1993865
theorem B1329279 : Blo 1328983 1329279 := bstep (se 1 (by rfl) ⟨996959, by rfl⟩ : syracuseStep 1329279 = 1993919) B1993919
theorem B3410075 : Blo 1328983 3410075 := bstep (se 1 (by rfl) ⟨2557556, by rfl⟩ : syracuseStep 3410075 = 5115113) B5115113
theorem B2992463 : Blo 1328983 2992463 := bstep (se 1 (by rfl) ⟨2244347, by rfl⟩ : syracuseStep 2992463 = 4488695) B4488695
theorem B1329639 : Blo 1328983 1329639 := bstep (se 1 (by rfl) ⟨997229, by rfl⟩ : syracuseStep 1329639 = 1994459) B1994459
theorem B7571987 : Blo 1328983 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B1329819 : Blo 1328983 1329819 := bstep (se 1 (by rfl) ⟨997364, by rfl⟩ : syracuseStep 1329819 = 1994729) B1994729
theorem B4491935 : Blo 1328983 4491935 := bstep (se 1 (by rfl) ⟨3368951, by rfl⟩ : syracuseStep 4491935 = 6737903) B6737903
theorem B1329831 : Blo 1328983 1329831 := bstep (se 1 (by rfl) ⟨997373, by rfl⟩ : syracuseStep 1329831 = 1994747) B1994747
theorem B1329855 : Blo 1328983 1329855 := bstep (se 1 (by rfl) ⟨997391, by rfl⟩ : syracuseStep 1329855 = 1994783) B1994783
theorem B1329871 : Blo 1328983 1329871 := bstep (se 1 (by rfl) ⟨997403, by rfl⟩ : syracuseStep 1329871 = 1994807) B1994807
theorem B2992895 : Blo 1328983 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B1329951 : Blo 1328983 1329951 := bstep (se 1 (by rfl) ⟨997463, by rfl⟩ : syracuseStep 1329951 = 1994927) B1994927
theorem B1993511 : Blo 1328983 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B5393233 : Blo 1328983 5393233 := bstep (se 2 (by rfl) ⟨2022462, by rfl⟩ : syracuseStep 5393233 = 4044925) B4044925
theorem B1330087 : Blo 1328983 1330087 := bstep (se 1 (by rfl) ⟨997565, by rfl⟩ : syracuseStep 1330087 = 1995131) B1995131
theorem B1330267 : Blo 1328983 1330267 := bstep (se 1 (by rfl) ⟨997700, by rfl⟩ : syracuseStep 1330267 = 1995401) B1995401
theorem B1682623 : Blo 1328983 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B1330407 : Blo 1328983 1330407 := bstep (se 1 (by rfl) ⟨997805, by rfl⟩ : syracuseStep 1330407 = 1995611) B1995611
theorem B1330427 : Blo 1328983 1330427 := bstep (se 1 (by rfl) ⟨997820, by rfl⟩ : syracuseStep 1330427 = 1995641) B1995641
theorem B2526547 : Blo 1328983 2526547 := bstep (se 1 (by rfl) ⟨1894910, by rfl⟩ : syracuseStep 2526547 = 3789821) B3789821
theorem B1994111 : Blo 1328983 1994111 := bstep (se 1 (by rfl) ⟨1495583, by rfl⟩ : syracuseStep 1994111 = 2991167) B2991167
theorem B3788329 : Blo 1328983 3788329 := bstep (se 2 (by rfl) ⟨1420623, by rfl⟩ : syracuseStep 3788329 = 2841247) B2841247
theorem B1330847 : Blo 1328983 1330847 := bstep (se 1 (by rfl) ⟨998135, by rfl⟩ : syracuseStep 1330847 = 1996271) B1996271
theorem B1330927 : Blo 1328983 1330927 := bstep (se 1 (by rfl) ⟨998195, by rfl⟩ : syracuseStep 1330927 = 1996391) B1996391
theorem B2994119 : Blo 1328983 2994119 := bstep (se 1 (by rfl) ⟨2245589, by rfl⟩ : syracuseStep 2994119 = 4491179) B4491179
theorem B92205013 : Blo 1328983 92205013 := bstep (se 7 (by rfl) ⟨1080527, by rfl⟩ : syracuseStep 92205013 = 2161055) B2161055
theorem B10104911 : Blo 1328983 10104911 := bstep (se 1 (by rfl) ⟨7578683, by rfl⟩ : syracuseStep 10104911 = 15157367) B15157367
theorem B9580679 : Blo 1328983 9580679 := bstep (se 1 (by rfl) ⟨7185509, by rfl⟩ : syracuseStep 9580679 = 14371019) B14371019
theorem B1994987 : Blo 1328983 1994987 := bstep (se 1 (by rfl) ⟨1496240, by rfl⟩ : syracuseStep 1994987 = 2992481) B2992481
theorem B1995047 : Blo 1328983 1995047 := bstep (se 1 (by rfl) ⟨1496285, by rfl⟩ : syracuseStep 1995047 = 2992571) B2992571
theorem B2994479 : Blo 1328983 2994479 := bstep (se 1 (by rfl) ⟨2245859, by rfl⟩ : syracuseStep 2994479 = 4491719) B4491719
theorem B5050937 : Blo 1328983 5050937 := bstep (se 2 (by rfl) ⟨1894101, by rfl⟩ : syracuseStep 5050937 = 3788203) B3788203
theorem B147509855 : Blo 1328983 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B5681947 : Blo 1328983 5681947 := bstep (se 1 (by rfl) ⟨4261460, by rfl⟩ : syracuseStep 5681947 = 8522921) B8522921
theorem B1995575 : Blo 1328983 1995575 := bstep (se 1 (by rfl) ⟨1496681, by rfl⟩ : syracuseStep 1995575 = 2993363) B2993363
theorem B1995689 : Blo 1328983 1995689 := bstep (se 2 (by rfl) ⟨748383, by rfl⟩ : syracuseStep 1995689 = 1496767) B1496767
theorem B17265581 : Blo 1328983 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B7492583 : Blo 1328983 7492583 := bstep (se 1 (by rfl) ⟨5619437, by rfl⟩ : syracuseStep 7492583 = 11238875) B11238875
theorem B1995755 : Blo 1328983 1995755 := bstep (se 1 (by rfl) ⟨1496816, by rfl⟩ : syracuseStep 1995755 = 2993633) B2993633
theorem B7779311 : Blo 1328983 7779311 := bstep (se 1 (by rfl) ⟨5834483, by rfl⟩ : syracuseStep 7779311 = 11668967) B11668967
theorem B1995887 : Blo 1328983 1995887 := bstep (se 1 (by rfl) ⟨1496915, by rfl⟩ : syracuseStep 1995887 = 2993831) B2993831
theorem B6730937 : Blo 1328983 6730937 := bstep (se 2 (by rfl) ⟨2524101, by rfl⟩ : syracuseStep 6730937 = 5048203) B5048203
theorem B3364031 : Blo 1328983 3364031 := bstep (se 1 (by rfl) ⟨2523023, by rfl⟩ : syracuseStep 3364031 = 5046047) B5046047
theorem B88716545 : Blo 1328983 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B2840059 : Blo 1328983 2840059 := bstep (se 1 (by rfl) ⟨2130044, by rfl⟩ : syracuseStep 2840059 = 4260089) B4260089
theorem B20756087 : Blo 1328983 20756087 := bstep (se 1 (by rfl) ⟨15567065, by rfl⟩ : syracuseStep 20756087 = 31134131) B31134131
theorem B2840359 : Blo 1328983 2840359 := bstep (se 1 (by rfl) ⟨2130269, by rfl⟩ : syracuseStep 2840359 = 4260539) B4260539
theorem B16177121 : Blo 1328983 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B5052395 : Blo 1328983 5052395 := bstep (se 1 (by rfl) ⟨3789296, by rfl⟩ : syracuseStep 5052395 = 7578593) B7578593
theorem B2242667 : Blo 1328983 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B1497199 : Blo 1328983 1497199 := bstep (se 1 (by rfl) ⟨1122899, by rfl⟩ : syracuseStep 1497199 = 2245799) B2245799
theorem B11360371 : Blo 1328983 11360371 := bstep (se 1 (by rfl) ⟨8520278, by rfl⟩ : syracuseStep 11360371 = 17040557) B17040557
theorem B4487507 : Blo 1328983 4487507 := bstep (se 1 (by rfl) ⟨3365630, by rfl⟩ : syracuseStep 4487507 = 6731261) B6731261
theorem B4487561 : Blo 1328983 4487561 := bstep (se 2 (by rfl) ⟨1682835, by rfl⟩ : syracuseStep 4487561 = 3365671) B3365671
theorem B809130559 : Blo 1328983 809130559 := bstep (se 1 (by rfl) ⟨606847919, by rfl⟩ : syracuseStep 809130559 = 1213695839) B1213695839
theorem B3365459 : Blo 1328983 3365459 := bstep (se 1 (by rfl) ⟨2524094, by rfl⟩ : syracuseStep 3365459 = 5048189) B5048189
theorem B2243335 : Blo 1328983 2243335 := bstep (se 1 (by rfl) ⟨1682501, by rfl⟩ : syracuseStep 2243335 = 3365003) B3365003
theorem B7576679 : Blo 1328983 7576679 := bstep (se 1 (by rfl) ⟨5682509, by rfl⟩ : syracuseStep 7576679 = 11365019) B11365019
theorem B8633465 : Blo 1328983 8633465 := bstep (se 2 (by rfl) ⟨3237549, by rfl⟩ : syracuseStep 8633465 = 6475099) B6475099
theorem B4488425 : Blo 1328983 4488425 := bstep (se 2 (by rfl) ⟨1683159, by rfl⟩ : syracuseStep 4488425 = 3366319) B3366319
theorem B17268029 : Blo 1328983 17268029 := bstep (se 3 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 17268029 = 6475511) B6475511
theorem B10100051 : Blo 1328983 10100051 := bstep (se 1 (by rfl) ⟨7575038, by rfl⟩ : syracuseStep 10100051 = 15150077) B15150077
theorem B25558375 : Blo 1328983 25558375 := bstep (se 1 (by rfl) ⟨19168781, by rfl⟩ : syracuseStep 25558375 = 38337563) B38337563
theorem B21577079 : Blo 1328983 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B3366299 : Blo 1328983 3366299 := bstep (se 1 (by rfl) ⟨2524724, by rfl⟩ : syracuseStep 3366299 = 5049449) B5049449
theorem B38370779 : Blo 1328983 38370779 := bstep (se 1 (by rfl) ⟨28778084, by rfl⟩ : syracuseStep 38370779 = 57556169) B57556169
theorem B10239641 : Blo 1328983 10239641 := bstep (se 2 (by rfl) ⟨3839865, by rfl⟩ : syracuseStep 10239641 = 7679731) B7679731
theorem B4791965 : Blo 1328983 4791965 := bstep (se 3 (by rfl) ⟨898493, by rfl⟩ : syracuseStep 4791965 = 1796987) B1796987
theorem B5684903 : Blo 1328983 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B2244415 : Blo 1328983 2244415 := bstep (se 1 (by rfl) ⟨1683311, by rfl⟩ : syracuseStep 2244415 = 3366623) B3366623
theorem B3031103 : Blo 1328983 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B15147161 : Blo 1328983 15147161 := bstep (se 2 (by rfl) ⟨5680185, by rfl⟩ : syracuseStep 15147161 = 11360371) B11360371
theorem B3367291 : Blo 1328983 3367291 := bstep (se 1 (by rfl) ⟨2525468, by rfl⟩ : syracuseStep 3367291 = 5050937) B5050937
theorem B11510387 : Blo 1328983 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B5186207 : Blo 1328983 5186207 := bstep (se 1 (by rfl) ⟨3889655, by rfl⟩ : syracuseStep 5186207 = 7779311) B7779311
theorem B6734663 : Blo 1328983 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B2245583 : Blo 1328983 2245583 := bstep (se 1 (by rfl) ⟨1684187, by rfl⟩ : syracuseStep 2245583 = 3368375) B3368375
theorem B2991113 : Blo 1328983 2991113 := bstep (se 2 (by rfl) ⟨1121667, by rfl⟩ : syracuseStep 2991113 = 2243335) B2243335
theorem B13837391 : Blo 1328983 13837391 := bstep (se 1 (by rfl) ⟨10378043, by rfl⟩ : syracuseStep 13837391 = 20756087) B20756087
theorem B4490423 : Blo 1328983 4490423 := bstep (se 1 (by rfl) ⟨3367817, by rfl⟩ : syracuseStep 4490423 = 6735635) B6735635
theorem B3368263 : Blo 1328983 3368263 := bstep (se 1 (by rfl) ⟨2526197, by rfl⟩ : syracuseStep 3368263 = 5052395) B5052395
theorem B2991671 : Blo 1328983 2991671 := bstep (se 1 (by rfl) ⟨2243753, by rfl⟩ : syracuseStep 2991671 = 4487507) B4487507
theorem B2991707 : Blo 1328983 2991707 := bstep (se 1 (by rfl) ⟨2243780, by rfl⟩ : syracuseStep 2991707 = 4487561) B4487561
theorem B5047991 : Blo 1328983 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B3368729 : Blo 1328983 3368729 := bstep (se 2 (by rfl) ⟨1263273, by rfl⟩ : syracuseStep 3368729 = 2526547) B2526547
theorem B1329007 : Blo 1328983 1329007 := bstep (se 1 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 1329007 = 1993511) B1993511
theorem B3786745 : Blo 1328983 3786745 := bstep (se 2 (by rfl) ⟨1420029, by rfl⟩ : syracuseStep 3786745 = 2840059) B2840059
theorem B4261985 : Blo 1328983 4261985 := bstep (se 2 (by rfl) ⟨1598244, by rfl⟩ : syracuseStep 4261985 = 3196489) B3196489
theorem B2992283 : Blo 1328983 2992283 := bstep (se 1 (by rfl) ⟨2244212, by rfl⟩ : syracuseStep 2992283 = 4488425) B4488425
theorem B11512019 : Blo 1328983 11512019 := bstep (se 1 (by rfl) ⟨8634014, by rfl⟩ : syracuseStep 11512019 = 17268029) B17268029
theorem B1329407 : Blo 1328983 1329407 := bstep (se 1 (by rfl) ⟨997055, by rfl⟩ : syracuseStep 1329407 = 1994111) B1994111
theorem B3787145 : Blo 1328983 3787145 := bstep (se 2 (by rfl) ⟨1420179, by rfl⟩ : syracuseStep 3787145 = 2840359) B2840359
theorem B2992553 : Blo 1328983 2992553 := bstep (se 2 (by rfl) ⟨1122207, by rfl⟩ : syracuseStep 2992553 = 2244415) B2244415
theorem B6826427 : Blo 1328983 6826427 := bstep (se 1 (by rfl) ⟨5119820, by rfl⟩ : syracuseStep 6826427 = 10239641) B10239641
theorem B122940017 : Blo 1328983 122940017 := bstep (se 2 (by rfl) ⟨46102506, by rfl⟩ : syracuseStep 122940017 = 92205013) B92205013
theorem B6736607 : Blo 1328983 6736607 := bstep (se 1 (by rfl) ⟨5052455, by rfl⟩ : syracuseStep 6736607 = 10104911) B10104911
theorem B1329991 : Blo 1328983 1329991 := bstep (se 1 (by rfl) ⟨997493, by rfl⟩ : syracuseStep 1329991 = 1994987) B1994987
theorem B2992967 : Blo 1328983 2992967 := bstep (se 1 (by rfl) ⟨2244725, by rfl⟩ : syracuseStep 2992967 = 4489451) B4489451
theorem B1330031 : Blo 1328983 1330031 := bstep (se 1 (by rfl) ⟨997523, by rfl⟩ : syracuseStep 1330031 = 1995047) B1995047
theorem B1682299 : Blo 1328983 1682299 := bstep (se 1 (by rfl) ⟨1261724, by rfl⟩ : syracuseStep 1682299 = 2523449) B2523449
theorem B98339903 : Blo 1328983 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B1993883 : Blo 1328983 1993883 := bstep (se 1 (by rfl) ⟨1495412, by rfl⟩ : syracuseStep 1993883 = 2990825) B2990825
theorem B1993895 : Blo 1328983 1993895 := bstep (se 1 (by rfl) ⟨1495421, by rfl⟩ : syracuseStep 1993895 = 2990843) B2990843
theorem B1330383 : Blo 1328983 1330383 := bstep (se 1 (by rfl) ⟨997787, by rfl⟩ : syracuseStep 1330383 = 1995575) B1995575
theorem B1330459 : Blo 1328983 1330459 := bstep (se 1 (by rfl) ⟨997844, by rfl⟩ : syracuseStep 1330459 = 1995689) B1995689
theorem B1330503 : Blo 1328983 1330503 := bstep (se 1 (by rfl) ⟨997877, by rfl⟩ : syracuseStep 1330503 = 1995755) B1995755
theorem B1330591 : Blo 1328983 1330591 := bstep (se 1 (by rfl) ⟨997943, by rfl⟩ : syracuseStep 1330591 = 1995887) B1995887
theorem B1078840745 : Blo 1328983 1078840745 := bstep (se 2 (by rfl) ⟨404565279, by rfl⟩ : syracuseStep 1078840745 = 809130559) B809130559
theorem B2993579 : Blo 1328983 2993579 := bstep (se 1 (by rfl) ⟨2245184, by rfl⟩ : syracuseStep 2993579 = 4490369) B4490369
theorem B2993705 : Blo 1328983 2993705 := bstep (se 2 (by rfl) ⟨1122639, by rfl⟩ : syracuseStep 2993705 = 2245279) B2245279
theorem B10784747 : Blo 1328983 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B1994735 : Blo 1328983 1994735 := bstep (se 1 (by rfl) ⟨1496051, by rfl⟩ : syracuseStep 1994735 = 2992103) B2992103
theorem B1495111 : Blo 1328983 1495111 := bstep (se 1 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 1495111 = 2242667) B2242667
theorem B2273383 : Blo 1328983 2273383 := bstep (se 1 (by rfl) ⟨1705037, by rfl⟩ : syracuseStep 2273383 = 3410075) B3410075
theorem B1994975 : Blo 1328983 1994975 := bstep (se 1 (by rfl) ⟨1496231, by rfl⟩ : syracuseStep 1994975 = 2992463) B2992463
theorem B2994623 : Blo 1328983 2994623 := bstep (se 1 (by rfl) ⟨2245967, by rfl⟩ : syracuseStep 2994623 = 4491935) B4491935
theorem B1995263 : Blo 1328983 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B5051105 : Blo 1328983 5051105 := bstep (se 2 (by rfl) ⟨1894164, by rfl⟩ : syracuseStep 5051105 = 3788329) B3788329
theorem B5051119 : Blo 1328983 5051119 := bstep (se 1 (by rfl) ⟨3788339, by rfl⟩ : syracuseStep 5051119 = 7576679) B7576679
theorem B5755643 : Blo 1328983 5755643 := bstep (se 1 (by rfl) ⟨4316732, by rfl⟩ : syracuseStep 5755643 = 8633465) B8633465
theorem B25580519 : Blo 1328983 25580519 := bstep (se 1 (by rfl) ⟨19185389, by rfl⟩ : syracuseStep 25580519 = 38370779) B38370779
theorem B3789935 : Blo 1328983 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B1996079 : Blo 1328983 1996079 := bstep (se 1 (by rfl) ⟨1497059, by rfl⟩ : syracuseStep 1996079 = 2994119) B2994119
theorem B6387119 : Blo 1328983 6387119 := bstep (se 1 (by rfl) ⟨4790339, by rfl⟩ : syracuseStep 6387119 = 9580679) B9580679
theorem B1996265 : Blo 1328983 1996265 := bstep (se 2 (by rfl) ⟨748599, by rfl⟩ : syracuseStep 1996265 = 1497199) B1497199
theorem B1996319 : Blo 1328983 1996319 := bstep (se 1 (by rfl) ⟨1497239, by rfl⟩ : syracuseStep 1996319 = 2994479) B2994479
theorem B6494059 : Blo 1328983 6494059 := bstep (se 1 (by rfl) ⟨4870544, by rfl⟩ : syracuseStep 6494059 = 9741089) B9741089
theorem B4995055 : Blo 1328983 4995055 := bstep (se 1 (by rfl) ⟨3746291, by rfl⟩ : syracuseStep 4995055 = 7492583) B7492583
theorem B4487291 : Blo 1328983 4487291 := bstep (se 1 (by rfl) ⟨3365468, by rfl⟩ : syracuseStep 4487291 = 6730937) B6730937
theorem B2242687 : Blo 1328983 2242687 := bstep (se 1 (by rfl) ⟨1682015, by rfl⟩ : syracuseStep 2242687 = 3364031) B3364031
theorem B59144363 : Blo 1328983 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B7575929 : Blo 1328983 7575929 := bstep (se 2 (by rfl) ⟨2840973, by rfl⟩ : syracuseStep 7575929 = 5681947) B5681947
theorem B7190977 : Blo 1328983 7190977 := bstep (se 2 (by rfl) ⟨2696616, by rfl⟩ : syracuseStep 7190977 = 5393233) B5393233
theorem B43113151 : Blo 1328983 43113151 := bstep (se 1 (by rfl) ⟨32334863, by rfl⟩ : syracuseStep 43113151 = 64669727) B64669727
theorem B2243497 : Blo 1328983 2243497 := bstep (se 2 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 2243497 = 1682623) B1682623
theorem B2243639 : Blo 1328983 2243639 := bstep (se 1 (by rfl) ⟨1682729, by rfl⟩ : syracuseStep 2243639 = 3365459) B3365459
theorem B12778573 : Blo 1328983 12778573 := bstep (se 3 (by rfl) ⟨2395982, by rfl⟩ : syracuseStep 12778573 = 4791965) B4791965
theorem B34077833 : Blo 1328983 34077833 := bstep (se 2 (by rfl) ⟨12779187, by rfl⟩ : syracuseStep 34077833 = 25558375) B25558375
theorem B6733367 : Blo 1328983 6733367 := bstep (se 1 (by rfl) ⟨5050025, by rfl⟩ : syracuseStep 6733367 = 10100051) B10100051
theorem B14384719 : Blo 1328983 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B2244199 : Blo 1328983 2244199 := bstep (se 1 (by rfl) ⟨1683149, by rfl⟩ : syracuseStep 2244199 = 3366299) B3366299
theorem B3031177 : Blo 1328983 3031177 := bstep (se 2 (by rfl) ⟨1136691, by rfl⟩ : syracuseStep 3031177 = 2273383) B2273383
theorem B2990249 : Blo 1328983 2990249 := bstep (se 2 (by rfl) ⟨1121343, by rfl⟩ : syracuseStep 2990249 = 2242687) B2242687
theorem B3367403 : Blo 1328983 3367403 := bstep (se 1 (by rfl) ⟨2525552, by rfl⟩ : syracuseStep 3367403 = 5051105) B5051105
theorem B4489721 : Blo 1328983 4489721 := bstep (se 2 (by rfl) ⟨1683645, by rfl⟩ : syracuseStep 4489721 = 3367291) B3367291
theorem B4489775 : Blo 1328983 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B9224927 : Blo 1328983 9224927 := bstep (se 1 (by rfl) ⟨6918695, by rfl⟩ : syracuseStep 9224927 = 13837391) B13837391
theorem B57484201 : Blo 1328983 57484201 := bstep (se 2 (by rfl) ⟨21556575, by rfl⟩ : syracuseStep 57484201 = 43113151) B43113151
theorem B6734825 : Blo 1328983 6734825 := bstep (se 2 (by rfl) ⟨2525559, by rfl⟩ : syracuseStep 6734825 = 5051119) B5051119
theorem B2245819 : Blo 1328983 2245819 := bstep (se 1 (by rfl) ⟨1684364, by rfl⟩ : syracuseStep 2245819 = 3368729) B3368729
theorem B2991329 : Blo 1328983 2991329 := bstep (se 2 (by rfl) ⟨1121748, by rfl⟩ : syracuseStep 2991329 = 2243497) B2243497
theorem B2991527 : Blo 1328983 2991527 := bstep (se 1 (by rfl) ⟨2243645, by rfl⟩ : syracuseStep 2991527 = 4487291) B4487291
theorem B39429575 : Blo 1328983 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B2524763 : Blo 1328983 2524763 := bstep (se 1 (by rfl) ⟨1893572, by rfl⟩ : syracuseStep 2524763 = 3787145) B3787145
theorem B13829885 : Blo 1328983 13829885 := bstep (se 3 (by rfl) ⟨2593103, by rfl⟩ : syracuseStep 13829885 = 5186207) B5186207
theorem B4491017 : Blo 1328983 4491017 := bstep (se 2 (by rfl) ⟨1684131, by rfl⟩ : syracuseStep 4491017 = 3368263) B3368263
theorem B4491071 : Blo 1328983 4491071 := bstep (se 1 (by rfl) ⟨3368303, by rfl⟩ : syracuseStep 4491071 = 6736607) B6736607
theorem B22718555 : Blo 1328983 22718555 := bstep (se 1 (by rfl) ⟨17038916, by rfl⟩ : syracuseStep 22718555 = 34077833) B34077833
theorem B1329255 : Blo 1328983 1329255 := bstep (se 1 (by rfl) ⟨996941, by rfl⟩ : syracuseStep 1329255 = 1993883) B1993883
theorem B19179625 : Blo 1328983 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B1329263 : Blo 1328983 1329263 := bstep (se 1 (by rfl) ⟨996947, by rfl⟩ : syracuseStep 1329263 = 1993895) B1993895
theorem B2992265 : Blo 1328983 2992265 := bstep (se 2 (by rfl) ⟨1122099, by rfl⟩ : syracuseStep 2992265 = 2244199) B2244199
theorem B719227163 : Blo 1328983 719227163 := bstep (se 1 (by rfl) ⟨539420372, by rfl⟩ : syracuseStep 719227163 = 1078840745) B1078840745
theorem B1329823 : Blo 1328983 1329823 := bstep (se 1 (by rfl) ⟨997367, by rfl⟩ : syracuseStep 1329823 = 1994735) B1994735
theorem B5048993 : Blo 1328983 5048993 := bstep (se 2 (by rfl) ⟨1893372, by rfl⟩ : syracuseStep 5048993 = 3786745) B3786745
theorem B1993481 : Blo 1328983 1993481 := bstep (se 2 (by rfl) ⟨747555, by rfl⟩ : syracuseStep 1993481 = 1495111) B1495111
theorem B1329983 : Blo 1328983 1329983 := bstep (se 1 (by rfl) ⟨997487, by rfl⟩ : syracuseStep 1329983 = 1994975) B1994975
theorem B1330175 : Blo 1328983 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B3837095 : Blo 1328983 3837095 := bstep (se 1 (by rfl) ⟨2877821, by rfl⟩ : syracuseStep 3837095 = 5755643) B5755643
theorem B9587969 : Blo 1328983 9587969 := bstep (se 2 (by rfl) ⟨3595488, by rfl⟩ : syracuseStep 9587969 = 7190977) B7190977
theorem B1994075 : Blo 1328983 1994075 := bstep (se 1 (by rfl) ⟨1495556, by rfl⟩ : syracuseStep 1994075 = 2991113) B2991113
theorem B2526623 : Blo 1328983 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B2993615 : Blo 1328983 2993615 := bstep (se 1 (by rfl) ⟨2245211, by rfl⟩ : syracuseStep 2993615 = 4490423) B4490423
theorem B1330719 : Blo 1328983 1330719 := bstep (se 1 (by rfl) ⟨998039, by rfl⟩ : syracuseStep 1330719 = 1996079) B1996079
theorem B1330843 : Blo 1328983 1330843 := bstep (se 1 (by rfl) ⟨998132, by rfl⟩ : syracuseStep 1330843 = 1996265) B1996265
theorem B1330879 : Blo 1328983 1330879 := bstep (se 1 (by rfl) ⟨998159, by rfl⟩ : syracuseStep 1330879 = 1996319) B1996319
theorem B1994447 : Blo 1328983 1994447 := bstep (se 1 (by rfl) ⟨1495835, by rfl⟩ : syracuseStep 1994447 = 2991671) B2991671
theorem B1994471 : Blo 1328983 1994471 := bstep (se 1 (by rfl) ⟨1495853, by rfl⟩ : syracuseStep 1994471 = 2991707) B2991707
theorem B1994855 : Blo 1328983 1994855 := bstep (se 1 (by rfl) ⟨1496141, by rfl⟩ : syracuseStep 1994855 = 2992283) B2992283
theorem B5050619 : Blo 1328983 5050619 := bstep (se 1 (by rfl) ⟨3787964, by rfl⟩ : syracuseStep 5050619 = 7575929) B7575929
theorem B1995035 : Blo 1328983 1995035 := bstep (se 1 (by rfl) ⟨1496276, by rfl⟩ : syracuseStep 1995035 = 2992553) B2992553
theorem B4550951 : Blo 1328983 4550951 := bstep (se 1 (by rfl) ⟨3413213, by rfl⟩ : syracuseStep 4550951 = 6826427) B6826427
theorem B1995311 : Blo 1328983 1995311 := bstep (se 1 (by rfl) ⟨1496483, by rfl⟩ : syracuseStep 1995311 = 2992967) B2992967
theorem B1495759 : Blo 1328983 1495759 := bstep (se 1 (by rfl) ⟨1121819, by rfl⟩ : syracuseStep 1495759 = 2243639) B2243639
theorem B1995719 : Blo 1328983 1995719 := bstep (se 1 (by rfl) ⟨1496789, by rfl⟩ : syracuseStep 1995719 = 2993579) B2993579
theorem B1995803 : Blo 1328983 1995803 := bstep (se 1 (by rfl) ⟨1496852, by rfl⟩ : syracuseStep 1995803 = 2993705) B2993705
theorem B7189831 : Blo 1328983 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B2020735 : Blo 1328983 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B10098107 : Blo 1328983 10098107 := bstep (se 1 (by rfl) ⟨7573580, by rfl⟩ : syracuseStep 10098107 = 15147161) B15147161
theorem B1996415 : Blo 1328983 1996415 := bstep (se 1 (by rfl) ⟨1497311, by rfl⟩ : syracuseStep 1996415 = 2994623) B2994623
theorem B7673591 : Blo 1328983 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B1497055 : Blo 1328983 1497055 := bstep (se 1 (by rfl) ⟨1122791, by rfl⟩ : syracuseStep 1497055 = 2245583) B2245583
theorem B17053679 : Blo 1328983 17053679 := bstep (se 1 (by rfl) ⟨12790259, by rfl⟩ : syracuseStep 17053679 = 25580519) B25580519
theorem B4258079 : Blo 1328983 4258079 := bstep (se 1 (by rfl) ⟨3193559, by rfl⟩ : syracuseStep 4258079 = 6387119) B6387119
theorem B3365327 : Blo 1328983 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2243065 : Blo 1328983 2243065 := bstep (se 2 (by rfl) ⟨841149, by rfl⟩ : syracuseStep 2243065 = 1682299) B1682299
theorem B2841323 : Blo 1328983 2841323 := bstep (se 1 (by rfl) ⟨2130992, by rfl⟩ : syracuseStep 2841323 = 4261985) B4261985
theorem B17038097 : Blo 1328983 17038097 := bstep (se 2 (by rfl) ⟨6389286, by rfl⟩ : syracuseStep 17038097 = 12778573) B12778573
theorem B7674679 : Blo 1328983 7674679 := bstep (se 1 (by rfl) ⟨5756009, by rfl⟩ : syracuseStep 7674679 = 11512019) B11512019
theorem B81960011 : Blo 1328983 81960011 := bstep (se 1 (by rfl) ⟨61470008, by rfl⟩ : syracuseStep 81960011 = 122940017) B122940017
theorem B34634981 : Blo 1328983 34634981 := bstep (se 4 (by rfl) ⟨3247029, by rfl⟩ : syracuseStep 34634981 = 6494059) B6494059
theorem B65559935 : Blo 1328983 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B4488911 : Blo 1328983 4488911 := bstep (se 1 (by rfl) ⟨3366683, by rfl⟩ : syracuseStep 4488911 = 6733367) B6733367
theorem B6660073 : Blo 1328983 6660073 := bstep (se 2 (by rfl) ⟨2497527, by rfl⟩ : syracuseStep 6660073 = 4995055) B4995055
theorem B3367079 : Blo 1328983 3367079 := bstep (se 1 (by rfl) ⟨2525309, by rfl⟩ : syracuseStep 3367079 = 5050619) B5050619
theorem B2244935 : Blo 1328983 2244935 := bstep (se 1 (by rfl) ⟨1683701, by rfl⟩ : syracuseStep 2244935 = 3367403) B3367403
theorem B4489883 : Blo 1328983 4489883 := bstep (se 1 (by rfl) ⟨3367412, by rfl⟩ : syracuseStep 4489883 = 6734825) B6734825
theorem B2990753 : Blo 1328983 2990753 := bstep (se 2 (by rfl) ⟨1121532, by rfl⟩ : syracuseStep 2990753 = 2243065) B2243065
theorem B10232905 : Blo 1328983 10232905 := bstep (se 2 (by rfl) ⟨3837339, by rfl⟩ : syracuseStep 10232905 = 7674679) B7674679
theorem B76645601 : Blo 1328983 76645601 := bstep (se 2 (by rfl) ⟨28742100, by rfl⟩ : syracuseStep 76645601 = 57484201) B57484201
theorem B9586441 : Blo 1328983 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B1328987 : Blo 1328983 1328987 := bstep (se 1 (by rfl) ⟨996740, by rfl⟩ : syracuseStep 1328987 = 1993481) B1993481
theorem B2558063 : Blo 1328983 2558063 := bstep (se 1 (by rfl) ⟨1918547, by rfl⟩ : syracuseStep 2558063 = 3837095) B3837095
theorem B6391979 : Blo 1328983 6391979 := bstep (se 1 (by rfl) ⟨4793984, by rfl⟩ : syracuseStep 6391979 = 9587969) B9587969
theorem B1329383 : Blo 1328983 1329383 := bstep (se 1 (by rfl) ⟨997037, by rfl⟩ : syracuseStep 1329383 = 1994075) B1994075
theorem B43706623 : Blo 1328983 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B1329631 : Blo 1328983 1329631 := bstep (se 1 (by rfl) ⟨997223, by rfl⟩ : syracuseStep 1329631 = 1994447) B1994447
theorem B2992607 : Blo 1328983 2992607 := bstep (se 1 (by rfl) ⟨2244455, by rfl⟩ : syracuseStep 2992607 = 4488911) B4488911
theorem B1329647 : Blo 1328983 1329647 := bstep (se 1 (by rfl) ⟨997235, by rfl⟩ : syracuseStep 1329647 = 1994471) B1994471
theorem B1329903 : Blo 1328983 1329903 := bstep (se 1 (by rfl) ⟨997427, by rfl⟩ : syracuseStep 1329903 = 1994855) B1994855
theorem B1993499 : Blo 1328983 1993499 := bstep (se 1 (by rfl) ⟨1495124, by rfl⟩ : syracuseStep 1993499 = 2990249) B2990249
theorem B4041569 : Blo 1328983 4041569 := bstep (se 2 (by rfl) ⟨1515588, by rfl⟩ : syracuseStep 4041569 = 3031177) B3031177
theorem B1330023 : Blo 1328983 1330023 := bstep (se 1 (by rfl) ⟨997517, by rfl⟩ : syracuseStep 1330023 = 1995035) B1995035
theorem B2993147 : Blo 1328983 2993147 := bstep (se 1 (by rfl) ⟨2244860, by rfl⟩ : syracuseStep 2993147 = 4489721) B4489721
theorem B1330207 : Blo 1328983 1330207 := bstep (se 1 (by rfl) ⟨997655, by rfl⟩ : syracuseStep 1330207 = 1995311) B1995311
theorem B2993183 : Blo 1328983 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B1330479 : Blo 1328983 1330479 := bstep (se 1 (by rfl) ⟨997859, by rfl⟩ : syracuseStep 1330479 = 1995719) B1995719
theorem B1330535 : Blo 1328983 1330535 := bstep (se 1 (by rfl) ⟨997901, by rfl⟩ : syracuseStep 1330535 = 1995803) B1995803
theorem B12135869 : Blo 1328983 12135869 := bstep (se 3 (by rfl) ⟨2275475, by rfl⟩ : syracuseStep 12135869 = 4550951) B4550951
theorem B1994219 : Blo 1328983 1994219 := bstep (se 1 (by rfl) ⟨1495664, by rfl⟩ : syracuseStep 1994219 = 2991329) B2991329
theorem B1994345 : Blo 1328983 1994345 := bstep (se 2 (by rfl) ⟨747879, by rfl⟩ : syracuseStep 1994345 = 1495759) B1495759
theorem B1994351 : Blo 1328983 1994351 := bstep (se 1 (by rfl) ⟨1495763, by rfl⟩ : syracuseStep 1994351 = 2991527) B2991527
theorem B1683175 : Blo 1328983 1683175 := bstep (se 1 (by rfl) ⟨1262381, by rfl⟩ : syracuseStep 1683175 = 2524763) B2524763
theorem B1330943 : Blo 1328983 1330943 := bstep (se 1 (by rfl) ⟨998207, by rfl⟩ : syracuseStep 1330943 = 1996415) B1996415
theorem B5115727 : Blo 1328983 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B9219923 : Blo 1328983 9219923 := bstep (se 1 (by rfl) ⟨6914942, by rfl⟩ : syracuseStep 9219923 = 13829885) B13829885
theorem B2994011 : Blo 1328983 2994011 := bstep (se 1 (by rfl) ⟨2245508, by rfl⟩ : syracuseStep 2994011 = 4491017) B4491017
theorem B2994047 : Blo 1328983 2994047 := bstep (se 1 (by rfl) ⟨2245535, by rfl⟩ : syracuseStep 2994047 = 4491071) B4491071
theorem B1994843 : Blo 1328983 1994843 := bstep (se 1 (by rfl) ⟨1496132, by rfl⟩ : syracuseStep 1994843 = 2992265) B2992265
theorem B2838719 : Blo 1328983 2838719 := bstep (se 1 (by rfl) ⟨2129039, by rfl⟩ : syracuseStep 2838719 = 4258079) B4258079
theorem B2994425 : Blo 1328983 2994425 := bstep (se 2 (by rfl) ⟨1122909, by rfl⟩ : syracuseStep 2994425 = 2245819) B2245819
theorem B11358731 : Blo 1328983 11358731 := bstep (se 1 (by rfl) ⟨8519048, by rfl⟩ : syracuseStep 11358731 = 17038097) B17038097
theorem B23089987 : Blo 1328983 23089987 := bstep (se 1 (by rfl) ⟨17317490, by rfl⟩ : syracuseStep 23089987 = 34634981) B34634981
theorem B1684415 : Blo 1328983 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B1995743 : Blo 1328983 1995743 := bstep (se 1 (by rfl) ⟨1496807, by rfl⟩ : syracuseStep 1995743 = 2993615) B2993615
theorem B1996073 : Blo 1328983 1996073 := bstep (se 2 (by rfl) ⟨748527, by rfl⟩ : syracuseStep 1996073 = 1497055) B1497055
theorem B25572833 : Blo 1328983 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B6149951 : Blo 1328983 6149951 := bstep (se 1 (by rfl) ⟨4612463, by rfl⟩ : syracuseStep 6149951 = 9224927) B9224927
theorem B6732071 : Blo 1328983 6732071 := bstep (se 1 (by rfl) ⟨5049053, by rfl⟩ : syracuseStep 6732071 = 10098107) B10098107
theorem B26286383 : Blo 1328983 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B11369119 : Blo 1328983 11369119 := bstep (se 1 (by rfl) ⟨8526839, by rfl⟩ : syracuseStep 11369119 = 17053679) B17053679
theorem B15145703 : Blo 1328983 15145703 := bstep (se 1 (by rfl) ⟨11359277, by rfl⟩ : syracuseStep 15145703 = 22718555) B22718555
theorem B479484775 : Blo 1328983 479484775 := bstep (se 1 (by rfl) ⟨359613581, by rfl⟩ : syracuseStep 479484775 = 719227163) B719227163
theorem B2243551 : Blo 1328983 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B3365995 : Blo 1328983 3365995 := bstep (se 1 (by rfl) ⟨2524496, by rfl⟩ : syracuseStep 3365995 = 5048993) B5048993
theorem B2694313 : Blo 1328983 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B7576861 : Blo 1328983 7576861 := bstep (se 3 (by rfl) ⟨1420661, by rfl⟩ : syracuseStep 7576861 = 2841323) B2841323
theorem B54640007 : Blo 1328983 54640007 := bstep (se 1 (by rfl) ⟨40980005, by rfl⟩ : syracuseStep 54640007 = 81960011) B81960011
theorem B8880097 : Blo 1328983 8880097 := bstep (se 2 (by rfl) ⟨3330036, by rfl⟩ : syracuseStep 8880097 = 6660073) B6660073
theorem B2244719 : Blo 1328983 2244719 := bstep (se 1 (by rfl) ⟨1683539, by rfl⟩ : syracuseStep 2244719 = 3367079) B3367079
theorem B1892479 : Blo 1328983 1892479 := bstep (se 1 (by rfl) ⟨1419359, by rfl⟩ : syracuseStep 1892479 = 2838719) B2838719
theorem B14369669 : Blo 1328983 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B17048555 : Blo 1328983 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B30786649 : Blo 1328983 30786649 := bstep (se 2 (by rfl) ⟨11544993, by rfl⟩ : syracuseStep 30786649 = 23089987) B23089987
theorem B639313033 : Blo 1328983 639313033 := bstep (se 2 (by rfl) ⟨239742387, by rfl⟩ : syracuseStep 639313033 = 479484775) B479484775
theorem B2991401 : Blo 1328983 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B4261319 : Blo 1328983 4261319 := bstep (se 1 (by rfl) ⟨3195989, by rfl⟩ : syracuseStep 4261319 = 6391979) B6391979
theorem B17524255 : Blo 1328983 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B10102481 : Blo 1328983 10102481 := bstep (se 2 (by rfl) ⟨3788430, by rfl⟩ : syracuseStep 10102481 = 7576861) B7576861
theorem B1328999 : Blo 1328983 1328999 := bstep (se 1 (by rfl) ⟨996749, by rfl⟩ : syracuseStep 1328999 = 1993499) B1993499
theorem B1329479 : Blo 1328983 1329479 := bstep (se 1 (by rfl) ⟨997109, by rfl⟩ : syracuseStep 1329479 = 1994219) B1994219
theorem B12781921 : Blo 1328983 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B1329563 : Blo 1328983 1329563 := bstep (se 1 (by rfl) ⟨997172, by rfl⟩ : syracuseStep 1329563 = 1994345) B1994345
theorem B1329567 : Blo 1328983 1329567 := bstep (se 1 (by rfl) ⟨997175, by rfl⟩ : syracuseStep 1329567 = 1994351) B1994351
theorem B4491773 : Blo 1328983 4491773 := bstep (se 3 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 4491773 = 1684415) B1684415
theorem B6146615 : Blo 1328983 6146615 := bstep (se 1 (by rfl) ⟨4609961, by rfl⟩ : syracuseStep 6146615 = 9219923) B9219923
theorem B11840129 : Blo 1328983 11840129 := bstep (se 2 (by rfl) ⟨4440048, by rfl⟩ : syracuseStep 11840129 = 8880097) B8880097
theorem B1329895 : Blo 1328983 1329895 := bstep (se 1 (by rfl) ⟨997421, by rfl⟩ : syracuseStep 1329895 = 1994843) B1994843
theorem B7572487 : Blo 1328983 7572487 := bstep (se 1 (by rfl) ⟨5679365, by rfl⟩ : syracuseStep 7572487 = 11358731) B11358731
theorem B2993255 : Blo 1328983 2993255 := bstep (se 1 (by rfl) ⟨2244941, by rfl⟩ : syracuseStep 2993255 = 4489883) B4489883
theorem B1993835 : Blo 1328983 1993835 := bstep (se 1 (by rfl) ⟨1495376, by rfl⟩ : syracuseStep 1993835 = 2990753) B2990753
theorem B1330495 : Blo 1328983 1330495 := bstep (se 1 (by rfl) ⟨997871, by rfl⟩ : syracuseStep 1330495 = 1995743) B1995743
theorem B51097067 : Blo 1328983 51097067 := bstep (se 1 (by rfl) ⟨38322800, by rfl⟩ : syracuseStep 51097067 = 76645601) B76645601
theorem B1330715 : Blo 1328983 1330715 := bstep (se 1 (by rfl) ⟨998036, by rfl⟩ : syracuseStep 1330715 = 1996073) B1996073
theorem B15158825 : Blo 1328983 15158825 := bstep (se 2 (by rfl) ⟨5684559, by rfl⟩ : syracuseStep 15158825 = 11369119) B11369119
theorem B4099967 : Blo 1328983 4099967 := bstep (se 1 (by rfl) ⟨3074975, by rfl⟩ : syracuseStep 4099967 = 6149951) B6149951
theorem B13643873 : Blo 1328983 13643873 := bstep (se 2 (by rfl) ⟨5116452, by rfl⟩ : syracuseStep 13643873 = 10232905) B10232905
theorem B1995071 : Blo 1328983 1995071 := bstep (se 1 (by rfl) ⟨1496303, by rfl⟩ : syracuseStep 1995071 = 2992607) B2992607
theorem B10097135 : Blo 1328983 10097135 := bstep (se 1 (by rfl) ⟨7572851, by rfl⟩ : syracuseStep 10097135 = 15145703) B15145703
theorem B1995431 : Blo 1328983 1995431 := bstep (se 1 (by rfl) ⟨1496573, by rfl⟩ : syracuseStep 1995431 = 2993147) B2993147
theorem B1995455 : Blo 1328983 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B36426671 : Blo 1328983 36426671 := bstep (se 1 (by rfl) ⟨27320003, by rfl⟩ : syracuseStep 36426671 = 54640007) B54640007
theorem B8090579 : Blo 1328983 8090579 := bstep (se 1 (by rfl) ⟨6067934, by rfl⟩ : syracuseStep 8090579 = 12135869) B12135869
theorem B6820969 : Blo 1328983 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B1996007 : Blo 1328983 1996007 := bstep (se 1 (by rfl) ⟨1497005, by rfl⟩ : syracuseStep 1996007 = 2994011) B2994011
theorem B1996031 : Blo 1328983 1996031 := bstep (se 1 (by rfl) ⟨1497023, by rfl⟩ : syracuseStep 1996031 = 2994047) B2994047
theorem B1996283 : Blo 1328983 1996283 := bstep (se 1 (by rfl) ⟨1497212, by rfl⟩ : syracuseStep 1996283 = 2994425) B2994425
theorem B1496623 : Blo 1328983 1496623 := bstep (se 1 (by rfl) ⟨1122467, by rfl⟩ : syracuseStep 1496623 = 2244935) B2244935
theorem B6821501 : Blo 1328983 6821501 := bstep (se 3 (by rfl) ⟨1279031, by rfl⟩ : syracuseStep 6821501 = 2558063) B2558063
theorem B58275497 : Blo 1328983 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B4487993 : Blo 1328983 4487993 := bstep (se 2 (by rfl) ⟨1682997, by rfl⟩ : syracuseStep 4487993 = 3365995) B3365995
theorem B4488047 : Blo 1328983 4488047 := bstep (se 1 (by rfl) ⟨3366035, by rfl⟩ : syracuseStep 4488047 = 6732071) B6732071
theorem B2694379 : Blo 1328983 2694379 := bstep (se 1 (by rfl) ⟨2020784, by rfl⟩ : syracuseStep 2694379 = 4041569) B4041569
theorem B2244233 : Blo 1328983 2244233 := bstep (se 2 (by rfl) ⟨841587, by rfl⟩ : syracuseStep 2244233 = 1683175) B1683175
theorem B2523305 : Blo 1328983 2523305 := bstep (se 2 (by rfl) ⟨946239, by rfl⟩ : syracuseStep 2523305 = 1892479) B1892479
theorem B6734987 : Blo 1328983 6734987 := bstep (se 1 (by rfl) ⟨5051240, by rfl⟩ : syracuseStep 6734987 = 10102481) B10102481
theorem B9094625 : Blo 1328983 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B2991995 : Blo 1328983 2991995 := bstep (se 1 (by rfl) ⟨2243996, by rfl⟩ : syracuseStep 2991995 = 4487993) B4487993
theorem B2992031 : Blo 1328983 2992031 := bstep (se 1 (by rfl) ⟨2244023, by rfl⟩ : syracuseStep 2992031 = 4488047) B4488047
theorem B23365673 : Blo 1328983 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B1329223 : Blo 1328983 1329223 := bstep (se 1 (by rfl) ⟨996917, by rfl⟩ : syracuseStep 1329223 = 1993835) B1993835
theorem B34064711 : Blo 1328983 34064711 := bstep (se 1 (by rfl) ⟨25548533, by rfl⟩ : syracuseStep 34064711 = 51097067) B51097067
theorem B9095915 : Blo 1328983 9095915 := bstep (se 1 (by rfl) ⟨6821936, by rfl⟩ : syracuseStep 9095915 = 13643873) B13643873
theorem B1330047 : Blo 1328983 1330047 := bstep (se 1 (by rfl) ⟨997535, by rfl⟩ : syracuseStep 1330047 = 1995071) B1995071
theorem B1330287 : Blo 1328983 1330287 := bstep (se 1 (by rfl) ⟨997715, by rfl⟩ : syracuseStep 1330287 = 1995431) B1995431
theorem B1330303 : Blo 1328983 1330303 := bstep (se 1 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 1330303 = 1995455) B1995455
theorem B17042561 : Blo 1328983 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B164195461 : Blo 1328983 164195461 := bstep (se 4 (by rfl) ⟨15393324, by rfl⟩ : syracuseStep 164195461 = 30786649) B30786649
theorem B9579779 : Blo 1328983 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B24284447 : Blo 1328983 24284447 := bstep (se 1 (by rfl) ⟨18213335, by rfl⟩ : syracuseStep 24284447 = 36426671) B36426671
theorem B5393719 : Blo 1328983 5393719 := bstep (se 1 (by rfl) ⟨4045289, by rfl⟩ : syracuseStep 5393719 = 8090579) B8090579
theorem B11365703 : Blo 1328983 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B1330671 : Blo 1328983 1330671 := bstep (se 1 (by rfl) ⟨998003, by rfl⟩ : syracuseStep 1330671 = 1996007) B1996007
theorem B1330687 : Blo 1328983 1330687 := bstep (se 1 (by rfl) ⟨998015, by rfl⟩ : syracuseStep 1330687 = 1996031) B1996031
theorem B1994267 : Blo 1328983 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B1330855 : Blo 1328983 1330855 := bstep (se 1 (by rfl) ⟨998141, by rfl⟩ : syracuseStep 1330855 = 1996283) B1996283
theorem B10096649 : Blo 1328983 10096649 := bstep (se 2 (by rfl) ⟨3786243, by rfl⟩ : syracuseStep 10096649 = 7572487) B7572487
theorem B3592505 : Blo 1328983 3592505 := bstep (se 2 (by rfl) ⟨1347189, by rfl⟩ : syracuseStep 3592505 = 2694379) B2694379
theorem B18190669 : Blo 1328983 18190669 := bstep (se 3 (by rfl) ⟨3410750, by rfl⟩ : syracuseStep 18190669 = 6821501) B6821501
theorem B2994515 : Blo 1328983 2994515 := bstep (se 1 (by rfl) ⟨2245886, by rfl⟩ : syracuseStep 2994515 = 4491773) B4491773
theorem B1995497 : Blo 1328983 1995497 := bstep (se 2 (by rfl) ⟨748311, by rfl⟩ : syracuseStep 1995497 = 1496623) B1496623
theorem B1995503 : Blo 1328983 1995503 := bstep (se 1 (by rfl) ⟨1496627, by rfl⟩ : syracuseStep 1995503 = 2993255) B2993255
theorem B10105883 : Blo 1328983 10105883 := bstep (se 1 (by rfl) ⟨7579412, by rfl⟩ : syracuseStep 10105883 = 15158825) B15158825
theorem B1496155 : Blo 1328983 1496155 := bstep (se 1 (by rfl) ⟨1122116, by rfl⟩ : syracuseStep 1496155 = 2244233) B2244233
theorem B2733311 : Blo 1328983 2733311 := bstep (se 1 (by rfl) ⟨2049983, by rfl⟩ : syracuseStep 2733311 = 4099967) B4099967
theorem B1496479 : Blo 1328983 1496479 := bstep (se 1 (by rfl) ⟨1122359, by rfl⟩ : syracuseStep 1496479 = 2244719) B2244719
theorem B6731423 : Blo 1328983 6731423 := bstep (se 1 (by rfl) ⟨5048567, by rfl⟩ : syracuseStep 6731423 = 10097135) B10097135
theorem B2840879 : Blo 1328983 2840879 := bstep (se 1 (by rfl) ⟨2130659, by rfl⟩ : syracuseStep 2840879 = 4261319) B4261319
theorem B126294709 : Blo 1328983 126294709 := bstep (se 5 (by rfl) ⟨5920064, by rfl⟩ : syracuseStep 126294709 = 11840129) B11840129
theorem B16390973 : Blo 1328983 16390973 := bstep (se 3 (by rfl) ⟨3073307, by rfl⟩ : syracuseStep 16390973 = 6146615) B6146615
theorem B852417377 : Blo 1328983 852417377 := bstep (se 2 (by rfl) ⟨319656516, by rfl⟩ : syracuseStep 852417377 = 639313033) B639313033
theorem B155401325 : Blo 1328983 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B4489991 : Blo 1328983 4489991 := bstep (se 1 (by rfl) ⟨3367493, by rfl⟩ : syracuseStep 4489991 = 6734987) B6734987
theorem B6063083 : Blo 1328983 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B22709807 : Blo 1328983 22709807 := bstep (se 1 (by rfl) ⟨17032355, by rfl⟩ : syracuseStep 22709807 = 34064711) B34064711
theorem B6063943 : Blo 1328983 6063943 := bstep (se 1 (by rfl) ⟨4547957, by rfl⟩ : syracuseStep 6063943 = 9095915) B9095915
theorem B16189631 : Blo 1328983 16189631 := bstep (se 1 (by rfl) ⟨12142223, by rfl⟩ : syracuseStep 16189631 = 24284447) B24284447
theorem B1329511 : Blo 1328983 1329511 := bstep (se 1 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 1329511 = 1994267) B1994267
theorem B1682203 : Blo 1328983 1682203 := bstep (se 1 (by rfl) ⟨1261652, by rfl⟩ : syracuseStep 1682203 = 2523305) B2523305
theorem B2395003 : Blo 1328983 2395003 := bstep (se 1 (by rfl) ⟨1796252, by rfl⟩ : syracuseStep 2395003 = 3592505) B3592505
theorem B1330331 : Blo 1328983 1330331 := bstep (se 1 (by rfl) ⟨997748, by rfl⟩ : syracuseStep 1330331 = 1995497) B1995497
theorem B1330335 : Blo 1328983 1330335 := bstep (se 1 (by rfl) ⟨997751, by rfl⟩ : syracuseStep 1330335 = 1995503) B1995503
theorem B6737255 : Blo 1328983 6737255 := bstep (se 1 (by rfl) ⟨5052941, by rfl⟩ : syracuseStep 6737255 = 10105883) B10105883
theorem B1822207 : Blo 1328983 1822207 := bstep (se 1 (by rfl) ⟨1366655, by rfl⟩ : syracuseStep 1822207 = 2733311) B2733311
theorem B1994663 : Blo 1328983 1994663 := bstep (se 1 (by rfl) ⟨1495997, by rfl⟩ : syracuseStep 1994663 = 2991995) B2991995
theorem B1994687 : Blo 1328983 1994687 := bstep (se 1 (by rfl) ⟨1496015, by rfl⟩ : syracuseStep 1994687 = 2992031) B2992031
theorem B15577115 : Blo 1328983 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B1994873 : Blo 1328983 1994873 := bstep (se 2 (by rfl) ⟨748077, by rfl⟩ : syracuseStep 1994873 = 1496155) B1496155
theorem B218927281 : Blo 1328983 218927281 := bstep (se 2 (by rfl) ⟨82097730, by rfl⟩ : syracuseStep 218927281 = 164195461) B164195461
theorem B28766501 : Blo 1328983 28766501 := bstep (se 4 (by rfl) ⟨2696859, by rfl⟩ : syracuseStep 28766501 = 5393719) B5393719
theorem B1995305 : Blo 1328983 1995305 := bstep (se 2 (by rfl) ⟨748239, by rfl⟩ : syracuseStep 1995305 = 1496479) B1496479
theorem B103600883 : Blo 1328983 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B6386519 : Blo 1328983 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B6731099 : Blo 1328983 6731099 := bstep (se 1 (by rfl) ⟨5048324, by rfl⟩ : syracuseStep 6731099 = 10096649) B10096649
theorem B1996343 : Blo 1328983 1996343 := bstep (se 1 (by rfl) ⟨1497257, by rfl⟩ : syracuseStep 1996343 = 2994515) B2994515
theorem B24254225 : Blo 1328983 24254225 := bstep (se 2 (by rfl) ⟨9095334, by rfl⟩ : syracuseStep 24254225 = 18190669) B18190669
theorem B7575677 : Blo 1328983 7575677 := bstep (se 3 (by rfl) ⟨1420439, by rfl⟩ : syracuseStep 7575677 = 2840879) B2840879
theorem B168392945 : Blo 1328983 168392945 := bstep (se 2 (by rfl) ⟨63147354, by rfl⟩ : syracuseStep 168392945 = 126294709) B126294709
theorem B4487615 : Blo 1328983 4487615 := bstep (se 1 (by rfl) ⟨3365711, by rfl⟩ : syracuseStep 4487615 = 6731423) B6731423
theorem B10927315 : Blo 1328983 10927315 := bstep (se 1 (by rfl) ⟨8195486, by rfl⟩ : syracuseStep 10927315 = 16390973) B16390973
theorem B568278251 : Blo 1328983 568278251 := bstep (se 1 (by rfl) ⟨426208688, by rfl⟩ : syracuseStep 568278251 = 852417377) B852417377
theorem B11361707 : Blo 1328983 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B7577135 : Blo 1328983 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B19177667 : Blo 1328983 19177667 := bstep (se 1 (by rfl) ⟨14383250, by rfl⟩ : syracuseStep 19177667 = 28766501) B28766501
theorem B69067255 : Blo 1328983 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B15139871 : Blo 1328983 15139871 := bstep (se 1 (by rfl) ⟨11354903, by rfl⟩ : syracuseStep 15139871 = 22709807) B22709807
theorem B2991743 : Blo 1328983 2991743 := bstep (se 1 (by rfl) ⟨2243807, by rfl⟩ : syracuseStep 2991743 = 4487615) B4487615
theorem B4491503 : Blo 1328983 4491503 := bstep (se 1 (by rfl) ⟨3368627, by rfl⟩ : syracuseStep 4491503 = 6737255) B6737255
theorem B1329775 : Blo 1328983 1329775 := bstep (se 1 (by rfl) ⟨997331, by rfl⟩ : syracuseStep 1329775 = 1994663) B1994663
theorem B1329791 : Blo 1328983 1329791 := bstep (se 1 (by rfl) ⟨997343, by rfl⟩ : syracuseStep 1329791 = 1994687) B1994687
theorem B1329915 : Blo 1328983 1329915 := bstep (se 1 (by rfl) ⟨997436, by rfl⟩ : syracuseStep 1329915 = 1994873) B1994873
theorem B1330203 : Blo 1328983 1330203 := bstep (se 1 (by rfl) ⟨997652, by rfl⟩ : syracuseStep 1330203 = 1995305) B1995305
theorem B2993327 : Blo 1328983 2993327 := bstep (se 1 (by rfl) ⟨2244995, by rfl⟩ : syracuseStep 2993327 = 4489991) B4489991
theorem B4042055 : Blo 1328983 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B1330895 : Blo 1328983 1330895 := bstep (se 1 (by rfl) ⟨998171, by rfl⟩ : syracuseStep 1330895 = 1996343) B1996343
theorem B5050451 : Blo 1328983 5050451 := bstep (se 1 (by rfl) ⟨3787838, by rfl⟩ : syracuseStep 5050451 = 7575677) B7575677
theorem B10793087 : Blo 1328983 10793087 := bstep (se 1 (by rfl) ⟨8094815, by rfl⟩ : syracuseStep 10793087 = 16189631) B16189631
theorem B14569753 : Blo 1328983 14569753 := bstep (se 2 (by rfl) ⟨5463657, by rfl⟩ : syracuseStep 14569753 = 10927315) B10927315
theorem B2429609 : Blo 1328983 2429609 := bstep (se 2 (by rfl) ⟨911103, by rfl⟩ : syracuseStep 2429609 = 1822207) B1822207
theorem B378852167 : Blo 1328983 378852167 := bstep (se 1 (by rfl) ⟨284139125, by rfl⟩ : syracuseStep 378852167 = 568278251) B568278251
theorem B7574471 : Blo 1328983 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B5051423 : Blo 1328983 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B41538973 : Blo 1328983 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B291903041 : Blo 1328983 291903041 := bstep (se 2 (by rfl) ⟨109463640, by rfl⟩ : syracuseStep 291903041 = 218927281) B218927281
theorem B4257679 : Blo 1328983 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B4487399 : Blo 1328983 4487399 := bstep (se 1 (by rfl) ⟨3365549, by rfl⟩ : syracuseStep 4487399 = 6731099) B6731099
theorem B2242937 : Blo 1328983 2242937 := bstep (se 2 (by rfl) ⟨841101, by rfl⟩ : syracuseStep 2242937 = 1682203) B1682203
theorem B3193337 : Blo 1328983 3193337 := bstep (se 2 (by rfl) ⟨1197501, by rfl⟩ : syracuseStep 3193337 = 2395003) B2395003
theorem B16169483 : Blo 1328983 16169483 := bstep (se 1 (by rfl) ⟨12127112, by rfl⟩ : syracuseStep 16169483 = 24254225) B24254225
theorem B112261963 : Blo 1328983 112261963 := bstep (se 1 (by rfl) ⟨84196472, by rfl⟩ : syracuseStep 112261963 = 168392945) B168392945
theorem B8085257 : Blo 1328983 8085257 := bstep (se 2 (by rfl) ⟨3031971, by rfl⟩ : syracuseStep 8085257 = 6063943) B6063943
theorem B3366967 : Blo 1328983 3366967 := bstep (se 1 (by rfl) ⟨2525225, by rfl⟩ : syracuseStep 3366967 = 5050451) B5050451
theorem B10093247 : Blo 1328983 10093247 := bstep (se 1 (by rfl) ⟨7569935, by rfl⟩ : syracuseStep 10093247 = 15139871) B15139871
theorem B3367615 : Blo 1328983 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B194602027 : Blo 1328983 194602027 := bstep (se 1 (by rfl) ⟨145951520, by rfl⟩ : syracuseStep 194602027 = 291903041) B291903041
theorem B2991599 : Blo 1328983 2991599 := bstep (se 1 (by rfl) ⟨2243699, by rfl⟩ : syracuseStep 2991599 = 4487399) B4487399
theorem B1010272445 : Blo 1328983 1010272445 := bstep (se 3 (by rfl) ⟨189426083, by rfl⟩ : syracuseStep 1010272445 = 378852167) B378852167
theorem B7195391 : Blo 1328983 7195391 := bstep (se 1 (by rfl) ⟨5396543, by rfl⟩ : syracuseStep 7195391 = 10793087) B10793087
theorem B19426337 : Blo 1328983 19426337 := bstep (se 2 (by rfl) ⟨7284876, by rfl⟩ : syracuseStep 19426337 = 14569753) B14569753
theorem B5049647 : Blo 1328983 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B92089673 : Blo 1328983 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B1994495 : Blo 1328983 1994495 := bstep (se 1 (by rfl) ⟨1495871, by rfl⟩ : syracuseStep 1994495 = 2991743) B2991743
theorem B2994335 : Blo 1328983 2994335 := bstep (se 1 (by rfl) ⟨2245751, by rfl⟩ : syracuseStep 2994335 = 4491503) B4491503
theorem B1495291 : Blo 1328983 1495291 := bstep (se 1 (by rfl) ⟨1121468, by rfl⟩ : syracuseStep 1495291 = 2242937) B2242937
theorem B1995551 : Blo 1328983 1995551 := bstep (se 1 (by rfl) ⟨1496663, by rfl⟩ : syracuseStep 1995551 = 2993327) B2993327
theorem B12785111 : Blo 1328983 12785111 := bstep (se 1 (by rfl) ⟨9588833, by rfl⟩ : syracuseStep 12785111 = 19177667) B19177667
theorem B149682617 : Blo 1328983 149682617 := bstep (se 2 (by rfl) ⟨56130981, by rfl⟩ : syracuseStep 149682617 = 112261963) B112261963
theorem B2128891 : Blo 1328983 2128891 := bstep (se 1 (by rfl) ⟨1596668, by rfl⟩ : syracuseStep 2128891 = 3193337) B3193337
theorem B10779655 : Blo 1328983 10779655 := bstep (se 1 (by rfl) ⟨8084741, by rfl⟩ : syracuseStep 10779655 = 16169483) B16169483
theorem B6478957 : Blo 1328983 6478957 := bstep (se 3 (by rfl) ⟨1214804, by rfl⟩ : syracuseStep 6478957 = 2429609) B2429609
theorem B55385297 : Blo 1328983 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B2694703 : Blo 1328983 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B5390171 : Blo 1328983 5390171 := bstep (se 1 (by rfl) ⟨4042628, by rfl⟩ : syracuseStep 5390171 = 8085257) B8085257
theorem B5676905 : Blo 1328983 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B4489289 : Blo 1328983 4489289 := bstep (se 2 (by rfl) ⟨1683483, by rfl⟩ : syracuseStep 4489289 = 3366967) B3366967
theorem B4490153 : Blo 1328983 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B673514963 : Blo 1328983 673514963 := bstep (se 1 (by rfl) ⟨505136222, by rfl⟩ : syracuseStep 673514963 = 1010272445) B1010272445
theorem B99788411 : Blo 1328983 99788411 := bstep (se 1 (by rfl) ⟨74841308, by rfl⟩ : syracuseStep 99788411 = 149682617) B149682617
theorem B36923531 : Blo 1328983 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B61393115 : Blo 1328983 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B1329663 : Blo 1328983 1329663 := bstep (se 1 (by rfl) ⟨997247, by rfl⟩ : syracuseStep 1329663 = 1994495) B1994495
theorem B1993721 : Blo 1328983 1993721 := bstep (se 2 (by rfl) ⟨747645, by rfl⟩ : syracuseStep 1993721 = 1495291) B1495291
theorem B6728831 : Blo 1328983 6728831 := bstep (se 1 (by rfl) ⟨5046623, by rfl⟩ : syracuseStep 6728831 = 10093247) B10093247
theorem B1330367 : Blo 1328983 1330367 := bstep (se 1 (by rfl) ⟨997775, by rfl⟩ : syracuseStep 1330367 = 1995551) B1995551
theorem B8523407 : Blo 1328983 8523407 := bstep (se 1 (by rfl) ⟨6392555, by rfl⟩ : syracuseStep 8523407 = 12785111) B12785111
theorem B1994399 : Blo 1328983 1994399 := bstep (se 1 (by rfl) ⟨1495799, by rfl⟩ : syracuseStep 1994399 = 2991599) B2991599
theorem B2838521 : Blo 1328983 2838521 := bstep (se 2 (by rfl) ⟨1064445, by rfl⟩ : syracuseStep 2838521 = 2128891) B2128891
theorem B14372873 : Blo 1328983 14372873 := bstep (se 2 (by rfl) ⟨5389827, by rfl⟩ : syracuseStep 14372873 = 10779655) B10779655
theorem B259469369 : Blo 1328983 259469369 := bstep (se 2 (by rfl) ⟨97301013, by rfl⟩ : syracuseStep 259469369 = 194602027) B194602027
theorem B8638609 : Blo 1328983 8638609 := bstep (se 2 (by rfl) ⟨3239478, by rfl⟩ : syracuseStep 8638609 = 6478957) B6478957
theorem B4796927 : Blo 1328983 4796927 := bstep (se 1 (by rfl) ⟨3597695, by rfl⟩ : syracuseStep 4796927 = 7195391) B7195391
theorem B3592937 : Blo 1328983 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B3593447 : Blo 1328983 3593447 := bstep (se 1 (by rfl) ⟨2695085, by rfl⟩ : syracuseStep 3593447 = 5390171) B5390171
theorem B1996223 : Blo 1328983 1996223 := bstep (se 1 (by rfl) ⟨1497167, by rfl⟩ : syracuseStep 1996223 = 2994335) B2994335
theorem B12950891 : Blo 1328983 12950891 := bstep (se 1 (by rfl) ⟨9713168, by rfl⟩ : syracuseStep 12950891 = 19426337) B19426337
theorem B3366431 : Blo 1328983 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B15138413 : Blo 1328983 15138413 := bstep (se 3 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 15138413 = 5676905) B5676905
theorem B11518145 : Blo 1328983 11518145 := bstep (se 2 (by rfl) ⟨4319304, by rfl⟩ : syracuseStep 11518145 = 8638609) B8638609
theorem B40928743 : Blo 1328983 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B1329147 : Blo 1328983 1329147 := bstep (se 1 (by rfl) ⟨996860, by rfl⟩ : syracuseStep 1329147 = 1993721) B1993721
theorem B1329599 : Blo 1328983 1329599 := bstep (se 1 (by rfl) ⟨997199, by rfl⟩ : syracuseStep 1329599 = 1994399) B1994399
theorem B2992859 : Blo 1328983 2992859 := bstep (se 1 (by rfl) ⟨2244644, by rfl⟩ : syracuseStep 2992859 = 4489289) B4489289
theorem B3197951 : Blo 1328983 3197951 := bstep (se 1 (by rfl) ⟨2398463, by rfl⟩ : syracuseStep 3197951 = 4796927) B4796927
theorem B98462749 : Blo 1328983 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B2993435 : Blo 1328983 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B2395631 : Blo 1328983 2395631 := bstep (se 1 (by rfl) ⟨1796723, by rfl⟩ : syracuseStep 2395631 = 3593447) B3593447
theorem B1330815 : Blo 1328983 1330815 := bstep (se 1 (by rfl) ⟨998111, by rfl⟩ : syracuseStep 1330815 = 1996223) B1996223
theorem B9581165 : Blo 1328983 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B4485887 : Blo 1328983 4485887 := bstep (se 1 (by rfl) ⟨3364415, by rfl⟩ : syracuseStep 4485887 = 6728831) B6728831
theorem B5682271 : Blo 1328983 5682271 := bstep (se 1 (by rfl) ⟨4261703, by rfl⟩ : syracuseStep 5682271 = 8523407) B8523407
theorem B9581915 : Blo 1328983 9581915 := bstep (se 1 (by rfl) ⟨7186436, by rfl⟩ : syracuseStep 9581915 = 14372873) B14372873
theorem B172979579 : Blo 1328983 172979579 := bstep (se 1 (by rfl) ⟨129734684, by rfl⟩ : syracuseStep 172979579 = 259469369) B259469369
theorem B449009975 : Blo 1328983 449009975 := bstep (se 1 (by rfl) ⟨336757481, by rfl⟩ : syracuseStep 449009975 = 673514963) B673514963
theorem B66525607 : Blo 1328983 66525607 := bstep (se 1 (by rfl) ⟨49894205, by rfl⟩ : syracuseStep 66525607 = 99788411) B99788411
theorem B8633927 : Blo 1328983 8633927 := bstep (se 1 (by rfl) ⟨6475445, by rfl⟩ : syracuseStep 8633927 = 12950891) B12950891
theorem B2244287 : Blo 1328983 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B10092275 : Blo 1328983 10092275 := bstep (se 1 (by rfl) ⟨7569206, by rfl⟩ : syracuseStep 10092275 = 15138413) B15138413
theorem B7569389 : Blo 1328983 7569389 := bstep (se 3 (by rfl) ⟨1419260, by rfl⟩ : syracuseStep 7569389 = 2838521) B2838521
theorem B2990591 : Blo 1328983 2990591 := bstep (se 1 (by rfl) ⟨2242943, by rfl⟩ : syracuseStep 2990591 = 4485887) B4485887
theorem B115319719 : Blo 1328983 115319719 := bstep (se 1 (by rfl) ⟨86489789, by rfl⟩ : syracuseStep 115319719 = 172979579) B172979579
theorem B2131967 : Blo 1328983 2131967 := bstep (se 1 (by rfl) ⟨1598975, by rfl⟩ : syracuseStep 2131967 = 3197951) B3197951
theorem B6728183 : Blo 1328983 6728183 := bstep (se 1 (by rfl) ⟨5046137, by rfl⟩ : syracuseStep 6728183 = 10092275) B10092275
theorem B7678763 : Blo 1328983 7678763 := bstep (se 1 (by rfl) ⟨5759072, by rfl⟩ : syracuseStep 7678763 = 11518145) B11518145
theorem B23023805 : Blo 1328983 23023805 := bstep (se 3 (by rfl) ⟨4316963, by rfl⟩ : syracuseStep 23023805 = 8633927) B8633927
theorem B299339983 : Blo 1328983 299339983 := bstep (se 1 (by rfl) ⟨224504987, by rfl⟩ : syracuseStep 299339983 = 449009975) B449009975
theorem B1995239 : Blo 1328983 1995239 := bstep (se 1 (by rfl) ⟨1496429, by rfl⟩ : syracuseStep 1995239 = 2992859) B2992859
theorem B54571657 : Blo 1328983 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B1995623 : Blo 1328983 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B1496191 : Blo 1328983 1496191 := bstep (se 1 (by rfl) ⟨1122143, by rfl⟩ : syracuseStep 1496191 = 2244287) B2244287
theorem B6387443 : Blo 1328983 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B6387943 : Blo 1328983 6387943 := bstep (se 1 (by rfl) ⟨4790957, by rfl⟩ : syracuseStep 6387943 = 9581915) B9581915
theorem B131283665 : Blo 1328983 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B7576361 : Blo 1328983 7576361 := bstep (se 2 (by rfl) ⟨2841135, by rfl⟩ : syracuseStep 7576361 = 5682271) B5682271
theorem B354803237 : Blo 1328983 354803237 := bstep (se 4 (by rfl) ⟨33262803, by rfl⟩ : syracuseStep 354803237 = 66525607) B66525607
theorem B1597087 : Blo 1328983 1597087 := bstep (se 1 (by rfl) ⟨1197815, by rfl⟩ : syracuseStep 1597087 = 2395631) B2395631
theorem B5046259 : Blo 1328983 5046259 := bstep (se 1 (by rfl) ⟨3784694, by rfl⟩ : syracuseStep 5046259 = 7569389) B7569389
theorem B72762209 : Blo 1328983 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B6728345 : Blo 1328983 6728345 := bstep (se 2 (by rfl) ⟨2523129, by rfl⟩ : syracuseStep 6728345 = 5046259) B5046259
theorem B1330159 : Blo 1328983 1330159 := bstep (se 1 (by rfl) ⟨997619, by rfl⟩ : syracuseStep 1330159 = 1995239) B1995239
theorem B1993727 : Blo 1328983 1993727 := bstep (se 1 (by rfl) ⟨1495295, by rfl⟩ : syracuseStep 1993727 = 2990591) B2990591
theorem B1330415 : Blo 1328983 1330415 := bstep (se 1 (by rfl) ⟨997811, by rfl⟩ : syracuseStep 1330415 = 1995623) B1995623
theorem B153759625 : Blo 1328983 153759625 := bstep (se 2 (by rfl) ⟨57659859, by rfl⟩ : syracuseStep 153759625 = 115319719) B115319719
theorem B1421311 : Blo 1328983 1421311 := bstep (se 1 (by rfl) ⟨1065983, by rfl⟩ : syracuseStep 1421311 = 2131967) B2131967
theorem B1994921 : Blo 1328983 1994921 := bstep (se 2 (by rfl) ⟨748095, by rfl⟩ : syracuseStep 1994921 = 1496191) B1496191
theorem B4485455 : Blo 1328983 4485455 := bstep (se 1 (by rfl) ⟨3364091, by rfl⟩ : syracuseStep 4485455 = 6728183) B6728183
theorem B5050907 : Blo 1328983 5050907 := bstep (se 1 (by rfl) ⟨3788180, by rfl⟩ : syracuseStep 5050907 = 7576361) B7576361
theorem B399119977 : Blo 1328983 399119977 := bstep (se 2 (by rfl) ⟨149669991, by rfl⟩ : syracuseStep 399119977 = 299339983) B299339983
theorem B8517257 : Blo 1328983 8517257 := bstep (se 2 (by rfl) ⟨3193971, by rfl⟩ : syracuseStep 8517257 = 6387943) B6387943
theorem B61396813 : Blo 1328983 61396813 := bstep (se 3 (by rfl) ⟨11511902, by rfl⟩ : syracuseStep 61396813 = 23023805) B23023805
theorem B8517797 : Blo 1328983 8517797 := bstep (se 4 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 8517797 = 1597087) B1597087
theorem B4258295 : Blo 1328983 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B87522443 : Blo 1328983 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B5119175 : Blo 1328983 5119175 := bstep (se 1 (by rfl) ⟨3839381, by rfl⟩ : syracuseStep 5119175 = 7678763) B7678763
theorem B236535491 : Blo 1328983 236535491 := bstep (se 1 (by rfl) ⟨177401618, by rfl⟩ : syracuseStep 236535491 = 354803237) B354803237
theorem B2990303 : Blo 1328983 2990303 := bstep (se 1 (by rfl) ⟨2242727, by rfl⟩ : syracuseStep 2990303 = 4485455) B4485455
theorem B3367271 : Blo 1328983 3367271 := bstep (se 1 (by rfl) ⟨2525453, by rfl⟩ : syracuseStep 3367271 = 5050907) B5050907
theorem B5678171 : Blo 1328983 5678171 := bstep (se 1 (by rfl) ⟨4258628, by rfl⟩ : syracuseStep 5678171 = 8517257) B8517257
theorem B5678531 : Blo 1328983 5678531 := bstep (se 1 (by rfl) ⟨4258898, by rfl⟩ : syracuseStep 5678531 = 8517797) B8517797
theorem B1329151 : Blo 1328983 1329151 := bstep (se 1 (by rfl) ⟨996863, by rfl⟩ : syracuseStep 1329151 = 1993727) B1993727
theorem B157690327 : Blo 1328983 157690327 := bstep (se 1 (by rfl) ⟨118267745, by rfl⟩ : syracuseStep 157690327 = 236535491) B236535491
theorem B1895081 : Blo 1328983 1895081 := bstep (se 2 (by rfl) ⟨710655, by rfl⟩ : syracuseStep 1895081 = 1421311) B1421311
theorem B1329947 : Blo 1328983 1329947 := bstep (se 1 (by rfl) ⟨997460, by rfl⟩ : syracuseStep 1329947 = 1994921) B1994921
theorem B48508139 : Blo 1328983 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B2838863 : Blo 1328983 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B4485563 : Blo 1328983 4485563 := bstep (se 1 (by rfl) ⟨3364172, by rfl⟩ : syracuseStep 4485563 = 6728345) B6728345
theorem B58348295 : Blo 1328983 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B3412783 : Blo 1328983 3412783 := bstep (se 1 (by rfl) ⟨2559587, by rfl⟩ : syracuseStep 3412783 = 5119175) B5119175
theorem B820051333 : Blo 1328983 820051333 := bstep (se 4 (by rfl) ⟨76879812, by rfl⟩ : syracuseStep 820051333 = 153759625) B153759625
theorem B532159969 : Blo 1328983 532159969 := bstep (se 2 (by rfl) ⟨199559988, by rfl⟩ : syracuseStep 532159969 = 399119977) B399119977
theorem B81862417 : Blo 1328983 81862417 := bstep (se 2 (by rfl) ⟨30698406, by rfl⟩ : syracuseStep 81862417 = 61396813) B61396813
theorem B1892575 : Blo 1328983 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B2244847 : Blo 1328983 2244847 := bstep (se 1 (by rfl) ⟨1683635, by rfl⟩ : syracuseStep 2244847 = 3367271) B3367271
theorem B2990375 : Blo 1328983 2990375 := bstep (se 1 (by rfl) ⟨2242781, by rfl⟩ : syracuseStep 2990375 = 4485563) B4485563
theorem B3785447 : Blo 1328983 3785447 := bstep (se 1 (by rfl) ⟨2839085, by rfl⟩ : syracuseStep 3785447 = 5678171) B5678171
theorem B3785687 : Blo 1328983 3785687 := bstep (se 1 (by rfl) ⟨2839265, by rfl⟩ : syracuseStep 3785687 = 5678531) B5678531
theorem B17494428437 : Blo 1328983 17494428437 := bstep (se 6 (by rfl) ⟨410025666, by rfl⟩ : syracuseStep 17494428437 = 820051333) B820051333
theorem B1993535 : Blo 1328983 1993535 := bstep (se 1 (by rfl) ⟨1495151, by rfl⟩ : syracuseStep 1993535 = 2990303) B2990303
theorem B38898863 : Blo 1328983 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B4550377 : Blo 1328983 4550377 := bstep (se 2 (by rfl) ⟨1706391, by rfl⟩ : syracuseStep 4550377 = 3412783) B3412783
theorem B709546625 : Blo 1328983 709546625 := bstep (se 2 (by rfl) ⟨266079984, by rfl⟩ : syracuseStep 709546625 = 532159969) B532159969
theorem B32338759 : Blo 1328983 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B210253769 : Blo 1328983 210253769 := bstep (se 2 (by rfl) ⟨78845163, by rfl⟩ : syracuseStep 210253769 = 157690327) B157690327
theorem B5053549 : Blo 1328983 5053549 := bstep (se 3 (by rfl) ⟨947540, by rfl⟩ : syracuseStep 5053549 = 1895081) B1895081
theorem B109149889 : Blo 1328983 109149889 := bstep (se 2 (by rfl) ⟨40931208, by rfl⟩ : syracuseStep 109149889 = 81862417) B81862417
theorem B473031083 : Blo 1328983 473031083 := bstep (se 1 (by rfl) ⟨354773312, by rfl⟩ : syracuseStep 473031083 = 709546625) B709546625
theorem B2523631 : Blo 1328983 2523631 := bstep (se 1 (by rfl) ⟨1892723, by rfl⟩ : syracuseStep 2523631 = 3785447) B3785447
theorem B2523791 : Blo 1328983 2523791 := bstep (se 1 (by rfl) ⟨1892843, by rfl⟩ : syracuseStep 2523791 = 3785687) B3785687
theorem B10093733 : Blo 1328983 10093733 := bstep (se 4 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 10093733 = 1892575) B1892575
theorem B11662952291 : Blo 1328983 11662952291 := bstep (se 1 (by rfl) ⟨8747214218, by rfl⟩ : syracuseStep 11662952291 = 17494428437) B17494428437
theorem B1329023 : Blo 1328983 1329023 := bstep (se 1 (by rfl) ⟨996767, by rfl⟩ : syracuseStep 1329023 = 1993535) B1993535
theorem B145533185 : Blo 1328983 145533185 := bstep (se 2 (by rfl) ⟨54574944, by rfl⟩ : syracuseStep 145533185 = 109149889) B109149889
theorem B1993583 : Blo 1328983 1993583 := bstep (se 1 (by rfl) ⟨1495187, by rfl⟩ : syracuseStep 1993583 = 2990375) B2990375
theorem B2993129 : Blo 1328983 2993129 := bstep (se 2 (by rfl) ⟨1122423, by rfl⟩ : syracuseStep 2993129 = 2244847) B2244847
theorem B43118345 : Blo 1328983 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B140169179 : Blo 1328983 140169179 := bstep (se 1 (by rfl) ⟨105126884, by rfl⟩ : syracuseStep 140169179 = 210253769) B210253769
theorem B6738065 : Blo 1328983 6738065 := bstep (se 2 (by rfl) ⟨2526774, by rfl⟩ : syracuseStep 6738065 = 5053549) B5053549
theorem B25932575 : Blo 1328983 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B6067169 : Blo 1328983 6067169 := bstep (se 2 (by rfl) ⟨2275188, by rfl⟩ : syracuseStep 6067169 = 4550377) B4550377
theorem B1329055 : Blo 1328983 1329055 := bstep (se 1 (by rfl) ⟨996791, by rfl⟩ : syracuseStep 1329055 = 1993583) B1993583
theorem B4492043 : Blo 1328983 4492043 := bstep (se 1 (by rfl) ⟨3369032, by rfl⟩ : syracuseStep 4492043 = 6738065) B6738065
theorem B315354055 : Blo 1328983 315354055 := bstep (se 1 (by rfl) ⟨236515541, by rfl⟩ : syracuseStep 315354055 = 473031083) B473031083
theorem B1682527 : Blo 1328983 1682527 := bstep (se 1 (by rfl) ⟨1261895, by rfl⟩ : syracuseStep 1682527 = 2523791) B2523791
theorem B6729155 : Blo 1328983 6729155 := bstep (se 1 (by rfl) ⟨5046866, by rfl⟩ : syracuseStep 6729155 = 10093733) B10093733
theorem B7775301527 : Blo 1328983 7775301527 := bstep (se 1 (by rfl) ⟨5831476145, by rfl⟩ : syracuseStep 7775301527 = 11662952291) B11662952291
theorem B97022123 : Blo 1328983 97022123 := bstep (se 1 (by rfl) ⟨72766592, by rfl⟩ : syracuseStep 97022123 = 145533185) B145533185
theorem B1995419 : Blo 1328983 1995419 := bstep (se 1 (by rfl) ⟨1496564, by rfl⟩ : syracuseStep 1995419 = 2993129) B2993129
theorem B69153533 : Blo 1328983 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B3364841 : Blo 1328983 3364841 := bstep (se 2 (by rfl) ⟨1261815, by rfl⟩ : syracuseStep 3364841 = 2523631) B2523631
theorem B4044779 : Blo 1328983 4044779 := bstep (se 1 (by rfl) ⟨3033584, by rfl⟩ : syracuseStep 4044779 = 6067169) B6067169
theorem B28745563 : Blo 1328983 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B93446119 : Blo 1328983 93446119 := bstep (se 1 (by rfl) ⟨70084589, by rfl⟩ : syracuseStep 93446119 = 140169179) B140169179
theorem B420472073 : Blo 1328983 420472073 := bstep (se 2 (by rfl) ⟨157677027, by rfl⟩ : syracuseStep 420472073 = 315354055) B315354055
theorem B2696519 : Blo 1328983 2696519 := bstep (se 1 (by rfl) ⟨2022389, by rfl⟩ : syracuseStep 2696519 = 4044779) B4044779
theorem B498379301 : Blo 1328983 498379301 := bstep (se 4 (by rfl) ⟨46723059, by rfl⟩ : syracuseStep 498379301 = 93446119) B93446119
theorem B1330279 : Blo 1328983 1330279 := bstep (se 1 (by rfl) ⟨997709, by rfl⟩ : syracuseStep 1330279 = 1995419) B1995419
theorem B2994695 : Blo 1328983 2994695 := bstep (se 1 (by rfl) ⟨2246021, by rfl⟩ : syracuseStep 2994695 = 4492043) B4492043
theorem B4486103 : Blo 1328983 4486103 := bstep (se 1 (by rfl) ⟨3364577, by rfl⟩ : syracuseStep 4486103 = 6729155) B6729155
theorem B38327417 : Blo 1328983 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B5183534351 : Blo 1328983 5183534351 := bstep (se 1 (by rfl) ⟨3887650763, by rfl⟩ : syracuseStep 5183534351 = 7775301527) B7775301527
theorem B64681415 : Blo 1328983 64681415 := bstep (se 1 (by rfl) ⟨48511061, by rfl⟩ : syracuseStep 64681415 = 97022123) B97022123
theorem B46102355 : Blo 1328983 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B2243227 : Blo 1328983 2243227 := bstep (se 1 (by rfl) ⟨1682420, by rfl⟩ : syracuseStep 2243227 = 3364841) B3364841
theorem B2243369 : Blo 1328983 2243369 := bstep (se 2 (by rfl) ⟨841263, by rfl⟩ : syracuseStep 2243369 = 1682527) B1682527
theorem B2990735 : Blo 1328983 2990735 := bstep (se 1 (by rfl) ⟨2243051, by rfl⟩ : syracuseStep 2990735 = 4486103) B4486103
theorem B25551611 : Blo 1328983 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B3455689567 : Blo 1328983 3455689567 := bstep (se 1 (by rfl) ⟨2591767175, by rfl⟩ : syracuseStep 3455689567 = 5183534351) B5183534351
theorem B2990969 : Blo 1328983 2990969 := bstep (se 2 (by rfl) ⟨1121613, by rfl⟩ : syracuseStep 2990969 = 2243227) B2243227
theorem B332252867 : Blo 1328983 332252867 := bstep (se 1 (by rfl) ⟨249189650, by rfl⟩ : syracuseStep 332252867 = 498379301) B498379301
theorem B1121258861 : Blo 1328983 1121258861 := bstep (se 3 (by rfl) ⟨210236036, by rfl⟩ : syracuseStep 1121258861 = 420472073) B420472073
theorem B1797679 : Blo 1328983 1797679 := bstep (se 1 (by rfl) ⟨1348259, by rfl⟩ : syracuseStep 1797679 = 2696519) B2696519
theorem B1495579 : Blo 1328983 1495579 := bstep (se 1 (by rfl) ⟨1121684, by rfl⟩ : syracuseStep 1495579 = 2243369) B2243369
theorem B1996463 : Blo 1328983 1996463 := bstep (se 1 (by rfl) ⟨1497347, by rfl⟩ : syracuseStep 1996463 = 2994695) B2994695
theorem B43120943 : Blo 1328983 43120943 := bstep (se 1 (by rfl) ⟨32340707, by rfl⟩ : syracuseStep 43120943 = 64681415) B64681415
theorem B30734903 : Blo 1328983 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B28747295 : Blo 1328983 28747295 := bstep (se 1 (by rfl) ⟨21560471, by rfl⟩ : syracuseStep 28747295 = 43120943) B43120943
theorem B20489935 : Blo 1328983 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B886007645 : Blo 1328983 886007645 := bstep (se 3 (by rfl) ⟨166126433, by rfl⟩ : syracuseStep 886007645 = 332252867) B332252867
theorem B747505907 : Blo 1328983 747505907 := bstep (se 1 (by rfl) ⟨560629430, by rfl⟩ : syracuseStep 747505907 = 1121258861) B1121258861
theorem B9587621 : Blo 1328983 9587621 := bstep (se 4 (by rfl) ⟨898839, by rfl⟩ : syracuseStep 9587621 = 1797679) B1797679
theorem B1993823 : Blo 1328983 1993823 := bstep (se 1 (by rfl) ⟨1495367, by rfl⟩ : syracuseStep 1993823 = 2990735) B2990735
theorem B17034407 : Blo 1328983 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B1993979 : Blo 1328983 1993979 := bstep (se 1 (by rfl) ⟨1495484, by rfl⟩ : syracuseStep 1993979 = 2990969) B2990969
theorem B1994105 : Blo 1328983 1994105 := bstep (se 2 (by rfl) ⟨747789, by rfl⟩ : syracuseStep 1994105 = 1495579) B1495579
theorem B1330975 : Blo 1328983 1330975 := bstep (se 1 (by rfl) ⟨998231, by rfl⟩ : syracuseStep 1330975 = 1996463) B1996463
theorem B4607586089 : Blo 1328983 4607586089 := bstep (se 2 (by rfl) ⟨1727844783, by rfl⟩ : syracuseStep 4607586089 = 3455689567) B3455689567
theorem B498337271 : Blo 1328983 498337271 := bstep (se 1 (by rfl) ⟨373752953, by rfl⟩ : syracuseStep 498337271 = 747505907) B747505907
theorem B6391747 : Blo 1328983 6391747 := bstep (se 1 (by rfl) ⟨4793810, by rfl⟩ : syracuseStep 6391747 = 9587621) B9587621
theorem B1329215 : Blo 1328983 1329215 := bstep (se 1 (by rfl) ⟨996911, by rfl⟩ : syracuseStep 1329215 = 1993823) B1993823
theorem B11356271 : Blo 1328983 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B1329319 : Blo 1328983 1329319 := bstep (se 1 (by rfl) ⟨996989, by rfl⟩ : syracuseStep 1329319 = 1993979) B1993979
theorem B1329403 : Blo 1328983 1329403 := bstep (se 1 (by rfl) ⟨997052, by rfl⟩ : syracuseStep 1329403 = 1994105) B1994105
theorem B3071724059 : Blo 1328983 3071724059 := bstep (se 1 (by rfl) ⟨2303793044, by rfl⟩ : syracuseStep 3071724059 = 4607586089) B4607586089
theorem B19164863 : Blo 1328983 19164863 := bstep (se 1 (by rfl) ⟨14373647, by rfl⟩ : syracuseStep 19164863 = 28747295) B28747295
theorem B590671763 : Blo 1328983 590671763 := bstep (se 1 (by rfl) ⟨443003822, by rfl⟩ : syracuseStep 590671763 = 886007645) B886007645
theorem B27319913 : Blo 1328983 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B7570847 : Blo 1328983 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B18213275 : Blo 1328983 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B8522329 : Blo 1328983 8522329 := bstep (se 2 (by rfl) ⟨3195873, by rfl⟩ : syracuseStep 8522329 = 6391747) B6391747
theorem B2047816039 : Blo 1328983 2047816039 := bstep (se 1 (by rfl) ⟨1535862029, by rfl⟩ : syracuseStep 2047816039 = 3071724059) B3071724059
theorem B12776575 : Blo 1328983 12776575 := bstep (se 1 (by rfl) ⟨9582431, by rfl⟩ : syracuseStep 12776575 = 19164863) B19164863
theorem B332224847 : Blo 1328983 332224847 := bstep (se 1 (by rfl) ⟨249168635, by rfl⟩ : syracuseStep 332224847 = 498337271) B498337271
theorem B393781175 : Blo 1328983 393781175 := bstep (se 1 (by rfl) ⟨295335881, by rfl⟩ : syracuseStep 393781175 = 590671763) B590671763
theorem B11363105 : Blo 1328983 11363105 := bstep (se 2 (by rfl) ⟨4261164, by rfl⟩ : syracuseStep 11363105 = 8522329) B8522329
theorem B5047231 : Blo 1328983 5047231 := bstep (se 1 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 5047231 = 7570847) B7570847
theorem B12142183 : Blo 1328983 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B2730421385 : Blo 1328983 2730421385 := bstep (se 2 (by rfl) ⟨1023908019, by rfl⟩ : syracuseStep 2730421385 = 2047816039) B2047816039
theorem B17035433 : Blo 1328983 17035433 := bstep (se 2 (by rfl) ⟨6388287, by rfl⟩ : syracuseStep 17035433 = 12776575) B12776575
theorem B221483231 : Blo 1328983 221483231 := bstep (se 1 (by rfl) ⟨166112423, by rfl⟩ : syracuseStep 221483231 = 332224847) B332224847
theorem B262520783 : Blo 1328983 262520783 := bstep (se 1 (by rfl) ⟨196890587, by rfl⟩ : syracuseStep 262520783 = 393781175) B393781175
theorem B1820280923 : Blo 1328983 1820280923 := bstep (se 1 (by rfl) ⟨1365210692, by rfl⟩ : syracuseStep 1820280923 = 2730421385) B2730421385
theorem B16189577 : Blo 1328983 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B11356955 : Blo 1328983 11356955 := bstep (se 1 (by rfl) ⟨8517716, by rfl⟩ : syracuseStep 11356955 = 17035433) B17035433
theorem B147655487 : Blo 1328983 147655487 := bstep (se 1 (by rfl) ⟨110741615, by rfl⟩ : syracuseStep 147655487 = 221483231) B221483231
theorem B6729641 : Blo 1328983 6729641 := bstep (se 2 (by rfl) ⟨2523615, by rfl⟩ : syracuseStep 6729641 = 5047231) B5047231
theorem B7575403 : Blo 1328983 7575403 := bstep (se 1 (by rfl) ⟨5681552, by rfl⟩ : syracuseStep 7575403 = 11363105) B11363105
theorem B175013855 : Blo 1328983 175013855 := bstep (se 1 (by rfl) ⟨131260391, by rfl⟩ : syracuseStep 175013855 = 262520783) B262520783
theorem B7571303 : Blo 1328983 7571303 := bstep (se 1 (by rfl) ⟨5678477, by rfl⟩ : syracuseStep 7571303 = 11356955) B11356955
theorem B98436991 : Blo 1328983 98436991 := bstep (se 1 (by rfl) ⟨73827743, by rfl⟩ : syracuseStep 98436991 = 147655487) B147655487
theorem B10793051 : Blo 1328983 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B4486427 : Blo 1328983 4486427 := bstep (se 1 (by rfl) ⟨3364820, by rfl⟩ : syracuseStep 4486427 = 6729641) B6729641
theorem B116675903 : Blo 1328983 116675903 := bstep (se 1 (by rfl) ⟨87506927, by rfl⟩ : syracuseStep 116675903 = 175013855) B175013855
theorem B1213520615 : Blo 1328983 1213520615 := bstep (se 1 (by rfl) ⟨910140461, by rfl⟩ : syracuseStep 1213520615 = 1820280923) B1820280923
theorem B10100537 : Blo 1328983 10100537 := bstep (se 2 (by rfl) ⟨3787701, by rfl⟩ : syracuseStep 10100537 = 7575403) B7575403
theorem B2990951 : Blo 1328983 2990951 := bstep (se 1 (by rfl) ⟨2243213, by rfl⟩ : syracuseStep 2990951 = 4486427) B4486427
theorem B77783935 : Blo 1328983 77783935 := bstep (se 1 (by rfl) ⟨58337951, by rfl⟩ : syracuseStep 77783935 = 116675903) B116675903
theorem B5047535 : Blo 1328983 5047535 := bstep (se 1 (by rfl) ⟨3785651, by rfl⟩ : syracuseStep 5047535 = 7571303) B7571303
theorem B7195367 : Blo 1328983 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B809013743 : Blo 1328983 809013743 := bstep (se 1 (by rfl) ⟨606760307, by rfl⟩ : syracuseStep 809013743 = 1213520615) B1213520615
theorem B131249321 : Blo 1328983 131249321 := bstep (se 2 (by rfl) ⟨49218495, by rfl⟩ : syracuseStep 131249321 = 98436991) B98436991
theorem B6733691 : Blo 1328983 6733691 := bstep (se 1 (by rfl) ⟨5050268, by rfl⟩ : syracuseStep 6733691 = 10100537) B10100537
theorem B87499547 : Blo 1328983 87499547 := bstep (se 1 (by rfl) ⟨65624660, by rfl⟩ : syracuseStep 87499547 = 131249321) B131249321
theorem B103711913 : Blo 1328983 103711913 := bstep (se 2 (by rfl) ⟨38891967, by rfl⟩ : syracuseStep 103711913 = 77783935) B77783935
theorem B1993967 : Blo 1328983 1993967 := bstep (se 1 (by rfl) ⟨1495475, by rfl⟩ : syracuseStep 1993967 = 2990951) B2990951
theorem B4796911 : Blo 1328983 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B539342495 : Blo 1328983 539342495 := bstep (se 1 (by rfl) ⟨404506871, by rfl⟩ : syracuseStep 539342495 = 809013743) B809013743
theorem B3365023 : Blo 1328983 3365023 := bstep (se 1 (by rfl) ⟨2523767, by rfl⟩ : syracuseStep 3365023 = 5047535) B5047535
theorem B4489127 : Blo 1328983 4489127 := bstep (se 1 (by rfl) ⟨3366845, by rfl⟩ : syracuseStep 4489127 = 6733691) B6733691
theorem B69141275 : Blo 1328983 69141275 := bstep (se 1 (by rfl) ⟨51855956, by rfl⟩ : syracuseStep 69141275 = 103711913) B103711913
theorem B1329311 : Blo 1328983 1329311 := bstep (se 1 (by rfl) ⟨996983, by rfl⟩ : syracuseStep 1329311 = 1993967) B1993967
theorem B2992751 : Blo 1328983 2992751 := bstep (se 1 (by rfl) ⟨2244563, by rfl⟩ : syracuseStep 2992751 = 4489127) B4489127
theorem B4486697 : Blo 1328983 4486697 := bstep (se 2 (by rfl) ⟨1682511, by rfl⟩ : syracuseStep 4486697 = 3365023) B3365023
theorem B58333031 : Blo 1328983 58333031 := bstep (se 1 (by rfl) ⟨43749773, by rfl⟩ : syracuseStep 58333031 = 87499547) B87499547
theorem B359561663 : Blo 1328983 359561663 := bstep (se 1 (by rfl) ⟨269671247, by rfl⟩ : syracuseStep 359561663 = 539342495) B539342495
theorem B25583525 : Blo 1328983 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B2991131 : Blo 1328983 2991131 := bstep (se 1 (by rfl) ⟨2243348, by rfl⟩ : syracuseStep 2991131 = 4486697) B4486697
theorem B38888687 : Blo 1328983 38888687 := bstep (se 1 (by rfl) ⟨29166515, by rfl⟩ : syracuseStep 38888687 = 58333031) B58333031
theorem B239707775 : Blo 1328983 239707775 := bstep (se 1 (by rfl) ⟨179780831, by rfl⟩ : syracuseStep 239707775 = 359561663) B359561663
theorem B1995167 : Blo 1328983 1995167 := bstep (se 1 (by rfl) ⟨1496375, by rfl⟩ : syracuseStep 1995167 = 2992751) B2992751
theorem B46094183 : Blo 1328983 46094183 := bstep (se 1 (by rfl) ⟨34570637, by rfl⟩ : syracuseStep 46094183 = 69141275) B69141275
theorem B17055683 : Blo 1328983 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B30729455 : Blo 1328983 30729455 := bstep (se 1 (by rfl) ⟨23047091, by rfl⟩ : syracuseStep 30729455 = 46094183) B46094183
theorem B1330111 : Blo 1328983 1330111 := bstep (se 1 (by rfl) ⟨997583, by rfl⟩ : syracuseStep 1330111 = 1995167) B1995167
theorem B1994087 : Blo 1328983 1994087 := bstep (se 1 (by rfl) ⟨1495565, by rfl⟩ : syracuseStep 1994087 = 2991131) B2991131
theorem B25925791 : Blo 1328983 25925791 := bstep (se 1 (by rfl) ⟨19444343, by rfl⟩ : syracuseStep 25925791 = 38888687) B38888687
theorem B639220733 : Blo 1328983 639220733 := bstep (se 3 (by rfl) ⟨119853887, by rfl⟩ : syracuseStep 639220733 = 239707775) B239707775
theorem B11370455 : Blo 1328983 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B1329391 : Blo 1328983 1329391 := bstep (se 1 (by rfl) ⟨997043, by rfl⟩ : syracuseStep 1329391 = 1994087) B1994087
theorem B7580303 : Blo 1328983 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B34567721 : Blo 1328983 34567721 := bstep (se 2 (by rfl) ⟨12962895, by rfl⟩ : syracuseStep 34567721 = 25925791) B25925791
theorem B20486303 : Blo 1328983 20486303 := bstep (se 1 (by rfl) ⟨15364727, by rfl⟩ : syracuseStep 20486303 = 30729455) B30729455
theorem B426147155 : Blo 1328983 426147155 := bstep (se 1 (by rfl) ⟨319610366, by rfl⟩ : syracuseStep 426147155 = 639220733) B639220733
theorem B23045147 : Blo 1328983 23045147 := bstep (se 1 (by rfl) ⟨17283860, by rfl⟩ : syracuseStep 23045147 = 34567721) B34567721
theorem B13657535 : Blo 1328983 13657535 := bstep (se 1 (by rfl) ⟨10243151, by rfl⟩ : syracuseStep 13657535 = 20486303) B20486303
theorem B5053535 : Blo 1328983 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B284098103 : Blo 1328983 284098103 := bstep (se 1 (by rfl) ⟨213073577, by rfl⟩ : syracuseStep 284098103 = 426147155) B426147155
theorem B3369023 : Blo 1328983 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B15363431 : Blo 1328983 15363431 := bstep (se 1 (by rfl) ⟨11522573, by rfl⟩ : syracuseStep 15363431 = 23045147) B23045147
theorem B9105023 : Blo 1328983 9105023 := bstep (se 1 (by rfl) ⟨6828767, by rfl⟩ : syracuseStep 9105023 = 13657535) B13657535
theorem B189398735 : Blo 1328983 189398735 := bstep (se 1 (by rfl) ⟨142049051, by rfl⟩ : syracuseStep 189398735 = 284098103) B284098103
theorem B2246015 : Blo 1328983 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B10242287 : Blo 1328983 10242287 := bstep (se 1 (by rfl) ⟨7681715, by rfl⟩ : syracuseStep 10242287 = 15363431) B15363431
theorem B126265823 : Blo 1328983 126265823 := bstep (se 1 (by rfl) ⟨94699367, by rfl⟩ : syracuseStep 126265823 = 189398735) B189398735
theorem B6070015 : Blo 1328983 6070015 := bstep (se 1 (by rfl) ⟨4552511, by rfl⟩ : syracuseStep 6070015 = 9105023) B9105023
theorem B6828191 : Blo 1328983 6828191 := bstep (se 1 (by rfl) ⟨5121143, by rfl⟩ : syracuseStep 6828191 = 10242287) B10242287
theorem B84177215 : Blo 1328983 84177215 := bstep (se 1 (by rfl) ⟨63132911, by rfl⟩ : syracuseStep 84177215 = 126265823) B126265823
theorem B1497343 : Blo 1328983 1497343 := bstep (se 1 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 1497343 = 2246015) B2246015
theorem B8093353 : Blo 1328983 8093353 := bstep (se 2 (by rfl) ⟨3035007, by rfl⟩ : syracuseStep 8093353 = 6070015) B6070015
theorem B10791137 : Blo 1328983 10791137 := bstep (se 2 (by rfl) ⟨4046676, by rfl⟩ : syracuseStep 10791137 = 8093353) B8093353
theorem B56118143 : Blo 1328983 56118143 := bstep (se 1 (by rfl) ⟨42088607, by rfl⟩ : syracuseStep 56118143 = 84177215) B84177215
theorem B4552127 : Blo 1328983 4552127 := bstep (se 1 (by rfl) ⟨3414095, by rfl⟩ : syracuseStep 4552127 = 6828191) B6828191
theorem B1996457 : Blo 1328983 1996457 := bstep (se 2 (by rfl) ⟨748671, by rfl⟩ : syracuseStep 1996457 = 1497343) B1497343
theorem B7194091 : Blo 1328983 7194091 := bstep (se 1 (by rfl) ⟨5395568, by rfl⟩ : syracuseStep 7194091 = 10791137) B10791137
theorem B3034751 : Blo 1328983 3034751 := bstep (se 1 (by rfl) ⟨2276063, by rfl⟩ : syracuseStep 3034751 = 4552127) B4552127
theorem B1330971 : Blo 1328983 1330971 := bstep (se 1 (by rfl) ⟨998228, by rfl⟩ : syracuseStep 1330971 = 1996457) B1996457
theorem B149648381 : Blo 1328983 149648381 := bstep (se 3 (by rfl) ⟨28059071, by rfl⟩ : syracuseStep 149648381 = 56118143) B56118143
theorem B99765587 : Blo 1328983 99765587 := bstep (se 1 (by rfl) ⟨74824190, by rfl⟩ : syracuseStep 99765587 = 149648381) B149648381
theorem B32370677 : Blo 1328983 32370677 := bstep (se 5 (by rfl) ⟨1517375, by rfl⟩ : syracuseStep 32370677 = 3034751) B3034751
theorem B9592121 : Blo 1328983 9592121 := bstep (se 2 (by rfl) ⟨3597045, by rfl⟩ : syracuseStep 9592121 = 7194091) B7194091
theorem B21580451 : Blo 1328983 21580451 := bstep (se 1 (by rfl) ⟨16185338, by rfl⟩ : syracuseStep 21580451 = 32370677) B32370677
theorem B6394747 : Blo 1328983 6394747 := bstep (se 1 (by rfl) ⟨4796060, by rfl⟩ : syracuseStep 6394747 = 9592121) B9592121
theorem B66510391 : Blo 1328983 66510391 := bstep (se 1 (by rfl) ⟨49882793, by rfl⟩ : syracuseStep 66510391 = 99765587) B99765587
theorem B14386967 : Blo 1328983 14386967 := bstep (se 1 (by rfl) ⟨10790225, by rfl⟩ : syracuseStep 14386967 = 21580451) B21580451
theorem B88680521 : Blo 1328983 88680521 := bstep (se 2 (by rfl) ⟨33255195, by rfl⟩ : syracuseStep 88680521 = 66510391) B66510391
theorem B8526329 : Blo 1328983 8526329 := bstep (se 2 (by rfl) ⟨3197373, by rfl⟩ : syracuseStep 8526329 = 6394747) B6394747
theorem B236481389 : Blo 1328983 236481389 := bstep (se 3 (by rfl) ⟨44340260, by rfl⟩ : syracuseStep 236481389 = 88680521) B88680521
theorem B9591311 : Blo 1328983 9591311 := bstep (se 1 (by rfl) ⟨7193483, by rfl⟩ : syracuseStep 9591311 = 14386967) B14386967
theorem B5684219 : Blo 1328983 5684219 := bstep (se 1 (by rfl) ⟨4263164, by rfl⟩ : syracuseStep 5684219 = 8526329) B8526329
theorem B25576829 : Blo 1328983 25576829 := bstep (se 3 (by rfl) ⟨4795655, by rfl⟩ : syracuseStep 25576829 = 9591311) B9591311
theorem B3789479 : Blo 1328983 3789479 := bstep (se 1 (by rfl) ⟨2842109, by rfl⟩ : syracuseStep 3789479 = 5684219) B5684219
theorem B157654259 : Blo 1328983 157654259 := bstep (se 1 (by rfl) ⟨118240694, by rfl⟩ : syracuseStep 157654259 = 236481389) B236481389
theorem B2526319 : Blo 1328983 2526319 := bstep (se 1 (by rfl) ⟨1894739, by rfl⟩ : syracuseStep 2526319 = 3789479) B3789479
theorem B17051219 : Blo 1328983 17051219 := bstep (se 1 (by rfl) ⟨12788414, by rfl⟩ : syracuseStep 17051219 = 25576829) B25576829
theorem B105102839 : Blo 1328983 105102839 := bstep (se 1 (by rfl) ⟨78827129, by rfl⟩ : syracuseStep 105102839 = 157654259) B157654259
theorem B3368425 : Blo 1328983 3368425 := bstep (se 2 (by rfl) ⟨1263159, by rfl⟩ : syracuseStep 3368425 = 2526319) B2526319
theorem B70068559 : Blo 1328983 70068559 := bstep (se 1 (by rfl) ⟨52551419, by rfl⟩ : syracuseStep 70068559 = 105102839) B105102839
theorem B11367479 : Blo 1328983 11367479 := bstep (se 1 (by rfl) ⟨8525609, by rfl⟩ : syracuseStep 11367479 = 17051219) B17051219
theorem B7578319 : Blo 1328983 7578319 := bstep (se 1 (by rfl) ⟨5683739, by rfl⟩ : syracuseStep 7578319 = 11367479) B11367479
theorem B4491233 : Blo 1328983 4491233 := bstep (se 2 (by rfl) ⟨1684212, by rfl⟩ : syracuseStep 4491233 = 3368425) B3368425
theorem B93424745 : Blo 1328983 93424745 := bstep (se 2 (by rfl) ⟨35034279, by rfl⟩ : syracuseStep 93424745 = 70068559) B70068559
theorem B10104425 : Blo 1328983 10104425 := bstep (se 2 (by rfl) ⟨3789159, by rfl⟩ : syracuseStep 10104425 = 7578319) B7578319
theorem B2994155 : Blo 1328983 2994155 := bstep (se 1 (by rfl) ⟨2245616, by rfl⟩ : syracuseStep 2994155 = 4491233) B4491233
theorem B62283163 : Blo 1328983 62283163 := bstep (se 1 (by rfl) ⟨46712372, by rfl⟩ : syracuseStep 62283163 = 93424745) B93424745
theorem B83044217 : Blo 1328983 83044217 := bstep (se 2 (by rfl) ⟨31141581, by rfl⟩ : syracuseStep 83044217 = 62283163) B62283163
theorem B6736283 : Blo 1328983 6736283 := bstep (se 1 (by rfl) ⟨5052212, by rfl⟩ : syracuseStep 6736283 = 10104425) B10104425
theorem B1996103 : Blo 1328983 1996103 := bstep (se 1 (by rfl) ⟨1497077, by rfl⟩ : syracuseStep 1996103 = 2994155) B2994155
theorem B55362811 : Blo 1328983 55362811 := bstep (se 1 (by rfl) ⟨41522108, by rfl⟩ : syracuseStep 55362811 = 83044217) B83044217
theorem B4490855 : Blo 1328983 4490855 := bstep (se 1 (by rfl) ⟨3368141, by rfl⟩ : syracuseStep 4490855 = 6736283) B6736283
theorem B1330735 : Blo 1328983 1330735 := bstep (se 1 (by rfl) ⟨998051, by rfl⟩ : syracuseStep 1330735 = 1996103) B1996103
theorem B2993903 : Blo 1328983 2993903 := bstep (se 1 (by rfl) ⟨2245427, by rfl⟩ : syracuseStep 2993903 = 4490855) B4490855
theorem B73817081 : Blo 1328983 73817081 := bstep (se 2 (by rfl) ⟨27681405, by rfl⟩ : syracuseStep 73817081 = 55362811) B55362811
theorem B49211387 : Blo 1328983 49211387 := bstep (se 1 (by rfl) ⟨36908540, by rfl⟩ : syracuseStep 49211387 = 73817081) B73817081
theorem B1995935 : Blo 1328983 1995935 := bstep (se 1 (by rfl) ⟨1496951, by rfl⟩ : syracuseStep 1995935 = 2993903) B2993903
theorem B1330623 : Blo 1328983 1330623 := bstep (se 1 (by rfl) ⟨997967, by rfl⟩ : syracuseStep 1330623 = 1995935) B1995935
theorem B32807591 : Blo 1328983 32807591 := bstep (se 1 (by rfl) ⟨24605693, by rfl⟩ : syracuseStep 32807591 = 49211387) B49211387
theorem B21871727 : Blo 1328983 21871727 := bstep (se 1 (by rfl) ⟨16403795, by rfl⟩ : syracuseStep 21871727 = 32807591) B32807591
theorem B14581151 : Blo 1328983 14581151 := bstep (se 1 (by rfl) ⟨10935863, by rfl⟩ : syracuseStep 14581151 = 21871727) B21871727
theorem B9720767 : Blo 1328983 9720767 := bstep (se 1 (by rfl) ⟨7290575, by rfl⟩ : syracuseStep 9720767 = 14581151) B14581151
theorem B25922045 : Blo 1328983 25922045 := bstep (se 3 (by rfl) ⟨4860383, by rfl⟩ : syracuseStep 25922045 = 9720767) B9720767
theorem B17281363 : Blo 1328983 17281363 := bstep (se 1 (by rfl) ⟨12961022, by rfl⟩ : syracuseStep 17281363 = 25922045) B25922045
theorem B23041817 : Blo 1328983 23041817 := bstep (se 2 (by rfl) ⟨8640681, by rfl⟩ : syracuseStep 23041817 = 17281363) B17281363
theorem B15361211 : Blo 1328983 15361211 := bstep (se 1 (by rfl) ⟨11520908, by rfl⟩ : syracuseStep 15361211 = 23041817) B23041817
theorem B40963229 : Blo 1328983 40963229 := bstep (se 3 (by rfl) ⟨7680605, by rfl⟩ : syracuseStep 40963229 = 15361211) B15361211
theorem B27308819 : Blo 1328983 27308819 := bstep (se 1 (by rfl) ⟨20481614, by rfl⟩ : syracuseStep 27308819 = 40963229) B40963229
theorem B18205879 : Blo 1328983 18205879 := bstep (se 1 (by rfl) ⟨13654409, by rfl⟩ : syracuseStep 18205879 = 27308819) B27308819
theorem B24274505 : Blo 1328983 24274505 := bstep (se 2 (by rfl) ⟨9102939, by rfl⟩ : syracuseStep 24274505 = 18205879) B18205879
theorem B16183003 : Blo 1328983 16183003 := bstep (se 1 (by rfl) ⟨12137252, by rfl⟩ : syracuseStep 16183003 = 24274505) B24274505
theorem B21577337 : Blo 1328983 21577337 := bstep (se 2 (by rfl) ⟨8091501, by rfl⟩ : syracuseStep 21577337 = 16183003) B16183003
theorem B14384891 : Blo 1328983 14384891 := bstep (se 1 (by rfl) ⟨10788668, by rfl⟩ : syracuseStep 14384891 = 21577337) B21577337
theorem B9589927 : Blo 1328983 9589927 := bstep (se 1 (by rfl) ⟨7192445, by rfl⟩ : syracuseStep 9589927 = 14384891) B14384891
theorem B12786569 : Blo 1328983 12786569 := bstep (se 2 (by rfl) ⟨4794963, by rfl⟩ : syracuseStep 12786569 = 9589927) B9589927
theorem B8524379 : Blo 1328983 8524379 := bstep (se 1 (by rfl) ⟨6393284, by rfl⟩ : syracuseStep 8524379 = 12786569) B12786569
theorem B22731677 : Blo 1328983 22731677 := bstep (se 3 (by rfl) ⟨4262189, by rfl⟩ : syracuseStep 22731677 = 8524379) B8524379
theorem B15154451 : Blo 1328983 15154451 := bstep (se 1 (by rfl) ⟨11365838, by rfl⟩ : syracuseStep 15154451 = 22731677) B22731677
theorem B10102967 : Blo 1328983 10102967 := bstep (se 1 (by rfl) ⟨7577225, by rfl⟩ : syracuseStep 10102967 = 15154451) B15154451
theorem B6735311 : Blo 1328983 6735311 := bstep (se 1 (by rfl) ⟨5051483, by rfl⟩ : syracuseStep 6735311 = 10102967) B10102967
theorem B4490207 : Blo 1328983 4490207 := bstep (se 1 (by rfl) ⟨3367655, by rfl⟩ : syracuseStep 4490207 = 6735311) B6735311
theorem B2993471 : Blo 1328983 2993471 := bstep (se 1 (by rfl) ⟨2245103, by rfl⟩ : syracuseStep 2993471 = 4490207) B4490207
theorem B1995647 : Blo 1328983 1995647 := bstep (se 1 (by rfl) ⟨1496735, by rfl⟩ : syracuseStep 1995647 = 2993471) B2993471
theorem B1330431 : Blo 1328983 1330431 := bstep (se 1 (by rfl) ⟨997823, by rfl⟩ : syracuseStep 1330431 = 1995647) B1995647

theorem C0 (j : ℕ) (h1 : 332245 ≤ j) (h2 : j ≤ 332745) : Blo 1328983 (4 * j + 3) := by
  interval_cases j
  · exact B1328983
  · exact B1328987
  · exact B1328991
  · exact B1328995
  · exact B1328999
  · exact B1329003
  · exact B1329007
  · exact B1329011
  · exact B1329015
  · exact B1329019
  · exact B1329023
  · exact B1329027
  · exact B1329031
  · exact B1329035
  · exact B1329039
  · exact B1329043
  · exact B1329047
  · exact B1329051
  · exact B1329055
  · exact B1329059
  · exact B1329063
  · exact B1329067
  · exact B1329071
  · exact B1329075
  · exact B1329079
  · exact B1329083
  · exact B1329087
  · exact B1329091
  · exact B1329095
  · exact B1329099
  · exact B1329103
  · exact B1329107
  · exact B1329111
  · exact B1329115
  · exact B1329119
  · exact B1329123
  · exact B1329127
  · exact B1329131
  · exact B1329135
  · exact B1329139
  · exact B1329143
  · exact B1329147
  · exact B1329151
  · exact B1329155
  · exact B1329159
  · exact B1329163
  · exact B1329167
  · exact B1329171
  · exact B1329175
  · exact B1329179
  · exact B1329183
  · exact B1329187
  · exact B1329191
  · exact B1329195
  · exact B1329199
  · exact B1329203
  · exact B1329207
  · exact B1329211
  · exact B1329215
  · exact B1329219
  · exact B1329223
  · exact B1329227
  · exact B1329231
  · exact B1329235
  · exact B1329239
  · exact B1329243
  · exact B1329247
  · exact B1329251
  · exact B1329255
  · exact B1329259
  · exact B1329263
  · exact B1329267
  · exact B1329271
  · exact B1329275
  · exact B1329279
  · exact B1329283
  · exact B1329287
  · exact B1329291
  · exact B1329295
  · exact B1329299
  · exact B1329303
  · exact B1329307
  · exact B1329311
  · exact B1329315
  · exact B1329319
  · exact B1329323
  · exact B1329327
  · exact B1329331
  · exact B1329335
  · exact B1329339
  · exact B1329343
  · exact B1329347
  · exact B1329351
  · exact B1329355
  · exact B1329359
  · exact B1329363
  · exact B1329367
  · exact B1329371
  · exact B1329375
  · exact B1329379
  · exact B1329383
  · exact B1329387
  · exact B1329391
  · exact B1329395
  · exact B1329399
  · exact B1329403
  · exact B1329407
  · exact B1329411
  · exact B1329415
  · exact B1329419
  · exact B1329423
  · exact B1329427
  · exact B1329431
  · exact B1329435
  · exact B1329439
  · exact B1329443
  · exact B1329447
  · exact B1329451
  · exact B1329455
  · exact B1329459
  · exact B1329463
  · exact B1329467
  · exact B1329471
  · exact B1329475
  · exact B1329479
  · exact B1329483
  · exact B1329487
  · exact B1329491
  · exact B1329495
  · exact B1329499
  · exact B1329503
  · exact B1329507
  · exact B1329511
  · exact B1329515
  · exact B1329519
  · exact B1329523
  · exact B1329527
  · exact B1329531
  · exact B1329535
  · exact B1329539
  · exact B1329543
  · exact B1329547
  · exact B1329551
  · exact B1329555
  · exact B1329559
  · exact B1329563
  · exact B1329567
  · exact B1329571
  · exact B1329575
  · exact B1329579
  · exact B1329583
  · exact B1329587
  · exact B1329591
  · exact B1329595
  · exact B1329599
  · exact B1329603
  · exact B1329607
  · exact B1329611
  · exact B1329615
  · exact B1329619
  · exact B1329623
  · exact B1329627
  · exact B1329631
  · exact B1329635
  · exact B1329639
  · exact B1329643
  · exact B1329647
  · exact B1329651
  · exact B1329655
  · exact B1329659
  · exact B1329663
  · exact B1329667
  · exact B1329671
  · exact B1329675
  · exact B1329679
  · exact B1329683
  · exact B1329687
  · exact B1329691
  · exact B1329695
  · exact B1329699
  · exact B1329703
  · exact B1329707
  · exact B1329711
  · exact B1329715
  · exact B1329719
  · exact B1329723
  · exact B1329727
  · exact B1329731
  · exact B1329735
  · exact B1329739
  · exact B1329743
  · exact B1329747
  · exact B1329751
  · exact B1329755
  · exact B1329759
  · exact B1329763
  · exact B1329767
  · exact B1329771
  · exact B1329775
  · exact B1329779
  · exact B1329783
  · exact B1329787
  · exact B1329791
  · exact B1329795
  · exact B1329799
  · exact B1329803
  · exact B1329807
  · exact B1329811
  · exact B1329815
  · exact B1329819
  · exact B1329823
  · exact B1329827
  · exact B1329831
  · exact B1329835
  · exact B1329839
  · exact B1329843
  · exact B1329847
  · exact B1329851
  · exact B1329855
  · exact B1329859
  · exact B1329863
  · exact B1329867
  · exact B1329871
  · exact B1329875
  · exact B1329879
  · exact B1329883
  · exact B1329887
  · exact B1329891
  · exact B1329895
  · exact B1329899
  · exact B1329903
  · exact B1329907
  · exact B1329911
  · exact B1329915
  · exact B1329919
  · exact B1329923
  · exact B1329927
  · exact B1329931
  · exact B1329935
  · exact B1329939
  · exact B1329943
  · exact B1329947
  · exact B1329951
  · exact B1329955
  · exact B1329959
  · exact B1329963
  · exact B1329967
  · exact B1329971
  · exact B1329975
  · exact B1329979
  · exact B1329983
  · exact B1329987
  · exact B1329991
  · exact B1329995
  · exact B1329999
  · exact B1330003
  · exact B1330007
  · exact B1330011
  · exact B1330015
  · exact B1330019
  · exact B1330023
  · exact B1330027
  · exact B1330031
  · exact B1330035
  · exact B1330039
  · exact B1330043
  · exact B1330047
  · exact B1330051
  · exact B1330055
  · exact B1330059
  · exact B1330063
  · exact B1330067
  · exact B1330071
  · exact B1330075
  · exact B1330079
  · exact B1330083
  · exact B1330087
  · exact B1330091
  · exact B1330095
  · exact B1330099
  · exact B1330103
  · exact B1330107
  · exact B1330111
  · exact B1330115
  · exact B1330119
  · exact B1330123
  · exact B1330127
  · exact B1330131
  · exact B1330135
  · exact B1330139
  · exact B1330143
  · exact B1330147
  · exact B1330151
  · exact B1330155
  · exact B1330159
  · exact B1330163
  · exact B1330167
  · exact B1330171
  · exact B1330175
  · exact B1330179
  · exact B1330183
  · exact B1330187
  · exact B1330191
  · exact B1330195
  · exact B1330199
  · exact B1330203
  · exact B1330207
  · exact B1330211
  · exact B1330215
  · exact B1330219
  · exact B1330223
  · exact B1330227
  · exact B1330231
  · exact B1330235
  · exact B1330239
  · exact B1330243
  · exact B1330247
  · exact B1330251
  · exact B1330255
  · exact B1330259
  · exact B1330263
  · exact B1330267
  · exact B1330271
  · exact B1330275
  · exact B1330279
  · exact B1330283
  · exact B1330287
  · exact B1330291
  · exact B1330295
  · exact B1330299
  · exact B1330303
  · exact B1330307
  · exact B1330311
  · exact B1330315
  · exact B1330319
  · exact B1330323
  · exact B1330327
  · exact B1330331
  · exact B1330335
  · exact B1330339
  · exact B1330343
  · exact B1330347
  · exact B1330351
  · exact B1330355
  · exact B1330359
  · exact B1330363
  · exact B1330367
  · exact B1330371
  · exact B1330375
  · exact B1330379
  · exact B1330383
  · exact B1330387
  · exact B1330391
  · exact B1330395
  · exact B1330399
  · exact B1330403
  · exact B1330407
  · exact B1330411
  · exact B1330415
  · exact B1330419
  · exact B1330423
  · exact B1330427
  · exact B1330431
  · exact B1330435
  · exact B1330439
  · exact B1330443
  · exact B1330447
  · exact B1330451
  · exact B1330455
  · exact B1330459
  · exact B1330463
  · exact B1330467
  · exact B1330471
  · exact B1330475
  · exact B1330479
  · exact B1330483
  · exact B1330487
  · exact B1330491
  · exact B1330495
  · exact B1330499
  · exact B1330503
  · exact B1330507
  · exact B1330511
  · exact B1330515
  · exact B1330519
  · exact B1330523
  · exact B1330527
  · exact B1330531
  · exact B1330535
  · exact B1330539
  · exact B1330543
  · exact B1330547
  · exact B1330551
  · exact B1330555
  · exact B1330559
  · exact B1330563
  · exact B1330567
  · exact B1330571
  · exact B1330575
  · exact B1330579
  · exact B1330583
  · exact B1330587
  · exact B1330591
  · exact B1330595
  · exact B1330599
  · exact B1330603
  · exact B1330607
  · exact B1330611
  · exact B1330615
  · exact B1330619
  · exact B1330623
  · exact B1330627
  · exact B1330631
  · exact B1330635
  · exact B1330639
  · exact B1330643
  · exact B1330647
  · exact B1330651
  · exact B1330655
  · exact B1330659
  · exact B1330663
  · exact B1330667
  · exact B1330671
  · exact B1330675
  · exact B1330679
  · exact B1330683
  · exact B1330687
  · exact B1330691
  · exact B1330695
  · exact B1330699
  · exact B1330703
  · exact B1330707
  · exact B1330711
  · exact B1330715
  · exact B1330719
  · exact B1330723
  · exact B1330727
  · exact B1330731
  · exact B1330735
  · exact B1330739
  · exact B1330743
  · exact B1330747
  · exact B1330751
  · exact B1330755
  · exact B1330759
  · exact B1330763
  · exact B1330767
  · exact B1330771
  · exact B1330775
  · exact B1330779
  · exact B1330783
  · exact B1330787
  · exact B1330791
  · exact B1330795
  · exact B1330799
  · exact B1330803
  · exact B1330807
  · exact B1330811
  · exact B1330815
  · exact B1330819
  · exact B1330823
  · exact B1330827
  · exact B1330831
  · exact B1330835
  · exact B1330839
  · exact B1330843
  · exact B1330847
  · exact B1330851
  · exact B1330855
  · exact B1330859
  · exact B1330863
  · exact B1330867
  · exact B1330871
  · exact B1330875
  · exact B1330879
  · exact B1330883
  · exact B1330887
  · exact B1330891
  · exact B1330895
  · exact B1330899
  · exact B1330903
  · exact B1330907
  · exact B1330911
  · exact B1330915
  · exact B1330919
  · exact B1330923
  · exact B1330927
  · exact B1330931
  · exact B1330935
  · exact B1330939
  · exact B1330943
  · exact B1330947
  · exact B1330951
  · exact B1330955
  · exact B1330959
  · exact B1330963
  · exact B1330967
  · exact B1330971
  · exact B1330975
  · exact B1330979
  · exact B1330983

theorem solution (m : ℕ) (hlo : 1328983 ≤ m) (hhi : m ≤ 1330983) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 332245 ≤ j := by omega
    have hj2 : j ≤ 332745 := by omega
    have hb : Blo 1328983 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
