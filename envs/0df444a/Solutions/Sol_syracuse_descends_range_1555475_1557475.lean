-- Prove2me | solution 1 for syracuse_descends_range_1555475_1557475
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:58.804797+00:00
-- url     : https://prove2.me/submissions/d3c5ff11-4501-4c62-bb86-da0b41937aa7

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


theorem B2334725 : Blo 1555475 2334725 := bbase (se 4 (by rfl) ⟨218880, by rfl⟩ : syracuseStep 2334725 = 437761) (by norm_num)
theorem B9469973 : Blo 1555475 9469973 := bbase (se 6 (by rfl) ⟨221952, by rfl⟩ : syracuseStep 9469973 = 443905) (by norm_num)
theorem B2334749 : Blo 1555475 2334749 := bbase (se 3 (by rfl) ⟨437765, by rfl⟩ : syracuseStep 2334749 = 875531) (by norm_num)
theorem B2662445 : Blo 1555475 2662445 := bbase (se 3 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 2662445 = 998417) (by norm_num)
theorem B3940397 : Blo 1555475 3940397 := bbase (se 3 (by rfl) ⟨738824, by rfl⟩ : syracuseStep 3940397 = 1477649) (by norm_num)
theorem B3153973 : Blo 1555475 3153973 := bbase (se 5 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 3153973 = 295685) (by norm_num)
theorem B2334773 : Blo 1555475 2334773 := bbase (se 5 (by rfl) ⟨109442, by rfl⟩ : syracuseStep 2334773 = 218885) (by norm_num)
theorem B2334797 : Blo 1555475 2334797 := bbase (se 3 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 2334797 = 875549) (by norm_num)
theorem B9969749 : Blo 1555475 9969749 := bbase (se 8 (by rfl) ⟨58416, by rfl⟩ : syracuseStep 9969749 = 116833) (by norm_num)
theorem B2334821 : Blo 1555475 2334821 := bbase (se 4 (by rfl) ⟨218889, by rfl⟩ : syracuseStep 2334821 = 437779) (by norm_num)
theorem B2334845 : Blo 1555475 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B2334869 : Blo 1555475 2334869 := bbase (se 6 (by rfl) ⟨54723, by rfl⟩ : syracuseStep 2334869 = 109447) (by norm_num)
theorem B2334893 : Blo 1555475 2334893 := bbase (se 3 (by rfl) ⟨437792, by rfl⟩ : syracuseStep 2334893 = 875585) (by norm_num)
theorem B2334917 : Blo 1555475 2334917 := bbase (se 4 (by rfl) ⟨218898, by rfl⟩ : syracuseStep 2334917 = 437797) (by norm_num)
theorem B2334941 : Blo 1555475 2334941 := bbase (se 3 (by rfl) ⟨437801, by rfl⟩ : syracuseStep 2334941 = 875603) (by norm_num)
theorem B3940589 : Blo 1555475 3940589 := bbase (se 3 (by rfl) ⟨738860, by rfl⟩ : syracuseStep 3940589 = 1477721) (by norm_num)
theorem B2334965 : Blo 1555475 2334965 := bbase (se 5 (by rfl) ⟨109451, by rfl⟩ : syracuseStep 2334965 = 218903) (by norm_num)
theorem B2334989 : Blo 1555475 2334989 := bbase (se 3 (by rfl) ⟨437810, by rfl⟩ : syracuseStep 2334989 = 875621) (by norm_num)
theorem B2335013 : Blo 1555475 2335013 := bbase (se 4 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 2335013 = 437815) (by norm_num)
theorem B2335037 : Blo 1555475 2335037 := bbase (se 3 (by rfl) ⟨437819, by rfl⟩ : syracuseStep 2335037 = 875639) (by norm_num)
theorem B2335061 : Blo 1555475 2335061 := bbase (se 10 (by rfl) ⟨3420, by rfl⟩ : syracuseStep 2335061 = 6841) (by norm_num)
theorem B4432229 : Blo 1555475 4432229 := bbase (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) (by norm_num)
theorem B2335085 : Blo 1555475 2335085 := bbase (se 3 (by rfl) ⟨437828, by rfl⟩ : syracuseStep 2335085 = 875657) (by norm_num)
theorem B5251445 : Blo 1555475 5251445 := bbase (se 5 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 5251445 = 492323) (by norm_num)
theorem B2335109 : Blo 1555475 2335109 := bbase (se 4 (by rfl) ⟨218916, by rfl⟩ : syracuseStep 2335109 = 437833) (by norm_num)
theorem B2335133 : Blo 1555475 2335133 := bbase (se 3 (by rfl) ⟨437837, by rfl⟩ : syracuseStep 2335133 = 875675) (by norm_num)
theorem B2335157 : Blo 1555475 2335157 := bbase (se 5 (by rfl) ⟨109460, by rfl⟩ : syracuseStep 2335157 = 218921) (by norm_num)
theorem B2245069 : Blo 1555475 2245069 := bbase (se 3 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 2245069 = 841901) (by norm_num)
theorem B2335181 : Blo 1555475 2335181 := bbase (se 3 (by rfl) ⟨437846, by rfl⟩ : syracuseStep 2335181 = 875693) (by norm_num)
theorem B2335205 : Blo 1555475 2335205 := bbase (se 4 (by rfl) ⟨218925, by rfl⟩ : syracuseStep 2335205 = 437851) (by norm_num)
theorem B2335229 : Blo 1555475 2335229 := bbase (se 3 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 2335229 = 875711) (by norm_num)
theorem B5906965 : Blo 1555475 5906965 := bbase (se 6 (by rfl) ⟨138444, by rfl⟩ : syracuseStep 5906965 = 276889) (by norm_num)
theorem B2335253 : Blo 1555475 2335253 := bbase (se 6 (by rfl) ⟨54732, by rfl⟩ : syracuseStep 2335253 = 109465) (by norm_num)
theorem B2335277 : Blo 1555475 2335277 := bbase (se 3 (by rfl) ⟨437864, by rfl⟩ : syracuseStep 2335277 = 875729) (by norm_num)
theorem B2335301 : Blo 1555475 2335301 := bbase (se 4 (by rfl) ⟨218934, by rfl⟩ : syracuseStep 2335301 = 437869) (by norm_num)
theorem B3940933 : Blo 1555475 3940933 := bbase (se 4 (by rfl) ⟨369462, by rfl⟩ : syracuseStep 3940933 = 738925) (by norm_num)
theorem B2335325 : Blo 1555475 2335325 := bbase (se 3 (by rfl) ⟨437873, by rfl⟩ : syracuseStep 2335325 = 875747) (by norm_num)
theorem B2335349 : Blo 1555475 2335349 := bbase (se 5 (by rfl) ⟨109469, by rfl⟩ : syracuseStep 2335349 = 218939) (by norm_num)
theorem B2335373 : Blo 1555475 2335373 := bbase (se 3 (by rfl) ⟨437882, by rfl⟩ : syracuseStep 2335373 = 875765) (by norm_num)
theorem B2335397 : Blo 1555475 2335397 := bbase (se 4 (by rfl) ⟨218943, by rfl⟩ : syracuseStep 2335397 = 437887) (by norm_num)
theorem B3941045 : Blo 1555475 3941045 := bbase (se 5 (by rfl) ⟨184736, by rfl⟩ : syracuseStep 3941045 = 369473) (by norm_num)
theorem B2335421 : Blo 1555475 2335421 := bbase (se 3 (by rfl) ⟨437891, by rfl⟩ : syracuseStep 2335421 = 875783) (by norm_num)
theorem B2335445 : Blo 1555475 2335445 := bbase (se 7 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 2335445 = 54737) (by norm_num)
theorem B2335469 : Blo 1555475 2335469 := bbase (se 3 (by rfl) ⟨437900, by rfl⟩ : syracuseStep 2335469 = 875801) (by norm_num)
theorem B7881461 : Blo 1555475 7881461 := bbase (se 5 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 7881461 = 738887) (by norm_num)
theorem B2335493 : Blo 1555475 2335493 := bbase (se 4 (by rfl) ⟨218952, by rfl⟩ : syracuseStep 2335493 = 437905) (by norm_num)
theorem B6644501 : Blo 1555475 6644501 := bbase (se 6 (by rfl) ⟨155730, by rfl⟩ : syracuseStep 6644501 = 311461) (by norm_num)
theorem B2335517 : Blo 1555475 2335517 := bbase (se 3 (by rfl) ⟨437909, by rfl⟩ : syracuseStep 2335517 = 875819) (by norm_num)
theorem B5251877 : Blo 1555475 5251877 := bbase (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) (by norm_num)
theorem B9462581 : Blo 1555475 9462581 := bbase (se 5 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 9462581 = 887117) (by norm_num)
theorem B2335541 : Blo 1555475 2335541 := bbase (se 5 (by rfl) ⟨109478, by rfl⟩ : syracuseStep 2335541 = 218957) (by norm_num)
theorem B5907269 : Blo 1555475 5907269 := bbase (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) (by norm_num)
theorem B2335565 : Blo 1555475 2335565 := bbase (se 3 (by rfl) ⟨437918, by rfl⟩ : syracuseStep 2335565 = 875837) (by norm_num)
theorem B2335589 : Blo 1555475 2335589 := bbase (se 4 (by rfl) ⟨218961, by rfl⟩ : syracuseStep 2335589 = 437923) (by norm_num)
theorem B3941237 : Blo 1555475 3941237 := bbase (se 5 (by rfl) ⟨184745, by rfl⟩ : syracuseStep 3941237 = 369491) (by norm_num)
theorem B2335613 : Blo 1555475 2335613 := bbase (se 3 (by rfl) ⟨437927, by rfl⟩ : syracuseStep 2335613 = 875855) (by norm_num)
theorem B1868689 : Blo 1555475 1868689 := bbase (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) (by norm_num)
theorem B2335637 : Blo 1555475 2335637 := bbase (se 6 (by rfl) ⟨54741, by rfl⟩ : syracuseStep 2335637 = 109483) (by norm_num)
theorem B2335661 : Blo 1555475 2335661 := bbase (se 3 (by rfl) ⟨437936, by rfl⟩ : syracuseStep 2335661 = 875873) (by norm_num)
theorem B2245565 : Blo 1555475 2245565 := bbase (se 3 (by rfl) ⟨421043, by rfl⟩ : syracuseStep 2245565 = 842087) (by norm_num)
theorem B2335685 : Blo 1555475 2335685 := bbase (se 4 (by rfl) ⟨218970, by rfl⟩ : syracuseStep 2335685 = 437941) (by norm_num)
theorem B2335709 : Blo 1555475 2335709 := bbase (se 3 (by rfl) ⟨437945, by rfl⟩ : syracuseStep 2335709 = 875891) (by norm_num)
theorem B2335733 : Blo 1555475 2335733 := bbase (se 5 (by rfl) ⟨109487, by rfl⟩ : syracuseStep 2335733 = 218975) (by norm_num)
theorem B9470965 : Blo 1555475 9470965 := bbase (se 5 (by rfl) ⟨443951, by rfl⟩ : syracuseStep 9470965 = 887903) (by norm_num)
theorem B2335757 : Blo 1555475 2335757 := bbase (se 3 (by rfl) ⟨437954, by rfl⟩ : syracuseStep 2335757 = 875909) (by norm_num)
theorem B2335781 : Blo 1555475 2335781 := bbase (se 4 (by rfl) ⟨218979, by rfl⟩ : syracuseStep 2335781 = 437959) (by norm_num)
theorem B2335805 : Blo 1555475 2335805 := bbase (se 3 (by rfl) ⟨437963, by rfl⟩ : syracuseStep 2335805 = 875927) (by norm_num)
theorem B4432981 : Blo 1555475 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B2335829 : Blo 1555475 2335829 := bbase (se 8 (by rfl) ⟨13686, by rfl⟩ : syracuseStep 2335829 = 27373) (by norm_num)
theorem B2335853 : Blo 1555475 2335853 := bbase (se 3 (by rfl) ⟨437972, by rfl⟩ : syracuseStep 2335853 = 875945) (by norm_num)
theorem B2335877 : Blo 1555475 2335877 := bbase (se 4 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 2335877 = 437977) (by norm_num)
theorem B2335901 : Blo 1555475 2335901 := bbase (se 3 (by rfl) ⟨437981, by rfl⟩ : syracuseStep 2335901 = 875963) (by norm_num)
theorem B2335925 : Blo 1555475 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B3941581 : Blo 1555475 3941581 := bbase (se 3 (by rfl) ⟨739046, by rfl⟩ : syracuseStep 3941581 = 1478093) (by norm_num)
theorem B2335949 : Blo 1555475 2335949 := bbase (se 3 (by rfl) ⟨437990, by rfl⟩ : syracuseStep 2335949 = 875981) (by norm_num)
theorem B5252309 : Blo 1555475 5252309 := bbase (se 7 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 5252309 = 123101) (by norm_num)
theorem B2335973 : Blo 1555475 2335973 := bbase (se 4 (by rfl) ⟨218997, by rfl⟩ : syracuseStep 2335973 = 437995) (by norm_num)
theorem B2335997 : Blo 1555475 2335997 := bbase (se 3 (by rfl) ⟨437999, by rfl⟩ : syracuseStep 2335997 = 875999) (by norm_num)
theorem B2336021 : Blo 1555475 2336021 := bbase (se 6 (by rfl) ⟨54750, by rfl⟩ : syracuseStep 2336021 = 109501) (by norm_num)
theorem B2336045 : Blo 1555475 2336045 := bbase (se 3 (by rfl) ⟨438008, by rfl⟩ : syracuseStep 2336045 = 876017) (by norm_num)
theorem B3941693 : Blo 1555475 3941693 := bbase (se 3 (by rfl) ⟨739067, by rfl⟩ : syracuseStep 3941693 = 1478135) (by norm_num)
theorem B2336069 : Blo 1555475 2336069 := bbase (se 4 (by rfl) ⟨219006, by rfl⟩ : syracuseStep 2336069 = 438013) (by norm_num)
theorem B5612885 : Blo 1555475 5612885 := bbase (se 12 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5612885 = 4111) (by norm_num)
theorem B2336093 : Blo 1555475 2336093 := bbase (se 3 (by rfl) ⟨438017, by rfl⟩ : syracuseStep 2336093 = 876035) (by norm_num)
theorem B2336117 : Blo 1555475 2336117 := bbase (se 5 (by rfl) ⟨109505, by rfl⟩ : syracuseStep 2336117 = 219011) (by norm_num)
theorem B2336141 : Blo 1555475 2336141 := bbase (se 3 (by rfl) ⟨438026, by rfl⟩ : syracuseStep 2336141 = 876053) (by norm_num)
theorem B2336165 : Blo 1555475 2336165 := bbase (se 4 (by rfl) ⟨219015, by rfl⟩ : syracuseStep 2336165 = 438031) (by norm_num)
theorem B2663869 : Blo 1555475 2663869 := bbase (se 3 (by rfl) ⟨499475, by rfl⟩ : syracuseStep 2663869 = 998951) (by norm_num)
theorem B2336189 : Blo 1555475 2336189 := bbase (se 3 (by rfl) ⟨438035, by rfl⟩ : syracuseStep 2336189 = 876071) (by norm_num)
theorem B28386773 : Blo 1555475 28386773 := bbase (se 7 (by rfl) ⟨332657, by rfl⟩ : syracuseStep 28386773 = 665315) (by norm_num)
theorem B2336213 : Blo 1555475 2336213 := bbase (se 7 (by rfl) ⟨27377, by rfl⟩ : syracuseStep 2336213 = 54755) (by norm_num)
theorem B3941885 : Blo 1555475 3941885 := bbase (se 3 (by rfl) ⟨739103, by rfl⟩ : syracuseStep 3941885 = 1478207) (by norm_num)
theorem B2803213 : Blo 1555475 2803213 := bbase (se 3 (by rfl) ⟨525602, by rfl⟩ : syracuseStep 2803213 = 1051205) (by norm_num)
theorem B3991133 : Blo 1555475 3991133 := bbase (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) (by norm_num)
theorem B3368549 : Blo 1555475 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B3368557 : Blo 1555475 3368557 := bbase (se 3 (by rfl) ⟨631604, by rfl⟩ : syracuseStep 3368557 = 1263209) (by norm_num)
theorem B5252741 : Blo 1555475 5252741 := bbase (se 4 (by rfl) ⟨492444, by rfl⟩ : syracuseStep 5252741 = 984889) (by norm_num)
theorem B6645509 : Blo 1555475 6645509 := bbase (se 4 (by rfl) ⟨623016, by rfl⟩ : syracuseStep 6645509 = 1246033) (by norm_num)
theorem B3499829 : Blo 1555475 3499829 := bbase (se 5 (by rfl) ⟨164054, by rfl⟩ : syracuseStep 3499829 = 328109) (by norm_num)
theorem B3942229 : Blo 1555475 3942229 := bbase (se 9 (by rfl) ⟨11549, by rfl⟩ : syracuseStep 3942229 = 23099) (by norm_num)
theorem B1869689 : Blo 1555475 1869689 := bbase (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) (by norm_num)
theorem B3499901 : Blo 1555475 3499901 := bbase (se 3 (by rfl) ⟨656231, by rfl⟩ : syracuseStep 3499901 = 1312463) (by norm_num)
theorem B2492309 : Blo 1555475 2492309 := bbase (se 6 (by rfl) ⟨58413, by rfl⟩ : syracuseStep 2492309 = 116827) (by norm_num)
theorem B3499973 : Blo 1555475 3499973 := bbase (se 4 (by rfl) ⟨328122, by rfl⟩ : syracuseStep 3499973 = 656245) (by norm_num)
theorem B3942341 : Blo 1555475 3942341 := bbase (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) (by norm_num)
theorem B5056469 : Blo 1555475 5056469 := bbase (se 7 (by rfl) ⟨59255, by rfl⟩ : syracuseStep 5056469 = 118511) (by norm_num)
theorem B7882757 : Blo 1555475 7882757 := bbase (se 4 (by rfl) ⟨739008, by rfl⟩ : syracuseStep 7882757 = 1478017) (by norm_num)
theorem B3500045 : Blo 1555475 3500045 := bbase (se 3 (by rfl) ⟨656258, by rfl⟩ : syracuseStep 3500045 = 1312517) (by norm_num)
theorem B5253173 : Blo 1555475 5253173 := bbase (se 5 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 5253173 = 492485) (by norm_num)
theorem B3500117 : Blo 1555475 3500117 := bbase (se 8 (by rfl) ⟨20508, by rfl⟩ : syracuseStep 3500117 = 41017) (by norm_num)
theorem B8988821 : Blo 1555475 8988821 := bbase (se 6 (by rfl) ⟨210675, by rfl⟩ : syracuseStep 8988821 = 421351) (by norm_num)
theorem B3500189 : Blo 1555475 3500189 := bbase (se 3 (by rfl) ⟨656285, by rfl⟩ : syracuseStep 3500189 = 1312571) (by norm_num)
theorem B3549341 : Blo 1555475 3549341 := bbase (se 3 (by rfl) ⟨665501, by rfl⟩ : syracuseStep 3549341 = 1331003) (by norm_num)
theorem B2803877 : Blo 1555475 2803877 := bbase (se 4 (by rfl) ⟨262863, by rfl⟩ : syracuseStep 2803877 = 525727) (by norm_num)
theorem B10651829 : Blo 1555475 10651829 := bbase (se 5 (by rfl) ⟨499304, by rfl⟩ : syracuseStep 10651829 = 998609) (by norm_num)
theorem B3500261 : Blo 1555475 3500261 := bbase (se 4 (by rfl) ⟨328149, by rfl⟩ : syracuseStep 3500261 = 656299) (by norm_num)
theorem B3500333 : Blo 1555475 3500333 := bbase (se 3 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 3500333 = 1312625) (by norm_num)
theorem B3737917 : Blo 1555475 3737917 := bbase (se 3 (by rfl) ⟨700859, by rfl⟩ : syracuseStep 3737917 = 1401719) (by norm_num)
theorem B2492765 : Blo 1555475 2492765 := bbase (se 3 (by rfl) ⟨467393, by rfl⟩ : syracuseStep 2492765 = 934787) (by norm_num)
theorem B3500405 : Blo 1555475 3500405 := bbase (se 5 (by rfl) ⟨164081, by rfl⟩ : syracuseStep 3500405 = 328163) (by norm_num)
theorem B7874981 : Blo 1555475 7874981 := bbase (se 4 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 7874981 = 1476559) (by norm_num)
theorem B5990821 : Blo 1555475 5990821 := bbase (se 4 (by rfl) ⟨561639, by rfl⟩ : syracuseStep 5990821 = 1123279) (by norm_num)
theorem B3500477 : Blo 1555475 3500477 := bbase (se 3 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 3500477 = 1312679) (by norm_num)
theorem B7096805 : Blo 1555475 7096805 := bbase (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) (by norm_num)
theorem B5253605 : Blo 1555475 5253605 := bbase (se 4 (by rfl) ⟨492525, by rfl⟩ : syracuseStep 5253605 = 985051) (by norm_num)
theorem B3156469 : Blo 1555475 3156469 := bbase (se 5 (by rfl) ⟨147959, by rfl⟩ : syracuseStep 3156469 = 295919) (by norm_num)
theorem B3500549 : Blo 1555475 3500549 := bbase (se 4 (by rfl) ⟨328176, by rfl⟩ : syracuseStep 3500549 = 656353) (by norm_num)
theorem B5327365 : Blo 1555475 5327365 := bbase (se 4 (by rfl) ⟨499440, by rfl⟩ : syracuseStep 5327365 = 998881) (by norm_num)
theorem B2525717 : Blo 1555475 2525717 := bbase (se 6 (by rfl) ⟨59196, by rfl⟩ : syracuseStep 2525717 = 118393) (by norm_num)
theorem B1870381 : Blo 1555475 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B1870385 : Blo 1555475 1870385 := bbase (se 2 (by rfl) ⟨701394, by rfl⟩ : syracuseStep 1870385 = 1402789) (by norm_num)
theorem B3500621 : Blo 1555475 3500621 := bbase (se 3 (by rfl) ⟨656366, by rfl⟩ : syracuseStep 3500621 = 1312733) (by norm_num)
theorem B1968725 : Blo 1555475 1968725 := bbase (se 8 (by rfl) ⟨11535, by rfl⟩ : syracuseStep 1968725 = 23071) (by norm_num)
theorem B7096949 : Blo 1555475 7096949 := bbase (se 5 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 7096949 = 665339) (by norm_num)
theorem B1968781 : Blo 1555475 1968781 := bbase (se 3 (by rfl) ⟨369146, by rfl⟩ : syracuseStep 1968781 = 738293) (by norm_num)
theorem B3500693 : Blo 1555475 3500693 := bbase (se 6 (by rfl) ⟨82047, by rfl⟩ : syracuseStep 3500693 = 164095) (by norm_num)
theorem B3500765 : Blo 1555475 3500765 := bbase (se 3 (by rfl) ⟨656393, by rfl⟩ : syracuseStep 3500765 = 1312787) (by norm_num)
theorem B1968877 : Blo 1555475 1968877 := bbase (se 3 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 1968877 = 738329) (by norm_num)
theorem B8416021 : Blo 1555475 8416021 := bbase (se 6 (by rfl) ⟨197250, by rfl⟩ : syracuseStep 8416021 = 394501) (by norm_num)
theorem B11823893 : Blo 1555475 11823893 := bbase (se 6 (by rfl) ⟨277122, by rfl⟩ : syracuseStep 11823893 = 554245) (by norm_num)
theorem B3500837 : Blo 1555475 3500837 := bbase (se 4 (by rfl) ⟨328203, by rfl⟩ : syracuseStep 3500837 = 656407) (by norm_num)
theorem B5327669 : Blo 1555475 5327669 := bbase (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) (by norm_num)
theorem B3500909 : Blo 1555475 3500909 := bbase (se 3 (by rfl) ⟨656420, by rfl⟩ : syracuseStep 3500909 = 1312841) (by norm_num)
theorem B5909381 : Blo 1555475 5909381 := bbase (se 4 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 5909381 = 1108009) (by norm_num)
theorem B2214805 : Blo 1555475 2214805 := bbase (se 6 (by rfl) ⟨51909, by rfl⟩ : syracuseStep 2214805 = 103819) (by norm_num)
theorem B5991317 : Blo 1555475 5991317 := bbase (se 6 (by rfl) ⟨140421, by rfl⟩ : syracuseStep 5991317 = 280843) (by norm_num)
theorem B5254037 : Blo 1555475 5254037 := bbase (se 6 (by rfl) ⟨123141, by rfl⟩ : syracuseStep 5254037 = 246283) (by norm_num)
theorem B1969049 : Blo 1555475 1969049 := bbase (se 2 (by rfl) ⟨738393, by rfl⟩ : syracuseStep 1969049 = 1476787) (by norm_num)
theorem B3500981 : Blo 1555475 3500981 := bbase (se 5 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 3500981 = 328217) (by norm_num)
theorem B3156941 : Blo 1555475 3156941 := bbase (se 3 (by rfl) ⟨591926, by rfl⟩ : syracuseStep 3156941 = 1183853) (by norm_num)
theorem B1969105 : Blo 1555475 1969105 := bbase (se 2 (by rfl) ⟨738414, by rfl⟩ : syracuseStep 1969105 = 1476829) (by norm_num)
theorem B3501053 : Blo 1555475 3501053 := bbase (se 3 (by rfl) ⟨656447, by rfl⟩ : syracuseStep 3501053 = 1312895) (by norm_num)
theorem B8645653 : Blo 1555475 8645653 := bbase (se 6 (by rfl) ⟨202632, by rfl⟩ : syracuseStep 8645653 = 405265) (by norm_num)
theorem B1870885 : Blo 1555475 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B1969201 : Blo 1555475 1969201 := bbase (se 2 (by rfl) ⟨738450, by rfl⟩ : syracuseStep 1969201 = 1476901) (by norm_num)
theorem B3501125 : Blo 1555475 3501125 := bbase (se 4 (by rfl) ⟨328230, by rfl⟩ : syracuseStep 3501125 = 656461) (by norm_num)
theorem B2215021 : Blo 1555475 2215021 := bbase (se 3 (by rfl) ⟨415316, by rfl⟩ : syracuseStep 2215021 = 830633) (by norm_num)
theorem B3501197 : Blo 1555475 3501197 := bbase (se 3 (by rfl) ⟨656474, by rfl⟩ : syracuseStep 3501197 = 1312949) (by norm_num)
theorem B2526365 : Blo 1555475 2526365 := bbase (se 3 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 2526365 = 947387) (by norm_num)
theorem B5909669 : Blo 1555475 5909669 := bbase (se 4 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 5909669 = 1108063) (by norm_num)
theorem B3550373 : Blo 1555475 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B11816117 : Blo 1555475 11816117 := bbase (se 5 (by rfl) ⟨553880, by rfl⟩ : syracuseStep 11816117 = 1107761) (by norm_num)
theorem B3501269 : Blo 1555475 3501269 := bbase (se 7 (by rfl) ⟨41030, by rfl⟩ : syracuseStep 3501269 = 82061) (by norm_num)
theorem B1969373 : Blo 1555475 1969373 := bbase (se 3 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 1969373 = 738515) (by norm_num)
theorem B1969429 : Blo 1555475 1969429 := bbase (se 6 (by rfl) ⟨46158, by rfl⟩ : syracuseStep 1969429 = 92317) (by norm_num)
theorem B7884053 : Blo 1555475 7884053 := bbase (se 6 (by rfl) ⟨184782, by rfl⟩ : syracuseStep 7884053 = 369565) (by norm_num)
theorem B3501341 : Blo 1555475 3501341 := bbase (se 3 (by rfl) ⟨656501, by rfl⟩ : syracuseStep 3501341 = 1313003) (by norm_num)
theorem B2493757 : Blo 1555475 2493757 := bbase (se 3 (by rfl) ⟨467579, by rfl⟩ : syracuseStep 2493757 = 935159) (by norm_num)
theorem B5254469 : Blo 1555475 5254469 := bbase (se 4 (by rfl) ⟨492606, by rfl⟩ : syracuseStep 5254469 = 985213) (by norm_num)
theorem B3501413 : Blo 1555475 3501413 := bbase (se 4 (by rfl) ⟨328257, by rfl⟩ : syracuseStep 3501413 = 656515) (by norm_num)
theorem B1969525 : Blo 1555475 1969525 := bbase (se 5 (by rfl) ⟨92321, by rfl⟩ : syracuseStep 1969525 = 184643) (by norm_num)
theorem B2624933 : Blo 1555475 2624933 := bbase (se 4 (by rfl) ⟨246087, by rfl⟩ : syracuseStep 2624933 = 492175) (by norm_num)
theorem B3501485 : Blo 1555475 3501485 := bbase (se 3 (by rfl) ⟨656528, by rfl⟩ : syracuseStep 3501485 = 1313057) (by norm_num)
theorem B2215397 : Blo 1555475 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B3739117 : Blo 1555475 3739117 := bbase (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) (by norm_num)
theorem B6647285 : Blo 1555475 6647285 := bbase (se 5 (by rfl) ⟨311591, by rfl⟩ : syracuseStep 6647285 = 623183) (by norm_num)
theorem B3501557 : Blo 1555475 3501557 := bbase (se 5 (by rfl) ⟨164135, by rfl⟩ : syracuseStep 3501557 = 328271) (by norm_num)
theorem B1969697 : Blo 1555475 1969697 := bbase (se 2 (by rfl) ⟨738636, by rfl⟩ : syracuseStep 1969697 = 1477273) (by norm_num)
theorem B2625061 : Blo 1555475 2625061 := bbase (se 4 (by rfl) ⟨246099, by rfl⟩ : syracuseStep 2625061 = 492199) (by norm_num)
theorem B2993717 : Blo 1555475 2993717 := bbase (se 5 (by rfl) ⟨140330, by rfl⟩ : syracuseStep 2993717 = 280661) (by norm_num)
theorem B3501629 : Blo 1555475 3501629 := bbase (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) (by norm_num)
theorem B1969753 : Blo 1555475 1969753 := bbase (se 2 (by rfl) ⟨738657, by rfl⟩ : syracuseStep 1969753 = 1477315) (by norm_num)
theorem B2993773 : Blo 1555475 2993773 := bbase (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) (by norm_num)
theorem B2625149 : Blo 1555475 2625149 := bbase (se 3 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 2625149 = 984431) (by norm_num)
theorem B3501701 : Blo 1555475 3501701 := bbase (se 4 (by rfl) ⟨328284, by rfl⟩ : syracuseStep 3501701 = 656569) (by norm_num)
theorem B7876277 : Blo 1555475 7876277 := bbase (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) (by norm_num)
theorem B1969849 : Blo 1555475 1969849 := bbase (se 2 (by rfl) ⟨738693, by rfl⟩ : syracuseStep 1969849 = 1477387) (by norm_num)
theorem B3501773 : Blo 1555475 3501773 := bbase (se 3 (by rfl) ⟨656582, by rfl⟩ : syracuseStep 3501773 = 1313165) (by norm_num)
theorem B2526949 : Blo 1555475 2526949 := bbase (se 4 (by rfl) ⟨236901, by rfl⟩ : syracuseStep 2526949 = 473803) (by norm_num)
theorem B5254901 : Blo 1555475 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B2625277 : Blo 1555475 2625277 := bbase (se 3 (by rfl) ⟨492239, by rfl⟩ : syracuseStep 2625277 = 984479) (by norm_num)
theorem B3501845 : Blo 1555475 3501845 := bbase (se 6 (by rfl) ⟨82074, by rfl⟩ : syracuseStep 3501845 = 164149) (by norm_num)
theorem B2625365 : Blo 1555475 2625365 := bbase (se 9 (by rfl) ⟨7691, by rfl⟩ : syracuseStep 2625365 = 15383) (by norm_num)
theorem B4206421 : Blo 1555475 4206421 := bbase (se 9 (by rfl) ⟨12323, by rfl⟩ : syracuseStep 4206421 = 24647) (by norm_num)
theorem B3501917 : Blo 1555475 3501917 := bbase (se 3 (by rfl) ⟨656609, by rfl⟩ : syracuseStep 3501917 = 1313219) (by norm_num)
theorem B1970021 : Blo 1555475 1970021 := bbase (se 4 (by rfl) ⟨184689, by rfl⟩ : syracuseStep 1970021 = 369379) (by norm_num)
theorem B1576837 : Blo 1555475 1576837 := bbase (se 4 (by rfl) ⟨147828, by rfl⟩ : syracuseStep 1576837 = 295657) (by norm_num)
theorem B1970077 : Blo 1555475 1970077 := bbase (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) (by norm_num)
theorem B3501989 : Blo 1555475 3501989 := bbase (se 4 (by rfl) ⟨328311, by rfl⟩ : syracuseStep 3501989 = 656623) (by norm_num)
theorem B2494405 : Blo 1555475 2494405 := bbase (se 4 (by rfl) ⟨233850, by rfl⟩ : syracuseStep 2494405 = 467701) (by norm_num)
theorem B2625493 : Blo 1555475 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B29921237 : Blo 1555475 29921237 := bbase (se 7 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 29921237 = 701279) (by norm_num)
theorem B3502061 : Blo 1555475 3502061 := bbase (se 3 (by rfl) ⟨656636, by rfl⟩ : syracuseStep 3502061 = 1313273) (by norm_num)
theorem B1970173 : Blo 1555475 1970173 := bbase (se 3 (by rfl) ⟨369407, by rfl⟩ : syracuseStep 1970173 = 738815) (by norm_num)
theorem B2625581 : Blo 1555475 2625581 := bbase (se 3 (by rfl) ⟨492296, by rfl⟩ : syracuseStep 2625581 = 984593) (by norm_num)
theorem B3502133 : Blo 1555475 3502133 := bbase (se 5 (by rfl) ⟨164162, by rfl⟩ : syracuseStep 3502133 = 328325) (by norm_num)
theorem B3993677 : Blo 1555475 3993677 := bbase (se 3 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 3993677 = 1497629) (by norm_num)
theorem B3739733 : Blo 1555475 3739733 := bbase (se 8 (by rfl) ⟨21912, by rfl⟩ : syracuseStep 3739733 = 43825) (by norm_num)
theorem B3502205 : Blo 1555475 3502205 := bbase (se 3 (by rfl) ⟨656663, by rfl⟩ : syracuseStep 3502205 = 1313327) (by norm_num)
theorem B4206725 : Blo 1555475 4206725 := bbase (se 4 (by rfl) ⟨394380, by rfl⟩ : syracuseStep 4206725 = 788761) (by norm_num)
theorem B5255333 : Blo 1555475 5255333 := bbase (se 4 (by rfl) ⟨492687, by rfl⟩ : syracuseStep 5255333 = 985375) (by norm_num)
theorem B1970345 : Blo 1555475 1970345 := bbase (se 2 (by rfl) ⟨738879, by rfl⟩ : syracuseStep 1970345 = 1477759) (by norm_num)
theorem B2625709 : Blo 1555475 2625709 := bbase (se 3 (by rfl) ⟨492320, by rfl⟩ : syracuseStep 2625709 = 984641) (by norm_num)
theorem B3993781 : Blo 1555475 3993781 := bbase (se 5 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 3993781 = 374417) (by norm_num)
theorem B3502277 : Blo 1555475 3502277 := bbase (se 4 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 3502277 = 656677) (by norm_num)
theorem B1970401 : Blo 1555475 1970401 := bbase (se 2 (by rfl) ⟨738900, by rfl⟩ : syracuseStep 1970401 = 1477801) (by norm_num)
theorem B7475429 : Blo 1555475 7475429 := bbase (se 4 (by rfl) ⟨700821, by rfl⟩ : syracuseStep 7475429 = 1401643) (by norm_num)
theorem B2625797 : Blo 1555475 2625797 := bbase (se 4 (by rfl) ⟨246168, by rfl⟩ : syracuseStep 2625797 = 492337) (by norm_num)
theorem B3502349 : Blo 1555475 3502349 := bbase (se 3 (by rfl) ⟨656690, by rfl⟩ : syracuseStep 3502349 = 1313381) (by norm_num)
theorem B3739925 : Blo 1555475 3739925 := bbase (se 6 (by rfl) ⟨87654, by rfl⟩ : syracuseStep 3739925 = 175309) (by norm_num)
theorem B8868149 : Blo 1555475 8868149 := bbase (se 5 (by rfl) ⟨415694, by rfl⟩ : syracuseStep 8868149 = 831389) (by norm_num)
theorem B1970497 : Blo 1555475 1970497 := bbase (se 2 (by rfl) ⟨738936, by rfl⟩ : syracuseStep 1970497 = 1477873) (by norm_num)
theorem B5910853 : Blo 1555475 5910853 := bbase (se 4 (by rfl) ⟨554142, by rfl⟩ : syracuseStep 5910853 = 1108285) (by norm_num)
theorem B3502421 : Blo 1555475 3502421 := bbase (se 10 (by rfl) ⟨5130, by rfl⟩ : syracuseStep 3502421 = 10261) (by norm_num)
theorem B3740021 : Blo 1555475 3740021 := bbase (se 5 (by rfl) ⟨175313, by rfl⟩ : syracuseStep 3740021 = 350627) (by norm_num)
theorem B2953597 : Blo 1555475 2953597 := bbase (se 3 (by rfl) ⟨553799, by rfl⟩ : syracuseStep 2953597 = 1107599) (by norm_num)
theorem B2625925 : Blo 1555475 2625925 := bbase (se 4 (by rfl) ⟨246180, by rfl⟩ : syracuseStep 2625925 = 492361) (by norm_num)
theorem B4985221 : Blo 1555475 4985221 := bbase (se 4 (by rfl) ⟨467364, by rfl⟩ : syracuseStep 4985221 = 934729) (by norm_num)
theorem B3502493 : Blo 1555475 3502493 := bbase (se 3 (by rfl) ⟨656717, by rfl⟩ : syracuseStep 3502493 = 1313435) (by norm_num)
theorem B2626013 : Blo 1555475 2626013 := bbase (se 3 (by rfl) ⟨492377, by rfl⟩ : syracuseStep 2626013 = 984755) (by norm_num)
theorem B3502565 : Blo 1555475 3502565 := bbase (se 4 (by rfl) ⟨328365, by rfl⟩ : syracuseStep 3502565 = 656731) (by norm_num)
theorem B1970669 : Blo 1555475 1970669 := bbase (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) (by norm_num)
theorem B2953741 : Blo 1555475 2953741 := bbase (se 3 (by rfl) ⟨553826, by rfl⟩ : syracuseStep 2953741 = 1107653) (by norm_num)
theorem B1970725 : Blo 1555475 1970725 := bbase (se 4 (by rfl) ⟨184755, by rfl⟩ : syracuseStep 1970725 = 369511) (by norm_num)
theorem B3502637 : Blo 1555475 3502637 := bbase (se 3 (by rfl) ⟨656744, by rfl⟩ : syracuseStep 3502637 = 1313489) (by norm_num)
theorem B5255765 : Blo 1555475 5255765 := bbase (se 8 (by rfl) ⟨30795, by rfl⟩ : syracuseStep 5255765 = 61591) (by norm_num)
theorem B2626141 : Blo 1555475 2626141 := bbase (se 3 (by rfl) ⟨492401, by rfl⟩ : syracuseStep 2626141 = 984803) (by norm_num)
theorem B3502709 : Blo 1555475 3502709 := bbase (se 5 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 3502709 = 328379) (by norm_num)
theorem B5911157 : Blo 1555475 5911157 := bbase (se 5 (by rfl) ⟨277085, by rfl⟩ : syracuseStep 5911157 = 554171) (by norm_num)
theorem B1970821 : Blo 1555475 1970821 := bbase (se 4 (by rfl) ⟨184764, by rfl⟩ : syracuseStep 1970821 = 369529) (by norm_num)
theorem B2953901 : Blo 1555475 2953901 := bbase (se 3 (by rfl) ⟨553856, by rfl⟩ : syracuseStep 2953901 = 1107713) (by norm_num)
theorem B3322549 : Blo 1555475 3322549 := bbase (se 5 (by rfl) ⟨155744, by rfl⟩ : syracuseStep 3322549 = 311489) (by norm_num)
theorem B2626229 : Blo 1555475 2626229 := bbase (se 5 (by rfl) ⟨123104, by rfl⟩ : syracuseStep 2626229 = 246209) (by norm_num)
theorem B3502781 : Blo 1555475 3502781 := bbase (se 3 (by rfl) ⟨656771, by rfl⟩ : syracuseStep 3502781 = 1313543) (by norm_num)
theorem B2806501 : Blo 1555475 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B1577713 : Blo 1555475 1577713 := bbase (se 2 (by rfl) ⟨591642, by rfl⟩ : syracuseStep 1577713 = 1183285) (by norm_num)
theorem B3502853 : Blo 1555475 3502853 := bbase (se 4 (by rfl) ⟨328392, by rfl⟩ : syracuseStep 3502853 = 656785) (by norm_num)
theorem B15971093 : Blo 1555475 15971093 := bbase (se 6 (by rfl) ⟨374322, by rfl⟩ : syracuseStep 15971093 = 748645) (by norm_num)
theorem B1577765 : Blo 1555475 1577765 := bbase (se 4 (by rfl) ⟨147915, by rfl⟩ : syracuseStep 1577765 = 295831) (by norm_num)
theorem B1970993 : Blo 1555475 1970993 := bbase (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) (by norm_num)
theorem B2626357 : Blo 1555475 2626357 := bbase (se 5 (by rfl) ⟨123110, by rfl⟩ : syracuseStep 2626357 = 246221) (by norm_num)
theorem B2954045 : Blo 1555475 2954045 := bbase (se 3 (by rfl) ⟨553883, by rfl⟩ : syracuseStep 2954045 = 1107767) (by norm_num)
theorem B2700101 : Blo 1555475 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B3502925 : Blo 1555475 3502925 := bbase (se 3 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 3502925 = 1313597) (by norm_num)
theorem B1971049 : Blo 1555475 1971049 := bbase (se 2 (by rfl) ⟨739143, by rfl⟩ : syracuseStep 1971049 = 1478287) (by norm_num)
theorem B2216821 : Blo 1555475 2216821 := bbase (se 5 (by rfl) ⟨103913, by rfl⟩ : syracuseStep 2216821 = 207827) (by norm_num)
theorem B2626445 : Blo 1555475 2626445 := bbase (se 3 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 2626445 = 984917) (by norm_num)
theorem B3502997 : Blo 1555475 3502997 := bbase (se 6 (by rfl) ⟨82101, by rfl⟩ : syracuseStep 3502997 = 164203) (by norm_num)
theorem B7484309 : Blo 1555475 7484309 := bbase (se 6 (by rfl) ⟨175413, by rfl⟩ : syracuseStep 7484309 = 350827) (by norm_num)
theorem B1749937 : Blo 1555475 1749937 := bbase (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) (by norm_num)
theorem B7877573 : Blo 1555475 7877573 := bbase (se 4 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 7877573 = 1477045) (by norm_num)
theorem B1971145 : Blo 1555475 1971145 := bbase (se 2 (by rfl) ⟨739179, by rfl⟩ : syracuseStep 1971145 = 1478359) (by norm_num)
theorem B1749973 : Blo 1555475 1749973 := bbase (se 7 (by rfl) ⟨20507, by rfl⟩ : syracuseStep 1749973 = 41015) (by norm_num)
theorem B3503069 : Blo 1555475 3503069 := bbase (se 3 (by rfl) ⟨656825, by rfl⟩ : syracuseStep 3503069 = 1313651) (by norm_num)
theorem B4207589 : Blo 1555475 4207589 := bbase (se 4 (by rfl) ⟨394461, by rfl⟩ : syracuseStep 4207589 = 788923) (by norm_num)
theorem B1750009 : Blo 1555475 1750009 := bbase (se 2 (by rfl) ⟨656253, by rfl⟩ : syracuseStep 1750009 = 1312507) (by norm_num)
theorem B5256197 : Blo 1555475 5256197 := bbase (se 4 (by rfl) ⟨492768, by rfl⟩ : syracuseStep 5256197 = 985537) (by norm_num)
theorem B2626573 : Blo 1555475 2626573 := bbase (se 3 (by rfl) ⟨492482, by rfl⟩ : syracuseStep 2626573 = 984965) (by norm_num)
theorem B1750045 : Blo 1555475 1750045 := bbase (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) (by norm_num)
theorem B3503141 : Blo 1555475 3503141 := bbase (se 4 (by rfl) ⟨328419, by rfl⟩ : syracuseStep 3503141 = 656839) (by norm_num)
theorem B1750081 : Blo 1555475 1750081 := bbase (se 2 (by rfl) ⟨656280, by rfl⟩ : syracuseStep 1750081 = 1312561) (by norm_num)
theorem B3937349 : Blo 1555475 3937349 := bbase (se 4 (by rfl) ⟨369126, by rfl⟩ : syracuseStep 3937349 = 738253) (by norm_num)
theorem B2954333 : Blo 1555475 2954333 := bbase (se 3 (by rfl) ⟨553937, by rfl⟩ : syracuseStep 2954333 = 1107875) (by norm_num)
theorem B1750117 : Blo 1555475 1750117 := bbase (se 4 (by rfl) ⟨164073, by rfl⟩ : syracuseStep 1750117 = 328147) (by norm_num)
theorem B2626661 : Blo 1555475 2626661 := bbase (se 4 (by rfl) ⟨246249, by rfl⟩ : syracuseStep 2626661 = 492499) (by norm_num)
theorem B3503213 : Blo 1555475 3503213 := bbase (se 3 (by rfl) ⟨656852, by rfl⟩ : syracuseStep 3503213 = 1313705) (by norm_num)
theorem B1750153 : Blo 1555475 1750153 := bbase (se 2 (by rfl) ⟨656307, by rfl⟩ : syracuseStep 1750153 = 1312615) (by norm_num)
theorem B3323045 : Blo 1555475 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B1750189 : Blo 1555475 1750189 := bbase (se 3 (by rfl) ⟨328160, by rfl⟩ : syracuseStep 1750189 = 656321) (by norm_num)
theorem B3503285 : Blo 1555475 3503285 := bbase (se 5 (by rfl) ⟨164216, by rfl⟩ : syracuseStep 3503285 = 328433) (by norm_num)
theorem B4986053 : Blo 1555475 4986053 := bbase (se 4 (by rfl) ⟨467442, by rfl⟩ : syracuseStep 4986053 = 934885) (by norm_num)
theorem B1750225 : Blo 1555475 1750225 := bbase (se 2 (by rfl) ⟨656334, by rfl⟩ : syracuseStep 1750225 = 1312669) (by norm_num)
theorem B2626789 : Blo 1555475 2626789 := bbase (se 4 (by rfl) ⟨246261, by rfl⟩ : syracuseStep 2626789 = 492523) (by norm_num)
theorem B1750261 : Blo 1555475 1750261 := bbase (se 5 (by rfl) ⟨82043, by rfl⟩ : syracuseStep 1750261 = 164087) (by norm_num)
theorem B2954485 : Blo 1555475 2954485 := bbase (se 5 (by rfl) ⟨138491, by rfl⟩ : syracuseStep 2954485 = 276983) (by norm_num)
theorem B3503357 : Blo 1555475 3503357 := bbase (se 3 (by rfl) ⟨656879, by rfl⟩ : syracuseStep 3503357 = 1313759) (by norm_num)
theorem B1750297 : Blo 1555475 1750297 := bbase (se 2 (by rfl) ⟨656361, by rfl⟩ : syracuseStep 1750297 = 1312723) (by norm_num)
theorem B4207925 : Blo 1555475 4207925 := bbase (se 5 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 4207925 = 394493) (by norm_num)
theorem B1750333 : Blo 1555475 1750333 := bbase (se 3 (by rfl) ⟨328187, by rfl⟩ : syracuseStep 1750333 = 656375) (by norm_num)
theorem B2626877 : Blo 1555475 2626877 := bbase (se 3 (by rfl) ⟨492539, by rfl⟩ : syracuseStep 2626877 = 985079) (by norm_num)
theorem B3503429 : Blo 1555475 3503429 := bbase (se 4 (by rfl) ⟨328446, by rfl⟩ : syracuseStep 3503429 = 656893) (by norm_num)
theorem B1750369 : Blo 1555475 1750369 := bbase (se 2 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 1750369 = 1312777) (by norm_num)
theorem B1750405 : Blo 1555475 1750405 := bbase (se 4 (by rfl) ⟨164100, by rfl⟩ : syracuseStep 1750405 = 328201) (by norm_num)
theorem B3503501 : Blo 1555475 3503501 := bbase (se 3 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 3503501 = 1313813) (by norm_num)
theorem B3937693 : Blo 1555475 3937693 := bbase (se 3 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 3937693 = 1476635) (by norm_num)
theorem B1750441 : Blo 1555475 1750441 := bbase (se 2 (by rfl) ⟨656415, by rfl⟩ : syracuseStep 1750441 = 1312831) (by norm_num)
theorem B2627005 : Blo 1555475 2627005 := bbase (se 3 (by rfl) ⟨492563, by rfl⟩ : syracuseStep 2627005 = 985127) (by norm_num)
theorem B2217413 : Blo 1555475 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B1750477 : Blo 1555475 1750477 := bbase (se 3 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 1750477 = 656429) (by norm_num)
theorem B5469653 : Blo 1555475 5469653 := bbase (se 7 (by rfl) ⟨64097, by rfl⟩ : syracuseStep 5469653 = 128195) (by norm_num)
theorem B3503573 : Blo 1555475 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B1750513 : Blo 1555475 1750513 := bbase (se 2 (by rfl) ⟨656442, by rfl⟩ : syracuseStep 1750513 = 1312885) (by norm_num)
theorem B3937805 : Blo 1555475 3937805 := bbase (se 3 (by rfl) ⟨738338, by rfl⟩ : syracuseStep 3937805 = 1476677) (by norm_num)
theorem B1750549 : Blo 1555475 1750549 := bbase (se 6 (by rfl) ⟨41028, by rfl⟩ : syracuseStep 1750549 = 82057) (by norm_num)
theorem B2627093 : Blo 1555475 2627093 := bbase (se 6 (by rfl) ⟨61572, by rfl⟩ : syracuseStep 2627093 = 123145) (by norm_num)
theorem B2217493 : Blo 1555475 2217493 := bbase (se 6 (by rfl) ⟨51972, by rfl⟩ : syracuseStep 2217493 = 103945) (by norm_num)
theorem B3503645 : Blo 1555475 3503645 := bbase (se 3 (by rfl) ⟨656933, by rfl⟩ : syracuseStep 3503645 = 1313867) (by norm_num)
theorem B2954789 : Blo 1555475 2954789 := bbase (se 4 (by rfl) ⟨277011, by rfl⟩ : syracuseStep 2954789 = 554023) (by norm_num)
theorem B1750585 : Blo 1555475 1750585 := bbase (se 2 (by rfl) ⟨656469, by rfl⟩ : syracuseStep 1750585 = 1312939) (by norm_num)
theorem B40416853 : Blo 1555475 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B1750621 : Blo 1555475 1750621 := bbase (se 3 (by rfl) ⟨328241, by rfl⟩ : syracuseStep 1750621 = 656483) (by norm_num)
theorem B6313573 : Blo 1555475 6313573 := bbase (se 4 (by rfl) ⟨591897, by rfl⟩ : syracuseStep 6313573 = 1183795) (by norm_num)
theorem B3503717 : Blo 1555475 3503717 := bbase (se 4 (by rfl) ⟨328473, by rfl⟩ : syracuseStep 3503717 = 656947) (by norm_num)
theorem B6313589 : Blo 1555475 6313589 := bbase (se 5 (by rfl) ⟨295949, by rfl⟩ : syracuseStep 6313589 = 591899) (by norm_num)
theorem B1750657 : Blo 1555475 1750657 := bbase (se 2 (by rfl) ⟨656496, by rfl⟩ : syracuseStep 1750657 = 1312993) (by norm_num)
theorem B2627221 : Blo 1555475 2627221 := bbase (se 6 (by rfl) ⟨61575, by rfl⟩ : syracuseStep 2627221 = 123151) (by norm_num)
theorem B1750693 : Blo 1555475 1750693 := bbase (se 4 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 1750693 = 328255) (by norm_num)
theorem B3503789 : Blo 1555475 3503789 := bbase (se 3 (by rfl) ⟨656960, by rfl⟩ : syracuseStep 3503789 = 1313921) (by norm_num)
theorem B1750729 : Blo 1555475 1750729 := bbase (se 2 (by rfl) ⟨656523, by rfl⟩ : syracuseStep 1750729 = 1313047) (by norm_num)
theorem B3937997 : Blo 1555475 3937997 := bbase (se 3 (by rfl) ⟨738374, by rfl⟩ : syracuseStep 3937997 = 1476749) (by norm_num)
theorem B4429541 : Blo 1555475 4429541 := bbase (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) (by norm_num)
theorem B1750765 : Blo 1555475 1750765 := bbase (se 3 (by rfl) ⟨328268, by rfl⟩ : syracuseStep 1750765 = 656537) (by norm_num)
theorem B2627309 : Blo 1555475 2627309 := bbase (se 3 (by rfl) ⟨492620, by rfl⟩ : syracuseStep 2627309 = 985241) (by norm_num)
theorem B6313717 : Blo 1555475 6313717 := bbase (se 5 (by rfl) ⟨295955, by rfl⟩ : syracuseStep 6313717 = 591911) (by norm_num)
theorem B3503861 : Blo 1555475 3503861 := bbase (se 5 (by rfl) ⟨164243, by rfl⟩ : syracuseStep 3503861 = 328487) (by norm_num)
theorem B1750801 : Blo 1555475 1750801 := bbase (se 2 (by rfl) ⟨656550, by rfl⟩ : syracuseStep 1750801 = 1313101) (by norm_num)
theorem B1750837 : Blo 1555475 1750837 := bbase (se 5 (by rfl) ⟨82070, by rfl⟩ : syracuseStep 1750837 = 164141) (by norm_num)
theorem B3503933 : Blo 1555475 3503933 := bbase (se 3 (by rfl) ⟨656987, by rfl⟩ : syracuseStep 3503933 = 1313975) (by norm_num)
theorem B4208453 : Blo 1555475 4208453 := bbase (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) (by norm_num)
theorem B1750873 : Blo 1555475 1750873 := bbase (se 2 (by rfl) ⟨656577, by rfl⟩ : syracuseStep 1750873 = 1313155) (by norm_num)
theorem B1996633 : Blo 1555475 1996633 := bbase (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) (by norm_num)
theorem B2627437 : Blo 1555475 2627437 := bbase (se 3 (by rfl) ⟨492644, by rfl⟩ : syracuseStep 2627437 = 985289) (by norm_num)
theorem B2365309 : Blo 1555475 2365309 := bbase (se 3 (by rfl) ⟨443495, by rfl⟩ : syracuseStep 2365309 = 886991) (by norm_num)
theorem B1750909 : Blo 1555475 1750909 := bbase (se 3 (by rfl) ⟨328295, by rfl⟩ : syracuseStep 1750909 = 656591) (by norm_num)
theorem B3504005 : Blo 1555475 3504005 := bbase (se 4 (by rfl) ⟨328500, by rfl⟩ : syracuseStep 3504005 = 657001) (by norm_num)
theorem B1750945 : Blo 1555475 1750945 := bbase (se 2 (by rfl) ⟨656604, by rfl⟩ : syracuseStep 1750945 = 1313209) (by norm_num)
theorem B1750981 : Blo 1555475 1750981 := bbase (se 4 (by rfl) ⟨164154, by rfl⟩ : syracuseStep 1750981 = 328309) (by norm_num)
theorem B2627525 : Blo 1555475 2627525 := bbase (se 4 (by rfl) ⟨246330, by rfl⟩ : syracuseStep 2627525 = 492661) (by norm_num)
theorem B3504077 : Blo 1555475 3504077 := bbase (se 3 (by rfl) ⟨657014, by rfl⟩ : syracuseStep 3504077 = 1314029) (by norm_num)
theorem B1751017 : Blo 1555475 1751017 := bbase (se 2 (by rfl) ⟨656631, by rfl⟩ : syracuseStep 1751017 = 1313263) (by norm_num)
theorem B9975797 : Blo 1555475 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B1751053 : Blo 1555475 1751053 := bbase (se 3 (by rfl) ⟨328322, by rfl⟩ : syracuseStep 1751053 = 656645) (by norm_num)
theorem B17733653 : Blo 1555475 17733653 := bbase (se 6 (by rfl) ⟨415632, by rfl⟩ : syracuseStep 17733653 = 831265) (by norm_num)
theorem B3504149 : Blo 1555475 3504149 := bbase (se 6 (by rfl) ⟨82128, by rfl⟩ : syracuseStep 3504149 = 164257) (by norm_num)
theorem B3323933 : Blo 1555475 3323933 := bbase (se 3 (by rfl) ⟨623237, by rfl⟩ : syracuseStep 3323933 = 1246475) (by norm_num)
theorem B3938341 : Blo 1555475 3938341 := bbase (se 4 (by rfl) ⟨369219, by rfl⟩ : syracuseStep 3938341 = 738439) (by norm_num)
theorem B1751089 : Blo 1555475 1751089 := bbase (se 2 (by rfl) ⟨656658, by rfl⟩ : syracuseStep 1751089 = 1313317) (by norm_num)
theorem B4380725 : Blo 1555475 4380725 := bbase (se 5 (by rfl) ⟨205346, by rfl⟩ : syracuseStep 4380725 = 410693) (by norm_num)
theorem B8534069 : Blo 1555475 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B2627653 : Blo 1555475 2627653 := bbase (se 4 (by rfl) ⟨246342, by rfl⟩ : syracuseStep 2627653 = 492685) (by norm_num)
theorem B1751125 : Blo 1555475 1751125 := bbase (se 8 (by rfl) ⟨10260, by rfl⟩ : syracuseStep 1751125 = 20521) (by norm_num)
theorem B3504221 : Blo 1555475 3504221 := bbase (se 3 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 3504221 = 1314083) (by norm_num)
theorem B1751161 : Blo 1555475 1751161 := bbase (se 2 (by rfl) ⟨656685, by rfl⟩ : syracuseStep 1751161 = 1313371) (by norm_num)
theorem B3938453 : Blo 1555475 3938453 := bbase (se 6 (by rfl) ⟨92307, by rfl⟩ : syracuseStep 3938453 = 184615) (by norm_num)
theorem B3324053 : Blo 1555475 3324053 := bbase (se 6 (by rfl) ⟨77907, by rfl⟩ : syracuseStep 3324053 = 155815) (by norm_num)
theorem B1751197 : Blo 1555475 1751197 := bbase (se 3 (by rfl) ⟨328349, by rfl⟩ : syracuseStep 1751197 = 656699) (by norm_num)
theorem B2627741 : Blo 1555475 2627741 := bbase (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) (by norm_num)
theorem B3504293 : Blo 1555475 3504293 := bbase (se 4 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 3504293 = 657055) (by norm_num)
theorem B1751233 : Blo 1555475 1751233 := bbase (se 2 (by rfl) ⟨656712, by rfl⟩ : syracuseStep 1751233 = 1313425) (by norm_num)
theorem B7878869 : Blo 1555475 7878869 := bbase (se 7 (by rfl) ⟨92330, by rfl⟩ : syracuseStep 7878869 = 184661) (by norm_num)
theorem B1751269 : Blo 1555475 1751269 := bbase (se 4 (by rfl) ⟨164181, by rfl⟩ : syracuseStep 1751269 = 328363) (by norm_num)
theorem B1751305 : Blo 1555475 1751305 := bbase (se 2 (by rfl) ⟨656739, by rfl⟩ : syracuseStep 1751305 = 1313479) (by norm_num)
theorem B2955541 : Blo 1555475 2955541 := bbase (se 6 (by rfl) ⟨69270, by rfl⟩ : syracuseStep 2955541 = 138541) (by norm_num)
theorem B2627869 : Blo 1555475 2627869 := bbase (se 3 (by rfl) ⟨492725, by rfl⟩ : syracuseStep 2627869 = 985451) (by norm_num)
theorem B1751341 : Blo 1555475 1751341 := bbase (se 3 (by rfl) ⟨328376, by rfl⟩ : syracuseStep 1751341 = 656753) (by norm_num)
theorem B1661249 : Blo 1555475 1661249 := bbase (se 2 (by rfl) ⟨622968, by rfl⟩ : syracuseStep 1661249 = 1245937) (by norm_num)
theorem B1751377 : Blo 1555475 1751377 := bbase (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) (by norm_num)
theorem B3938645 : Blo 1555475 3938645 := bbase (se 10 (by rfl) ⟨5769, by rfl⟩ : syracuseStep 3938645 = 11539) (by norm_num)
theorem B1751413 : Blo 1555475 1751413 := bbase (se 5 (by rfl) ⟨82097, by rfl⟩ : syracuseStep 1751413 = 164195) (by norm_num)
theorem B2627957 : Blo 1555475 2627957 := bbase (se 5 (by rfl) ⟨123185, by rfl⟩ : syracuseStep 2627957 = 246371) (by norm_num)
theorem B1751449 : Blo 1555475 1751449 := bbase (se 2 (by rfl) ⟨656793, by rfl⟩ : syracuseStep 1751449 = 1313587) (by norm_num)
theorem B1776025 : Blo 1555475 1776025 := bbase (se 2 (by rfl) ⟨666009, by rfl⟩ : syracuseStep 1776025 = 1332019) (by norm_num)
theorem B2955685 : Blo 1555475 2955685 := bbase (se 4 (by rfl) ⟨277095, by rfl⟩ : syracuseStep 2955685 = 554191) (by norm_num)
theorem B1751485 : Blo 1555475 1751485 := bbase (se 3 (by rfl) ⟨328403, by rfl⟩ : syracuseStep 1751485 = 656807) (by norm_num)
theorem B2275781 : Blo 1555475 2275781 := bbase (se 4 (by rfl) ⟨213354, by rfl⟩ : syracuseStep 2275781 = 426709) (by norm_num)
theorem B1751521 : Blo 1555475 1751521 := bbase (se 2 (by rfl) ⟨656820, by rfl⟩ : syracuseStep 1751521 = 1313641) (by norm_num)
theorem B2628085 : Blo 1555475 2628085 := bbase (se 5 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 2628085 = 246383) (by norm_num)
theorem B5609989 : Blo 1555475 5609989 := bbase (se 4 (by rfl) ⟨525936, by rfl⟩ : syracuseStep 5609989 = 1051873) (by norm_num)
theorem B1751557 : Blo 1555475 1751557 := bbase (se 4 (by rfl) ⟨164208, by rfl⟩ : syracuseStep 1751557 = 328417) (by norm_num)
theorem B2333213 : Blo 1555475 2333213 := bbase (se 3 (by rfl) ⟨437477, by rfl⟩ : syracuseStep 2333213 = 874955) (by norm_num)
theorem B1751593 : Blo 1555475 1751593 := bbase (se 2 (by rfl) ⟨656847, by rfl⟩ : syracuseStep 1751593 = 1313695) (by norm_num)
theorem B2333237 : Blo 1555475 2333237 := bbase (se 5 (by rfl) ⟨109370, by rfl⟩ : syracuseStep 2333237 = 218741) (by norm_num)
theorem B2955845 : Blo 1555475 2955845 := bbase (se 4 (by rfl) ⟨277110, by rfl⟩ : syracuseStep 2955845 = 554221) (by norm_num)
theorem B2333261 : Blo 1555475 2333261 := bbase (se 3 (by rfl) ⟨437486, by rfl⟩ : syracuseStep 2333261 = 874973) (by norm_num)
theorem B1751629 : Blo 1555475 1751629 := bbase (se 3 (by rfl) ⟨328430, by rfl⟩ : syracuseStep 1751629 = 656861) (by norm_num)
theorem B2628173 : Blo 1555475 2628173 := bbase (se 3 (by rfl) ⟨492782, by rfl⟩ : syracuseStep 2628173 = 985565) (by norm_num)
theorem B2333285 : Blo 1555475 2333285 := bbase (se 4 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 2333285 = 437491) (by norm_num)
theorem B1751665 : Blo 1555475 1751665 := bbase (se 2 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 1751665 = 1313749) (by norm_num)
theorem B2333309 : Blo 1555475 2333309 := bbase (se 3 (by rfl) ⟨437495, by rfl⟩ : syracuseStep 2333309 = 874991) (by norm_num)
theorem B2333333 : Blo 1555475 2333333 := bbase (se 6 (by rfl) ⟨54687, by rfl⟩ : syracuseStep 2333333 = 109375) (by norm_num)
theorem B1751701 : Blo 1555475 1751701 := bbase (se 6 (by rfl) ⟨41055, by rfl⟩ : syracuseStep 1751701 = 82111) (by norm_num)
theorem B2333357 : Blo 1555475 2333357 := bbase (se 3 (by rfl) ⟨437504, by rfl⟩ : syracuseStep 2333357 = 875009) (by norm_num)
theorem B3938989 : Blo 1555475 3938989 := bbase (se 3 (by rfl) ⟨738560, by rfl⟩ : syracuseStep 3938989 = 1477121) (by norm_num)
theorem B5913269 : Blo 1555475 5913269 := bbase (se 5 (by rfl) ⟨277184, by rfl⟩ : syracuseStep 5913269 = 554369) (by norm_num)
theorem B1751737 : Blo 1555475 1751737 := bbase (se 2 (by rfl) ⟨656901, by rfl⟩ : syracuseStep 1751737 = 1313803) (by norm_num)
theorem B2333381 : Blo 1555475 2333381 := bbase (se 4 (by rfl) ⟨218754, by rfl⟩ : syracuseStep 2333381 = 437509) (by norm_num)
theorem B2955989 : Blo 1555475 2955989 := bbase (se 7 (by rfl) ⟨34640, by rfl⟩ : syracuseStep 2955989 = 69281) (by norm_num)
theorem B2333405 : Blo 1555475 2333405 := bbase (se 3 (by rfl) ⟨437513, by rfl⟩ : syracuseStep 2333405 = 875027) (by norm_num)
theorem B1751773 : Blo 1555475 1751773 := bbase (se 3 (by rfl) ⟨328457, by rfl⟩ : syracuseStep 1751773 = 656915) (by norm_num)
theorem B2333429 : Blo 1555475 2333429 := bbase (se 5 (by rfl) ⟨109379, by rfl⟩ : syracuseStep 2333429 = 218759) (by norm_num)
theorem B1661693 : Blo 1555475 1661693 := bbase (se 3 (by rfl) ⟨311567, by rfl⟩ : syracuseStep 1661693 = 623135) (by norm_num)
theorem B1751809 : Blo 1555475 1751809 := bbase (se 2 (by rfl) ⟨656928, by rfl⟩ : syracuseStep 1751809 = 1313857) (by norm_num)
theorem B2333453 : Blo 1555475 2333453 := bbase (se 3 (by rfl) ⟨437522, by rfl⟩ : syracuseStep 2333453 = 875045) (by norm_num)
theorem B3324685 : Blo 1555475 3324685 := bbase (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) (by norm_num)
theorem B3939101 : Blo 1555475 3939101 := bbase (se 3 (by rfl) ⟨738581, by rfl⟩ : syracuseStep 3939101 = 1477163) (by norm_num)
theorem B2333477 : Blo 1555475 2333477 := bbase (se 4 (by rfl) ⟨218763, by rfl⟩ : syracuseStep 2333477 = 437527) (by norm_num)
theorem B1751845 : Blo 1555475 1751845 := bbase (se 4 (by rfl) ⟨164235, by rfl⟩ : syracuseStep 1751845 = 328471) (by norm_num)
theorem B1661753 : Blo 1555475 1661753 := bbase (se 2 (by rfl) ⟨623157, by rfl⟩ : syracuseStep 1661753 = 1246315) (by norm_num)
theorem B2333501 : Blo 1555475 2333501 := bbase (se 3 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 2333501 = 875063) (by norm_num)
theorem B5323589 : Blo 1555475 5323589 := bbase (se 4 (by rfl) ⟨499086, by rfl⟩ : syracuseStep 5323589 = 998173) (by norm_num)
theorem B1751881 : Blo 1555475 1751881 := bbase (se 2 (by rfl) ⟨656955, by rfl⟩ : syracuseStep 1751881 = 1313911) (by norm_num)
theorem B2333525 : Blo 1555475 2333525 := bbase (se 9 (by rfl) ⟨6836, by rfl⟩ : syracuseStep 2333525 = 13673) (by norm_num)
theorem B2333549 : Blo 1555475 2333549 := bbase (se 3 (by rfl) ⟨437540, by rfl⟩ : syracuseStep 2333549 = 875081) (by norm_num)
theorem B1751917 : Blo 1555475 1751917 := bbase (se 3 (by rfl) ⟨328484, by rfl⟩ : syracuseStep 1751917 = 656969) (by norm_num)
theorem B2333573 : Blo 1555475 2333573 := bbase (se 4 (by rfl) ⟨218772, by rfl⟩ : syracuseStep 2333573 = 437545) (by norm_num)
theorem B1751953 : Blo 1555475 1751953 := bbase (se 2 (by rfl) ⟨656982, by rfl⟩ : syracuseStep 1751953 = 1313965) (by norm_num)
theorem B26598293 : Blo 1555475 26598293 := bbase (se 6 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 26598293 = 1246795) (by norm_num)
theorem B2333597 : Blo 1555475 2333597 := bbase (se 3 (by rfl) ⟨437549, by rfl⟩ : syracuseStep 2333597 = 875099) (by norm_num)
theorem B2333621 : Blo 1555475 2333621 := bbase (se 5 (by rfl) ⟨109388, by rfl⟩ : syracuseStep 2333621 = 218777) (by norm_num)
theorem B1751989 : Blo 1555475 1751989 := bbase (se 5 (by rfl) ⟨82124, by rfl⟩ : syracuseStep 1751989 = 164249) (by norm_num)
theorem B1661881 : Blo 1555475 1661881 := bbase (se 2 (by rfl) ⟨623205, by rfl⟩ : syracuseStep 1661881 = 1246411) (by norm_num)
theorem B2333645 : Blo 1555475 2333645 := bbase (se 3 (by rfl) ⟨437558, by rfl⟩ : syracuseStep 2333645 = 875117) (by norm_num)
theorem B1752025 : Blo 1555475 1752025 := bbase (se 2 (by rfl) ⟨657009, by rfl⟩ : syracuseStep 1752025 = 1314019) (by norm_num)
theorem B3939293 : Blo 1555475 3939293 := bbase (se 3 (by rfl) ⟨738617, by rfl⟩ : syracuseStep 3939293 = 1477235) (by norm_num)
theorem B2333669 : Blo 1555475 2333669 := bbase (se 4 (by rfl) ⟨218781, by rfl⟩ : syracuseStep 2333669 = 437563) (by norm_num)
theorem B2956277 : Blo 1555475 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B2333693 : Blo 1555475 2333693 := bbase (se 3 (by rfl) ⟨437567, by rfl⟩ : syracuseStep 2333693 = 875135) (by norm_num)
theorem B1752061 : Blo 1555475 1752061 := bbase (se 3 (by rfl) ⟨328511, by rfl⟩ : syracuseStep 1752061 = 657023) (by norm_num)
theorem B2366477 : Blo 1555475 2366477 := bbase (se 3 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 2366477 = 887429) (by norm_num)
theorem B2333717 : Blo 1555475 2333717 := bbase (se 6 (by rfl) ⟨54696, by rfl⟩ : syracuseStep 2333717 = 109393) (by norm_num)
theorem B4987925 : Blo 1555475 4987925 := bbase (se 6 (by rfl) ⟨116904, by rfl⟩ : syracuseStep 4987925 = 233809) (by norm_num)
theorem B1752097 : Blo 1555475 1752097 := bbase (se 2 (by rfl) ⟨657036, by rfl⟩ : syracuseStep 1752097 = 1314073) (by norm_num)
theorem B2333741 : Blo 1555475 2333741 := bbase (se 3 (by rfl) ⟨437576, by rfl⟩ : syracuseStep 2333741 = 875153) (by norm_num)
theorem B2333765 : Blo 1555475 2333765 := bbase (se 4 (by rfl) ⟨218790, by rfl⟩ : syracuseStep 2333765 = 437581) (by norm_num)
theorem B1752133 : Blo 1555475 1752133 := bbase (se 4 (by rfl) ⟨164262, by rfl⟩ : syracuseStep 1752133 = 328525) (by norm_num)
theorem B2333789 : Blo 1555475 2333789 := bbase (se 3 (by rfl) ⟨437585, by rfl⟩ : syracuseStep 2333789 = 875171) (by norm_num)
theorem B5250149 : Blo 1555475 5250149 := bbase (se 4 (by rfl) ⟨492201, by rfl⟩ : syracuseStep 5250149 = 984403) (by norm_num)
theorem B2333813 : Blo 1555475 2333813 := bbase (se 5 (by rfl) ⟨109397, by rfl⟩ : syracuseStep 2333813 = 218795) (by norm_num)
theorem B2399357 : Blo 1555475 2399357 := bbase (se 3 (by rfl) ⟨449879, by rfl⟩ : syracuseStep 2399357 = 899759) (by norm_num)
theorem B2333837 : Blo 1555475 2333837 := bbase (se 3 (by rfl) ⟨437594, by rfl⟩ : syracuseStep 2333837 = 875189) (by norm_num)
theorem B2956429 : Blo 1555475 2956429 := bbase (se 3 (by rfl) ⟨554330, by rfl⟩ : syracuseStep 2956429 = 1108661) (by norm_num)
theorem B2333861 : Blo 1555475 2333861 := bbase (se 4 (by rfl) ⟨218799, by rfl⟩ : syracuseStep 2333861 = 437599) (by norm_num)
theorem B2333885 : Blo 1555475 2333885 := bbase (se 3 (by rfl) ⟨437603, by rfl⟩ : syracuseStep 2333885 = 875207) (by norm_num)
theorem B2333909 : Blo 1555475 2333909 := bbase (se 7 (by rfl) ⟨27350, by rfl⟩ : syracuseStep 2333909 = 54701) (by norm_num)
theorem B2333933 : Blo 1555475 2333933 := bbase (se 3 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 2333933 = 875225) (by norm_num)
theorem B2333957 : Blo 1555475 2333957 := bbase (se 4 (by rfl) ⟨218808, by rfl⟩ : syracuseStep 2333957 = 437617) (by norm_num)
theorem B4431125 : Blo 1555475 4431125 := bbase (se 6 (by rfl) ⟨103854, by rfl⟩ : syracuseStep 4431125 = 207709) (by norm_num)
theorem B2333981 : Blo 1555475 2333981 := bbase (se 3 (by rfl) ⟨437621, by rfl⟩ : syracuseStep 2333981 = 875243) (by norm_num)
theorem B2334005 : Blo 1555475 2334005 := bbase (se 5 (by rfl) ⟨109406, by rfl⟩ : syracuseStep 2334005 = 218813) (by norm_num)
theorem B3939637 : Blo 1555475 3939637 := bbase (se 5 (by rfl) ⟨184670, by rfl⟩ : syracuseStep 3939637 = 369341) (by norm_num)
theorem B2334029 : Blo 1555475 2334029 := bbase (se 3 (by rfl) ⟨437630, by rfl⟩ : syracuseStep 2334029 = 875261) (by norm_num)
theorem B67304789 : Blo 1555475 67304789 := bbase (se 11 (by rfl) ⟨49295, by rfl⟩ : syracuseStep 67304789 = 98591) (by norm_num)
theorem B2366813 : Blo 1555475 2366813 := bbase (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) (by norm_num)
theorem B2334053 : Blo 1555475 2334053 := bbase (se 4 (by rfl) ⟨218817, by rfl⟩ : syracuseStep 2334053 = 437635) (by norm_num)
theorem B1662325 : Blo 1555475 1662325 := bbase (se 5 (by rfl) ⟨77921, by rfl⟩ : syracuseStep 1662325 = 155843) (by norm_num)
theorem B2334077 : Blo 1555475 2334077 := bbase (se 3 (by rfl) ⟨437639, by rfl⟩ : syracuseStep 2334077 = 875279) (by norm_num)
theorem B2334101 : Blo 1555475 2334101 := bbase (se 6 (by rfl) ⟨54705, by rfl⟩ : syracuseStep 2334101 = 109411) (by norm_num)
theorem B3939749 : Blo 1555475 3939749 := bbase (se 4 (by rfl) ⟨369351, by rfl⟩ : syracuseStep 3939749 = 738703) (by norm_num)
theorem B2334125 : Blo 1555475 2334125 := bbase (se 3 (by rfl) ⟨437648, by rfl⟩ : syracuseStep 2334125 = 875297) (by norm_num)
theorem B12795317 : Blo 1555475 12795317 := bbase (se 5 (by rfl) ⟨599780, by rfl⟩ : syracuseStep 12795317 = 1199561) (by norm_num)
theorem B2956733 : Blo 1555475 2956733 := bbase (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) (by norm_num)
theorem B2334149 : Blo 1555475 2334149 := bbase (se 4 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 2334149 = 437653) (by norm_num)
theorem B2334173 : Blo 1555475 2334173 := bbase (se 3 (by rfl) ⟨437657, by rfl⟩ : syracuseStep 2334173 = 875315) (by norm_num)
theorem B7880165 : Blo 1555475 7880165 := bbase (se 4 (by rfl) ⟨738765, by rfl⟩ : syracuseStep 7880165 = 1477531) (by norm_num)
theorem B1662445 : Blo 1555475 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B2334197 : Blo 1555475 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B3153421 : Blo 1555475 3153421 := bbase (se 3 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 3153421 = 1182533) (by norm_num)
theorem B2334221 : Blo 1555475 2334221 := bbase (se 3 (by rfl) ⟨437666, by rfl⟩ : syracuseStep 2334221 = 875333) (by norm_num)
theorem B5250581 : Blo 1555475 5250581 := bbase (se 6 (by rfl) ⟨123060, by rfl⟩ : syracuseStep 5250581 = 246121) (by norm_num)
theorem B2334245 : Blo 1555475 2334245 := bbase (se 4 (by rfl) ⟨218835, by rfl⟩ : syracuseStep 2334245 = 437671) (by norm_num)
theorem B2334269 : Blo 1555475 2334269 := bbase (se 3 (by rfl) ⟨437675, by rfl⟩ : syracuseStep 2334269 = 875351) (by norm_num)
theorem B1621577 : Blo 1555475 1621577 := bbase (se 2 (by rfl) ⟨608091, by rfl⟩ : syracuseStep 1621577 = 1216183) (by norm_num)
theorem B2334293 : Blo 1555475 2334293 := bbase (se 8 (by rfl) ⟨13677, by rfl⟩ : syracuseStep 2334293 = 27355) (by norm_num)
theorem B3939941 : Blo 1555475 3939941 := bbase (se 4 (by rfl) ⟨369369, by rfl⟩ : syracuseStep 3939941 = 738739) (by norm_num)
theorem B2334317 : Blo 1555475 2334317 := bbase (se 3 (by rfl) ⟨437684, by rfl⟩ : syracuseStep 2334317 = 875369) (by norm_num)
theorem B2334341 : Blo 1555475 2334341 := bbase (se 4 (by rfl) ⟨218844, by rfl⟩ : syracuseStep 2334341 = 437689) (by norm_num)
theorem B3325573 : Blo 1555475 3325573 := bbase (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) (by norm_num)
theorem B2334365 : Blo 1555475 2334365 := bbase (se 3 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 2334365 = 875387) (by norm_num)
theorem B6651557 : Blo 1555475 6651557 := bbase (se 4 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 6651557 = 1247167) (by norm_num)
theorem B2334389 : Blo 1555475 2334389 := bbase (se 5 (by rfl) ⟨109424, by rfl⟩ : syracuseStep 2334389 = 218849) (by norm_num)
theorem B2334413 : Blo 1555475 2334413 := bbase (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) (by norm_num)
theorem B2334437 : Blo 1555475 2334437 := bbase (se 4 (by rfl) ⟨218853, by rfl⟩ : syracuseStep 2334437 = 437707) (by norm_num)
theorem B1662697 : Blo 1555475 1662697 := bbase (se 2 (by rfl) ⟨623511, by rfl⟩ : syracuseStep 1662697 = 1247023) (by norm_num)
theorem B1662701 : Blo 1555475 1662701 := bbase (se 3 (by rfl) ⟨311756, by rfl⟩ : syracuseStep 1662701 = 623513) (by norm_num)
theorem B2334461 : Blo 1555475 2334461 := bbase (se 3 (by rfl) ⟨437711, by rfl⟩ : syracuseStep 2334461 = 875423) (by norm_num)
theorem B3325693 : Blo 1555475 3325693 := bbase (se 3 (by rfl) ⟨623567, by rfl⟩ : syracuseStep 3325693 = 1247135) (by norm_num)
theorem B2334485 : Blo 1555475 2334485 := bbase (se 6 (by rfl) ⟨54714, by rfl⟩ : syracuseStep 2334485 = 109429) (by norm_num)
theorem B2334509 : Blo 1555475 2334509 := bbase (se 3 (by rfl) ⟨437720, by rfl⟩ : syracuseStep 2334509 = 875441) (by norm_num)
theorem B2334533 : Blo 1555475 2334533 := bbase (se 4 (by rfl) ⟨218862, by rfl⟩ : syracuseStep 2334533 = 437725) (by norm_num)
theorem B2334557 : Blo 1555475 2334557 := bbase (se 3 (by rfl) ⟨437729, by rfl⟩ : syracuseStep 2334557 = 875459) (by norm_num)
theorem B6307685 : Blo 1555475 6307685 := bbase (se 4 (by rfl) ⟨591345, by rfl⟩ : syracuseStep 6307685 = 1182691) (by norm_num)
theorem B2334581 : Blo 1555475 2334581 := bbase (se 5 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 2334581 = 218867) (by norm_num)
theorem B2334605 : Blo 1555475 2334605 := bbase (se 3 (by rfl) ⟨437738, by rfl⟩ : syracuseStep 2334605 = 875477) (by norm_num)
theorem B2334629 : Blo 1555475 2334629 := bbase (se 4 (by rfl) ⟨218871, by rfl⟩ : syracuseStep 2334629 = 437743) (by norm_num)
theorem B4431797 : Blo 1555475 4431797 := bbase (se 5 (by rfl) ⟨207740, by rfl⟩ : syracuseStep 4431797 = 415481) (by norm_num)
theorem B2334653 : Blo 1555475 2334653 := bbase (se 3 (by rfl) ⟨437747, by rfl⟩ : syracuseStep 2334653 = 875495) (by norm_num)
theorem B3940285 : Blo 1555475 3940285 := bbase (se 3 (by rfl) ⟨738803, by rfl⟩ : syracuseStep 3940285 = 1477607) (by norm_num)
theorem B5251013 : Blo 1555475 5251013 := bbase (se 4 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 5251013 = 984565) (by norm_num)
theorem B2334677 : Blo 1555475 2334677 := bbase (se 7 (by rfl) ⟨27359, by rfl⟩ : syracuseStep 2334677 = 54719) (by norm_num)
theorem B2334701 : Blo 1555475 2334701 := bbase (se 3 (by rfl) ⟨437756, by rfl⟩ : syracuseStep 2334701 = 875513) (by norm_num)
theorem B3325949 : Blo 1555475 3325949 := bbase (se 3 (by rfl) ⟨623615, by rfl⟩ : syracuseStep 3325949 = 1247231) (by norm_num)
theorem B1556483 : Blo 1555475 1556483 := bstep (se 1 (by rfl) ⟨1167362, by rfl⟩ : syracuseStep 1556483 = 2334725) B2334725
theorem B2334737 : Blo 1555475 2334737 := bstep (se 2 (by rfl) ⟨875526, by rfl⟩ : syracuseStep 2334737 = 1751053) B1751053
theorem B1556499 : Blo 1555475 1556499 := bstep (se 1 (by rfl) ⟨1167374, by rfl⟩ : syracuseStep 1556499 = 2334749) B2334749
theorem B2334755 : Blo 1555475 2334755 := bstep (se 1 (by rfl) ⟨1751066, by rfl⟩ : syracuseStep 2334755 = 3502133) B3502133
theorem B1556515 : Blo 1555475 1556515 := bstep (se 1 (by rfl) ⟨1167386, by rfl⟩ : syracuseStep 1556515 = 2334773) B2334773
theorem B5251121 : Blo 1555475 5251121 := bstep (se 2 (by rfl) ⟨1969170, by rfl⟩ : syracuseStep 5251121 = 3938341) B3938341
theorem B2662451 : Blo 1555475 2662451 := bstep (se 1 (by rfl) ⟨1996838, by rfl⟩ : syracuseStep 2662451 = 3993677) B3993677
theorem B1556531 : Blo 1555475 1556531 := bstep (se 1 (by rfl) ⟨1167398, by rfl⟩ : syracuseStep 1556531 = 2334797) B2334797
theorem B2334785 : Blo 1555475 2334785 := bstep (se 2 (by rfl) ⟨875544, by rfl⟩ : syracuseStep 2334785 = 1751089) B1751089
theorem B1556547 : Blo 1555475 1556547 := bstep (se 1 (by rfl) ⟨1167410, by rfl⟩ : syracuseStep 1556547 = 2334821) B2334821
theorem B14950469 : Blo 1555475 14950469 := bstep (se 4 (by rfl) ⟨1401606, by rfl⟩ : syracuseStep 14950469 = 2803213) B2803213
theorem B2334803 : Blo 1555475 2334803 := bstep (se 1 (by rfl) ⟨1751102, by rfl⟩ : syracuseStep 2334803 = 3502205) B3502205
theorem B1556563 : Blo 1555475 1556563 := bstep (se 1 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 1556563 = 2334845) B2334845
theorem B1556579 : Blo 1555475 1556579 := bstep (se 1 (by rfl) ⟨1167434, by rfl⟩ : syracuseStep 1556579 = 2334869) B2334869
theorem B2334833 : Blo 1555475 2334833 := bstep (se 2 (by rfl) ⟨875562, by rfl⟩ : syracuseStep 2334833 = 1751125) B1751125
theorem B1556595 : Blo 1555475 1556595 := bstep (se 1 (by rfl) ⟨1167446, by rfl⟩ : syracuseStep 1556595 = 2334893) B2334893
theorem B2334851 : Blo 1555475 2334851 := bstep (se 1 (by rfl) ⟨1751138, by rfl⟩ : syracuseStep 2334851 = 3502277) B3502277
theorem B1556611 : Blo 1555475 1556611 := bstep (se 1 (by rfl) ⟨1167458, by rfl⟩ : syracuseStep 1556611 = 2334917) B2334917
theorem B1556627 : Blo 1555475 1556627 := bstep (se 1 (by rfl) ⟨1167470, by rfl⟩ : syracuseStep 1556627 = 2334941) B2334941
theorem B2334881 : Blo 1555475 2334881 := bstep (se 2 (by rfl) ⟨875580, by rfl⟩ : syracuseStep 2334881 = 1751161) B1751161
theorem B1556643 : Blo 1555475 1556643 := bstep (se 1 (by rfl) ⟨1167482, by rfl⟩ : syracuseStep 1556643 = 2334965) B2334965
theorem B2334899 : Blo 1555475 2334899 := bstep (se 1 (by rfl) ⟨1751174, by rfl⟩ : syracuseStep 2334899 = 3502349) B3502349
theorem B1556659 : Blo 1555475 1556659 := bstep (se 1 (by rfl) ⟨1167494, by rfl⟩ : syracuseStep 1556659 = 2334989) B2334989
theorem B1556675 : Blo 1555475 1556675 := bstep (se 1 (by rfl) ⟨1167506, by rfl⟩ : syracuseStep 1556675 = 2335013) B2335013
theorem B2334929 : Blo 1555475 2334929 := bstep (se 2 (by rfl) ⟨875598, by rfl⟩ : syracuseStep 2334929 = 1751197) B1751197
theorem B1556691 : Blo 1555475 1556691 := bstep (se 1 (by rfl) ⟨1167518, by rfl⟩ : syracuseStep 1556691 = 2335037) B2335037
theorem B2334947 : Blo 1555475 2334947 := bstep (se 1 (by rfl) ⟨1751210, by rfl⟩ : syracuseStep 2334947 = 3502421) B3502421
theorem B1556707 : Blo 1555475 1556707 := bstep (se 1 (by rfl) ⟨1167530, by rfl⟩ : syracuseStep 1556707 = 2335061) B2335061
theorem B5325041 : Blo 1555475 5325041 := bstep (se 2 (by rfl) ⟨1996890, by rfl⟩ : syracuseStep 5325041 = 3993781) B3993781
theorem B1556723 : Blo 1555475 1556723 := bstep (se 1 (by rfl) ⟨1167542, by rfl⟩ : syracuseStep 1556723 = 2335085) B2335085
theorem B2334977 : Blo 1555475 2334977 := bstep (se 2 (by rfl) ⟨875616, by rfl⟩ : syracuseStep 2334977 = 1751233) B1751233
theorem B1556739 : Blo 1555475 1556739 := bstep (se 1 (by rfl) ⟨1167554, by rfl⟩ : syracuseStep 1556739 = 2335109) B2335109
theorem B2334995 : Blo 1555475 2334995 := bstep (se 1 (by rfl) ⟨1751246, by rfl⟩ : syracuseStep 2334995 = 3502493) B3502493
theorem B1556755 : Blo 1555475 1556755 := bstep (se 1 (by rfl) ⟨1167566, by rfl⟩ : syracuseStep 1556755 = 2335133) B2335133
theorem B1556771 : Blo 1555475 1556771 := bstep (se 1 (by rfl) ⟨1167578, by rfl⟩ : syracuseStep 1556771 = 2335157) B2335157
theorem B2335025 : Blo 1555475 2335025 := bstep (se 2 (by rfl) ⟨875634, by rfl⟩ : syracuseStep 2335025 = 1751269) B1751269
theorem B1556787 : Blo 1555475 1556787 := bstep (se 1 (by rfl) ⟨1167590, by rfl⟩ : syracuseStep 1556787 = 2335181) B2335181
theorem B2335043 : Blo 1555475 2335043 := bstep (se 1 (by rfl) ⟨1751282, by rfl⟩ : syracuseStep 2335043 = 3502565) B3502565
theorem B1556803 : Blo 1555475 1556803 := bstep (se 1 (by rfl) ⟨1167602, by rfl⟩ : syracuseStep 1556803 = 2335205) B2335205
theorem B1556819 : Blo 1555475 1556819 := bstep (se 1 (by rfl) ⟨1167614, by rfl⟩ : syracuseStep 1556819 = 2335229) B2335229
theorem B2335073 : Blo 1555475 2335073 := bstep (se 2 (by rfl) ⟨875652, by rfl⟩ : syracuseStep 2335073 = 1751305) B1751305
theorem B1556835 : Blo 1555475 1556835 := bstep (se 1 (by rfl) ⟨1167626, by rfl⟩ : syracuseStep 1556835 = 2335253) B2335253
theorem B3940721 : Blo 1555475 3940721 := bstep (se 2 (by rfl) ⟨1477770, by rfl⟩ : syracuseStep 3940721 = 2955541) B2955541
theorem B2335091 : Blo 1555475 2335091 := bstep (se 1 (by rfl) ⟨1751318, by rfl⟩ : syracuseStep 2335091 = 3502637) B3502637
theorem B1556851 : Blo 1555475 1556851 := bstep (se 1 (by rfl) ⟨1167638, by rfl⟩ : syracuseStep 1556851 = 2335277) B2335277
theorem B1556867 : Blo 1555475 1556867 := bstep (se 1 (by rfl) ⟨1167650, by rfl⟩ : syracuseStep 1556867 = 2335301) B2335301
theorem B2335121 : Blo 1555475 2335121 := bstep (se 2 (by rfl) ⟨875670, by rfl⟩ : syracuseStep 2335121 = 1751341) B1751341
theorem B1556883 : Blo 1555475 1556883 := bstep (se 1 (by rfl) ⟨1167662, by rfl⟩ : syracuseStep 1556883 = 2335325) B2335325
theorem B2335139 : Blo 1555475 2335139 := bstep (se 1 (by rfl) ⟨1751354, by rfl⟩ : syracuseStep 2335139 = 3502709) B3502709
theorem B3940771 : Blo 1555475 3940771 := bstep (se 1 (by rfl) ⟨2955578, by rfl⟩ : syracuseStep 3940771 = 5911157) B5911157
theorem B1556899 : Blo 1555475 1556899 := bstep (se 1 (by rfl) ⟨1167674, by rfl⟩ : syracuseStep 1556899 = 2335349) B2335349
theorem B7881137 : Blo 1555475 7881137 := bstep (se 2 (by rfl) ⟨2955426, by rfl⟩ : syracuseStep 7881137 = 5910853) B5910853
theorem B1556915 : Blo 1555475 1556915 := bstep (se 1 (by rfl) ⟨1167686, by rfl⟩ : syracuseStep 1556915 = 2335373) B2335373
theorem B2335169 : Blo 1555475 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B1556931 : Blo 1555475 1556931 := bstep (se 1 (by rfl) ⟨1167698, by rfl⟩ : syracuseStep 1556931 = 2335397) B2335397
theorem B2335187 : Blo 1555475 2335187 := bstep (se 1 (by rfl) ⟨1751390, by rfl⟩ : syracuseStep 2335187 = 3502781) B3502781
theorem B1556947 : Blo 1555475 1556947 := bstep (se 1 (by rfl) ⟨1167710, by rfl⟩ : syracuseStep 1556947 = 2335421) B2335421
theorem B1556963 : Blo 1555475 1556963 := bstep (se 1 (by rfl) ⟨1167722, by rfl⟩ : syracuseStep 1556963 = 2335445) B2335445
theorem B2335217 : Blo 1555475 2335217 := bstep (se 2 (by rfl) ⟨875706, by rfl⟩ : syracuseStep 2335217 = 1751413) B1751413
theorem B1556979 : Blo 1555475 1556979 := bstep (se 1 (by rfl) ⟨1167734, by rfl⟩ : syracuseStep 1556979 = 2335469) B2335469
theorem B2335235 : Blo 1555475 2335235 := bstep (se 1 (by rfl) ⟨1751426, by rfl⟩ : syracuseStep 2335235 = 3502853) B3502853
theorem B1556995 : Blo 1555475 1556995 := bstep (se 1 (by rfl) ⟨1167746, by rfl⟩ : syracuseStep 1556995 = 2335493) B2335493
theorem B1557011 : Blo 1555475 1557011 := bstep (se 1 (by rfl) ⟨1167758, by rfl⟩ : syracuseStep 1557011 = 2335517) B2335517
theorem B2335265 : Blo 1555475 2335265 := bstep (se 2 (by rfl) ⟨875724, by rfl⟩ : syracuseStep 2335265 = 1751449) B1751449
theorem B6308387 : Blo 1555475 6308387 := bstep (se 1 (by rfl) ⟨4731290, by rfl⟩ : syracuseStep 6308387 = 9462581) B9462581
theorem B1557027 : Blo 1555475 1557027 := bstep (se 1 (by rfl) ⟨1167770, by rfl⟩ : syracuseStep 1557027 = 2335541) B2335541
theorem B3940913 : Blo 1555475 3940913 := bstep (se 2 (by rfl) ⟨1477842, by rfl⟩ : syracuseStep 3940913 = 2955685) B2955685
theorem B2335283 : Blo 1555475 2335283 := bstep (se 1 (by rfl) ⟨1751462, by rfl⟩ : syracuseStep 2335283 = 3502925) B3502925
theorem B1557043 : Blo 1555475 1557043 := bstep (se 1 (by rfl) ⟨1167782, by rfl⟩ : syracuseStep 1557043 = 2335565) B2335565
theorem B1557059 : Blo 1555475 1557059 := bstep (se 1 (by rfl) ⟨1167794, by rfl⟩ : syracuseStep 1557059 = 2335589) B2335589
theorem B17965637 : Blo 1555475 17965637 := bstep (se 4 (by rfl) ⟨1684278, by rfl⟩ : syracuseStep 17965637 = 3368557) B3368557
theorem B5251661 : Blo 1555475 5251661 := bstep (se 3 (by rfl) ⟨984686, by rfl⟩ : syracuseStep 5251661 = 1969373) B1969373
theorem B2335313 : Blo 1555475 2335313 := bstep (se 2 (by rfl) ⟨875742, by rfl⟩ : syracuseStep 2335313 = 1751485) B1751485
theorem B1557075 : Blo 1555475 1557075 := bstep (se 1 (by rfl) ⟨1167806, by rfl⟩ : syracuseStep 1557075 = 2335613) B2335613
theorem B2335331 : Blo 1555475 2335331 := bstep (se 1 (by rfl) ⟨1751498, by rfl⟩ : syracuseStep 2335331 = 3502997) B3502997
theorem B1557091 : Blo 1555475 1557091 := bstep (se 1 (by rfl) ⟨1167818, by rfl⟩ : syracuseStep 1557091 = 2335637) B2335637
theorem B4989539 : Blo 1555475 4989539 := bstep (se 1 (by rfl) ⟨3742154, by rfl⟩ : syracuseStep 4989539 = 7484309) B7484309
theorem B1557107 : Blo 1555475 1557107 := bstep (se 1 (by rfl) ⟨1167830, by rfl⟩ : syracuseStep 1557107 = 2335661) B2335661
theorem B2335361 : Blo 1555475 2335361 := bstep (se 2 (by rfl) ⟨875760, by rfl⟩ : syracuseStep 2335361 = 1751521) B1751521
theorem B5251715 : Blo 1555475 5251715 := bstep (se 1 (by rfl) ⟨3938786, by rfl⟩ : syracuseStep 5251715 = 7877573) B7877573
theorem B1557123 : Blo 1555475 1557123 := bstep (se 1 (by rfl) ⟨1167842, by rfl⟩ : syracuseStep 1557123 = 2335685) B2335685
theorem B2335379 : Blo 1555475 2335379 := bstep (se 1 (by rfl) ⟨1751534, by rfl⟩ : syracuseStep 2335379 = 3503069) B3503069
theorem B1557139 : Blo 1555475 1557139 := bstep (se 1 (by rfl) ⟨1167854, by rfl⟩ : syracuseStep 1557139 = 2335709) B2335709
theorem B1557155 : Blo 1555475 1557155 := bstep (se 1 (by rfl) ⟨1167866, by rfl⟩ : syracuseStep 1557155 = 2335733) B2335733
theorem B7479985 : Blo 1555475 7479985 := bstep (se 2 (by rfl) ⟨2804994, by rfl⟩ : syracuseStep 7479985 = 5609989) B5609989
theorem B2335409 : Blo 1555475 2335409 := bstep (se 2 (by rfl) ⟨875778, by rfl⟩ : syracuseStep 2335409 = 1751557) B1751557
theorem B1557171 : Blo 1555475 1557171 := bstep (se 1 (by rfl) ⟨1167878, by rfl⟩ : syracuseStep 1557171 = 2335757) B2335757
theorem B7103153 : Blo 1555475 7103153 := bstep (se 2 (by rfl) ⟨2663682, by rfl⟩ : syracuseStep 7103153 = 5327365) B5327365
theorem B2335427 : Blo 1555475 2335427 := bstep (se 1 (by rfl) ⟨1751570, by rfl⟩ : syracuseStep 2335427 = 3503141) B3503141
theorem B1557187 : Blo 1555475 1557187 := bstep (se 1 (by rfl) ⟨1167890, by rfl⟩ : syracuseStep 1557187 = 2335781) B2335781
theorem B1557203 : Blo 1555475 1557203 := bstep (se 1 (by rfl) ⟨1167902, by rfl⟩ : syracuseStep 1557203 = 2335805) B2335805
theorem B2335457 : Blo 1555475 2335457 := bstep (se 2 (by rfl) ⟨875796, by rfl⟩ : syracuseStep 2335457 = 1751593) B1751593
theorem B1557219 : Blo 1555475 1557219 := bstep (se 1 (by rfl) ⟨1167914, by rfl⟩ : syracuseStep 1557219 = 2335829) B2335829
theorem B2335475 : Blo 1555475 2335475 := bstep (se 1 (by rfl) ⟨1751606, by rfl⟩ : syracuseStep 2335475 = 3503213) B3503213
theorem B1557235 : Blo 1555475 1557235 := bstep (se 1 (by rfl) ⟨1167926, by rfl⟩ : syracuseStep 1557235 = 2335853) B2335853
theorem B1557251 : Blo 1555475 1557251 := bstep (se 1 (by rfl) ⟨1167938, by rfl⟩ : syracuseStep 1557251 = 2335877) B2335877
theorem B2335505 : Blo 1555475 2335505 := bstep (se 2 (by rfl) ⟨875814, by rfl⟩ : syracuseStep 2335505 = 1751629) B1751629
theorem B1557267 : Blo 1555475 1557267 := bstep (se 1 (by rfl) ⟨1167950, by rfl⟩ : syracuseStep 1557267 = 2335901) B2335901
theorem B2335523 : Blo 1555475 2335523 := bstep (se 1 (by rfl) ⟨1751642, by rfl⟩ : syracuseStep 2335523 = 3503285) B3503285
theorem B1557283 : Blo 1555475 1557283 := bstep (se 1 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 1557283 = 2335925) B2335925
theorem B1557299 : Blo 1555475 1557299 := bstep (se 1 (by rfl) ⟨1167974, by rfl⟩ : syracuseStep 1557299 = 2335949) B2335949
theorem B2335553 : Blo 1555475 2335553 := bstep (se 2 (by rfl) ⟨875832, by rfl⟩ : syracuseStep 2335553 = 1751665) B1751665
theorem B1557315 : Blo 1555475 1557315 := bstep (se 1 (by rfl) ⟨1167986, by rfl⟩ : syracuseStep 1557315 = 2335973) B2335973
theorem B2335571 : Blo 1555475 2335571 := bstep (se 1 (by rfl) ⟨1751678, by rfl⟩ : syracuseStep 2335571 = 3503357) B3503357
theorem B1557331 : Blo 1555475 1557331 := bstep (se 1 (by rfl) ⟨1167998, by rfl⟩ : syracuseStep 1557331 = 2335997) B2335997
theorem B1557347 : Blo 1555475 1557347 := bstep (se 1 (by rfl) ⟨1168010, by rfl⟩ : syracuseStep 1557347 = 2336021) B2336021
theorem B2335601 : Blo 1555475 2335601 := bstep (se 2 (by rfl) ⟨875850, by rfl⟩ : syracuseStep 2335601 = 1751701) B1751701
theorem B1557363 : Blo 1555475 1557363 := bstep (se 1 (by rfl) ⟨1168022, by rfl⟩ : syracuseStep 1557363 = 2336045) B2336045
theorem B2335619 : Blo 1555475 2335619 := bstep (se 1 (by rfl) ⟨1751714, by rfl⟩ : syracuseStep 2335619 = 3503429) B3503429
theorem B1557379 : Blo 1555475 1557379 := bstep (se 1 (by rfl) ⟨1168034, by rfl⟩ : syracuseStep 1557379 = 2336069) B2336069
theorem B5251985 : Blo 1555475 5251985 := bstep (se 2 (by rfl) ⟨1969494, by rfl⟩ : syracuseStep 5251985 = 3938989) B3938989
theorem B1557395 : Blo 1555475 1557395 := bstep (se 1 (by rfl) ⟨1168046, by rfl⟩ : syracuseStep 1557395 = 2336093) B2336093
theorem B2335649 : Blo 1555475 2335649 := bstep (se 2 (by rfl) ⟨875868, by rfl⟩ : syracuseStep 2335649 = 1751737) B1751737
theorem B1557411 : Blo 1555475 1557411 := bstep (se 1 (by rfl) ⟨1168058, by rfl⟩ : syracuseStep 1557411 = 2336117) B2336117
theorem B2335667 : Blo 1555475 2335667 := bstep (se 1 (by rfl) ⟨1751750, by rfl⟩ : syracuseStep 2335667 = 3503501) B3503501
theorem B1557427 : Blo 1555475 1557427 := bstep (se 1 (by rfl) ⟨1168070, by rfl⟩ : syracuseStep 1557427 = 2336141) B2336141
theorem B1557443 : Blo 1555475 1557443 := bstep (se 1 (by rfl) ⟨1168082, by rfl⟩ : syracuseStep 1557443 = 2336165) B2336165
theorem B2335697 : Blo 1555475 2335697 := bstep (se 2 (by rfl) ⟨875886, by rfl⟩ : syracuseStep 2335697 = 1751773) B1751773
theorem B1557459 : Blo 1555475 1557459 := bstep (se 1 (by rfl) ⟨1168094, by rfl⟩ : syracuseStep 1557459 = 2336189) B2336189
theorem B18924515 : Blo 1555475 18924515 := bstep (se 1 (by rfl) ⟨14193386, by rfl⟩ : syracuseStep 18924515 = 28386773) B28386773
theorem B2335715 : Blo 1555475 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B1557475 : Blo 1555475 1557475 := bstep (se 1 (by rfl) ⟨1168106, by rfl⟩ : syracuseStep 1557475 = 2336213) B2336213
theorem B2335745 : Blo 1555475 2335745 := bstep (se 2 (by rfl) ⟨875904, by rfl⟩ : syracuseStep 2335745 = 1751809) B1751809
theorem B4432913 : Blo 1555475 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B2335763 : Blo 1555475 2335763 := bstep (se 1 (by rfl) ⟨1751822, by rfl⟩ : syracuseStep 2335763 = 3503645) B3503645
theorem B2335793 : Blo 1555475 2335793 := bstep (se 2 (by rfl) ⟨875922, by rfl⟩ : syracuseStep 2335793 = 1751845) B1751845
theorem B2245699 : Blo 1555475 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B2335811 : Blo 1555475 2335811 := bstep (se 1 (by rfl) ⟨1751858, by rfl⟩ : syracuseStep 2335811 = 3503717) B3503717
theorem B2335841 : Blo 1555475 2335841 := bstep (se 2 (by rfl) ⟨875940, by rfl⟩ : syracuseStep 2335841 = 1751881) B1751881
theorem B2335859 : Blo 1555475 2335859 := bstep (se 1 (by rfl) ⟨1751894, by rfl⟩ : syracuseStep 2335859 = 3503789) B3503789
theorem B2335889 : Blo 1555475 2335889 := bstep (se 2 (by rfl) ⟨875958, by rfl⟩ : syracuseStep 2335889 = 1751917) B1751917
theorem B2335907 : Blo 1555475 2335907 := bstep (se 1 (by rfl) ⟨1751930, by rfl⟩ : syracuseStep 2335907 = 3503861) B3503861
theorem B2335937 : Blo 1555475 2335937 := bstep (se 2 (by rfl) ⟨875976, by rfl⟩ : syracuseStep 2335937 = 1751953) B1751953
theorem B13477061 : Blo 1555475 13477061 := bstep (se 4 (by rfl) ⟨1263474, by rfl⟩ : syracuseStep 13477061 = 2526949) B2526949
theorem B2335955 : Blo 1555475 2335955 := bstep (se 1 (by rfl) ⟨1751966, by rfl⟩ : syracuseStep 2335955 = 3503933) B3503933
theorem B2335985 : Blo 1555475 2335985 := bstep (se 2 (by rfl) ⟨875994, by rfl⟩ : syracuseStep 2335985 = 1751989) B1751989
theorem B2336003 : Blo 1555475 2336003 := bstep (se 1 (by rfl) ⟨1752002, by rfl⟩ : syracuseStep 2336003 = 3504005) B3504005
theorem B5907725 : Blo 1555475 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B2336033 : Blo 1555475 2336033 := bstep (se 2 (by rfl) ⟨876012, by rfl⟩ : syracuseStep 2336033 = 1752025) B1752025
theorem B2336051 : Blo 1555475 2336051 := bstep (se 1 (by rfl) ⟨1752038, by rfl⟩ : syracuseStep 2336051 = 3504077) B3504077
theorem B2336081 : Blo 1555475 2336081 := bstep (se 2 (by rfl) ⟨876030, by rfl⟩ : syracuseStep 2336081 = 1752061) B1752061
theorem B11822435 : Blo 1555475 11822435 := bstep (se 1 (by rfl) ⟨8866826, by rfl⟩ : syracuseStep 11822435 = 17733653) B17733653
theorem B2336099 : Blo 1555475 2336099 := bstep (se 1 (by rfl) ⟨1752074, by rfl⟩ : syracuseStep 2336099 = 3504149) B3504149
theorem B11527537 : Blo 1555475 11527537 := bstep (se 2 (by rfl) ⟨4322826, by rfl⟩ : syracuseStep 11527537 = 8645653) B8645653
theorem B2336129 : Blo 1555475 2336129 := bstep (se 2 (by rfl) ⟨876048, by rfl⟩ : syracuseStep 2336129 = 1752097) B1752097
theorem B2336147 : Blo 1555475 2336147 := bstep (se 1 (by rfl) ⟨1752110, by rfl⟩ : syracuseStep 2336147 = 3504221) B3504221
theorem B5252525 : Blo 1555475 5252525 := bstep (se 3 (by rfl) ⟨984848, by rfl⟩ : syracuseStep 5252525 = 1969697) B1969697
theorem B2336177 : Blo 1555475 2336177 := bstep (se 2 (by rfl) ⟨876066, by rfl⟩ : syracuseStep 2336177 = 1752133) B1752133
theorem B1869251 : Blo 1555475 1869251 := bstep (se 1 (by rfl) ⟨1401938, by rfl⟩ : syracuseStep 1869251 = 2803877) B2803877
theorem B2336195 : Blo 1555475 2336195 := bstep (se 1 (by rfl) ⟨1752146, by rfl⟩ : syracuseStep 2336195 = 3504293) B3504293
theorem B5252579 : Blo 1555475 5252579 := bstep (se 1 (by rfl) ⟨3939434, by rfl⟩ : syracuseStep 5252579 = 7878869) B7878869
theorem B3941905 : Blo 1555475 3941905 := bstep (se 2 (by rfl) ⟨1478214, by rfl⟩ : syracuseStep 3941905 = 2956429) B2956429
theorem B10643021 : Blo 1555475 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B5252849 : Blo 1555475 5252849 := bstep (se 2 (by rfl) ⟨1969818, by rfl⟩ : syracuseStep 5252849 = 3939637) B3939637
theorem B3942179 : Blo 1555475 3942179 := bstep (se 1 (by rfl) ⟨2956634, by rfl⟩ : syracuseStep 3942179 = 5913269) B5913269
theorem B7882595 : Blo 1555475 7882595 := bstep (se 1 (by rfl) ⟨5911946, by rfl⟩ : syracuseStep 7882595 = 11823893) B11823893
theorem B3549059 : Blo 1555475 3549059 := bstep (se 1 (by rfl) ⟨2661794, by rfl⟩ : syracuseStep 3549059 = 5323589) B5323589
theorem B8865733 : Blo 1555475 8865733 := bstep (se 4 (by rfl) ⟨831162, by rfl⟩ : syracuseStep 8865733 = 1662325) B1662325
theorem B4433869 : Blo 1555475 4433869 := bstep (se 3 (by rfl) ⟨831350, by rfl⟩ : syracuseStep 4433869 = 1662701) B1662701
theorem B4204561 : Blo 1555475 4204561 := bstep (se 2 (by rfl) ⟨1576710, by rfl⟩ : syracuseStep 4204561 = 3153421) B3153421
theorem B3500081 : Blo 1555475 3500081 := bstep (se 2 (by rfl) ⟨1312530, by rfl⟩ : syracuseStep 3500081 = 2625061) B2625061
theorem B3500099 : Blo 1555475 3500099 := bstep (se 1 (by rfl) ⟨2625074, by rfl⟩ : syracuseStep 3500099 = 5250149) B5250149
theorem B1599571 : Blo 1555475 1599571 := bstep (se 1 (by rfl) ⟨1199678, by rfl⟩ : syracuseStep 1599571 = 2399357) B2399357
theorem B53889137 : Blo 1555475 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B9472133 : Blo 1555475 9472133 := bstep (se 4 (by rfl) ⟨888012, by rfl⟩ : syracuseStep 9472133 = 1776025) B1776025
theorem B3991697 : Blo 1555475 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B4434097 : Blo 1555475 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B31951045 : Blo 1555475 31951045 := bstep (se 4 (by rfl) ⟨2995410, by rfl⟩ : syracuseStep 31951045 = 5990821) B5990821
theorem B44869859 : Blo 1555475 44869859 := bstep (se 1 (by rfl) ⟨33652394, by rfl⟩ : syracuseStep 44869859 = 67304789) B67304789
theorem B5253389 : Blo 1555475 5253389 := bstep (se 3 (by rfl) ⟨985010, by rfl⟩ : syracuseStep 5253389 = 1970021) B1970021
theorem B8530211 : Blo 1555475 8530211 := bstep (se 1 (by rfl) ⟨6397658, by rfl⟩ : syracuseStep 8530211 = 12795317) B12795317
theorem B5253443 : Blo 1555475 5253443 := bstep (se 1 (by rfl) ⟨3940082, by rfl⟩ : syracuseStep 5253443 = 7880165) B7880165
theorem B3500369 : Blo 1555475 3500369 := bstep (se 2 (by rfl) ⟨1312638, by rfl⟩ : syracuseStep 3500369 = 2625277) B2625277
theorem B4434257 : Blo 1555475 4434257 := bstep (se 2 (by rfl) ⟨1662846, by rfl⟩ : syracuseStep 4434257 = 3325693) B3325693
theorem B3500387 : Blo 1555475 3500387 := bstep (se 1 (by rfl) ⟨2625290, by rfl⟩ : syracuseStep 3500387 = 5250581) B5250581
theorem B6646157 : Blo 1555475 6646157 := bstep (se 3 (by rfl) ⟨1246154, by rfl⟩ : syracuseStep 6646157 = 2492309) B2492309
theorem B4434371 : Blo 1555475 4434371 := bstep (se 1 (by rfl) ⟨3325778, by rfl⟩ : syracuseStep 4434371 = 6651557) B6651557
theorem B4205123 : Blo 1555475 4205123 := bstep (se 1 (by rfl) ⟨3153842, by rfl⟩ : syracuseStep 4205123 = 6307685) B6307685
theorem B5253713 : Blo 1555475 5253713 := bstep (se 2 (by rfl) ⟨1970142, by rfl⟩ : syracuseStep 5253713 = 3940285) B3940285
theorem B3500657 : Blo 1555475 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B3500675 : Blo 1555475 3500675 := bstep (se 1 (by rfl) ⟨2625506, by rfl⟩ : syracuseStep 3500675 = 5251013) B5251013
theorem B7883405 : Blo 1555475 7883405 := bstep (se 3 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 7883405 = 2956277) B2956277
theorem B6646499 : Blo 1555475 6646499 := bstep (se 1 (by rfl) ⟨4984874, by rfl⟩ : syracuseStep 6646499 = 9969749) B9969749
theorem B2493155 : Blo 1555475 2493155 := bstep (se 1 (by rfl) ⟨1869866, by rfl⟩ : syracuseStep 2493155 = 3739733) B3739733
theorem B4205297 : Blo 1555475 4205297 := bstep (se 2 (by rfl) ⟨1576986, by rfl⟩ : syracuseStep 4205297 = 3153973) B3153973
theorem B2804483 : Blo 1555475 2804483 := bstep (se 1 (by rfl) ⟨2103362, by rfl⟩ : syracuseStep 2804483 = 4206725) B4206725
theorem B4983619 : Blo 1555475 4983619 := bstep (se 1 (by rfl) ⟨3737714, by rfl⟩ : syracuseStep 4983619 = 7475429) B7475429
theorem B2493283 : Blo 1555475 2493283 := bstep (se 1 (by rfl) ⟨1869962, by rfl⟩ : syracuseStep 2493283 = 3739925) B3739925
theorem B3500945 : Blo 1555475 3500945 := bstep (se 2 (by rfl) ⟨1312854, by rfl⟩ : syracuseStep 3500945 = 2625709) B2625709
theorem B3500963 : Blo 1555475 3500963 := bstep (se 1 (by rfl) ⟨2625722, by rfl⟩ : syracuseStep 3500963 = 5251445) B5251445
theorem B2493347 : Blo 1555475 2493347 := bstep (se 1 (by rfl) ⟨1870010, by rfl⟩ : syracuseStep 2493347 = 3740021) B3740021
theorem B9464909 : Blo 1555475 9464909 := bstep (se 3 (by rfl) ⟨1774670, by rfl⟩ : syracuseStep 9464909 = 3549341) B3549341
theorem B4983889 : Blo 1555475 4983889 := bstep (se 2 (by rfl) ⟨1868958, by rfl⟩ : syracuseStep 4983889 = 3737917) B3737917
theorem B5254253 : Blo 1555475 5254253 := bstep (se 3 (by rfl) ⟨985172, by rfl⟩ : syracuseStep 5254253 = 1970345) B1970345
theorem B1969267 : Blo 1555475 1969267 := bstep (se 1 (by rfl) ⟨1476950, by rfl⟩ : syracuseStep 1969267 = 2953901) B2953901
theorem B28404877 : Blo 1555475 28404877 := bstep (se 3 (by rfl) ⟨5325914, by rfl⟩ : syracuseStep 28404877 = 10651829) B10651829
theorem B5254307 : Blo 1555475 5254307 := bstep (se 1 (by rfl) ⟨3940730, by rfl⟩ : syracuseStep 5254307 = 7881461) B7881461
theorem B3501233 : Blo 1555475 3501233 := bstep (se 2 (by rfl) ⟨1312962, by rfl⟩ : syracuseStep 3501233 = 2625925) B2625925
theorem B6646961 : Blo 1555475 6646961 := bstep (se 2 (by rfl) ⟨2492610, by rfl⟩ : syracuseStep 6646961 = 4985221) B4985221
theorem B3501251 : Blo 1555475 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B1969363 : Blo 1555475 1969363 := bstep (se 1 (by rfl) ⟨1477022, by rfl⟩ : syracuseStep 1969363 = 2954045) B2954045
theorem B2993425 : Blo 1555475 2993425 := bstep (se 2 (by rfl) ⟨1122534, by rfl⟩ : syracuseStep 2993425 = 2245069) B2245069
theorem B2805059 : Blo 1555475 2805059 := bstep (se 1 (by rfl) ⟨2103794, by rfl⟩ : syracuseStep 2805059 = 4207589) B4207589
theorem B7875953 : Blo 1555475 7875953 := bstep (se 2 (by rfl) ⟨2953482, by rfl⟩ : syracuseStep 7875953 = 5906965) B5906965
theorem B2624899 : Blo 1555475 2624899 := bstep (se 1 (by rfl) ⟨1968674, by rfl⟩ : syracuseStep 2624899 = 3937349) B3937349
theorem B2493841 : Blo 1555475 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B5254577 : Blo 1555475 5254577 := bstep (se 2 (by rfl) ⟨1970466, by rfl⟩ : syracuseStep 5254577 = 3940933) B3940933
theorem B2215363 : Blo 1555475 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B3501521 : Blo 1555475 3501521 := bstep (se 2 (by rfl) ⟨1313070, by rfl⟩ : syracuseStep 3501521 = 2626141) B2626141
theorem B3501539 : Blo 1555475 3501539 := bstep (se 1 (by rfl) ⟨2626154, by rfl⟩ : syracuseStep 3501539 = 5252309) B5252309
theorem B2625041 : Blo 1555475 2625041 := bstep (se 2 (by rfl) ⟨984390, by rfl⟩ : syracuseStep 2625041 = 1968781) B1968781
theorem B2805283 : Blo 1555475 2805283 := bstep (se 1 (by rfl) ⟨2103962, by rfl⟩ : syracuseStep 2805283 = 4207925) B4207925
theorem B2625169 : Blo 1555475 2625169 := bstep (se 2 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 2625169 = 1968877) B1968877
theorem B2625203 : Blo 1555475 2625203 := bstep (se 1 (by rfl) ⟨1968902, by rfl⟩ : syracuseStep 2625203 = 3937805) B3937805
theorem B1969859 : Blo 1555475 1969859 := bstep (se 1 (by rfl) ⟨1477394, by rfl⟩ : syracuseStep 1969859 = 2954789) B2954789
theorem B3501809 : Blo 1555475 3501809 := bstep (se 2 (by rfl) ⟨1313178, by rfl⟩ : syracuseStep 3501809 = 2626357) B2626357
theorem B3501827 : Blo 1555475 3501827 := bstep (se 1 (by rfl) ⟨2626370, by rfl⟩ : syracuseStep 3501827 = 5252741) B5252741
theorem B2625331 : Blo 1555475 2625331 := bstep (se 1 (by rfl) ⟨1968998, by rfl⟩ : syracuseStep 2625331 = 3937997) B3937997
theorem B2953027 : Blo 1555475 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B2953073 : Blo 1555475 2953073 := bstep (se 2 (by rfl) ⟨1107402, by rfl⟩ : syracuseStep 2953073 = 2214805) B2214805
theorem B2805635 : Blo 1555475 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B8867717 : Blo 1555475 8867717 := bstep (se 4 (by rfl) ⟨831348, by rfl⟩ : syracuseStep 8867717 = 1662697) B1662697
theorem B14585741 : Blo 1555475 14585741 := bstep (se 3 (by rfl) ⟨2734826, by rfl⟩ : syracuseStep 14585741 = 5469653) B5469653
theorem B2215841 : Blo 1555475 2215841 := bstep (se 2 (by rfl) ⟨830940, by rfl⟩ : syracuseStep 2215841 = 1661881) B1661881
theorem B2625473 : Blo 1555475 2625473 := bstep (se 2 (by rfl) ⟨984552, by rfl⟩ : syracuseStep 2625473 = 1969105) B1969105
theorem B33673157 : Blo 1555475 33673157 := bstep (se 4 (by rfl) ⟨3156858, by rfl⟩ : syracuseStep 33673157 = 6313717) B6313717
theorem B5255117 : Blo 1555475 5255117 := bstep (se 3 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 5255117 = 1970669) B1970669
theorem B12627953 : Blo 1555475 12627953 := bstep (se 2 (by rfl) ⟨4735482, by rfl⟩ : syracuseStep 12627953 = 9470965) B9470965
theorem B5255171 : Blo 1555475 5255171 := bstep (se 1 (by rfl) ⟨3941378, by rfl⟩ : syracuseStep 5255171 = 7882757) B7882757
theorem B3502097 : Blo 1555475 3502097 := bstep (se 2 (by rfl) ⟨1313286, by rfl⟩ : syracuseStep 3502097 = 2626573) B2626573
theorem B2215955 : Blo 1555475 2215955 := bstep (se 1 (by rfl) ⟨1661966, by rfl⟩ : syracuseStep 2215955 = 3323933) B3323933
theorem B2920483 : Blo 1555475 2920483 := bstep (se 1 (by rfl) ⟨2190362, by rfl⟩ : syracuseStep 2920483 = 4380725) B4380725
theorem B3502115 : Blo 1555475 3502115 := bstep (se 1 (by rfl) ⟨2626586, by rfl⟩ : syracuseStep 3502115 = 5253173) B5253173
theorem B5689379 : Blo 1555475 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B2494513 : Blo 1555475 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B2625601 : Blo 1555475 2625601 := bstep (se 2 (by rfl) ⟨984600, by rfl⟩ : syracuseStep 2625601 = 1969201) B1969201
theorem B2625635 : Blo 1555475 2625635 := bstep (se 1 (by rfl) ⟨1969226, by rfl⟩ : syracuseStep 2625635 = 3938453) B3938453
theorem B2216035 : Blo 1555475 2216035 := bstep (se 1 (by rfl) ⟨1662026, by rfl⟩ : syracuseStep 2216035 = 3324053) B3324053
theorem B5992547 : Blo 1555475 5992547 := bstep (se 1 (by rfl) ⟨4494410, by rfl⟩ : syracuseStep 5992547 = 8988821) B8988821
theorem B5910641 : Blo 1555475 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B7983245 : Blo 1555475 7983245 := bstep (se 3 (by rfl) ⟨1496858, by rfl⟩ : syracuseStep 7983245 = 2993717) B2993717
theorem B2953361 : Blo 1555475 2953361 := bstep (se 2 (by rfl) ⟨1107510, by rfl⟩ : syracuseStep 2953361 = 2215021) B2215021
theorem B2625763 : Blo 1555475 2625763 := bstep (se 1 (by rfl) ⟨1969322, by rfl⟩ : syracuseStep 2625763 = 3938645) B3938645
theorem B5255441 : Blo 1555475 5255441 := bstep (se 2 (by rfl) ⟨1970790, by rfl⟩ : syracuseStep 5255441 = 3941581) B3941581
theorem B3502385 : Blo 1555475 3502385 := bstep (se 2 (by rfl) ⟨1313394, by rfl⟩ : syracuseStep 3502385 = 2626789) B2626789
theorem B4731203 : Blo 1555475 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B3502403 : Blo 1555475 3502403 := bstep (se 1 (by rfl) ⟨2626802, by rfl⟩ : syracuseStep 3502403 = 5253605) B5253605
theorem B13300037 : Blo 1555475 13300037 := bstep (se 4 (by rfl) ⟨1246878, by rfl⟩ : syracuseStep 13300037 = 2493757) B2493757
theorem B1683811 : Blo 1555475 1683811 := bstep (se 1 (by rfl) ⟨1262858, by rfl⟩ : syracuseStep 1683811 = 2525717) B2525717
theorem B2625905 : Blo 1555475 2625905 := bstep (se 2 (by rfl) ⟨984714, by rfl⟩ : syracuseStep 2625905 = 1969429) B1969429
theorem B1970563 : Blo 1555475 1970563 := bstep (se 1 (by rfl) ⟨1477922, by rfl⟩ : syracuseStep 1970563 = 2955845) B2955845
theorem B4731299 : Blo 1555475 4731299 := bstep (se 1 (by rfl) ⟨3548474, by rfl⟩ : syracuseStep 4731299 = 7096949) B7096949
theorem B22434245 : Blo 1555475 22434245 := bstep (se 4 (by rfl) ⟨2103210, by rfl⟩ : syracuseStep 22434245 = 4206421) B4206421
theorem B1970659 : Blo 1555475 1970659 := bstep (se 1 (by rfl) ⟨1477994, by rfl⟩ : syracuseStep 1970659 = 2955989) B2955989
theorem B2626033 : Blo 1555475 2626033 := bstep (se 2 (by rfl) ⟨984762, by rfl⟩ : syracuseStep 2626033 = 1969525) B1969525
theorem B2626067 : Blo 1555475 2626067 := bstep (se 1 (by rfl) ⟨1969550, by rfl⟩ : syracuseStep 2626067 = 3939101) B3939101
theorem B3551779 : Blo 1555475 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B3502673 : Blo 1555475 3502673 := bstep (se 2 (by rfl) ⟨1313502, by rfl⟩ : syracuseStep 3502673 = 2627005) B2627005
theorem B3551825 : Blo 1555475 3551825 := bstep (se 2 (by rfl) ⟨1331934, by rfl⟩ : syracuseStep 3551825 = 2663869) B2663869
theorem B3994211 : Blo 1555475 3994211 := bstep (se 1 (by rfl) ⟨2995658, by rfl⟩ : syracuseStep 3994211 = 5991317) B5991317
theorem B17732195 : Blo 1555475 17732195 := bstep (se 1 (by rfl) ⟨13299146, by rfl⟩ : syracuseStep 17732195 = 26598293) B26598293
theorem B3502691 : Blo 1555475 3502691 := bstep (se 1 (by rfl) ⟨2627018, by rfl⟩ : syracuseStep 3502691 = 5254037) B5254037
theorem B4985489 : Blo 1555475 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B2216593 : Blo 1555475 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B2626195 : Blo 1555475 2626195 := bstep (se 1 (by rfl) ⟨1969646, by rfl⟩ : syracuseStep 2626195 = 3939293) B3939293
theorem B1577651 : Blo 1555475 1577651 := bstep (se 1 (by rfl) ⟨1183238, by rfl⟩ : syracuseStep 1577651 = 2366477) B2366477
theorem B9966341 : Blo 1555475 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B4207373 : Blo 1555475 4207373 := bstep (se 3 (by rfl) ⟨788882, by rfl⟩ : syracuseStep 4207373 = 1577765) B1577765
theorem B1684243 : Blo 1555475 1684243 := bstep (se 1 (by rfl) ⟨1263182, by rfl⟩ : syracuseStep 1684243 = 2526365) B2526365
theorem B2626337 : Blo 1555475 2626337 := bstep (se 2 (by rfl) ⟨984876, by rfl⟩ : syracuseStep 2626337 = 1969753) B1969753
theorem B7877411 : Blo 1555475 7877411 := bstep (se 1 (by rfl) ⟨5908058, by rfl⟩ : syracuseStep 7877411 = 11816117) B11816117
theorem B5255981 : Blo 1555475 5255981 := bstep (se 3 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 5255981 = 1970993) B1970993
theorem B8418097 : Blo 1555475 8418097 := bstep (se 2 (by rfl) ⟨3156786, by rfl⟩ : syracuseStep 8418097 = 6313573) B6313573
theorem B2954083 : Blo 1555475 2954083 := bstep (se 1 (by rfl) ⟨2215562, by rfl⟩ : syracuseStep 2954083 = 4431125) B4431125
theorem B5256035 : Blo 1555475 5256035 := bstep (se 1 (by rfl) ⟨3942026, by rfl⟩ : syracuseStep 5256035 = 7884053) B7884053
theorem B3502961 : Blo 1555475 3502961 := bstep (se 2 (by rfl) ⟨1313610, by rfl⟩ : syracuseStep 3502961 = 2627221) B2627221
theorem B3502979 : Blo 1555475 3502979 := bstep (se 1 (by rfl) ⟨2627234, by rfl⟩ : syracuseStep 3502979 = 5254469) B5254469
theorem B1577875 : Blo 1555475 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B2626465 : Blo 1555475 2626465 := bstep (se 2 (by rfl) ⟨984924, by rfl⟩ : syracuseStep 2626465 = 1969849) B1969849
theorem B1749955 : Blo 1555475 1749955 := bstep (se 1 (by rfl) ⟨1312466, by rfl⟩ : syracuseStep 1749955 = 2624933) B2624933
theorem B2626499 : Blo 1555475 2626499 := bstep (se 1 (by rfl) ⟨1969874, by rfl⟩ : syracuseStep 2626499 = 3939749) B3939749
theorem B1971155 : Blo 1555475 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B4985837 : Blo 1555475 4985837 := bstep (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) B1869689
theorem B2626627 : Blo 1555475 2626627 := bstep (se 1 (by rfl) ⟨1969970, by rfl⟩ : syracuseStep 2626627 = 3939941) B3939941
theorem B1750099 : Blo 1555475 1750099 := bstep (se 1 (by rfl) ⟨1312574, by rfl⟩ : syracuseStep 1750099 = 2625149) B2625149
theorem B5256305 : Blo 1555475 5256305 := bstep (se 2 (by rfl) ⟨1971114, by rfl⟩ : syracuseStep 5256305 = 3942229) B3942229
theorem B3503249 : Blo 1555475 3503249 := bstep (se 2 (by rfl) ⟨1313718, by rfl⟩ : syracuseStep 3503249 = 2627437) B2627437
theorem B3503267 : Blo 1555475 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B2102449 : Blo 1555475 2102449 := bstep (se 2 (by rfl) ⟨788418, by rfl⟩ : syracuseStep 2102449 = 1576837) B1576837
theorem B2626769 : Blo 1555475 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B1750243 : Blo 1555475 1750243 := bstep (se 1 (by rfl) ⟨1312682, by rfl⟩ : syracuseStep 1750243 = 2625365) B2625365
theorem B2954531 : Blo 1555475 2954531 := bstep (se 1 (by rfl) ⟨2215898, by rfl⟩ : syracuseStep 2954531 = 4431797) B4431797
theorem B2626897 : Blo 1555475 2626897 := bstep (se 2 (by rfl) ⟨985086, by rfl⟩ : syracuseStep 2626897 = 1970173) B1970173
theorem B2217299 : Blo 1555475 2217299 := bstep (se 1 (by rfl) ⟨1662974, by rfl⟩ : syracuseStep 2217299 = 3325949) B3325949
theorem B6313315 : Blo 1555475 6313315 := bstep (se 1 (by rfl) ⟨4734986, by rfl⟩ : syracuseStep 6313315 = 9469973) B9469973
theorem B1750387 : Blo 1555475 1750387 := bstep (se 1 (by rfl) ⟨1312790, by rfl⟩ : syracuseStep 1750387 = 2625581) B2625581
theorem B1774963 : Blo 1555475 1774963 := bstep (se 1 (by rfl) ⟨1331222, by rfl⟩ : syracuseStep 1774963 = 2662445) B2662445
theorem B2626931 : Blo 1555475 2626931 := bstep (se 1 (by rfl) ⟨1970198, by rfl⟩ : syracuseStep 2626931 = 3940397) B3940397
theorem B3503537 : Blo 1555475 3503537 := bstep (se 2 (by rfl) ⟨1313826, by rfl⟩ : syracuseStep 3503537 = 2627653) B2627653
theorem B3503555 : Blo 1555475 3503555 := bstep (se 1 (by rfl) ⟨2627666, by rfl⟩ : syracuseStep 3503555 = 5255333) B5255333
theorem B2627059 : Blo 1555475 2627059 := bstep (se 1 (by rfl) ⟨1970294, by rfl⟩ : syracuseStep 2627059 = 3940589) B3940589
theorem B1750531 : Blo 1555475 1750531 := bstep (se 1 (by rfl) ⟨1312898, by rfl⟩ : syracuseStep 1750531 = 2625797) B2625797
theorem B5912099 : Blo 1555475 5912099 := bstep (se 1 (by rfl) ⟨4434074, by rfl⟩ : syracuseStep 5912099 = 8868149) B8868149
theorem B2954819 : Blo 1555475 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B7878221 : Blo 1555475 7878221 := bstep (se 3 (by rfl) ⟨1477166, by rfl⟩ : syracuseStep 7878221 = 2954333) B2954333
theorem B2627201 : Blo 1555475 2627201 := bstep (se 2 (by rfl) ⟨985200, by rfl⟩ : syracuseStep 2627201 = 1970401) B1970401
theorem B1750675 : Blo 1555475 1750675 := bstep (se 1 (by rfl) ⟨1313006, by rfl⟩ : syracuseStep 1750675 = 2626013) B2626013
theorem B3503825 : Blo 1555475 3503825 := bstep (se 2 (by rfl) ⟨1313934, by rfl⟩ : syracuseStep 3503825 = 2627869) B2627869
theorem B3503843 : Blo 1555475 3503843 := bstep (se 1 (by rfl) ⟨2627882, by rfl⟩ : syracuseStep 3503843 = 5255765) B5255765
theorem B2627329 : Blo 1555475 2627329 := bstep (se 2 (by rfl) ⟨985248, by rfl⟩ : syracuseStep 2627329 = 1970497) B1970497
theorem B1750819 : Blo 1555475 1750819 := bstep (se 1 (by rfl) ⟨1313114, by rfl⟩ : syracuseStep 1750819 = 2626229) B2626229
theorem B2627363 : Blo 1555475 2627363 := bstep (se 1 (by rfl) ⟨1970522, by rfl⟩ : syracuseStep 2627363 = 3941045) B3941045
theorem B3938129 : Blo 1555475 3938129 := bstep (se 2 (by rfl) ⟨1476798, by rfl⟩ : syracuseStep 3938129 = 2953597) B2953597
theorem B4429667 : Blo 1555475 4429667 := bstep (se 1 (by rfl) ⟨3322250, by rfl⟩ : syracuseStep 4429667 = 6644501) B6644501
theorem B10647395 : Blo 1555475 10647395 := bstep (se 1 (by rfl) ⟨7985546, by rfl⟩ : syracuseStep 10647395 = 15971093) B15971093
theorem B3938179 : Blo 1555475 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B2627491 : Blo 1555475 2627491 := bstep (se 1 (by rfl) ⟨1970618, by rfl⟩ : syracuseStep 2627491 = 3941237) B3941237
theorem B1750963 : Blo 1555475 1750963 := bstep (se 1 (by rfl) ⟨1313222, by rfl⟩ : syracuseStep 1750963 = 2626445) B2626445
theorem B3504113 : Blo 1555475 3504113 := bstep (se 2 (by rfl) ⟨1314042, by rfl⟩ : syracuseStep 3504113 = 2628085) B2628085
theorem B3504131 : Blo 1555475 3504131 := bstep (se 1 (by rfl) ⟨2628098, by rfl⟩ : syracuseStep 3504131 = 5256197) B5256197
theorem B3938321 : Blo 1555475 3938321 := bstep (se 2 (by rfl) ⟨1476870, by rfl⟩ : syracuseStep 3938321 = 2953741) B2953741
theorem B2627633 : Blo 1555475 2627633 := bstep (se 2 (by rfl) ⟨985362, by rfl⟩ : syracuseStep 2627633 = 1970725) B1970725
theorem B1751107 : Blo 1555475 1751107 := bstep (se 1 (by rfl) ⟨1313330, by rfl⟩ : syracuseStep 1751107 = 2626661) B2626661
theorem B3324035 : Blo 1555475 3324035 := bstep (se 1 (by rfl) ⟨2493026, by rfl⟩ : syracuseStep 3324035 = 4986053) B4986053
theorem B4429997 : Blo 1555475 4429997 := bstep (se 3 (by rfl) ⟨830624, by rfl⟩ : syracuseStep 4429997 = 1661249) B1661249
theorem B2627761 : Blo 1555475 2627761 := bstep (se 2 (by rfl) ⟨985410, by rfl⟩ : syracuseStep 2627761 = 1970821) B1970821
theorem B1751251 : Blo 1555475 1751251 := bstep (se 1 (by rfl) ⟨1313438, by rfl⟩ : syracuseStep 1751251 = 2626877) B2626877
theorem B2627795 : Blo 1555475 2627795 := bstep (se 1 (by rfl) ⟨1970846, by rfl⟩ : syracuseStep 2627795 = 3941693) B3941693
theorem B3741923 : Blo 1555475 3741923 := bstep (se 1 (by rfl) ⟨2806442, by rfl⟩ : syracuseStep 3741923 = 5612885) B5612885
theorem B4430065 : Blo 1555475 4430065 := bstep (se 2 (by rfl) ⟨1661274, by rfl⟩ : syracuseStep 4430065 = 3322549) B3322549
theorem B3742001 : Blo 1555475 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B2103617 : Blo 1555475 2103617 := bstep (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) B1577713
theorem B2627923 : Blo 1555475 2627923 := bstep (se 1 (by rfl) ⟨1970942, by rfl⟩ : syracuseStep 2627923 = 3941885) B3941885
theorem B1751395 : Blo 1555475 1751395 := bstep (se 1 (by rfl) ⟨1313546, by rfl⟩ : syracuseStep 1751395 = 2627093) B2627093
theorem B11221361 : Blo 1555475 11221361 := bstep (se 2 (by rfl) ⟨4208010, by rfl⟩ : syracuseStep 11221361 = 8416021) B8416021
theorem B4209059 : Blo 1555475 4209059 := bstep (se 1 (by rfl) ⟨3156794, by rfl⟩ : syracuseStep 4209059 = 6313589) B6313589
theorem B2628065 : Blo 1555475 2628065 := bstep (se 2 (by rfl) ⟨985524, by rfl⟩ : syracuseStep 2628065 = 1971049) B1971049
theorem B2955761 : Blo 1555475 2955761 := bstep (se 2 (by rfl) ⟨1108410, by rfl⟩ : syracuseStep 2955761 = 2216821) B2216821
theorem B1751539 : Blo 1555475 1751539 := bstep (se 1 (by rfl) ⟨1313654, by rfl⟩ : syracuseStep 1751539 = 2627309) B2627309
theorem B4430339 : Blo 1555475 4430339 := bstep (se 1 (by rfl) ⟨3322754, by rfl⟩ : syracuseStep 4430339 = 6645509) B6645509
theorem B6068749 : Blo 1555475 6068749 := bstep (se 3 (by rfl) ⟨1137890, by rfl⟩ : syracuseStep 6068749 = 2275781) B2275781
theorem B5913101 : Blo 1555475 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B2333219 : Blo 1555475 2333219 := bstep (se 1 (by rfl) ⟨1749914, by rfl⟩ : syracuseStep 2333219 = 3499829) B3499829
theorem B2333249 : Blo 1555475 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B2333267 : Blo 1555475 2333267 := bstep (se 1 (by rfl) ⟨1749950, by rfl⟩ : syracuseStep 2333267 = 3499901) B3499901
theorem B2628193 : Blo 1555475 2628193 := bstep (se 2 (by rfl) ⟨985572, by rfl⟩ : syracuseStep 2628193 = 1971145) B1971145
theorem B2333297 : Blo 1555475 2333297 := bstep (se 2 (by rfl) ⟨874986, by rfl⟩ : syracuseStep 2333297 = 1749973) B1749973
theorem B2333315 : Blo 1555475 2333315 := bstep (se 1 (by rfl) ⟨1749986, by rfl⟩ : syracuseStep 2333315 = 3499973) B3499973
theorem B1751683 : Blo 1555475 1751683 := bstep (se 1 (by rfl) ⟨1313762, by rfl⟩ : syracuseStep 1751683 = 2627525) B2627525
theorem B2628227 : Blo 1555475 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B2333345 : Blo 1555475 2333345 := bstep (se 2 (by rfl) ⟨875004, by rfl⟩ : syracuseStep 2333345 = 1750009) B1750009
theorem B6650531 : Blo 1555475 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B2333363 : Blo 1555475 2333363 := bstep (se 1 (by rfl) ⟨1750022, by rfl⟩ : syracuseStep 2333363 = 3500045) B3500045
theorem B2333393 : Blo 1555475 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B2333411 : Blo 1555475 2333411 := bstep (se 1 (by rfl) ⟨1750058, by rfl⟩ : syracuseStep 2333411 = 3500117) B3500117
theorem B2333441 : Blo 1555475 2333441 := bstep (se 2 (by rfl) ⟨875040, by rfl⟩ : syracuseStep 2333441 = 1750081) B1750081
theorem B2333459 : Blo 1555475 2333459 := bstep (se 1 (by rfl) ⟨1750094, by rfl⟩ : syracuseStep 2333459 = 3500189) B3500189
theorem B1751827 : Blo 1555475 1751827 := bstep (se 1 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 1751827 = 2627741) B2627741
theorem B4987693 : Blo 1555475 4987693 := bstep (se 3 (by rfl) ⟨935192, by rfl⟩ : syracuseStep 4987693 = 1870385) B1870385
theorem B2333489 : Blo 1555475 2333489 := bstep (se 2 (by rfl) ⟨875058, by rfl⟩ : syracuseStep 2333489 = 1750117) B1750117
theorem B2333507 : Blo 1555475 2333507 := bstep (se 1 (by rfl) ⟨1750130, by rfl⟩ : syracuseStep 2333507 = 3500261) B3500261
theorem B2333537 : Blo 1555475 2333537 := bstep (se 2 (by rfl) ⟨875076, by rfl⟩ : syracuseStep 2333537 = 1750153) B1750153
theorem B4324205 : Blo 1555475 4324205 := bstep (se 3 (by rfl) ⟨810788, by rfl⟩ : syracuseStep 4324205 = 1621577) B1621577
theorem B2333555 : Blo 1555475 2333555 := bstep (se 1 (by rfl) ⟨1750166, by rfl⟩ : syracuseStep 2333555 = 3500333) B3500333
theorem B5249933 : Blo 1555475 5249933 := bstep (se 3 (by rfl) ⟨984362, by rfl⟩ : syracuseStep 5249933 = 1968725) B1968725
theorem B2333585 : Blo 1555475 2333585 := bstep (se 2 (by rfl) ⟨875094, by rfl⟩ : syracuseStep 2333585 = 1750189) B1750189
theorem B1661843 : Blo 1555475 1661843 := bstep (se 1 (by rfl) ⟨1246382, by rfl⟩ : syracuseStep 1661843 = 2492765) B2492765
theorem B2333603 : Blo 1555475 2333603 := bstep (se 1 (by rfl) ⟨1750202, by rfl⟩ : syracuseStep 2333603 = 3500405) B3500405
theorem B1751971 : Blo 1555475 1751971 := bstep (se 1 (by rfl) ⟨1313978, by rfl⟩ : syracuseStep 1751971 = 2627957) B2627957
theorem B2333633 : Blo 1555475 2333633 := bstep (se 2 (by rfl) ⟨875112, by rfl⟩ : syracuseStep 2333633 = 1750225) B1750225
theorem B5249987 : Blo 1555475 5249987 := bstep (se 1 (by rfl) ⟨3937490, by rfl⟩ : syracuseStep 5249987 = 7874981) B7874981
theorem B2333651 : Blo 1555475 2333651 := bstep (se 1 (by rfl) ⟨1750238, by rfl⟩ : syracuseStep 2333651 = 3500477) B3500477
theorem B2333681 : Blo 1555475 2333681 := bstep (se 2 (by rfl) ⟨875130, by rfl⟩ : syracuseStep 2333681 = 1750261) B1750261
theorem B3939313 : Blo 1555475 3939313 := bstep (se 2 (by rfl) ⟨1477242, by rfl⟩ : syracuseStep 3939313 = 2954485) B2954485
theorem B2333699 : Blo 1555475 2333699 := bstep (se 1 (by rfl) ⟨1750274, by rfl⟩ : syracuseStep 2333699 = 3500549) B3500549
theorem B1555475 : Blo 1555475 1555475 := bstep (se 1 (by rfl) ⟨1166606, by rfl⟩ : syracuseStep 1555475 = 2333213) B2333213
theorem B2333729 : Blo 1555475 2333729 := bstep (se 2 (by rfl) ⟨875148, by rfl⟩ : syracuseStep 2333729 = 1750297) B1750297
theorem B1555491 : Blo 1555475 1555491 := bstep (se 1 (by rfl) ⟨1166618, by rfl⟩ : syracuseStep 1555491 = 2333237) B2333237
theorem B1555507 : Blo 1555475 1555507 := bstep (se 1 (by rfl) ⟨1166630, by rfl⟩ : syracuseStep 1555507 = 2333261) B2333261
theorem B2333747 : Blo 1555475 2333747 := bstep (se 1 (by rfl) ⟨1750310, by rfl⟩ : syracuseStep 2333747 = 3500621) B3500621
theorem B1752115 : Blo 1555475 1752115 := bstep (se 1 (by rfl) ⟨1314086, by rfl⟩ : syracuseStep 1752115 = 2628173) B2628173
theorem B1555523 : Blo 1555475 1555523 := bstep (se 1 (by rfl) ⟨1166642, by rfl⟩ : syracuseStep 1555523 = 2333285) B2333285
theorem B2333777 : Blo 1555475 2333777 := bstep (se 2 (by rfl) ⟨875166, by rfl⟩ : syracuseStep 2333777 = 1750333) B1750333
theorem B1555539 : Blo 1555475 1555539 := bstep (se 1 (by rfl) ⟨1166654, by rfl⟩ : syracuseStep 1555539 = 2333309) B2333309
theorem B1555555 : Blo 1555475 1555555 := bstep (se 1 (by rfl) ⟨1166666, by rfl⟩ : syracuseStep 1555555 = 2333333) B2333333
theorem B2333795 : Blo 1555475 2333795 := bstep (se 1 (by rfl) ⟨1750346, by rfl⟩ : syracuseStep 2333795 = 3500693) B3500693
theorem B1555571 : Blo 1555475 1555571 := bstep (se 1 (by rfl) ⟨1166678, by rfl⟩ : syracuseStep 1555571 = 2333357) B2333357
theorem B2333825 : Blo 1555475 2333825 := bstep (se 2 (by rfl) ⟨875184, by rfl⟩ : syracuseStep 2333825 = 1750369) B1750369
theorem B1555587 : Blo 1555475 1555587 := bstep (se 1 (by rfl) ⟨1166690, by rfl⟩ : syracuseStep 1555587 = 2333381) B2333381
theorem B10648709 : Blo 1555475 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B1555603 : Blo 1555475 1555603 := bstep (se 1 (by rfl) ⟨1166702, by rfl⟩ : syracuseStep 1555603 = 2333405) B2333405
theorem B2333843 : Blo 1555475 2333843 := bstep (se 1 (by rfl) ⟨1750382, by rfl⟩ : syracuseStep 2333843 = 3500765) B3500765
theorem B1555619 : Blo 1555475 1555619 := bstep (se 1 (by rfl) ⟨1166714, by rfl⟩ : syracuseStep 1555619 = 2333429) B2333429
theorem B2333873 : Blo 1555475 2333873 := bstep (se 2 (by rfl) ⟨875202, by rfl⟩ : syracuseStep 2333873 = 1750405) B1750405
theorem B1555635 : Blo 1555475 1555635 := bstep (se 1 (by rfl) ⟨1166726, by rfl⟩ : syracuseStep 1555635 = 2333453) B2333453
theorem B1555651 : Blo 1555475 1555651 := bstep (se 1 (by rfl) ⟨1166738, by rfl⟩ : syracuseStep 1555651 = 2333477) B2333477
theorem B2333891 : Blo 1555475 2333891 := bstep (se 1 (by rfl) ⟨1750418, by rfl⟩ : syracuseStep 2333891 = 3500837) B3500837
theorem B5250257 : Blo 1555475 5250257 := bstep (se 2 (by rfl) ⟨1968846, by rfl⟩ : syracuseStep 5250257 = 3937693) B3937693
theorem B1555667 : Blo 1555475 1555667 := bstep (se 1 (by rfl) ⟨1166750, by rfl⟩ : syracuseStep 1555667 = 2333501) B2333501
theorem B2333921 : Blo 1555475 2333921 := bstep (se 2 (by rfl) ⟨875220, by rfl⟩ : syracuseStep 2333921 = 1750441) B1750441
theorem B1555683 : Blo 1555475 1555683 := bstep (se 1 (by rfl) ⟨1166762, by rfl⟩ : syracuseStep 1555683 = 2333525) B2333525
theorem B1555699 : Blo 1555475 1555699 := bstep (se 1 (by rfl) ⟨1166774, by rfl⟩ : syracuseStep 1555699 = 2333549) B2333549
theorem B2333939 : Blo 1555475 2333939 := bstep (se 1 (by rfl) ⟨1750454, by rfl⟩ : syracuseStep 2333939 = 3500909) B3500909
theorem B1555715 : Blo 1555475 1555715 := bstep (se 1 (by rfl) ⟨1166786, by rfl⟩ : syracuseStep 1555715 = 2333573) B2333573
theorem B3939587 : Blo 1555475 3939587 := bstep (se 1 (by rfl) ⟨2954690, by rfl⟩ : syracuseStep 3939587 = 5909381) B5909381
theorem B2333969 : Blo 1555475 2333969 := bstep (se 2 (by rfl) ⟨875238, by rfl⟩ : syracuseStep 2333969 = 1750477) B1750477
theorem B1555731 : Blo 1555475 1555731 := bstep (se 1 (by rfl) ⟨1166798, by rfl⟩ : syracuseStep 1555731 = 2333597) B2333597
theorem B1555747 : Blo 1555475 1555747 := bstep (se 1 (by rfl) ⟨1166810, by rfl⟩ : syracuseStep 1555747 = 2333621) B2333621
theorem B2333987 : Blo 1555475 2333987 := bstep (se 1 (by rfl) ⟨1750490, by rfl⟩ : syracuseStep 2333987 = 3500981) B3500981
theorem B1555763 : Blo 1555475 1555763 := bstep (se 1 (by rfl) ⟨1166822, by rfl⟩ : syracuseStep 1555763 = 2333645) B2333645
theorem B2104627 : Blo 1555475 2104627 := bstep (se 1 (by rfl) ⟨1578470, by rfl⟩ : syracuseStep 2104627 = 3156941) B3156941
theorem B2334017 : Blo 1555475 2334017 := bstep (se 2 (by rfl) ⟨875256, by rfl⟩ : syracuseStep 2334017 = 1750513) B1750513
theorem B1555779 : Blo 1555475 1555779 := bstep (se 1 (by rfl) ⟨1166834, by rfl⟩ : syracuseStep 1555779 = 2333669) B2333669
theorem B4431181 : Blo 1555475 4431181 := bstep (se 3 (by rfl) ⟨830846, by rfl⟩ : syracuseStep 4431181 = 1661693) B1661693
theorem B1555795 : Blo 1555475 1555795 := bstep (se 1 (by rfl) ⟨1166846, by rfl⟩ : syracuseStep 1555795 = 2333693) B2333693
theorem B2334035 : Blo 1555475 2334035 := bstep (se 1 (by rfl) ⟨1750526, by rfl⟩ : syracuseStep 2334035 = 3501053) B3501053
theorem B1555811 : Blo 1555475 1555811 := bstep (se 1 (by rfl) ⟨1166858, by rfl⟩ : syracuseStep 1555811 = 2333717) B2333717
theorem B3325283 : Blo 1555475 3325283 := bstep (se 1 (by rfl) ⟨2493962, by rfl⟩ : syracuseStep 3325283 = 4987925) B4987925
theorem B2334065 : Blo 1555475 2334065 := bstep (se 2 (by rfl) ⟨875274, by rfl⟩ : syracuseStep 2334065 = 1750549) B1750549
theorem B2956657 : Blo 1555475 2956657 := bstep (se 2 (by rfl) ⟨1108746, by rfl⟩ : syracuseStep 2956657 = 2217493) B2217493
theorem B1555827 : Blo 1555475 1555827 := bstep (se 1 (by rfl) ⟨1166870, by rfl⟩ : syracuseStep 1555827 = 2333741) B2333741
theorem B2334083 : Blo 1555475 2334083 := bstep (se 1 (by rfl) ⟨1750562, by rfl⟩ : syracuseStep 2334083 = 3501125) B3501125
theorem B1555843 : Blo 1555475 1555843 := bstep (se 1 (by rfl) ⟨1166882, by rfl⟩ : syracuseStep 1555843 = 2333765) B2333765
theorem B1555859 : Blo 1555475 1555859 := bstep (se 1 (by rfl) ⟨1166894, by rfl⟩ : syracuseStep 1555859 = 2333789) B2333789
theorem B2334113 : Blo 1555475 2334113 := bstep (se 2 (by rfl) ⟨875292, by rfl⟩ : syracuseStep 2334113 = 1750585) B1750585
theorem B1555875 : Blo 1555475 1555875 := bstep (se 1 (by rfl) ⟨1166906, by rfl⟩ : syracuseStep 1555875 = 2333813) B2333813
theorem B1555891 : Blo 1555475 1555891 := bstep (se 1 (by rfl) ⟨1166918, by rfl⟩ : syracuseStep 1555891 = 2333837) B2333837
theorem B2334131 : Blo 1555475 2334131 := bstep (se 1 (by rfl) ⟨1750598, by rfl⟩ : syracuseStep 2334131 = 3501197) B3501197
theorem B1555907 : Blo 1555475 1555907 := bstep (se 1 (by rfl) ⟨1166930, by rfl⟩ : syracuseStep 1555907 = 2333861) B2333861
theorem B3939779 : Blo 1555475 3939779 := bstep (se 1 (by rfl) ⟨2954834, by rfl⟩ : syracuseStep 3939779 = 5909669) B5909669
theorem B2366915 : Blo 1555475 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B2334161 : Blo 1555475 2334161 := bstep (se 2 (by rfl) ⟨875310, by rfl⟩ : syracuseStep 2334161 = 1750621) B1750621
theorem B1555923 : Blo 1555475 1555923 := bstep (se 1 (by rfl) ⟨1166942, by rfl⟩ : syracuseStep 1555923 = 2333885) B2333885
theorem B1555939 : Blo 1555475 1555939 := bstep (se 1 (by rfl) ⟨1166954, by rfl⟩ : syracuseStep 1555939 = 2333909) B2333909
theorem B2334179 : Blo 1555475 2334179 := bstep (se 1 (by rfl) ⟨1750634, by rfl⟩ : syracuseStep 2334179 = 3501269) B3501269
theorem B4431341 : Blo 1555475 4431341 := bstep (se 3 (by rfl) ⟨830876, by rfl⟩ : syracuseStep 4431341 = 1661753) B1661753
theorem B1555955 : Blo 1555475 1555955 := bstep (se 1 (by rfl) ⟨1166966, by rfl⟩ : syracuseStep 1555955 = 2333933) B2333933
theorem B2334209 : Blo 1555475 2334209 := bstep (se 2 (by rfl) ⟨875328, by rfl⟩ : syracuseStep 2334209 = 1750657) B1750657
theorem B1555971 : Blo 1555475 1555971 := bstep (se 1 (by rfl) ⟨1166978, by rfl⟩ : syracuseStep 1555971 = 2333957) B2333957
theorem B7200269 : Blo 1555475 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B1555987 : Blo 1555475 1555987 := bstep (se 1 (by rfl) ⟨1166990, by rfl⟩ : syracuseStep 1555987 = 2333981) B2333981
theorem B2334227 : Blo 1555475 2334227 := bstep (se 1 (by rfl) ⟨1750670, by rfl⟩ : syracuseStep 2334227 = 3501341) B3501341
theorem B1556003 : Blo 1555475 1556003 := bstep (se 1 (by rfl) ⟨1167002, by rfl⟩ : syracuseStep 1556003 = 2334005) B2334005
theorem B2334257 : Blo 1555475 2334257 := bstep (se 2 (by rfl) ⟨875346, by rfl⟩ : syracuseStep 2334257 = 1750693) B1750693
theorem B1556019 : Blo 1555475 1556019 := bstep (se 1 (by rfl) ⟨1167014, by rfl⟩ : syracuseStep 1556019 = 2334029) B2334029
theorem B53935669 : Blo 1555475 53935669 := bstep (se 5 (by rfl) ⟨2528234, by rfl⟩ : syracuseStep 53935669 = 5056469) B5056469
theorem B1556035 : Blo 1555475 1556035 := bstep (se 1 (by rfl) ⟨1167026, by rfl⟩ : syracuseStep 1556035 = 2334053) B2334053
theorem B2334275 : Blo 1555475 2334275 := bstep (se 1 (by rfl) ⟨1750706, by rfl⟩ : syracuseStep 2334275 = 3501413) B3501413
theorem B1556051 : Blo 1555475 1556051 := bstep (se 1 (by rfl) ⟨1167038, by rfl⟩ : syracuseStep 1556051 = 2334077) B2334077
theorem B2334305 : Blo 1555475 2334305 := bstep (se 2 (by rfl) ⟨875364, by rfl⟩ : syracuseStep 2334305 = 1750729) B1750729
theorem B1556067 : Blo 1555475 1556067 := bstep (se 1 (by rfl) ⟨1167050, by rfl⟩ : syracuseStep 1556067 = 2334101) B2334101
theorem B1556083 : Blo 1555475 1556083 := bstep (se 1 (by rfl) ⟨1167062, by rfl⟩ : syracuseStep 1556083 = 2334125) B2334125
theorem B2334323 : Blo 1555475 2334323 := bstep (se 1 (by rfl) ⟨1750742, by rfl⟩ : syracuseStep 2334323 = 3501485) B3501485
theorem B1556099 : Blo 1555475 1556099 := bstep (se 1 (by rfl) ⟨1167074, by rfl⟩ : syracuseStep 1556099 = 2334149) B2334149
theorem B2334353 : Blo 1555475 2334353 := bstep (se 2 (by rfl) ⟨875382, by rfl⟩ : syracuseStep 2334353 = 1750765) B1750765
theorem B1556115 : Blo 1555475 1556115 := bstep (se 1 (by rfl) ⟨1167086, by rfl⟩ : syracuseStep 1556115 = 2334173) B2334173
theorem B1556131 : Blo 1555475 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B4431523 : Blo 1555475 4431523 := bstep (se 1 (by rfl) ⟨3323642, by rfl⟩ : syracuseStep 4431523 = 6647285) B6647285
theorem B2334371 : Blo 1555475 2334371 := bstep (se 1 (by rfl) ⟨1750778, by rfl⟩ : syracuseStep 2334371 = 3501557) B3501557
theorem B1556147 : Blo 1555475 1556147 := bstep (se 1 (by rfl) ⟨1167110, by rfl⟩ : syracuseStep 1556147 = 2334221) B2334221
theorem B2334401 : Blo 1555475 2334401 := bstep (se 2 (by rfl) ⟨875400, by rfl⟩ : syracuseStep 2334401 = 1750801) B1750801
theorem B1556163 : Blo 1555475 1556163 := bstep (se 1 (by rfl) ⟨1167122, by rfl⟩ : syracuseStep 1556163 = 2334245) B2334245
theorem B1556179 : Blo 1555475 1556179 := bstep (se 1 (by rfl) ⟨1167134, by rfl⟩ : syracuseStep 1556179 = 2334269) B2334269
theorem B2334419 : Blo 1555475 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B1556195 : Blo 1555475 1556195 := bstep (se 1 (by rfl) ⟨1167146, by rfl⟩ : syracuseStep 1556195 = 2334293) B2334293
theorem B5250797 : Blo 1555475 5250797 := bstep (se 3 (by rfl) ⟨984524, by rfl⟩ : syracuseStep 5250797 = 1969049) B1969049
theorem B2334449 : Blo 1555475 2334449 := bstep (se 2 (by rfl) ⟨875418, by rfl⟩ : syracuseStep 2334449 = 1750837) B1750837
theorem B1556211 : Blo 1555475 1556211 := bstep (se 1 (by rfl) ⟨1167158, by rfl⟩ : syracuseStep 1556211 = 2334317) B2334317
theorem B1556227 : Blo 1555475 1556227 := bstep (se 1 (by rfl) ⟨1167170, by rfl⟩ : syracuseStep 1556227 = 2334341) B2334341
theorem B2334467 : Blo 1555475 2334467 := bstep (se 1 (by rfl) ⟨1750850, by rfl⟩ : syracuseStep 2334467 = 3501701) B3501701
theorem B1556243 : Blo 1555475 1556243 := bstep (se 1 (by rfl) ⟨1167182, by rfl⟩ : syracuseStep 1556243 = 2334365) B2334365
theorem B2334497 : Blo 1555475 2334497 := bstep (se 2 (by rfl) ⟨875436, by rfl⟩ : syracuseStep 2334497 = 1750873) B1750873
theorem B5250851 : Blo 1555475 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B1556259 : Blo 1555475 1556259 := bstep (se 1 (by rfl) ⟨1167194, by rfl⟩ : syracuseStep 1556259 = 2334389) B2334389
theorem B1556275 : Blo 1555475 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B2334515 : Blo 1555475 2334515 := bstep (se 1 (by rfl) ⟨1750886, by rfl⟩ : syracuseStep 2334515 = 3501773) B3501773
theorem B1556291 : Blo 1555475 1556291 := bstep (se 1 (by rfl) ⟨1167218, by rfl⟩ : syracuseStep 1556291 = 2334437) B2334437
theorem B5988173 : Blo 1555475 5988173 := bstep (se 3 (by rfl) ⟨1122782, by rfl⟩ : syracuseStep 5988173 = 2245565) B2245565
theorem B3153745 : Blo 1555475 3153745 := bstep (se 2 (by rfl) ⟨1182654, by rfl⟩ : syracuseStep 3153745 = 2365309) B2365309
theorem B2334545 : Blo 1555475 2334545 := bstep (se 2 (by rfl) ⟨875454, by rfl⟩ : syracuseStep 2334545 = 1750909) B1750909
theorem B1556307 : Blo 1555475 1556307 := bstep (se 1 (by rfl) ⟨1167230, by rfl⟩ : syracuseStep 1556307 = 2334461) B2334461
theorem B1556323 : Blo 1555475 1556323 := bstep (se 1 (by rfl) ⟨1167242, by rfl⟩ : syracuseStep 1556323 = 2334485) B2334485
theorem B2334563 : Blo 1555475 2334563 := bstep (se 1 (by rfl) ⟨1750922, by rfl⟩ : syracuseStep 2334563 = 3501845) B3501845
theorem B1556339 : Blo 1555475 1556339 := bstep (se 1 (by rfl) ⟨1167254, by rfl⟩ : syracuseStep 1556339 = 2334509) B2334509
theorem B2334593 : Blo 1555475 2334593 := bstep (se 2 (by rfl) ⟨875472, by rfl⟩ : syracuseStep 2334593 = 1750945) B1750945
theorem B1556355 : Blo 1555475 1556355 := bstep (se 1 (by rfl) ⟨1167266, by rfl⟩ : syracuseStep 1556355 = 2334533) B2334533
theorem B1556371 : Blo 1555475 1556371 := bstep (se 1 (by rfl) ⟨1167278, by rfl⟩ : syracuseStep 1556371 = 2334557) B2334557
theorem B2334611 : Blo 1555475 2334611 := bstep (se 1 (by rfl) ⟨1750958, by rfl⟩ : syracuseStep 2334611 = 3501917) B3501917
theorem B1556387 : Blo 1555475 1556387 := bstep (se 1 (by rfl) ⟨1167290, by rfl⟩ : syracuseStep 1556387 = 2334581) B2334581
theorem B2334641 : Blo 1555475 2334641 := bstep (se 2 (by rfl) ⟨875490, by rfl⟩ : syracuseStep 2334641 = 1750981) B1750981
theorem B1556403 : Blo 1555475 1556403 := bstep (se 1 (by rfl) ⟨1167302, by rfl⟩ : syracuseStep 1556403 = 2334605) B2334605
theorem B3325873 : Blo 1555475 3325873 := bstep (se 2 (by rfl) ⟨1247202, by rfl⟩ : syracuseStep 3325873 = 2494405) B2494405
theorem B1556419 : Blo 1555475 1556419 := bstep (se 1 (by rfl) ⟨1167314, by rfl⟩ : syracuseStep 1556419 = 2334629) B2334629
theorem B2334659 : Blo 1555475 2334659 := bstep (se 1 (by rfl) ⟨1750994, by rfl⟩ : syracuseStep 2334659 = 3501989) B3501989
theorem B16834501 : Blo 1555475 16834501 := bstep (se 4 (by rfl) ⟨1578234, by rfl⟩ : syracuseStep 16834501 = 3156469) B3156469
theorem B1556435 : Blo 1555475 1556435 := bstep (se 1 (by rfl) ⟨1167326, by rfl⟩ : syracuseStep 1556435 = 2334653) B2334653
theorem B2334689 : Blo 1555475 2334689 := bstep (se 2 (by rfl) ⟨875508, by rfl⟩ : syracuseStep 2334689 = 1751017) B1751017
theorem B1556451 : Blo 1555475 1556451 := bstep (se 1 (by rfl) ⟨1167338, by rfl⟩ : syracuseStep 1556451 = 2334677) B2334677
theorem B19947491 : Blo 1555475 19947491 := bstep (se 1 (by rfl) ⟨14960618, by rfl⟩ : syracuseStep 19947491 = 29921237) B29921237
theorem B1556467 : Blo 1555475 1556467 := bstep (se 1 (by rfl) ⟨1167350, by rfl⟩ : syracuseStep 1556467 = 2334701) B2334701
theorem B2334707 : Blo 1555475 2334707 := bstep (se 1 (by rfl) ⟨1751030, by rfl⟩ : syracuseStep 2334707 = 3502061) B3502061
theorem B2334731 : Blo 1555475 2334731 := bstep (se 1 (by rfl) ⟨1751048, by rfl⟩ : syracuseStep 2334731 = 3502097) B3502097
theorem B1556491 : Blo 1555475 1556491 := bstep (se 1 (by rfl) ⟨1167368, by rfl⟩ : syracuseStep 1556491 = 2334737) B2334737
theorem B2334743 : Blo 1555475 2334743 := bstep (se 1 (by rfl) ⟨1751057, by rfl⟩ : syracuseStep 2334743 = 3502115) B3502115
theorem B1556503 : Blo 1555475 1556503 := bstep (se 1 (by rfl) ⟨1167377, by rfl⟩ : syracuseStep 1556503 = 2334755) B2334755
theorem B3792919 : Blo 1555475 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B1556523 : Blo 1555475 1556523 := bstep (se 1 (by rfl) ⟨1167392, by rfl⟩ : syracuseStep 1556523 = 2334785) B2334785
theorem B1556535 : Blo 1555475 1556535 := bstep (se 1 (by rfl) ⟨1167401, by rfl⟩ : syracuseStep 1556535 = 2334803) B2334803
theorem B3326017 : Blo 1555475 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B1556555 : Blo 1555475 1556555 := bstep (se 1 (by rfl) ⟨1167416, by rfl⟩ : syracuseStep 1556555 = 2334833) B2334833
theorem B3940427 : Blo 1555475 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1556567 : Blo 1555475 1556567 := bstep (se 1 (by rfl) ⟨1167425, by rfl⟩ : syracuseStep 1556567 = 2334851) B2334851
theorem B2334809 : Blo 1555475 2334809 := bstep (se 2 (by rfl) ⟨875553, by rfl⟩ : syracuseStep 2334809 = 1751107) B1751107
theorem B1556587 : Blo 1555475 1556587 := bstep (se 1 (by rfl) ⟨1167440, by rfl⟩ : syracuseStep 1556587 = 2334881) B2334881
theorem B1556599 : Blo 1555475 1556599 := bstep (se 1 (by rfl) ⟨1167449, by rfl⟩ : syracuseStep 1556599 = 2334899) B2334899
theorem B1556619 : Blo 1555475 1556619 := bstep (se 1 (by rfl) ⟨1167464, by rfl⟩ : syracuseStep 1556619 = 2334929) B2334929
theorem B1556631 : Blo 1555475 1556631 := bstep (se 1 (by rfl) ⟨1167473, by rfl⟩ : syracuseStep 1556631 = 2334947) B2334947
theorem B1556651 : Blo 1555475 1556651 := bstep (se 1 (by rfl) ⟨1167488, by rfl⟩ : syracuseStep 1556651 = 2334977) B2334977
theorem B1556663 : Blo 1555475 1556663 := bstep (se 1 (by rfl) ⟨1167497, by rfl⟩ : syracuseStep 1556663 = 2334995) B2334995
theorem B2334923 : Blo 1555475 2334923 := bstep (se 1 (by rfl) ⟨1751192, by rfl⟩ : syracuseStep 2334923 = 3502385) B3502385
theorem B1556683 : Blo 1555475 1556683 := bstep (se 1 (by rfl) ⟨1167512, by rfl⟩ : syracuseStep 1556683 = 2335025) B2335025
theorem B25239757 : Blo 1555475 25239757 := bstep (se 3 (by rfl) ⟨4732454, by rfl⟩ : syracuseStep 25239757 = 9464909) B9464909
theorem B3154135 : Blo 1555475 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B2334935 : Blo 1555475 2334935 := bstep (se 1 (by rfl) ⟨1751201, by rfl⟩ : syracuseStep 2334935 = 3502403) B3502403
theorem B1556695 : Blo 1555475 1556695 := bstep (se 1 (by rfl) ⟨1167521, by rfl⟩ : syracuseStep 1556695 = 2335043) B2335043
theorem B1556715 : Blo 1555475 1556715 := bstep (se 1 (by rfl) ⟨1167536, by rfl⟩ : syracuseStep 1556715 = 2335073) B2335073
theorem B1556727 : Blo 1555475 1556727 := bstep (se 1 (by rfl) ⟨1167545, by rfl⟩ : syracuseStep 1556727 = 2335091) B2335091
theorem B1556747 : Blo 1555475 1556747 := bstep (se 1 (by rfl) ⟨1167560, by rfl⟩ : syracuseStep 1556747 = 2335121) B2335121
theorem B3154199 : Blo 1555475 3154199 := bstep (se 1 (by rfl) ⟨2365649, by rfl⟩ : syracuseStep 3154199 = 4731299) B4731299
theorem B1556759 : Blo 1555475 1556759 := bstep (se 1 (by rfl) ⟨1167569, by rfl⟩ : syracuseStep 1556759 = 2335139) B2335139
theorem B2335001 : Blo 1555475 2335001 := bstep (se 2 (by rfl) ⟨875625, by rfl⟩ : syracuseStep 2335001 = 1751251) B1751251
theorem B1556779 : Blo 1555475 1556779 := bstep (se 1 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 1556779 = 2335169) B2335169
theorem B1556791 : Blo 1555475 1556791 := bstep (se 1 (by rfl) ⟨1167593, by rfl⟩ : syracuseStep 1556791 = 2335187) B2335187
theorem B5906753 : Blo 1555475 5906753 := bstep (se 2 (by rfl) ⟨2215032, by rfl⟩ : syracuseStep 5906753 = 4430065) B4430065
theorem B1556811 : Blo 1555475 1556811 := bstep (se 1 (by rfl) ⟨1167608, by rfl⟩ : syracuseStep 1556811 = 2335217) B2335217
theorem B1556823 : Blo 1555475 1556823 := bstep (se 1 (by rfl) ⟨1167617, by rfl⟩ : syracuseStep 1556823 = 2335235) B2335235
theorem B8864093 : Blo 1555475 8864093 := bstep (se 3 (by rfl) ⟨1662017, by rfl⟩ : syracuseStep 8864093 = 3324035) B3324035
theorem B1556843 : Blo 1555475 1556843 := bstep (se 1 (by rfl) ⟨1167632, by rfl⟩ : syracuseStep 1556843 = 2335265) B2335265
theorem B1556855 : Blo 1555475 1556855 := bstep (se 1 (by rfl) ⟨1167641, by rfl⟩ : syracuseStep 1556855 = 2335283) B2335283
theorem B11977091 : Blo 1555475 11977091 := bstep (se 1 (by rfl) ⟨8982818, by rfl⟩ : syracuseStep 11977091 = 17965637) B17965637
theorem B2335115 : Blo 1555475 2335115 := bstep (se 1 (by rfl) ⟨1751336, by rfl⟩ : syracuseStep 2335115 = 3502673) B3502673
theorem B1556875 : Blo 1555475 1556875 := bstep (se 1 (by rfl) ⟨1167656, by rfl⟩ : syracuseStep 1556875 = 2335313) B2335313
theorem B2367883 : Blo 1555475 2367883 := bstep (se 1 (by rfl) ⟨1775912, by rfl⟩ : syracuseStep 2367883 = 3551825) B3551825
theorem B2662807 : Blo 1555475 2662807 := bstep (se 1 (by rfl) ⟨1997105, by rfl⟩ : syracuseStep 2662807 = 3994211) B3994211
theorem B11821463 : Blo 1555475 11821463 := bstep (se 1 (by rfl) ⟨8866097, by rfl⟩ : syracuseStep 11821463 = 17732195) B17732195
theorem B2335127 : Blo 1555475 2335127 := bstep (se 1 (by rfl) ⟨1751345, by rfl⟩ : syracuseStep 2335127 = 3502691) B3502691
theorem B1556887 : Blo 1555475 1556887 := bstep (se 1 (by rfl) ⟨1167665, by rfl⟩ : syracuseStep 1556887 = 2335331) B2335331
theorem B3326359 : Blo 1555475 3326359 := bstep (se 1 (by rfl) ⟨2494769, by rfl⟩ : syracuseStep 3326359 = 4989539) B4989539
theorem B1556907 : Blo 1555475 1556907 := bstep (se 1 (by rfl) ⟨1167680, by rfl⟩ : syracuseStep 1556907 = 2335361) B2335361
theorem B1556919 : Blo 1555475 1556919 := bstep (se 1 (by rfl) ⟨1167689, by rfl⟩ : syracuseStep 1556919 = 2335379) B2335379
theorem B1556939 : Blo 1555475 1556939 := bstep (se 1 (by rfl) ⟨1167704, by rfl⟩ : syracuseStep 1556939 = 2335409) B2335409
theorem B4735435 : Blo 1555475 4735435 := bstep (se 1 (by rfl) ⟨3551576, by rfl⟩ : syracuseStep 4735435 = 7103153) B7103153
theorem B1556951 : Blo 1555475 1556951 := bstep (se 1 (by rfl) ⟨1167713, by rfl⟩ : syracuseStep 1556951 = 2335427) B2335427
theorem B2245081 : Blo 1555475 2245081 := bstep (se 2 (by rfl) ⟨841905, by rfl⟩ : syracuseStep 2245081 = 1683811) B1683811
theorem B2335193 : Blo 1555475 2335193 := bstep (se 2 (by rfl) ⟨875697, by rfl⟩ : syracuseStep 2335193 = 1751395) B1751395
theorem B1556971 : Blo 1555475 1556971 := bstep (se 1 (by rfl) ⟨1167728, by rfl⟩ : syracuseStep 1556971 = 2335457) B2335457
theorem B1556983 : Blo 1555475 1556983 := bstep (se 1 (by rfl) ⟨1167737, by rfl⟩ : syracuseStep 1556983 = 2335475) B2335475
theorem B6644227 : Blo 1555475 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B1557003 : Blo 1555475 1557003 := bstep (se 1 (by rfl) ⟨1167752, by rfl⟩ : syracuseStep 1557003 = 2335505) B2335505
theorem B35938829 : Blo 1555475 35938829 := bstep (se 3 (by rfl) ⟨6738530, by rfl⟩ : syracuseStep 35938829 = 13477061) B13477061
theorem B5251607 : Blo 1555475 5251607 := bstep (se 1 (by rfl) ⟨3938705, by rfl⟩ : syracuseStep 5251607 = 7877411) B7877411
theorem B1557015 : Blo 1555475 1557015 := bstep (se 1 (by rfl) ⟨1167761, by rfl⟩ : syracuseStep 1557015 = 2335523) B2335523
theorem B1557035 : Blo 1555475 1557035 := bstep (se 1 (by rfl) ⟨1167776, by rfl⟩ : syracuseStep 1557035 = 2335553) B2335553
theorem B1557047 : Blo 1555475 1557047 := bstep (se 1 (by rfl) ⟨1167785, by rfl⟩ : syracuseStep 1557047 = 2335571) B2335571
theorem B2335307 : Blo 1555475 2335307 := bstep (se 1 (by rfl) ⟨1751480, by rfl⟩ : syracuseStep 2335307 = 3502961) B3502961
theorem B1557067 : Blo 1555475 1557067 := bstep (se 1 (by rfl) ⟨1167800, by rfl⟩ : syracuseStep 1557067 = 2335601) B2335601
theorem B2335319 : Blo 1555475 2335319 := bstep (se 1 (by rfl) ⟨1751489, by rfl⟩ : syracuseStep 2335319 = 3502979) B3502979
theorem B1557079 : Blo 1555475 1557079 := bstep (se 1 (by rfl) ⟨1167809, by rfl⟩ : syracuseStep 1557079 = 2335619) B2335619
theorem B9978461 : Blo 1555475 9978461 := bstep (se 3 (by rfl) ⟨1870961, by rfl⟩ : syracuseStep 9978461 = 3741923) B3741923
theorem B1557099 : Blo 1555475 1557099 := bstep (se 1 (by rfl) ⟨1167824, by rfl⟩ : syracuseStep 1557099 = 2335649) B2335649
theorem B1557111 : Blo 1555475 1557111 := bstep (se 1 (by rfl) ⟨1167833, by rfl⟩ : syracuseStep 1557111 = 2335667) B2335667
theorem B1557131 : Blo 1555475 1557131 := bstep (se 1 (by rfl) ⟨1167848, by rfl⟩ : syracuseStep 1557131 = 2335697) B2335697
theorem B12616343 : Blo 1555475 12616343 := bstep (se 1 (by rfl) ⟨9462257, by rfl⟩ : syracuseStep 12616343 = 18924515) B18924515
theorem B1557143 : Blo 1555475 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B2335385 : Blo 1555475 2335385 := bstep (se 2 (by rfl) ⟨875769, by rfl⟩ : syracuseStep 2335385 = 1751539) B1751539
theorem B1557163 : Blo 1555475 1557163 := bstep (se 1 (by rfl) ⟨1167872, by rfl⟩ : syracuseStep 1557163 = 2335745) B2335745
theorem B1557175 : Blo 1555475 1557175 := bstep (se 1 (by rfl) ⟨1167881, by rfl⟩ : syracuseStep 1557175 = 2335763) B2335763
theorem B1557195 : Blo 1555475 1557195 := bstep (se 1 (by rfl) ⟨1167896, by rfl⟩ : syracuseStep 1557195 = 2335793) B2335793
theorem B1557207 : Blo 1555475 1557207 := bstep (se 1 (by rfl) ⟨1167905, by rfl⟩ : syracuseStep 1557207 = 2335811) B2335811
theorem B4735705 : Blo 1555475 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B1557227 : Blo 1555475 1557227 := bstep (se 1 (by rfl) ⟨1167920, by rfl⟩ : syracuseStep 1557227 = 2335841) B2335841
theorem B1557239 : Blo 1555475 1557239 := bstep (se 1 (by rfl) ⟨1167929, by rfl⟩ : syracuseStep 1557239 = 2335859) B2335859
theorem B2335499 : Blo 1555475 2335499 := bstep (se 1 (by rfl) ⟨1751624, by rfl⟩ : syracuseStep 2335499 = 3503249) B3503249
theorem B1557259 : Blo 1555475 1557259 := bstep (se 1 (by rfl) ⟨1167944, by rfl⟩ : syracuseStep 1557259 = 2335889) B2335889
theorem B2335511 : Blo 1555475 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B1557271 : Blo 1555475 1557271 := bstep (se 1 (by rfl) ⟨1167953, by rfl⟩ : syracuseStep 1557271 = 2335907) B2335907
theorem B1557291 : Blo 1555475 1557291 := bstep (se 1 (by rfl) ⟨1167968, by rfl⟩ : syracuseStep 1557291 = 2335937) B2335937
theorem B1557303 : Blo 1555475 1557303 := bstep (se 1 (by rfl) ⟨1167977, by rfl⟩ : syracuseStep 1557303 = 2335955) B2335955
theorem B1557323 : Blo 1555475 1557323 := bstep (se 1 (by rfl) ⟨1167992, by rfl⟩ : syracuseStep 1557323 = 2335985) B2335985
theorem B2335577 : Blo 1555475 2335577 := bstep (se 2 (by rfl) ⟨875841, by rfl⟩ : syracuseStep 2335577 = 1751683) B1751683
theorem B1557335 : Blo 1555475 1557335 := bstep (se 1 (by rfl) ⟨1168001, by rfl⟩ : syracuseStep 1557335 = 2336003) B2336003
theorem B1557355 : Blo 1555475 1557355 := bstep (se 1 (by rfl) ⟨1168016, by rfl⟩ : syracuseStep 1557355 = 2336033) B2336033
theorem B1557367 : Blo 1555475 1557367 := bstep (se 1 (by rfl) ⟨1168025, by rfl⟩ : syracuseStep 1557367 = 2336051) B2336051
theorem B1557387 : Blo 1555475 1557387 := bstep (se 1 (by rfl) ⟨1168040, by rfl⟩ : syracuseStep 1557387 = 2336081) B2336081
theorem B7881623 : Blo 1555475 7881623 := bstep (se 1 (by rfl) ⟨5911217, by rfl⟩ : syracuseStep 7881623 = 11822435) B11822435
theorem B1557399 : Blo 1555475 1557399 := bstep (se 1 (by rfl) ⟨1168049, by rfl⟩ : syracuseStep 1557399 = 2336099) B2336099
theorem B1557419 : Blo 1555475 1557419 := bstep (se 1 (by rfl) ⟨1168064, by rfl⟩ : syracuseStep 1557419 = 2336129) B2336129
theorem B1557431 : Blo 1555475 1557431 := bstep (se 1 (by rfl) ⟨1168073, by rfl⟩ : syracuseStep 1557431 = 2336147) B2336147
theorem B2335691 : Blo 1555475 2335691 := bstep (se 1 (by rfl) ⟨1751768, by rfl⟩ : syracuseStep 2335691 = 3503537) B3503537
theorem B1557451 : Blo 1555475 1557451 := bstep (se 1 (by rfl) ⟨1168088, by rfl⟩ : syracuseStep 1557451 = 2336177) B2336177
theorem B2335703 : Blo 1555475 2335703 := bstep (se 1 (by rfl) ⟨1751777, by rfl⟩ : syracuseStep 2335703 = 3503555) B3503555
theorem B1557463 : Blo 1555475 1557463 := bstep (se 1 (by rfl) ⟨1168097, by rfl⟩ : syracuseStep 1557463 = 2336195) B2336195
theorem B3941399 : Blo 1555475 3941399 := bstep (se 1 (by rfl) ⟨2956049, by rfl⟩ : syracuseStep 3941399 = 5912099) B5912099
theorem B2335769 : Blo 1555475 2335769 := bstep (se 2 (by rfl) ⟨875913, by rfl⟩ : syracuseStep 2335769 = 1751827) B1751827
theorem B7095347 : Blo 1555475 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B5252147 : Blo 1555475 5252147 := bstep (se 1 (by rfl) ⟨3939110, by rfl⟩ : syracuseStep 5252147 = 7878221) B7878221
theorem B11224129 : Blo 1555475 11224129 := bstep (se 2 (by rfl) ⟨4209048, by rfl⟩ : syracuseStep 11224129 = 8418097) B8418097
theorem B6644825 : Blo 1555475 6644825 := bstep (se 2 (by rfl) ⟨2491809, by rfl⟩ : syracuseStep 6644825 = 4983619) B4983619
theorem B2335883 : Blo 1555475 2335883 := bstep (se 1 (by rfl) ⟨1751912, by rfl⟩ : syracuseStep 2335883 = 3503825) B3503825
theorem B2335895 : Blo 1555475 2335895 := bstep (se 1 (by rfl) ⟨1751921, by rfl⟩ : syracuseStep 2335895 = 3503843) B3503843
theorem B2335961 : Blo 1555475 2335961 := bstep (se 2 (by rfl) ⟨875985, by rfl⟩ : syracuseStep 2335961 = 1751971) B1751971
theorem B5252417 : Blo 1555475 5252417 := bstep (se 2 (by rfl) ⟨1969656, by rfl⟩ : syracuseStep 5252417 = 3939313) B3939313
theorem B2336075 : Blo 1555475 2336075 := bstep (se 1 (by rfl) ⟨1752056, by rfl⟩ : syracuseStep 2336075 = 3504113) B3504113
theorem B2336087 : Blo 1555475 2336087 := bstep (se 1 (by rfl) ⟨1752065, by rfl⟩ : syracuseStep 2336087 = 3504131) B3504131
theorem B2336153 : Blo 1555475 2336153 := bstep (se 2 (by rfl) ⟨876057, by rfl⟩ : syracuseStep 2336153 = 1752115) B1752115
theorem B6645185 : Blo 1555475 6645185 := bstep (se 2 (by rfl) ⟨2491944, by rfl⟩ : syracuseStep 6645185 = 4983889) B4983889
theorem B37873169 : Blo 1555475 37873169 := bstep (se 2 (by rfl) ⟨14202438, by rfl⟩ : syracuseStep 37873169 = 28404877) B28404877
theorem B2803265 : Blo 1555475 2803265 := bstep (se 2 (by rfl) ⟨1051224, by rfl⟩ : syracuseStep 2803265 = 2102449) B2102449
theorem B7480907 : Blo 1555475 7480907 := bstep (se 1 (by rfl) ⟨5610680, by rfl⟩ : syracuseStep 7480907 = 11221361) B11221361
theorem B3942067 : Blo 1555475 3942067 := bstep (se 1 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 3942067 = 5913101) B5913101
theorem B2803415 : Blo 1555475 2803415 := bstep (se 1 (by rfl) ⟨2102561, by rfl⟩ : syracuseStep 2803415 = 4205123) B4205123
theorem B16819973 : Blo 1555475 16819973 := bstep (se 4 (by rfl) ⟨1576872, by rfl⟩ : syracuseStep 16819973 = 3153745) B3153745
theorem B5908241 : Blo 1555475 5908241 := bstep (se 2 (by rfl) ⟨2215590, by rfl⟩ : syracuseStep 5908241 = 4431181) B4431181
theorem B4433687 : Blo 1555475 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B15370049 : Blo 1555475 15370049 := bstep (se 2 (by rfl) ⟨5763768, by rfl⟩ : syracuseStep 15370049 = 11527537) B11527537
theorem B3942209 : Blo 1555475 3942209 := bstep (se 2 (by rfl) ⟨1478328, by rfl⟩ : syracuseStep 3942209 = 2956657) B2956657
theorem B1869655 : Blo 1555475 1869655 := bstep (se 1 (by rfl) ⟨1402241, by rfl⟩ : syracuseStep 1869655 = 2804483) B2804483
theorem B3499865 : Blo 1555475 3499865 := bstep (se 2 (by rfl) ⟨1312449, by rfl⟩ : syracuseStep 3499865 = 2624899) B2624899
theorem B5252957 : Blo 1555475 5252957 := bstep (se 3 (by rfl) ⟨984929, by rfl⟩ : syracuseStep 5252957 = 1969859) B1969859
theorem B3499955 : Blo 1555475 3499955 := bstep (se 1 (by rfl) ⟨2624966, by rfl⟩ : syracuseStep 3499955 = 5249933) B5249933
theorem B3499991 : Blo 1555475 3499991 := bstep (se 1 (by rfl) ⟨2624993, by rfl⟩ : syracuseStep 3499991 = 5249987) B5249987
theorem B3500171 : Blo 1555475 3500171 := bstep (se 1 (by rfl) ⟨2625128, by rfl⟩ : syracuseStep 3500171 = 5250257) B5250257
theorem B3500225 : Blo 1555475 3500225 := bstep (se 2 (by rfl) ⟨1312584, by rfl⟩ : syracuseStep 3500225 = 2625169) B2625169
theorem B15968461 : Blo 1555475 15968461 := bstep (se 3 (by rfl) ⟨2994086, by rfl⟩ : syracuseStep 15968461 = 5988173) B5988173
theorem B1870039 : Blo 1555475 1870039 := bstep (se 1 (by rfl) ⟨1402529, by rfl⟩ : syracuseStep 1870039 = 2805059) B2805059
theorem B5908697 : Blo 1555475 5908697 := bstep (se 2 (by rfl) ⟨2215761, by rfl⟩ : syracuseStep 5908697 = 4431523) B4431523
theorem B7481693 : Blo 1555475 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B3500441 : Blo 1555475 3500441 := bstep (se 2 (by rfl) ⟨1312665, by rfl⟩ : syracuseStep 3500441 = 2625331) B2625331
theorem B5908909 : Blo 1555475 5908909 := bstep (se 3 (by rfl) ⟨1107920, by rfl⟩ : syracuseStep 5908909 = 2215841) B2215841
theorem B3500531 : Blo 1555475 3500531 := bstep (se 1 (by rfl) ⟨2625398, by rfl⟩ : syracuseStep 3500531 = 5250797) B5250797
theorem B3500567 : Blo 1555475 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B4434497 : Blo 1555475 4434497 := bstep (se 2 (by rfl) ⟨1662936, by rfl⟩ : syracuseStep 4434497 = 3325873) B3325873
theorem B1968715 : Blo 1555475 1968715 := bstep (se 1 (by rfl) ⟨1476536, by rfl⟩ : syracuseStep 1968715 = 2953073) B2953073
theorem B22448771 : Blo 1555475 22448771 := bstep (se 1 (by rfl) ⟨16836578, by rfl⟩ : syracuseStep 22448771 = 33673157) B33673157
theorem B13298327 : Blo 1555475 13298327 := bstep (se 1 (by rfl) ⟨9973745, by rfl⟩ : syracuseStep 13298327 = 19947491) B19947491
theorem B5606081 : Blo 1555475 5606081 := bstep (se 2 (by rfl) ⟨2102280, by rfl⟩ : syracuseStep 5606081 = 4204561) B4204561
theorem B3500747 : Blo 1555475 3500747 := bstep (se 1 (by rfl) ⟨2625560, by rfl⟩ : syracuseStep 3500747 = 5251121) B5251121
theorem B3893977 : Blo 1555475 3893977 := bstep (se 2 (by rfl) ⟨1460241, by rfl⟩ : syracuseStep 3893977 = 2920483) B2920483
theorem B5909213 : Blo 1555475 5909213 := bstep (se 3 (by rfl) ⟨1107977, by rfl⟩ : syracuseStep 5909213 = 2215955) B2215955
theorem B3500801 : Blo 1555475 3500801 := bstep (se 2 (by rfl) ⟨1312800, by rfl⟩ : syracuseStep 3500801 = 2625601) B2625601
theorem B2132761 : Blo 1555475 2132761 := bstep (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) B1599571
theorem B14961509 : Blo 1555475 14961509 := bstep (se 4 (by rfl) ⟨1402641, by rfl⟩ : syracuseStep 14961509 = 2805283) B2805283
theorem B8866691 : Blo 1555475 8866691 := bstep (se 1 (by rfl) ⟨6650018, by rfl⟩ : syracuseStep 8866691 = 13300037) B13300037
theorem B42601393 : Blo 1555475 42601393 := bstep (se 2 (by rfl) ⟨15975522, by rfl⟩ : syracuseStep 42601393 = 31951045) B31951045
theorem B5254091 : Blo 1555475 5254091 := bstep (se 1 (by rfl) ⟨3940568, by rfl⟩ : syracuseStep 5254091 = 7881137) B7881137
theorem B3501017 : Blo 1555475 3501017 := bstep (se 2 (by rfl) ⟨1312881, by rfl⟩ : syracuseStep 3501017 = 2625763) B2625763
theorem B4205591 : Blo 1555475 4205591 := bstep (se 1 (by rfl) ⟨3154193, by rfl⟩ : syracuseStep 4205591 = 6308387) B6308387
theorem B7875629 : Blo 1555475 7875629 := bstep (se 3 (by rfl) ⟨1476680, by rfl⟩ : syracuseStep 7875629 = 2953361) B2953361
theorem B3501107 : Blo 1555475 3501107 := bstep (se 1 (by rfl) ⟨2625830, by rfl⟩ : syracuseStep 3501107 = 5251661) B5251661
theorem B3501143 : Blo 1555475 3501143 := bstep (se 1 (by rfl) ⟨2625857, by rfl⟩ : syracuseStep 3501143 = 5251715) B5251715
theorem B2804915 : Blo 1555475 2804915 := bstep (se 1 (by rfl) ⟨2103686, by rfl⟩ : syracuseStep 2804915 = 4207373) B4207373
theorem B5254361 : Blo 1555475 5254361 := bstep (se 2 (by rfl) ⟨1970385, by rfl⟩ : syracuseStep 5254361 = 3940771) B3940771
theorem B3501323 : Blo 1555475 3501323 := bstep (se 1 (by rfl) ⟨2625992, by rfl⟩ : syracuseStep 3501323 = 5251985) B5251985
theorem B14200109 : Blo 1555475 14200109 := bstep (se 3 (by rfl) ⟨2662520, by rfl⟩ : syracuseStep 14200109 = 5325041) B5325041
theorem B3501377 : Blo 1555475 3501377 := bstep (se 2 (by rfl) ⟨1313016, by rfl⟩ : syracuseStep 3501377 = 2626033) B2626033
theorem B1969687 : Blo 1555475 1969687 := bstep (se 1 (by rfl) ⟨1477265, by rfl⟩ : syracuseStep 1969687 = 2954531) B2954531
theorem B3501593 : Blo 1555475 3501593 := bstep (se 2 (by rfl) ⟨1313097, by rfl⟩ : syracuseStep 3501593 = 2626195) B2626195
theorem B9973313 : Blo 1555475 9973313 := bstep (se 2 (by rfl) ⟨3739992, by rfl⟩ : syracuseStep 9973313 = 7479985) B7479985
theorem B3501683 : Blo 1555475 3501683 := bstep (se 1 (by rfl) ⟨2626262, by rfl⟩ : syracuseStep 3501683 = 5252525) B5252525
theorem B3501719 : Blo 1555475 3501719 := bstep (se 1 (by rfl) ⟨2626289, by rfl⟩ : syracuseStep 3501719 = 5252579) B5252579
theorem B3501899 : Blo 1555475 3501899 := bstep (se 1 (by rfl) ⟨2626424, by rfl⟩ : syracuseStep 3501899 = 5252849) B5252849
theorem B4984669 : Blo 1555475 4984669 := bstep (se 3 (by rfl) ⟨934625, by rfl⟩ : syracuseStep 4984669 = 1869251) B1869251
theorem B6311773 : Blo 1555475 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B3501953 : Blo 1555475 3501953 := bstep (se 2 (by rfl) ⟨1313232, by rfl⟩ : syracuseStep 3501953 = 2626465) B2626465
theorem B2625419 : Blo 1555475 2625419 := bstep (se 1 (by rfl) ⟨1969064, by rfl⟩ : syracuseStep 2625419 = 3938129) B3938129
theorem B2953111 : Blo 1555475 2953111 := bstep (se 1 (by rfl) ⟨2214833, by rfl⟩ : syracuseStep 2953111 = 4429667) B4429667
theorem B7098263 : Blo 1555475 7098263 := bstep (se 1 (by rfl) ⟨5323697, by rfl⟩ : syracuseStep 7098263 = 10647395) B10647395
theorem B5255063 : Blo 1555475 5255063 := bstep (se 1 (by rfl) ⟨3941297, by rfl⟩ : syracuseStep 5255063 = 7882595) B7882595
theorem B2625547 : Blo 1555475 2625547 := bstep (se 1 (by rfl) ⟨1969160, by rfl⟩ : syracuseStep 2625547 = 3938321) B3938321
theorem B35926091 : Blo 1555475 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B2994265 : Blo 1555475 2994265 := bstep (se 2 (by rfl) ⟨1122849, by rfl⟩ : syracuseStep 2994265 = 2245699) B2245699
theorem B3502169 : Blo 1555475 3502169 := bstep (se 2 (by rfl) ⟨1313313, by rfl⟩ : syracuseStep 3502169 = 2626627) B2626627
theorem B8982629 : Blo 1555475 8982629 := bstep (se 4 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 8982629 = 1684243) B1684243
theorem B2953331 : Blo 1555475 2953331 := bstep (se 1 (by rfl) ⟨2214998, by rfl⟩ : syracuseStep 2953331 = 4429997) B4429997
theorem B29913239 : Blo 1555475 29913239 := bstep (se 1 (by rfl) ⟨22434929, by rfl⟩ : syracuseStep 29913239 = 44869859) B44869859
theorem B2625689 : Blo 1555475 2625689 := bstep (se 2 (by rfl) ⟨984633, by rfl⟩ : syracuseStep 2625689 = 1969267) B1969267
theorem B3502259 : Blo 1555475 3502259 := bstep (se 1 (by rfl) ⟨2626694, by rfl⟩ : syracuseStep 3502259 = 5253389) B5253389
theorem B2494667 : Blo 1555475 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B3502295 : Blo 1555475 3502295 := bstep (se 1 (by rfl) ⟨2626721, by rfl⟩ : syracuseStep 3502295 = 5253443) B5253443
theorem B2806039 : Blo 1555475 2806039 := bstep (se 1 (by rfl) ⟨2104529, by rfl⟩ : syracuseStep 2806039 = 4209059) B4209059
theorem B2625817 : Blo 1555475 2625817 := bstep (se 2 (by rfl) ⟨984681, by rfl⟩ : syracuseStep 2625817 = 1969363) B1969363
theorem B1970507 : Blo 1555475 1970507 := bstep (se 1 (by rfl) ⟨1477880, by rfl⟩ : syracuseStep 1970507 = 2955761) B2955761
theorem B2953559 : Blo 1555475 2953559 := bstep (se 1 (by rfl) ⟨2215169, by rfl⟩ : syracuseStep 2953559 = 4430339) B4430339
theorem B3502475 : Blo 1555475 3502475 := bstep (se 1 (by rfl) ⟨2626856, by rfl⟩ : syracuseStep 3502475 = 5253713) B5253713
theorem B2806169 : Blo 1555475 2806169 := bstep (se 2 (by rfl) ⟨1052313, by rfl⟩ : syracuseStep 2806169 = 2104627) B2104627
theorem B5255603 : Blo 1555475 5255603 := bstep (se 1 (by rfl) ⟨3941702, by rfl⟩ : syracuseStep 5255603 = 7883405) B7883405
theorem B3502529 : Blo 1555475 3502529 := bstep (se 2 (by rfl) ⟨1313448, by rfl⟩ : syracuseStep 3502529 = 2626897) B2626897
theorem B8417753 : Blo 1555475 8417753 := bstep (se 2 (by rfl) ⟨3156657, by rfl⟩ : syracuseStep 8417753 = 6313315) B6313315
theorem B4207069 : Blo 1555475 4207069 := bstep (se 3 (by rfl) ⟨788825, by rfl⟩ : syracuseStep 4207069 = 1577651) B1577651
theorem B2953817 : Blo 1555475 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B9466469 : Blo 1555475 9466469 := bstep (se 4 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 9466469 = 1774963) B1774963
theorem B3502745 : Blo 1555475 3502745 := bstep (se 2 (by rfl) ⟨1313529, by rfl⟩ : syracuseStep 3502745 = 2627059) B2627059
theorem B5255873 : Blo 1555475 5255873 := bstep (se 2 (by rfl) ⟨1970952, by rfl⟩ : syracuseStep 5255873 = 3941905) B3941905
theorem B71914225 : Blo 1555475 71914225 := bstep (se 2 (by rfl) ⟨26967834, by rfl⟩ : syracuseStep 71914225 = 53935669) B53935669
theorem B3502835 : Blo 1555475 3502835 := bstep (se 1 (by rfl) ⟨2627126, by rfl⟩ : syracuseStep 3502835 = 5254253) B5254253
theorem B7099139 : Blo 1555475 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B3502871 : Blo 1555475 3502871 := bstep (se 1 (by rfl) ⟨2627153, by rfl⟩ : syracuseStep 3502871 = 5254307) B5254307
theorem B2626391 : Blo 1555475 2626391 := bstep (se 1 (by rfl) ⟨1969793, by rfl⟩ : syracuseStep 2626391 = 3939587) B3939587
theorem B2216855 : Blo 1555475 2216855 := bstep (se 1 (by rfl) ⟨1662641, by rfl⟩ : syracuseStep 2216855 = 3325283) B3325283
theorem B3503051 : Blo 1555475 3503051 := bstep (se 1 (by rfl) ⟨2627288, by rfl⟩ : syracuseStep 3503051 = 5254577) B5254577
theorem B11531213 : Blo 1555475 11531213 := bstep (se 3 (by rfl) ⟨2162102, by rfl⟩ : syracuseStep 11531213 = 4324205) B4324205
theorem B2626519 : Blo 1555475 2626519 := bstep (se 1 (by rfl) ⟨1969889, by rfl⟩ : syracuseStep 2626519 = 3939779) B3939779
theorem B2954227 : Blo 1555475 2954227 := bstep (se 1 (by rfl) ⟨2215670, by rfl⟩ : syracuseStep 2954227 = 4431341) B4431341
theorem B3503105 : Blo 1555475 3503105 := bstep (se 2 (by rfl) ⟨1313664, by rfl⟩ : syracuseStep 3503105 = 2627329) B2627329
theorem B1750027 : Blo 1555475 1750027 := bstep (se 1 (by rfl) ⟨1312520, by rfl⟩ : syracuseStep 1750027 = 2625041) B2625041
theorem B3937369 : Blo 1555475 3937369 := bstep (se 2 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 3937369 = 2953027) B2953027
theorem B6648925 : Blo 1555475 6648925 := bstep (se 3 (by rfl) ⟨1246673, by rfl⟩ : syracuseStep 6648925 = 2493347) B2493347
theorem B1750135 : Blo 1555475 1750135 := bstep (se 1 (by rfl) ⟨1312601, by rfl⟩ : syracuseStep 1750135 = 2625203) B2625203
theorem B3503321 : Blo 1555475 3503321 := bstep (se 2 (by rfl) ⟨1313745, by rfl⟩ : syracuseStep 3503321 = 2627491) B2627491
theorem B5256413 : Blo 1555475 5256413 := bstep (se 3 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 5256413 = 1971155) B1971155
theorem B5911811 : Blo 1555475 5911811 := bstep (se 1 (by rfl) ⟨4433858, by rfl⟩ : syracuseStep 5911811 = 8867717) B8867717
theorem B5911825 : Blo 1555475 5911825 := bstep (se 2 (by rfl) ⟨2216934, by rfl⟩ : syracuseStep 5911825 = 4433869) B4433869
theorem B1750315 : Blo 1555475 1750315 := bstep (se 1 (by rfl) ⟨1312736, by rfl⟩ : syracuseStep 1750315 = 2625473) B2625473
theorem B3503411 : Blo 1555475 3503411 := bstep (se 1 (by rfl) ⟨2627558, by rfl⟩ : syracuseStep 3503411 = 5255117) B5255117
theorem B8418635 : Blo 1555475 8418635 := bstep (se 1 (by rfl) ⟨6313976, by rfl⟩ : syracuseStep 8418635 = 12627953) B12627953
theorem B3503447 : Blo 1555475 3503447 := bstep (se 1 (by rfl) ⟨2627585, by rfl⟩ : syracuseStep 3503447 = 5255171) B5255171
theorem B1774967 : Blo 1555475 1774967 := bstep (se 1 (by rfl) ⟨1331225, by rfl⟩ : syracuseStep 1774967 = 2662451) B2662451
theorem B9966979 : Blo 1555475 9966979 := bstep (se 1 (by rfl) ⟨7475234, by rfl⟩ : syracuseStep 9966979 = 14950469) B14950469
theorem B1750423 : Blo 1555475 1750423 := bstep (se 1 (by rfl) ⟨1312817, by rfl⟩ : syracuseStep 1750423 = 2625635) B2625635
theorem B2954713 : Blo 1555475 2954713 := bstep (se 2 (by rfl) ⟨1108017, by rfl⟩ : syracuseStep 2954713 = 2216035) B2216035
theorem B3503627 : Blo 1555475 3503627 := bstep (se 1 (by rfl) ⟨2627720, by rfl⟩ : syracuseStep 3503627 = 5255441) B5255441
theorem B5912129 : Blo 1555475 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B3503681 : Blo 1555475 3503681 := bstep (se 2 (by rfl) ⟨1313880, by rfl⟩ : syracuseStep 3503681 = 2627761) B2627761
theorem B1750603 : Blo 1555475 1750603 := bstep (se 1 (by rfl) ⟨1312952, by rfl⟩ : syracuseStep 1750603 = 2625905) B2625905
theorem B2627147 : Blo 1555475 2627147 := bstep (se 1 (by rfl) ⟨1970360, by rfl⟩ : syracuseStep 2627147 = 3940721) B3940721
theorem B15980125 : Blo 1555475 15980125 := bstep (se 3 (by rfl) ⟨2996273, by rfl⟩ : syracuseStep 15980125 = 5992547) B5992547
theorem B14956163 : Blo 1555475 14956163 := bstep (se 1 (by rfl) ⟨11217122, by rfl⟩ : syracuseStep 14956163 = 22434245) B22434245
theorem B1750711 : Blo 1555475 1750711 := bstep (se 1 (by rfl) ⟨1313033, by rfl⟩ : syracuseStep 1750711 = 2626067) B2626067
theorem B2627275 : Blo 1555475 2627275 := bstep (se 1 (by rfl) ⟨1970456, by rfl⟩ : syracuseStep 2627275 = 3940913) B3940913
theorem B21288653 : Blo 1555475 21288653 := bstep (se 3 (by rfl) ⟨3991622, by rfl⟩ : syracuseStep 21288653 = 7983245) B7983245
theorem B3503897 : Blo 1555475 3503897 := bstep (se 2 (by rfl) ⟨1313961, by rfl⟩ : syracuseStep 3503897 = 2627923) B2627923
theorem B2627417 : Blo 1555475 2627417 := bstep (se 2 (by rfl) ⟨985281, by rfl⟩ : syracuseStep 2627417 = 1970563) B1970563
theorem B1750891 : Blo 1555475 1750891 := bstep (se 1 (by rfl) ⟨1313168, by rfl⟩ : syracuseStep 1750891 = 2626337) B2626337
theorem B3503987 : Blo 1555475 3503987 := bstep (se 1 (by rfl) ⟨2627990, by rfl⟩ : syracuseStep 3503987 = 5255981) B5255981
theorem B3504023 : Blo 1555475 3504023 := bstep (se 1 (by rfl) ⟨2628017, by rfl⟩ : syracuseStep 3504023 = 5256035) B5256035
theorem B1750999 : Blo 1555475 1750999 := bstep (se 1 (by rfl) ⟨1313249, by rfl⟩ : syracuseStep 1750999 = 2626499) B2626499
theorem B2627545 : Blo 1555475 2627545 := bstep (se 2 (by rfl) ⟨985329, by rfl⟩ : syracuseStep 2627545 = 1970659) B1970659
theorem B3323891 : Blo 1555475 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B2955275 : Blo 1555475 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B8091665 : Blo 1555475 8091665 := bstep (se 2 (by rfl) ⟨3034374, by rfl⟩ : syracuseStep 8091665 = 6068749) B6068749
theorem B3504203 : Blo 1555475 3504203 := bstep (se 1 (by rfl) ⟨2628152, by rfl⟩ : syracuseStep 3504203 = 5256305) B5256305
theorem B22747229 : Blo 1555475 22747229 := bstep (se 3 (by rfl) ⟨4265105, by rfl⟩ : syracuseStep 22747229 = 8530211) B8530211
theorem B3504257 : Blo 1555475 3504257 := bstep (se 2 (by rfl) ⟨1314096, by rfl⟩ : syracuseStep 3504257 = 2628193) B2628193
theorem B1751179 : Blo 1555475 1751179 := bstep (se 1 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 1751179 = 2626769) B2626769
theorem B5609645 : Blo 1555475 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B3938483 : Blo 1555475 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B2955457 : Blo 1555475 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B5912797 : Blo 1555475 5912797 := bstep (se 3 (by rfl) ⟨1108649, by rfl⟩ : syracuseStep 5912797 = 2217299) B2217299
theorem B1751287 : Blo 1555475 1751287 := bstep (se 1 (by rfl) ⟨1313465, by rfl⟩ : syracuseStep 1751287 = 2626931) B2626931
theorem B6650257 : Blo 1555475 6650257 := bstep (se 2 (by rfl) ⟨2493846, by rfl⟩ : syracuseStep 6650257 = 4987693) B4987693
theorem B1751467 : Blo 1555475 1751467 := bstep (se 1 (by rfl) ⟨1313600, by rfl⟩ : syracuseStep 1751467 = 2627201) B2627201
theorem B3938777 : Blo 1555475 3938777 := bstep (se 2 (by rfl) ⟨1477041, by rfl⟩ : syracuseStep 3938777 = 2954083) B2954083
theorem B3324377 : Blo 1555475 3324377 := bstep (se 2 (by rfl) ⟨1246641, by rfl⟩ : syracuseStep 3324377 = 2493283) B2493283
theorem B1751575 : Blo 1555475 1751575 := bstep (se 1 (by rfl) ⟨1313681, by rfl⟩ : syracuseStep 1751575 = 2627363) B2627363
theorem B2103833 : Blo 1555475 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B2628119 : Blo 1555475 2628119 := bstep (se 1 (by rfl) ⟨1971089, by rfl⟩ : syracuseStep 2628119 = 3942179) B3942179
theorem B2366039 : Blo 1555475 2366039 := bstep (se 1 (by rfl) ⟨1774529, by rfl⟩ : syracuseStep 2366039 = 3549059) B3549059
theorem B2333273 : Blo 1555475 2333273 := bstep (se 2 (by rfl) ⟨874977, by rfl⟩ : syracuseStep 2333273 = 1749955) B1749955
theorem B2333387 : Blo 1555475 2333387 := bstep (se 1 (by rfl) ⟨1750040, by rfl⟩ : syracuseStep 2333387 = 3500081) B3500081
theorem B1751755 : Blo 1555475 1751755 := bstep (se 1 (by rfl) ⟨1313816, by rfl⟩ : syracuseStep 1751755 = 2627633) B2627633
theorem B2333399 : Blo 1555475 2333399 := bstep (se 1 (by rfl) ⟨1750049, by rfl⟩ : syracuseStep 2333399 = 3500099) B3500099
theorem B6314755 : Blo 1555475 6314755 := bstep (se 1 (by rfl) ⟨4736066, by rfl⟩ : syracuseStep 6314755 = 9472133) B9472133
theorem B15964933 : Blo 1555475 15964933 := bstep (se 4 (by rfl) ⟨1496712, by rfl⟩ : syracuseStep 15964933 = 2993425) B2993425
theorem B2661131 : Blo 1555475 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B2333465 : Blo 1555475 2333465 := bstep (se 2 (by rfl) ⟨875049, by rfl⟩ : syracuseStep 2333465 = 1750099) B1750099
theorem B1751863 : Blo 1555475 1751863 := bstep (se 1 (by rfl) ⟨1313897, by rfl⟩ : syracuseStep 1751863 = 2627795) B2627795
theorem B7879517 : Blo 1555475 7879517 := bstep (se 3 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 7879517 = 2954819) B2954819
theorem B2333579 : Blo 1555475 2333579 := bstep (se 1 (by rfl) ⟨1750184, by rfl⟩ : syracuseStep 2333579 = 3500369) B3500369
theorem B2956171 : Blo 1555475 2956171 := bstep (se 1 (by rfl) ⟨2217128, by rfl⟩ : syracuseStep 2956171 = 4434257) B4434257
theorem B2333591 : Blo 1555475 2333591 := bstep (se 1 (by rfl) ⟨1750193, by rfl⟩ : syracuseStep 2333591 = 3500387) B3500387
theorem B4430771 : Blo 1555475 4430771 := bstep (se 1 (by rfl) ⟨3323078, by rfl⟩ : syracuseStep 4430771 = 6646157) B6646157
theorem B2956247 : Blo 1555475 2956247 := bstep (se 1 (by rfl) ⟨2217185, by rfl⟩ : syracuseStep 2956247 = 4434371) B4434371
theorem B2333657 : Blo 1555475 2333657 := bstep (se 2 (by rfl) ⟨875121, by rfl⟩ : syracuseStep 2333657 = 1750243) B1750243
theorem B1752043 : Blo 1555475 1752043 := bstep (se 1 (by rfl) ⟨1314032, by rfl⟩ : syracuseStep 1752043 = 2628065) B2628065
theorem B1555479 : Blo 1555475 1555479 := bstep (se 1 (by rfl) ⟨1166609, by rfl⟩ : syracuseStep 1555479 = 2333219) B2333219
theorem B1555499 : Blo 1555475 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B13294637 : Blo 1555475 13294637 := bstep (se 3 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 13294637 = 4985489) B4985489
theorem B1555511 : Blo 1555475 1555511 := bstep (se 1 (by rfl) ⟨1166633, by rfl⟩ : syracuseStep 1555511 = 2333267) B2333267
theorem B1555531 : Blo 1555475 1555531 := bstep (se 1 (by rfl) ⟨1166648, by rfl⟩ : syracuseStep 1555531 = 2333297) B2333297
theorem B2333771 : Blo 1555475 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B1555543 : Blo 1555475 1555543 := bstep (se 1 (by rfl) ⟨1166657, by rfl⟩ : syracuseStep 1555543 = 2333315) B2333315
theorem B2333783 : Blo 1555475 2333783 := bstep (se 1 (by rfl) ⟨1750337, by rfl⟩ : syracuseStep 2333783 = 3500675) B3500675
theorem B1752151 : Blo 1555475 1752151 := bstep (se 1 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 1752151 = 2628227) B2628227
theorem B1555563 : Blo 1555475 1555563 := bstep (se 1 (by rfl) ⟨1166672, by rfl⟩ : syracuseStep 1555563 = 2333345) B2333345
theorem B1555575 : Blo 1555475 1555575 := bstep (se 1 (by rfl) ⟨1166681, by rfl⟩ : syracuseStep 1555575 = 2333363) B2333363
theorem B1555595 : Blo 1555475 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B1555607 : Blo 1555475 1555607 := bstep (se 1 (by rfl) ⟨1166705, by rfl⟩ : syracuseStep 1555607 = 2333411) B2333411
theorem B4430999 : Blo 1555475 4430999 := bstep (se 1 (by rfl) ⟨3323249, by rfl⟩ : syracuseStep 4430999 = 6646499) B6646499
theorem B2333849 : Blo 1555475 2333849 := bstep (se 2 (by rfl) ⟨875193, by rfl⟩ : syracuseStep 2333849 = 1750387) B1750387
theorem B1662103 : Blo 1555475 1662103 := bstep (se 1 (by rfl) ⟨1246577, by rfl⟩ : syracuseStep 1662103 = 2493155) B2493155
theorem B1555627 : Blo 1555475 1555627 := bstep (se 1 (by rfl) ⟨1166720, by rfl⟩ : syracuseStep 1555627 = 2333441) B2333441
theorem B1555639 : Blo 1555475 1555639 := bstep (se 1 (by rfl) ⟨1166729, by rfl⟩ : syracuseStep 1555639 = 2333459) B2333459
theorem B3325121 : Blo 1555475 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B1555659 : Blo 1555475 1555659 := bstep (se 1 (by rfl) ⟨1166744, by rfl⟩ : syracuseStep 1555659 = 2333489) B2333489
theorem B1555671 : Blo 1555475 1555671 := bstep (se 1 (by rfl) ⟨1166753, by rfl⟩ : syracuseStep 1555671 = 2333507) B2333507
theorem B1555691 : Blo 1555475 1555691 := bstep (se 1 (by rfl) ⟨1166768, by rfl⟩ : syracuseStep 1555691 = 2333537) B2333537
theorem B1555703 : Blo 1555475 1555703 := bstep (se 1 (by rfl) ⟨1166777, by rfl⟩ : syracuseStep 1555703 = 2333555) B2333555
theorem B1555723 : Blo 1555475 1555723 := bstep (se 1 (by rfl) ⟨1166792, by rfl⟩ : syracuseStep 1555723 = 2333585) B2333585
theorem B2333963 : Blo 1555475 2333963 := bstep (se 1 (by rfl) ⟨1750472, by rfl⟩ : syracuseStep 2333963 = 3500945) B3500945
theorem B1555735 : Blo 1555475 1555735 := bstep (se 1 (by rfl) ⟨1166801, by rfl⟩ : syracuseStep 1555735 = 2333603) B2333603
theorem B2333975 : Blo 1555475 2333975 := bstep (se 1 (by rfl) ⟨1750481, by rfl⟩ : syracuseStep 2333975 = 3500963) B3500963
theorem B1555755 : Blo 1555475 1555755 := bstep (se 1 (by rfl) ⟨1166816, by rfl⟩ : syracuseStep 1555755 = 2333633) B2333633
theorem B11214125 : Blo 1555475 11214125 := bstep (se 3 (by rfl) ⟨2102648, by rfl⟩ : syracuseStep 11214125 = 4205297) B4205297
theorem B1555767 : Blo 1555475 1555767 := bstep (se 1 (by rfl) ⟨1166825, by rfl⟩ : syracuseStep 1555767 = 2333651) B2333651
theorem B1555787 : Blo 1555475 1555787 := bstep (se 1 (by rfl) ⟨1166840, by rfl⟩ : syracuseStep 1555787 = 2333681) B2333681
theorem B1555799 : Blo 1555475 1555799 := bstep (se 1 (by rfl) ⟨1166849, by rfl⟩ : syracuseStep 1555799 = 2333699) B2333699
theorem B2334041 : Blo 1555475 2334041 := bstep (se 2 (by rfl) ⟨875265, by rfl⟩ : syracuseStep 2334041 = 1750531) B1750531
theorem B1555819 : Blo 1555475 1555819 := bstep (se 1 (by rfl) ⟨1166864, by rfl⟩ : syracuseStep 1555819 = 2333729) B2333729
theorem B1555831 : Blo 1555475 1555831 := bstep (se 1 (by rfl) ⟨1166873, by rfl⟩ : syracuseStep 1555831 = 2333747) B2333747
theorem B1555851 : Blo 1555475 1555851 := bstep (se 1 (by rfl) ⟨1166888, by rfl⟩ : syracuseStep 1555851 = 2333777) B2333777
theorem B1555863 : Blo 1555475 1555863 := bstep (se 1 (by rfl) ⟨1166897, by rfl⟩ : syracuseStep 1555863 = 2333795) B2333795
theorem B1555883 : Blo 1555475 1555883 := bstep (se 1 (by rfl) ⟨1166912, by rfl⟩ : syracuseStep 1555883 = 2333825) B2333825
theorem B1555895 : Blo 1555475 1555895 := bstep (se 1 (by rfl) ⟨1166921, by rfl⟩ : syracuseStep 1555895 = 2333843) B2333843
theorem B1555915 : Blo 1555475 1555915 := bstep (se 1 (by rfl) ⟨1166936, by rfl⟩ : syracuseStep 1555915 = 2333873) B2333873
theorem B2334155 : Blo 1555475 2334155 := bstep (se 1 (by rfl) ⟨1750616, by rfl⟩ : syracuseStep 2334155 = 3501233) B3501233
theorem B4431307 : Blo 1555475 4431307 := bstep (se 1 (by rfl) ⟨3323480, by rfl⟩ : syracuseStep 4431307 = 6646961) B6646961
theorem B1555927 : Blo 1555475 1555927 := bstep (se 1 (by rfl) ⟨1166945, by rfl⟩ : syracuseStep 1555927 = 2333891) B2333891
theorem B2334167 : Blo 1555475 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1555947 : Blo 1555475 1555947 := bstep (se 1 (by rfl) ⟨1166960, by rfl⟩ : syracuseStep 1555947 = 2333921) B2333921
theorem B1555959 : Blo 1555475 1555959 := bstep (se 1 (by rfl) ⟨1166969, by rfl⟩ : syracuseStep 1555959 = 2333939) B2333939
theorem B1555979 : Blo 1555475 1555979 := bstep (se 1 (by rfl) ⟨1166984, by rfl⟩ : syracuseStep 1555979 = 2333969) B2333969
theorem B1555991 : Blo 1555475 1555991 := bstep (se 1 (by rfl) ⟨1166993, by rfl⟩ : syracuseStep 1555991 = 2333987) B2333987
theorem B2334233 : Blo 1555475 2334233 := bstep (se 2 (by rfl) ⟨875337, by rfl⟩ : syracuseStep 2334233 = 1750675) B1750675
theorem B1556011 : Blo 1555475 1556011 := bstep (se 1 (by rfl) ⟨1167008, by rfl⟩ : syracuseStep 1556011 = 2334017) B2334017
theorem B1556023 : Blo 1555475 1556023 := bstep (se 1 (by rfl) ⟨1167017, by rfl⟩ : syracuseStep 1556023 = 2334035) B2334035
theorem B5250635 : Blo 1555475 5250635 := bstep (se 1 (by rfl) ⟨3937976, by rfl⟩ : syracuseStep 5250635 = 7875953) B7875953
theorem B1556043 : Blo 1555475 1556043 := bstep (se 1 (by rfl) ⟨1167032, by rfl⟩ : syracuseStep 1556043 = 2334065) B2334065
theorem B1556055 : Blo 1555475 1556055 := bstep (se 1 (by rfl) ⟨1167041, by rfl⟩ : syracuseStep 1556055 = 2334083) B2334083
theorem B1556075 : Blo 1555475 1556075 := bstep (se 1 (by rfl) ⟨1167056, by rfl⟩ : syracuseStep 1556075 = 2334113) B2334113
theorem B1556087 : Blo 1555475 1556087 := bstep (se 1 (by rfl) ⟨1167065, by rfl⟩ : syracuseStep 1556087 = 2334131) B2334131
theorem B1556107 : Blo 1555475 1556107 := bstep (se 1 (by rfl) ⟨1167080, by rfl⟩ : syracuseStep 1556107 = 2334161) B2334161
theorem B2334347 : Blo 1555475 2334347 := bstep (se 1 (by rfl) ⟨1750760, by rfl⟩ : syracuseStep 2334347 = 3501521) B3501521
theorem B1556119 : Blo 1555475 1556119 := bstep (se 1 (by rfl) ⟨1167089, by rfl⟩ : syracuseStep 1556119 = 2334179) B2334179
theorem B2334359 : Blo 1555475 2334359 := bstep (se 1 (by rfl) ⟨1750769, by rfl⟩ : syracuseStep 2334359 = 3501539) B3501539
theorem B1556139 : Blo 1555475 1556139 := bstep (se 1 (by rfl) ⟨1167104, by rfl⟩ : syracuseStep 1556139 = 2334209) B2334209
theorem B4800179 : Blo 1555475 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B1556151 : Blo 1555475 1556151 := bstep (se 1 (by rfl) ⟨1167113, by rfl⟩ : syracuseStep 1556151 = 2334227) B2334227
theorem B1556171 : Blo 1555475 1556171 := bstep (se 1 (by rfl) ⟨1167128, by rfl⟩ : syracuseStep 1556171 = 2334257) B2334257
theorem B1556183 : Blo 1555475 1556183 := bstep (se 1 (by rfl) ⟨1167137, by rfl⟩ : syracuseStep 1556183 = 2334275) B2334275
theorem B2334425 : Blo 1555475 2334425 := bstep (se 2 (by rfl) ⟨875409, by rfl⟩ : syracuseStep 2334425 = 1750819) B1750819
theorem B4431581 : Blo 1555475 4431581 := bstep (se 3 (by rfl) ⟨830921, by rfl⟩ : syracuseStep 4431581 = 1661843) B1661843
theorem B1556203 : Blo 1555475 1556203 := bstep (se 1 (by rfl) ⟨1167152, by rfl⟩ : syracuseStep 1556203 = 2334305) B2334305
theorem B1556215 : Blo 1555475 1556215 := bstep (se 1 (by rfl) ⟨1167161, by rfl⟩ : syracuseStep 1556215 = 2334323) B2334323
theorem B1556235 : Blo 1555475 1556235 := bstep (se 1 (by rfl) ⟨1167176, by rfl⟩ : syracuseStep 1556235 = 2334353) B2334353
theorem B1556247 : Blo 1555475 1556247 := bstep (se 1 (by rfl) ⟨1167185, by rfl⟩ : syracuseStep 1556247 = 2334371) B2334371
theorem B1556267 : Blo 1555475 1556267 := bstep (se 1 (by rfl) ⟨1167200, by rfl⟩ : syracuseStep 1556267 = 2334401) B2334401
theorem B1556279 : Blo 1555475 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B1556299 : Blo 1555475 1556299 := bstep (se 1 (by rfl) ⟨1167224, by rfl⟩ : syracuseStep 1556299 = 2334449) B2334449
theorem B2334539 : Blo 1555475 2334539 := bstep (se 1 (by rfl) ⟨1750904, by rfl⟩ : syracuseStep 2334539 = 3501809) B3501809
theorem B1556311 : Blo 1555475 1556311 := bstep (se 1 (by rfl) ⟨1167233, by rfl⟩ : syracuseStep 1556311 = 2334467) B2334467
theorem B2334551 : Blo 1555475 2334551 := bstep (se 1 (by rfl) ⟨1750913, by rfl⟩ : syracuseStep 2334551 = 3501827) B3501827
theorem B5250905 : Blo 1555475 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B1556331 : Blo 1555475 1556331 := bstep (se 1 (by rfl) ⟨1167248, by rfl⟩ : syracuseStep 1556331 = 2334497) B2334497
theorem B1556343 : Blo 1555475 1556343 := bstep (se 1 (by rfl) ⟨1167257, by rfl⟩ : syracuseStep 1556343 = 2334515) B2334515
theorem B1556363 : Blo 1555475 1556363 := bstep (se 1 (by rfl) ⟨1167272, by rfl⟩ : syracuseStep 1556363 = 2334545) B2334545
theorem B1556375 : Blo 1555475 1556375 := bstep (se 1 (by rfl) ⟨1167281, by rfl⟩ : syracuseStep 1556375 = 2334563) B2334563
theorem B2334617 : Blo 1555475 2334617 := bstep (se 2 (by rfl) ⟨875481, by rfl⟩ : syracuseStep 2334617 = 1750963) B1750963
theorem B1556395 : Blo 1555475 1556395 := bstep (se 1 (by rfl) ⟨1167296, by rfl⟩ : syracuseStep 1556395 = 2334593) B2334593
theorem B11820977 : Blo 1555475 11820977 := bstep (se 2 (by rfl) ⟨4432866, by rfl⟩ : syracuseStep 11820977 = 8865733) B8865733
theorem B9723827 : Blo 1555475 9723827 := bstep (se 1 (by rfl) ⟨7292870, by rfl⟩ : syracuseStep 9723827 = 14585741) B14585741
theorem B22446001 : Blo 1555475 22446001 := bstep (se 2 (by rfl) ⟨8417250, by rfl⟩ : syracuseStep 22446001 = 16834501) B16834501
theorem B1556407 : Blo 1555475 1556407 := bstep (se 1 (by rfl) ⟨1167305, by rfl⟩ : syracuseStep 1556407 = 2334611) B2334611
theorem B1556427 : Blo 1555475 1556427 := bstep (se 1 (by rfl) ⟨1167320, by rfl⟩ : syracuseStep 1556427 = 2334641) B2334641
theorem B1556439 : Blo 1555475 1556439 := bstep (se 1 (by rfl) ⟨1167329, by rfl⟩ : syracuseStep 1556439 = 2334659) B2334659
theorem B1556459 : Blo 1555475 1556459 := bstep (se 1 (by rfl) ⟨1167344, by rfl⟩ : syracuseStep 1556459 = 2334689) B2334689
theorem B1556471 : Blo 1555475 1556471 := bstep (se 1 (by rfl) ⟨1167353, by rfl⟩ : syracuseStep 1556471 = 2334707) B2334707
theorem B1556487 : Blo 1555475 1556487 := bstep (se 1 (by rfl) ⟨1167365, by rfl⟩ : syracuseStep 1556487 = 2334731) B2334731
theorem B1556495 : Blo 1555475 1556495 := bstep (se 1 (by rfl) ⟨1167371, by rfl⟩ : syracuseStep 1556495 = 2334743) B2334743
theorem B2334779 : Blo 1555475 2334779 := bstep (se 1 (by rfl) ⟨1751084, by rfl⟩ : syracuseStep 2334779 = 3502169) B3502169
theorem B1556539 : Blo 1555475 1556539 := bstep (se 1 (by rfl) ⟨1167404, by rfl⟩ : syracuseStep 1556539 = 2334809) B2334809
theorem B5988419 : Blo 1555475 5988419 := bstep (se 1 (by rfl) ⟨4491314, by rfl⟩ : syracuseStep 5988419 = 8982629) B8982629
theorem B2334839 : Blo 1555475 2334839 := bstep (se 1 (by rfl) ⟨1751129, by rfl⟩ : syracuseStep 2334839 = 3502259) B3502259
theorem B1556615 : Blo 1555475 1556615 := bstep (se 1 (by rfl) ⟨1167461, by rfl⟩ : syracuseStep 1556615 = 2334923) B2334923
theorem B1663111 : Blo 1555475 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B2334863 : Blo 1555475 2334863 := bstep (se 1 (by rfl) ⟨1751147, by rfl⟩ : syracuseStep 2334863 = 3502295) B3502295
theorem B1556623 : Blo 1555475 1556623 := bstep (se 1 (by rfl) ⟨1167467, by rfl⟩ : syracuseStep 1556623 = 2334935) B2334935
theorem B2334905 : Blo 1555475 2334905 := bstep (se 2 (by rfl) ⟨875589, by rfl⟩ : syracuseStep 2334905 = 1751179) B1751179
theorem B1556667 : Blo 1555475 1556667 := bstep (se 1 (by rfl) ⟨1167500, by rfl⟩ : syracuseStep 1556667 = 2335001) B2335001
theorem B3940609 : Blo 1555475 3940609 := bstep (se 2 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 3940609 = 2955457) B2955457
theorem B2334983 : Blo 1555475 2334983 := bstep (se 1 (by rfl) ⟨1751237, by rfl⟩ : syracuseStep 2334983 = 3502475) B3502475
theorem B1556743 : Blo 1555475 1556743 := bstep (se 1 (by rfl) ⟨1167557, by rfl⟩ : syracuseStep 1556743 = 2335115) B2335115
theorem B7880975 : Blo 1555475 7880975 := bstep (se 1 (by rfl) ⟨5910731, by rfl⟩ : syracuseStep 7880975 = 11821463) B11821463
theorem B1556751 : Blo 1555475 1556751 := bstep (se 1 (by rfl) ⟨1167563, by rfl⟩ : syracuseStep 1556751 = 2335127) B2335127
theorem B21291281 : Blo 1555475 21291281 := bstep (se 2 (by rfl) ⟨7984230, by rfl⟩ : syracuseStep 21291281 = 15968461) B15968461
theorem B33653009 : Blo 1555475 33653009 := bstep (se 2 (by rfl) ⟨12619878, by rfl⟩ : syracuseStep 33653009 = 25239757) B25239757
theorem B2335019 : Blo 1555475 2335019 := bstep (se 1 (by rfl) ⟨1751264, by rfl⟩ : syracuseStep 2335019 = 3502529) B3502529
theorem B1556795 : Blo 1555475 1556795 := bstep (se 1 (by rfl) ⟨1167596, by rfl⟩ : syracuseStep 1556795 = 2335193) B2335193
theorem B5611835 : Blo 1555475 5611835 := bstep (se 1 (by rfl) ⟨4208876, by rfl⟩ : syracuseStep 5611835 = 8417753) B8417753
theorem B2335049 : Blo 1555475 2335049 := bstep (se 2 (by rfl) ⟨875643, by rfl⟩ : syracuseStep 2335049 = 1751287) B1751287
theorem B1556871 : Blo 1555475 1556871 := bstep (se 1 (by rfl) ⟨1167653, by rfl⟩ : syracuseStep 1556871 = 2335307) B2335307
theorem B1556879 : Blo 1555475 1556879 := bstep (se 1 (by rfl) ⟨1167659, by rfl⟩ : syracuseStep 1556879 = 2335319) B2335319
theorem B6652307 : Blo 1555475 6652307 := bstep (se 1 (by rfl) ⟨4989230, by rfl⟩ : syracuseStep 6652307 = 9978461) B9978461
theorem B2335163 : Blo 1555475 2335163 := bstep (se 1 (by rfl) ⟨1751372, by rfl⟩ : syracuseStep 2335163 = 3502745) B3502745
theorem B1556923 : Blo 1555475 1556923 := bstep (se 1 (by rfl) ⟨1167692, by rfl⟩ : syracuseStep 1556923 = 2335385) B2335385
theorem B7479773 : Blo 1555475 7479773 := bstep (se 3 (by rfl) ⟨1402457, by rfl⟩ : syracuseStep 7479773 = 2804915) B2804915
theorem B2335223 : Blo 1555475 2335223 := bstep (se 1 (by rfl) ⟨1751417, by rfl⟩ : syracuseStep 2335223 = 3502835) B3502835
theorem B1556999 : Blo 1555475 1556999 := bstep (se 1 (by rfl) ⟨1167749, by rfl⟩ : syracuseStep 1556999 = 2335499) B2335499
theorem B2335247 : Blo 1555475 2335247 := bstep (se 1 (by rfl) ⟨1751435, by rfl⟩ : syracuseStep 2335247 = 3502871) B3502871
theorem B1557007 : Blo 1555475 1557007 := bstep (se 1 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 1557007 = 2335511) B2335511
theorem B2335289 : Blo 1555475 2335289 := bstep (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) B1751467
theorem B1557051 : Blo 1555475 1557051 := bstep (se 1 (by rfl) ⟨1167788, by rfl⟩ : syracuseStep 1557051 = 2335577) B2335577
theorem B2335367 : Blo 1555475 2335367 := bstep (se 1 (by rfl) ⟨1751525, by rfl⟩ : syracuseStep 2335367 = 3503051) B3503051
theorem B1557127 : Blo 1555475 1557127 := bstep (se 1 (by rfl) ⟨1167845, by rfl⟩ : syracuseStep 1557127 = 2335691) B2335691
theorem B1557135 : Blo 1555475 1557135 := bstep (se 1 (by rfl) ⟨1167851, by rfl⟩ : syracuseStep 1557135 = 2335703) B2335703
theorem B2335403 : Blo 1555475 2335403 := bstep (se 1 (by rfl) ⟨1751552, by rfl⟩ : syracuseStep 2335403 = 3503105) B3503105
theorem B1557179 : Blo 1555475 1557179 := bstep (se 1 (by rfl) ⟨1167884, by rfl⟩ : syracuseStep 1557179 = 2335769) B2335769
theorem B2335433 : Blo 1555475 2335433 := bstep (se 2 (by rfl) ⟨875787, by rfl⟩ : syracuseStep 2335433 = 1751575) B1751575
theorem B1557255 : Blo 1555475 1557255 := bstep (se 1 (by rfl) ⟨1167941, by rfl⟩ : syracuseStep 1557255 = 2335883) B2335883
theorem B1557263 : Blo 1555475 1557263 := bstep (se 1 (by rfl) ⟨1167947, by rfl⟩ : syracuseStep 1557263 = 2335895) B2335895
theorem B8864549 : Blo 1555475 8864549 := bstep (se 4 (by rfl) ⟨831051, by rfl⟩ : syracuseStep 8864549 = 1662103) B1662103
theorem B2335547 : Blo 1555475 2335547 := bstep (se 1 (by rfl) ⟨1751660, by rfl⟩ : syracuseStep 2335547 = 3503321) B3503321
theorem B1557307 : Blo 1555475 1557307 := bstep (se 1 (by rfl) ⟨1167980, by rfl⟩ : syracuseStep 1557307 = 2335961) B2335961
theorem B3941207 : Blo 1555475 3941207 := bstep (se 1 (by rfl) ⟨2955905, by rfl⟩ : syracuseStep 3941207 = 5911811) B5911811
theorem B2335607 : Blo 1555475 2335607 := bstep (se 1 (by rfl) ⟨1751705, by rfl⟩ : syracuseStep 2335607 = 3503411) B3503411
theorem B5612423 : Blo 1555475 5612423 := bstep (se 1 (by rfl) ⟨4209317, by rfl⟩ : syracuseStep 5612423 = 8418635) B8418635
theorem B1557383 : Blo 1555475 1557383 := bstep (se 1 (by rfl) ⟨1168037, by rfl⟩ : syracuseStep 1557383 = 2336075) B2336075
theorem B2335631 : Blo 1555475 2335631 := bstep (se 1 (by rfl) ⟨1751723, by rfl⟩ : syracuseStep 2335631 = 3503447) B3503447
theorem B1557391 : Blo 1555475 1557391 := bstep (se 1 (by rfl) ⟨1168043, by rfl⟩ : syracuseStep 1557391 = 2336087) B2336087
theorem B2335673 : Blo 1555475 2335673 := bstep (se 2 (by rfl) ⟨875877, by rfl⟩ : syracuseStep 2335673 = 1751755) B1751755
theorem B1557435 : Blo 1555475 1557435 := bstep (se 1 (by rfl) ⟨1168076, by rfl⟩ : syracuseStep 1557435 = 2336153) B2336153
theorem B2335751 : Blo 1555475 2335751 := bstep (se 1 (by rfl) ⟨1751813, by rfl⟩ : syracuseStep 2335751 = 3503627) B3503627
theorem B25248779 : Blo 1555475 25248779 := bstep (se 1 (by rfl) ⟨18936584, by rfl⟩ : syracuseStep 25248779 = 37873169) B37873169
theorem B2843681 : Blo 1555475 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B1868843 : Blo 1555475 1868843 := bstep (se 1 (by rfl) ⟨1401632, by rfl⟩ : syracuseStep 1868843 = 2803265) B2803265
theorem B3941419 : Blo 1555475 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B2335787 : Blo 1555475 2335787 := bstep (se 1 (by rfl) ⟨1751840, by rfl⟩ : syracuseStep 2335787 = 3503681) B3503681
theorem B2335817 : Blo 1555475 2335817 := bstep (se 2 (by rfl) ⟨875931, by rfl⟩ : syracuseStep 2335817 = 1751863) B1751863
theorem B9970775 : Blo 1555475 9970775 := bstep (se 1 (by rfl) ⟨7478081, by rfl⟩ : syracuseStep 9970775 = 14956163) B14956163
theorem B3941561 : Blo 1555475 3941561 := bstep (se 2 (by rfl) ⟨1478085, by rfl⟩ : syracuseStep 3941561 = 2956171) B2956171
theorem B2335931 : Blo 1555475 2335931 := bstep (se 1 (by rfl) ⟨1751948, by rfl⟩ : syracuseStep 2335931 = 3503897) B3503897
theorem B2335991 : Blo 1555475 2335991 := bstep (se 1 (by rfl) ⟨1751993, by rfl⟩ : syracuseStep 2335991 = 3503987) B3503987
theorem B2336015 : Blo 1555475 2336015 := bstep (se 1 (by rfl) ⟨1752011, by rfl⟩ : syracuseStep 2336015 = 3504023) B3504023
theorem B2336057 : Blo 1555475 2336057 := bstep (se 2 (by rfl) ⟨876021, by rfl⟩ : syracuseStep 2336057 = 1752043) B1752043
theorem B2336135 : Blo 1555475 2336135 := bstep (se 1 (by rfl) ⟨1752101, by rfl⟩ : syracuseStep 2336135 = 3504203) B3504203
theorem B15164819 : Blo 1555475 15164819 := bstep (se 1 (by rfl) ⟨11373614, by rfl⟩ : syracuseStep 15164819 = 22747229) B22747229
theorem B2336171 : Blo 1555475 2336171 := bstep (se 1 (by rfl) ⟨1752128, by rfl⟩ : syracuseStep 2336171 = 3504257) B3504257
theorem B2336201 : Blo 1555475 2336201 := bstep (se 2 (by rfl) ⟨876075, by rfl⟩ : syracuseStep 2336201 = 1752151) B1752151
theorem B8865233 : Blo 1555475 8865233 := bstep (se 2 (by rfl) ⟨3324462, by rfl⟩ : syracuseStep 8865233 = 6648925) B6648925
theorem B7882433 : Blo 1555475 7882433 := bstep (se 2 (by rfl) ⟨2955912, by rfl⟩ : syracuseStep 7882433 = 5911825) B5911825
theorem B8865551 : Blo 1555475 8865551 := bstep (se 1 (by rfl) ⟨6649163, by rfl⟩ : syracuseStep 8865551 = 13298327) B13298327
theorem B3737387 : Blo 1555475 3737387 := bstep (se 1 (by rfl) ⟨2803040, by rfl⟩ : syracuseStep 3737387 = 5606081) B5606081
theorem B13289305 : Blo 1555475 13289305 := bstep (se 2 (by rfl) ⟨4983489, by rfl⟩ : syracuseStep 13289305 = 9966979) B9966979
theorem B5253011 : Blo 1555475 5253011 := bstep (se 1 (by rfl) ⟨3939758, by rfl⟩ : syracuseStep 5253011 = 7879517) B7879517
theorem B5908409 : Blo 1555475 5908409 := bstep (se 2 (by rfl) ⟨2215653, by rfl⟩ : syracuseStep 5908409 = 4431307) B4431307
theorem B2803727 : Blo 1555475 2803727 := bstep (se 1 (by rfl) ⟨2102795, by rfl⟩ : syracuseStep 2803727 = 4205591) B4205591
theorem B7096349 : Blo 1555475 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B29903093 : Blo 1555475 29903093 := bstep (se 5 (by rfl) ⟨1401707, by rfl⟩ : syracuseStep 29903093 = 2803415) B2803415
theorem B3500423 : Blo 1555475 3500423 := bstep (se 1 (by rfl) ⟨2625317, by rfl⟩ : syracuseStep 3500423 = 5250635) B5250635
theorem B2492873 : Blo 1555475 2492873 := bstep (se 2 (by rfl) ⟨934827, by rfl⟩ : syracuseStep 2492873 = 1869655) B1869655
theorem B6646225 : Blo 1555475 6646225 := bstep (se 2 (by rfl) ⟨2492334, by rfl⟩ : syracuseStep 6646225 = 4984669) B4984669
theorem B8415697 : Blo 1555475 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B3500603 : Blo 1555475 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B29928001 : Blo 1555475 29928001 := bstep (se 2 (by rfl) ⟨11223000, by rfl⟩ : syracuseStep 29928001 = 22446001) B22446001
theorem B6482551 : Blo 1555475 6482551 := bstep (se 1 (by rfl) ⟨4861913, by rfl⟩ : syracuseStep 6482551 = 9723827) B9723827
theorem B3500729 : Blo 1555475 3500729 := bstep (se 2 (by rfl) ⟨1312773, by rfl⟩ : syracuseStep 3500729 = 2625547) B2625547
theorem B5057225 : Blo 1555475 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B1968887 : Blo 1555475 1968887 := bstep (se 1 (by rfl) ⟨1476665, by rfl⟩ : syracuseStep 1968887 = 2953331) B2953331
theorem B4434689 : Blo 1555475 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B19942159 : Blo 1555475 19942159 := bstep (se 1 (by rfl) ⟨14956619, by rfl⟩ : syracuseStep 19942159 = 29913239) B29913239
theorem B1969039 : Blo 1555475 1969039 := bstep (se 1 (by rfl) ⟨1476779, by rfl⟩ : syracuseStep 1969039 = 2953559) B2953559
theorem B5909395 : Blo 1555475 5909395 := bstep (se 1 (by rfl) ⟨4432046, by rfl⟩ : syracuseStep 5909395 = 8864093) B8864093
theorem B4205513 : Blo 1555475 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B2493385 : Blo 1555475 2493385 := bstep (se 2 (by rfl) ⟨935019, by rfl⟩ : syracuseStep 2493385 = 1870039) B1870039
theorem B7883729 : Blo 1555475 7883729 := bstep (se 2 (by rfl) ⟨2956398, by rfl⟩ : syracuseStep 7883729 = 5912797) B5912797
theorem B3501071 : Blo 1555475 3501071 := bstep (se 1 (by rfl) ⟨2625803, by rfl⟩ : syracuseStep 3501071 = 5251607) B5251607
theorem B3501089 : Blo 1555475 3501089 := bstep (se 2 (by rfl) ⟨1312908, by rfl⟩ : syracuseStep 3501089 = 2625817) B2625817
theorem B1969211 : Blo 1555475 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B6310979 : Blo 1555475 6310979 := bstep (se 1 (by rfl) ⟨4733234, by rfl⟩ : syracuseStep 6310979 = 9466469) B9466469
theorem B15969413 : Blo 1555475 15969413 := bstep (se 4 (by rfl) ⟨1497132, by rfl⟩ : syracuseStep 15969413 = 2994265) B2994265
theorem B8867009 : Blo 1555475 8867009 := bstep (se 2 (by rfl) ⟨3325128, by rfl⟩ : syracuseStep 8867009 = 6650257) B6650257
theorem B3550409 : Blo 1555475 3550409 := bstep (se 2 (by rfl) ⟨1331403, by rfl⟩ : syracuseStep 3550409 = 2662807) B2662807
theorem B4435145 : Blo 1555475 4435145 := bstep (se 2 (by rfl) ⟨1663179, by rfl⟩ : syracuseStep 4435145 = 3326359) B3326359
theorem B5254415 : Blo 1555475 5254415 := bstep (se 1 (by rfl) ⟨3940811, by rfl⟩ : syracuseStep 5254415 = 7881623) B7881623
theorem B2993441 : Blo 1555475 2993441 := bstep (se 2 (by rfl) ⟨1122540, by rfl⟩ : syracuseStep 2993441 = 2245081) B2245081
theorem B7687475 : Blo 1555475 7687475 := bstep (se 1 (by rfl) ⟨5765606, by rfl⟩ : syracuseStep 7687475 = 11531213) B11531213
theorem B8858969 : Blo 1555475 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B4730231 : Blo 1555475 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B3501431 : Blo 1555475 3501431 := bstep (se 1 (by rfl) ⟨2626073, by rfl⟩ : syracuseStep 3501431 = 5252147) B5252147
theorem B2624953 : Blo 1555475 2624953 := bstep (se 2 (by rfl) ⟨984357, by rfl⟩ : syracuseStep 2624953 = 1968715) B1968715
theorem B5254685 : Blo 1555475 5254685 := bstep (se 3 (by rfl) ⟨985253, by rfl⟩ : syracuseStep 5254685 = 1970507) B1970507
theorem B3501611 : Blo 1555475 3501611 := bstep (se 1 (by rfl) ⟨2626208, by rfl⟩ : syracuseStep 3501611 = 5252417) B5252417
theorem B19951181 : Blo 1555475 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B21286577 : Blo 1555475 21286577 := bstep (se 2 (by rfl) ⟨7982466, by rfl⟩ : syracuseStep 21286577 = 15964933) B15964933
theorem B7483117 : Blo 1555475 7483117 := bstep (se 3 (by rfl) ⟨1403084, by rfl⟩ : syracuseStep 7483117 = 2806169) B2806169
theorem B14192435 : Blo 1555475 14192435 := bstep (se 1 (by rfl) ⟨10644326, by rfl⟩ : syracuseStep 14192435 = 21288653) B21288653
theorem B3501971 : Blo 1555475 3501971 := bstep (se 1 (by rfl) ⟨2626478, by rfl⟩ : syracuseStep 3501971 = 5252957) B5252957
theorem B3502025 : Blo 1555475 3502025 := bstep (se 2 (by rfl) ⟨1313259, by rfl⟩ : syracuseStep 3502025 = 2626519) B2626519
theorem B2215927 : Blo 1555475 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B1970183 : Blo 1555475 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B5394443 : Blo 1555475 5394443 := bstep (se 1 (by rfl) ⟨4045832, by rfl⟩ : syracuseStep 5394443 = 8091665) B8091665
theorem B3739763 : Blo 1555475 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B2625655 : Blo 1555475 2625655 := bstep (se 1 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 2625655 = 3938483) B3938483
theorem B2625851 : Blo 1555475 2625851 := bstep (se 1 (by rfl) ⟨1969388, by rfl⟩ : syracuseStep 2625851 = 3938777) B3938777
theorem B2216251 : Blo 1555475 2216251 := bstep (se 1 (by rfl) ⟨1662188, by rfl⟩ : syracuseStep 2216251 = 3324377) B3324377
theorem B1577359 : Blo 1555475 1577359 := bstep (se 1 (by rfl) ⟨1183019, by rfl⟩ : syracuseStep 1577359 = 2366039) B2366039
theorem B12800477 : Blo 1555475 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B9974339 : Blo 1555475 9974339 := bstep (se 1 (by rfl) ⟨7480754, by rfl⟩ : syracuseStep 9974339 = 14961509) B14961509
theorem B5911127 : Blo 1555475 5911127 := bstep (se 1 (by rfl) ⟨4433345, by rfl⟩ : syracuseStep 5911127 = 8866691) B8866691
theorem B2953847 : Blo 1555475 2953847 := bstep (se 1 (by rfl) ⟨2215385, by rfl⟩ : syracuseStep 2953847 = 4430771) B4430771
theorem B3502727 : Blo 1555475 3502727 := bstep (se 1 (by rfl) ⟨2627045, by rfl⟩ : syracuseStep 3502727 = 5254091) B5254091
theorem B1970831 : Blo 1555475 1970831 := bstep (se 1 (by rfl) ⟨1478123, by rfl⟩ : syracuseStep 1970831 = 2956247) B2956247
theorem B2626249 : Blo 1555475 2626249 := bstep (se 2 (by rfl) ⟨984843, by rfl⟩ : syracuseStep 2626249 = 1969687) B1969687
theorem B12628709 : Blo 1555475 12628709 := bstep (se 4 (by rfl) ⟨1183941, by rfl⟩ : syracuseStep 12628709 = 2367883) B2367883
theorem B2953999 : Blo 1555475 2953999 := bstep (se 1 (by rfl) ⟨2215499, by rfl⟩ : syracuseStep 2953999 = 4430999) B4430999
theorem B2216747 : Blo 1555475 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B3502907 : Blo 1555475 3502907 := bstep (se 1 (by rfl) ⟨2627180, by rfl⟩ : syracuseStep 3502907 = 5254361) B5254361
theorem B7476083 : Blo 1555475 7476083 := bstep (se 1 (by rfl) ⟨5607062, by rfl⟩ : syracuseStep 7476083 = 11214125) B11214125
theorem B9466739 : Blo 1555475 9466739 := bstep (se 1 (by rfl) ⟨7100054, by rfl⟩ : syracuseStep 9466739 = 14200109) B14200109
theorem B5256089 : Blo 1555475 5256089 := bstep (se 2 (by rfl) ⟨1971033, by rfl⟩ : syracuseStep 5256089 = 3942067) B3942067
theorem B3503033 : Blo 1555475 3503033 := bstep (se 2 (by rfl) ⟨1313637, by rfl⟩ : syracuseStep 3503033 = 2627275) B2627275
theorem B6648875 : Blo 1555475 6648875 := bstep (se 1 (by rfl) ⟨4986656, by rfl⟩ : syracuseStep 6648875 = 9973313) B9973313
theorem B5911613 : Blo 1555475 5911613 := bstep (se 3 (by rfl) ⟨1108427, by rfl⟩ : syracuseStep 5911613 = 2216855) B2216855
theorem B2954387 : Blo 1555475 2954387 := bstep (se 1 (by rfl) ⟨2215790, by rfl⟩ : syracuseStep 2954387 = 4431581) B4431581
theorem B3937481 : Blo 1555475 3937481 := bstep (se 2 (by rfl) ⟨1476555, by rfl⟩ : syracuseStep 3937481 = 2953111) B2953111
theorem B1750279 : Blo 1555475 1750279 := bstep (se 1 (by rfl) ⟨1312709, by rfl⟩ : syracuseStep 1750279 = 2625419) B2625419
theorem B4732175 : Blo 1555475 4732175 := bstep (se 1 (by rfl) ⟨3549131, by rfl⟩ : syracuseStep 4732175 = 7098263) B7098263
theorem B3503375 : Blo 1555475 3503375 := bstep (se 1 (by rfl) ⟨2627531, by rfl⟩ : syracuseStep 3503375 = 5255063) B5255063
theorem B3503393 : Blo 1555475 3503393 := bstep (se 2 (by rfl) ⟨1313772, by rfl⟩ : syracuseStep 3503393 = 2627545) B2627545
theorem B23950727 : Blo 1555475 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B2626951 : Blo 1555475 2626951 := bstep (se 1 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 2626951 = 3940427) B3940427
theorem B1750459 : Blo 1555475 1750459 := bstep (se 1 (by rfl) ⟨1312844, by rfl⟩ : syracuseStep 1750459 = 2625689) B2625689
theorem B3937835 : Blo 1555475 3937835 := bstep (se 1 (by rfl) ⟨2953376, by rfl⟩ : syracuseStep 3937835 = 5906753) B5906753
theorem B7984727 : Blo 1555475 7984727 := bstep (se 1 (by rfl) ⟨5988545, by rfl⟩ : syracuseStep 7984727 = 11977091) B11977091
theorem B3503735 : Blo 1555475 3503735 := bstep (se 1 (by rfl) ⟨2627801, by rfl⟩ : syracuseStep 3503735 = 5255603) B5255603
theorem B3741385 : Blo 1555475 3741385 := bstep (se 2 (by rfl) ⟨1403019, by rfl⟩ : syracuseStep 3741385 = 2806039) B2806039
theorem B8410895 : Blo 1555475 8410895 := bstep (se 1 (by rfl) ⟨6308171, by rfl⟩ : syracuseStep 8410895 = 12616343) B12616343
theorem B3503915 : Blo 1555475 3503915 := bstep (se 1 (by rfl) ⟨2627936, by rfl⟩ : syracuseStep 3503915 = 5255873) B5255873
theorem B4732759 : Blo 1555475 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B1750927 : Blo 1555475 1750927 := bstep (se 1 (by rfl) ⟨1313195, by rfl⟩ : syracuseStep 1750927 = 2626391) B2626391
theorem B7878545 : Blo 1555475 7878545 := bstep (se 2 (by rfl) ⟨2954454, by rfl⟩ : syracuseStep 7878545 = 5908909) B5908909
theorem B6313913 : Blo 1555475 6313913 := bstep (se 2 (by rfl) ⟨2367717, by rfl⟩ : syracuseStep 6313913 = 4735435) B4735435
theorem B5609425 : Blo 1555475 5609425 := bstep (se 2 (by rfl) ⟨2103534, by rfl⟩ : syracuseStep 5609425 = 4207069) B4207069
theorem B2627599 : Blo 1555475 2627599 := bstep (se 1 (by rfl) ⟨1970699, by rfl⟩ : syracuseStep 2627599 = 3941399) B3941399
theorem B4429883 : Blo 1555475 4429883 := bstep (se 1 (by rfl) ⟨3322412, by rfl⟩ : syracuseStep 4429883 = 6644825) B6644825
theorem B8411197 : Blo 1555475 8411197 := bstep (se 3 (by rfl) ⟨1577099, by rfl⟩ : syracuseStep 8411197 = 3154199) B3154199
theorem B3504275 : Blo 1555475 3504275 := bstep (se 1 (by rfl) ⟨2628206, by rfl⟩ : syracuseStep 3504275 = 5256413) B5256413
theorem B5191969 : Blo 1555475 5191969 := bstep (se 2 (by rfl) ⟨1946988, by rfl⟩ : syracuseStep 5191969 = 3893977) B3893977
theorem B6314273 : Blo 1555475 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B4430123 : Blo 1555475 4430123 := bstep (se 1 (by rfl) ⟨3322592, by rfl⟩ : syracuseStep 4430123 = 6645185) B6645185
theorem B4733245 : Blo 1555475 4733245 := bstep (se 3 (by rfl) ⟨887483, by rfl⟩ : syracuseStep 4733245 = 1774967) B1774967
theorem B95885633 : Blo 1555475 95885633 := bstep (se 2 (by rfl) ⟨35957112, by rfl⟩ : syracuseStep 95885633 = 71914225) B71914225
theorem B8419673 : Blo 1555475 8419673 := bstep (se 2 (by rfl) ⟨3157377, by rfl⟩ : syracuseStep 8419673 = 6314755) B6314755
theorem B4987271 : Blo 1555475 4987271 := bstep (se 1 (by rfl) ⟨3740453, by rfl⟩ : syracuseStep 4987271 = 7480907) B7480907
theorem B1751431 : Blo 1555475 1751431 := bstep (se 1 (by rfl) ⟨1313573, by rfl⟩ : syracuseStep 1751431 = 2627147) B2627147
theorem B11213315 : Blo 1555475 11213315 := bstep (se 1 (by rfl) ⟨8409986, by rfl⟩ : syracuseStep 11213315 = 16819973) B16819973
theorem B3938827 : Blo 1555475 3938827 := bstep (se 1 (by rfl) ⟨2954120, by rfl⟩ : syracuseStep 3938827 = 5908241) B5908241
theorem B2955791 : Blo 1555475 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B10246699 : Blo 1555475 10246699 := bstep (se 1 (by rfl) ⟨7685024, by rfl⟩ : syracuseStep 10246699 = 15370049) B15370049
theorem B2628139 : Blo 1555475 2628139 := bstep (se 1 (by rfl) ⟨1971104, by rfl⟩ : syracuseStep 2628139 = 3942209) B3942209
theorem B2333243 : Blo 1555475 2333243 := bstep (se 1 (by rfl) ⟨1749932, by rfl⟩ : syracuseStep 2333243 = 3499865) B3499865
theorem B1751611 : Blo 1555475 1751611 := bstep (se 1 (by rfl) ⟨1313708, by rfl⟩ : syracuseStep 1751611 = 2627417) B2627417
theorem B56801857 : Blo 1555475 56801857 := bstep (se 2 (by rfl) ⟨21300696, by rfl⟩ : syracuseStep 56801857 = 42601393) B42601393
theorem B2333303 : Blo 1555475 2333303 := bstep (se 1 (by rfl) ⟨1749977, by rfl⟩ : syracuseStep 2333303 = 3499955) B3499955
theorem B2333327 : Blo 1555475 2333327 := bstep (se 1 (by rfl) ⟨1749995, by rfl⟩ : syracuseStep 2333327 = 3499991) B3499991
theorem B3938969 : Blo 1555475 3938969 := bstep (se 2 (by rfl) ⟨1477113, by rfl⟩ : syracuseStep 3938969 = 2954227) B2954227
theorem B2333369 : Blo 1555475 2333369 := bstep (se 2 (by rfl) ⟨875013, by rfl⟩ : syracuseStep 2333369 = 1750027) B1750027
theorem B95836877 : Blo 1555475 95836877 := bstep (se 3 (by rfl) ⟨17969414, by rfl⟩ : syracuseStep 95836877 = 35938829) B35938829
theorem B5610221 : Blo 1555475 5610221 := bstep (se 3 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 5610221 = 2103833) B2103833
theorem B14965505 : Blo 1555475 14965505 := bstep (se 2 (by rfl) ⟨5612064, by rfl⟩ : syracuseStep 14965505 = 11224129) B11224129
theorem B2333447 : Blo 1555475 2333447 := bstep (se 1 (by rfl) ⟨1750085, by rfl⟩ : syracuseStep 2333447 = 3500171) B3500171
theorem B5249825 : Blo 1555475 5249825 := bstep (se 2 (by rfl) ⟨1968684, by rfl⟩ : syracuseStep 5249825 = 3937369) B3937369
theorem B2333483 : Blo 1555475 2333483 := bstep (se 1 (by rfl) ⟨1750112, by rfl⟩ : syracuseStep 2333483 = 3500225) B3500225
theorem B3939131 : Blo 1555475 3939131 := bstep (se 1 (by rfl) ⟨2954348, by rfl⟩ : syracuseStep 3939131 = 5908697) B5908697
theorem B2333513 : Blo 1555475 2333513 := bstep (se 2 (by rfl) ⟨875067, by rfl⟩ : syracuseStep 2333513 = 1750135) B1750135
theorem B2333627 : Blo 1555475 2333627 := bstep (se 1 (by rfl) ⟨1750220, by rfl⟩ : syracuseStep 2333627 = 3500441) B3500441
theorem B2333687 : Blo 1555475 2333687 := bstep (se 1 (by rfl) ⟨1750265, by rfl⟩ : syracuseStep 2333687 = 3500531) B3500531
theorem B2333711 : Blo 1555475 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B1752079 : Blo 1555475 1752079 := bstep (se 1 (by rfl) ⟨1314059, by rfl⟩ : syracuseStep 1752079 = 2628119) B2628119
theorem B2956331 : Blo 1555475 2956331 := bstep (se 1 (by rfl) ⟨2217248, by rfl⟩ : syracuseStep 2956331 = 4434497) B4434497
theorem B2333753 : Blo 1555475 2333753 := bstep (se 2 (by rfl) ⟨875157, by rfl⟩ : syracuseStep 2333753 = 1750315) B1750315
theorem B1555515 : Blo 1555475 1555515 := bstep (se 1 (by rfl) ⟨1166636, by rfl⟩ : syracuseStep 1555515 = 2333273) B2333273
theorem B14965847 : Blo 1555475 14965847 := bstep (se 1 (by rfl) ⟨11224385, by rfl⟩ : syracuseStep 14965847 = 22448771) B22448771
theorem B1555591 : Blo 1555475 1555591 := bstep (se 1 (by rfl) ⟨1166693, by rfl⟩ : syracuseStep 1555591 = 2333387) B2333387
theorem B2333831 : Blo 1555475 2333831 := bstep (se 1 (by rfl) ⟨1750373, by rfl⟩ : syracuseStep 2333831 = 3500747) B3500747
theorem B1555599 : Blo 1555475 1555599 := bstep (se 1 (by rfl) ⟨1166699, by rfl⟩ : syracuseStep 1555599 = 2333399) B2333399
theorem B3939475 : Blo 1555475 3939475 := bstep (se 1 (by rfl) ⟨2954606, by rfl⟩ : syracuseStep 3939475 = 5909213) B5909213
theorem B2333867 : Blo 1555475 2333867 := bstep (se 1 (by rfl) ⟨1750400, by rfl⟩ : syracuseStep 2333867 = 3500801) B3500801
theorem B1555643 : Blo 1555475 1555643 := bstep (se 1 (by rfl) ⟨1166732, by rfl⟩ : syracuseStep 1555643 = 2333465) B2333465
theorem B2333897 : Blo 1555475 2333897 := bstep (se 2 (by rfl) ⟨875211, by rfl⟩ : syracuseStep 2333897 = 1750423) B1750423
theorem B1555719 : Blo 1555475 1555719 := bstep (se 1 (by rfl) ⟨1166789, by rfl⟩ : syracuseStep 1555719 = 2333579) B2333579
theorem B1555727 : Blo 1555475 1555727 := bstep (se 1 (by rfl) ⟨1166795, by rfl⟩ : syracuseStep 1555727 = 2333591) B2333591
theorem B3939617 : Blo 1555475 3939617 := bstep (se 2 (by rfl) ⟨1477356, by rfl⟩ : syracuseStep 3939617 = 2954713) B2954713
theorem B1555771 : Blo 1555475 1555771 := bstep (se 1 (by rfl) ⟨1166828, by rfl⟩ : syracuseStep 1555771 = 2333657) B2333657
theorem B2334011 : Blo 1555475 2334011 := bstep (se 1 (by rfl) ⟨1750508, by rfl⟩ : syracuseStep 2334011 = 3501017) B3501017
theorem B8863091 : Blo 1555475 8863091 := bstep (se 1 (by rfl) ⟨6647318, by rfl⟩ : syracuseStep 8863091 = 13294637) B13294637
theorem B5250419 : Blo 1555475 5250419 := bstep (se 1 (by rfl) ⟨3937814, by rfl⟩ : syracuseStep 5250419 = 7875629) B7875629
theorem B2334071 : Blo 1555475 2334071 := bstep (se 1 (by rfl) ⟨1750553, by rfl⟩ : syracuseStep 2334071 = 3501107) B3501107
theorem B1555847 : Blo 1555475 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1555855 : Blo 1555475 1555855 := bstep (se 1 (by rfl) ⟨1166891, by rfl⟩ : syracuseStep 1555855 = 2333783) B2333783
theorem B2334095 : Blo 1555475 2334095 := bstep (se 1 (by rfl) ⟨1750571, by rfl⟩ : syracuseStep 2334095 = 3501143) B3501143
theorem B2334137 : Blo 1555475 2334137 := bstep (se 2 (by rfl) ⟨875301, by rfl⟩ : syracuseStep 2334137 = 1750603) B1750603
theorem B1555899 : Blo 1555475 1555899 := bstep (se 1 (by rfl) ⟨1166924, by rfl⟩ : syracuseStep 1555899 = 2333849) B2333849
theorem B21306833 : Blo 1555475 21306833 := bstep (se 2 (by rfl) ⟨7990062, by rfl⟩ : syracuseStep 21306833 = 15980125) B15980125
theorem B2334215 : Blo 1555475 2334215 := bstep (se 1 (by rfl) ⟨1750661, by rfl⟩ : syracuseStep 2334215 = 3501323) B3501323
theorem B1555975 : Blo 1555475 1555975 := bstep (se 1 (by rfl) ⟨1166981, by rfl⟩ : syracuseStep 1555975 = 2333963) B2333963
theorem B1555983 : Blo 1555475 1555983 := bstep (se 1 (by rfl) ⟨1166987, by rfl⟩ : syracuseStep 1555983 = 2333975) B2333975
theorem B2334251 : Blo 1555475 2334251 := bstep (se 1 (by rfl) ⟨1750688, by rfl⟩ : syracuseStep 2334251 = 3501377) B3501377
theorem B1556027 : Blo 1555475 1556027 := bstep (se 1 (by rfl) ⟨1167020, by rfl⟩ : syracuseStep 1556027 = 2334041) B2334041
theorem B2334281 : Blo 1555475 2334281 := bstep (se 2 (by rfl) ⟨875355, by rfl⟩ : syracuseStep 2334281 = 1750711) B1750711
theorem B1556103 : Blo 1555475 1556103 := bstep (se 1 (by rfl) ⟨1167077, by rfl⟩ : syracuseStep 1556103 = 2334155) B2334155
theorem B1556111 : Blo 1555475 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1556155 : Blo 1555475 1556155 := bstep (se 1 (by rfl) ⟨1167116, by rfl⟩ : syracuseStep 1556155 = 2334233) B2334233
theorem B2334395 : Blo 1555475 2334395 := bstep (se 1 (by rfl) ⟨1750796, by rfl⟩ : syracuseStep 2334395 = 3501593) B3501593
theorem B2334455 : Blo 1555475 2334455 := bstep (se 1 (by rfl) ⟨1750841, by rfl⟩ : syracuseStep 2334455 = 3501683) B3501683
theorem B1556231 : Blo 1555475 1556231 := bstep (se 1 (by rfl) ⟨1167173, by rfl⟩ : syracuseStep 1556231 = 2334347) B2334347
theorem B1556239 : Blo 1555475 1556239 := bstep (se 1 (by rfl) ⟨1167179, by rfl⟩ : syracuseStep 1556239 = 2334359) B2334359
theorem B2334479 : Blo 1555475 2334479 := bstep (se 1 (by rfl) ⟨1750859, by rfl⟩ : syracuseStep 2334479 = 3501719) B3501719
theorem B2334521 : Blo 1555475 2334521 := bstep (se 2 (by rfl) ⟨875445, by rfl⟩ : syracuseStep 2334521 = 1750891) B1750891
theorem B1556283 : Blo 1555475 1556283 := bstep (se 1 (by rfl) ⟨1167212, by rfl⟩ : syracuseStep 1556283 = 2334425) B2334425
theorem B1556359 : Blo 1555475 1556359 := bstep (se 1 (by rfl) ⟨1167269, by rfl⟩ : syracuseStep 1556359 = 2334539) B2334539
theorem B2334599 : Blo 1555475 2334599 := bstep (se 1 (by rfl) ⟨1750949, by rfl⟩ : syracuseStep 2334599 = 3501899) B3501899
theorem B1556367 : Blo 1555475 1556367 := bstep (se 1 (by rfl) ⟨1167275, by rfl⟩ : syracuseStep 1556367 = 2334551) B2334551
theorem B2334635 : Blo 1555475 2334635 := bstep (se 1 (by rfl) ⟨1750976, by rfl⟩ : syracuseStep 2334635 = 3501953) B3501953
theorem B1556411 : Blo 1555475 1556411 := bstep (se 1 (by rfl) ⟨1167308, by rfl⟩ : syracuseStep 1556411 = 2334617) B2334617
theorem B2334665 : Blo 1555475 2334665 := bstep (se 2 (by rfl) ⟨875499, by rfl⟩ : syracuseStep 2334665 = 1750999) B1750999
theorem B7880651 : Blo 1555475 7880651 := bstep (se 1 (by rfl) ⟨5910488, by rfl⟩ : syracuseStep 7880651 = 11820977) B11820977
theorem B14385181 : Blo 1555475 14385181 := bstep (se 3 (by rfl) ⟨2697221, by rfl⟩ : syracuseStep 14385181 = 5394443) B5394443
theorem B1556519 : Blo 1555475 1556519 := bstep (se 1 (by rfl) ⟨1167389, by rfl⟩ : syracuseStep 1556519 = 2334779) B2334779
theorem B1556559 : Blo 1555475 1556559 := bstep (se 1 (by rfl) ⟨1167419, by rfl⟩ : syracuseStep 1556559 = 2334839) B2334839
theorem B11214929 : Blo 1555475 11214929 := bstep (se 2 (by rfl) ⟨4205598, by rfl⟩ : syracuseStep 11214929 = 8411197) B8411197
theorem B1556575 : Blo 1555475 1556575 := bstep (se 1 (by rfl) ⟨1167431, by rfl⟩ : syracuseStep 1556575 = 2334863) B2334863
theorem B1556603 : Blo 1555475 1556603 := bstep (se 1 (by rfl) ⟨1167452, by rfl⟩ : syracuseStep 1556603 = 2334905) B2334905
theorem B5251229 : Blo 1555475 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B1556655 : Blo 1555475 1556655 := bstep (se 1 (by rfl) ⟨1167491, by rfl⟩ : syracuseStep 1556655 = 2334983) B2334983
theorem B1556679 : Blo 1555475 1556679 := bstep (se 1 (by rfl) ⟨1167509, by rfl⟩ : syracuseStep 1556679 = 2335019) B2335019
theorem B1556699 : Blo 1555475 1556699 := bstep (se 1 (by rfl) ⟨1167524, by rfl⟩ : syracuseStep 1556699 = 2335049) B2335049
theorem B1556775 : Blo 1555475 1556775 := bstep (se 1 (by rfl) ⟨1167581, by rfl⟩ : syracuseStep 1556775 = 2335163) B2335163
theorem B1556815 : Blo 1555475 1556815 := bstep (se 1 (by rfl) ⟨1167611, by rfl⟩ : syracuseStep 1556815 = 2335223) B2335223
theorem B1556831 : Blo 1555475 1556831 := bstep (se 1 (by rfl) ⟨1167623, by rfl⟩ : syracuseStep 1556831 = 2335247) B2335247
theorem B1556859 : Blo 1555475 1556859 := bstep (se 1 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 1556859 = 2335289) B2335289
theorem B6922625 : Blo 1555475 6922625 := bstep (se 2 (by rfl) ⟨2595984, by rfl⟩ : syracuseStep 6922625 = 5191969) B5191969
theorem B3940751 : Blo 1555475 3940751 := bstep (se 1 (by rfl) ⟨2955563, by rfl⟩ : syracuseStep 3940751 = 5911127) B5911127
theorem B2335151 : Blo 1555475 2335151 := bstep (se 1 (by rfl) ⟨1751363, by rfl⟩ : syracuseStep 2335151 = 3502727) B3502727
theorem B1556911 : Blo 1555475 1556911 := bstep (se 1 (by rfl) ⟨1167683, by rfl⟩ : syracuseStep 1556911 = 2335367) B2335367
theorem B1556935 : Blo 1555475 1556935 := bstep (se 1 (by rfl) ⟨1167701, by rfl⟩ : syracuseStep 1556935 = 2335403) B2335403
theorem B1556955 : Blo 1555475 1556955 := bstep (se 1 (by rfl) ⟨1167716, by rfl⟩ : syracuseStep 1556955 = 2335433) B2335433
theorem B2335241 : Blo 1555475 2335241 := bstep (se 2 (by rfl) ⟨875715, by rfl⟩ : syracuseStep 2335241 = 1751431) B1751431
theorem B2335271 : Blo 1555475 2335271 := bstep (se 1 (by rfl) ⟨1751453, by rfl⟩ : syracuseStep 2335271 = 3502907) B3502907
theorem B1557031 : Blo 1555475 1557031 := bstep (se 1 (by rfl) ⟨1167773, by rfl⟩ : syracuseStep 1557031 = 2335547) B2335547
theorem B1557071 : Blo 1555475 1557071 := bstep (se 1 (by rfl) ⟨1167803, by rfl⟩ : syracuseStep 1557071 = 2335607) B2335607
theorem B1557087 : Blo 1555475 1557087 := bstep (se 1 (by rfl) ⟨1167815, by rfl⟩ : syracuseStep 1557087 = 2335631) B2335631
theorem B2335355 : Blo 1555475 2335355 := bstep (se 1 (by rfl) ⟨1751516, by rfl⟩ : syracuseStep 2335355 = 3503033) B3503033
theorem B1557115 : Blo 1555475 1557115 := bstep (se 1 (by rfl) ⟨1167836, by rfl⟩ : syracuseStep 1557115 = 2335673) B2335673
theorem B1557167 : Blo 1555475 1557167 := bstep (se 1 (by rfl) ⟨1167875, by rfl⟩ : syracuseStep 1557167 = 2335751) B2335751
theorem B5251769 : Blo 1555475 5251769 := bstep (se 2 (by rfl) ⟨1969413, by rfl⟩ : syracuseStep 5251769 = 3938827) B3938827
theorem B4432583 : Blo 1555475 4432583 := bstep (se 1 (by rfl) ⟨3324437, by rfl⟩ : syracuseStep 4432583 = 6648875) B6648875
theorem B1557191 : Blo 1555475 1557191 := bstep (se 1 (by rfl) ⟨1167893, by rfl⟩ : syracuseStep 1557191 = 2335787) B2335787
theorem B3941075 : Blo 1555475 3941075 := bstep (se 1 (by rfl) ⟨2955806, by rfl⟩ : syracuseStep 3941075 = 5911613) B5911613
theorem B1557211 : Blo 1555475 1557211 := bstep (se 1 (by rfl) ⟨1167908, by rfl⟩ : syracuseStep 1557211 = 2335817) B2335817
theorem B2335481 : Blo 1555475 2335481 := bstep (se 2 (by rfl) ⟨875805, by rfl⟩ : syracuseStep 2335481 = 1751611) B1751611
theorem B75735809 : Blo 1555475 75735809 := bstep (se 2 (by rfl) ⟨28400928, by rfl⟩ : syracuseStep 75735809 = 56801857) B56801857
theorem B39904001 : Blo 1555475 39904001 := bstep (se 2 (by rfl) ⟨14964000, by rfl⟩ : syracuseStep 39904001 = 29928001) B29928001
theorem B1557287 : Blo 1555475 1557287 := bstep (se 1 (by rfl) ⟨1167965, by rfl⟩ : syracuseStep 1557287 = 2335931) B2335931
theorem B8643401 : Blo 1555475 8643401 := bstep (se 2 (by rfl) ⟨3241275, by rfl⟩ : syracuseStep 8643401 = 6482551) B6482551
theorem B1557327 : Blo 1555475 1557327 := bstep (se 1 (by rfl) ⟨1167995, by rfl⟩ : syracuseStep 1557327 = 2335991) B2335991
theorem B3154783 : Blo 1555475 3154783 := bstep (se 1 (by rfl) ⟨2366087, by rfl⟩ : syracuseStep 3154783 = 4732175) B4732175
theorem B2335583 : Blo 1555475 2335583 := bstep (se 1 (by rfl) ⟨1751687, by rfl⟩ : syracuseStep 2335583 = 3503375) B3503375
theorem B1557343 : Blo 1555475 1557343 := bstep (se 1 (by rfl) ⟨1168007, by rfl⟩ : syracuseStep 1557343 = 2336015) B2336015
theorem B2335595 : Blo 1555475 2335595 := bstep (se 1 (by rfl) ⟨1751696, by rfl⟩ : syracuseStep 2335595 = 3503393) B3503393
theorem B1557371 : Blo 1555475 1557371 := bstep (se 1 (by rfl) ⟨1168028, by rfl⟩ : syracuseStep 1557371 = 2336057) B2336057
theorem B15967151 : Blo 1555475 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B1557423 : Blo 1555475 1557423 := bstep (se 1 (by rfl) ⟨1168067, by rfl⟩ : syracuseStep 1557423 = 2336135) B2336135
theorem B10109879 : Blo 1555475 10109879 := bstep (se 1 (by rfl) ⟨7582409, by rfl⟩ : syracuseStep 10109879 = 15164819) B15164819
theorem B1557447 : Blo 1555475 1557447 := bstep (se 1 (by rfl) ⟨1168085, by rfl⟩ : syracuseStep 1557447 = 2336171) B2336171
theorem B1557467 : Blo 1555475 1557467 := bstep (se 1 (by rfl) ⟨1168100, by rfl⟩ : syracuseStep 1557467 = 2336201) B2336201
theorem B2335823 : Blo 1555475 2335823 := bstep (se 1 (by rfl) ⟨1751867, by rfl⟩ : syracuseStep 2335823 = 3503735) B3503735
theorem B2335943 : Blo 1555475 2335943 := bstep (se 1 (by rfl) ⟨1751957, by rfl⟩ : syracuseStep 2335943 = 3503915) B3503915
theorem B5252363 : Blo 1555475 5252363 := bstep (se 1 (by rfl) ⟨3939272, by rfl⟩ : syracuseStep 5252363 = 7878545) B7878545
theorem B1869151 : Blo 1555475 1869151 := bstep (se 1 (by rfl) ⟨1401863, by rfl⟩ : syracuseStep 1869151 = 2803727) B2803727
theorem B2336105 : Blo 1555475 2336105 := bstep (se 2 (by rfl) ⟨876039, by rfl⟩ : syracuseStep 2336105 = 1752079) B1752079
theorem B7882109 : Blo 1555475 7882109 := bstep (se 3 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 7882109 = 2955791) B2955791
theorem B2336183 : Blo 1555475 2336183 := bstep (se 1 (by rfl) ⟨1752137, by rfl⟩ : syracuseStep 2336183 = 3504275) B3504275
theorem B5252633 : Blo 1555475 5252633 := bstep (se 2 (by rfl) ⟨1969737, by rfl⟩ : syracuseStep 5252633 = 3939475) B3939475
theorem B63923755 : Blo 1555475 63923755 := bstep (se 1 (by rfl) ⟨47942816, by rfl⟩ : syracuseStep 63923755 = 95885633) B95885633
theorem B63891251 : Blo 1555475 63891251 := bstep (se 1 (by rfl) ⟨47918438, by rfl⟩ : syracuseStep 63891251 = 95836877) B95836877
theorem B3499883 : Blo 1555475 3499883 := bstep (se 1 (by rfl) ⟨2624912, by rfl⟩ : syracuseStep 3499883 = 5249825) B5249825
theorem B3499937 : Blo 1555475 3499937 := bstep (se 2 (by rfl) ⟨1312476, by rfl⟩ : syracuseStep 3499937 = 2624953) B2624953
theorem B2803675 : Blo 1555475 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B3500279 : Blo 1555475 3500279 := bstep (se 1 (by rfl) ⟨2625209, by rfl⟩ : syracuseStep 3500279 = 5250419) B5250419
theorem B5908727 : Blo 1555475 5908727 := bstep (se 1 (by rfl) ⟨4431545, by rfl⟩ : syracuseStep 5908727 = 8863091) B8863091
theorem B13298053 : Blo 1555475 13298053 := bstep (se 4 (by rfl) ⟨1246692, by rfl⟩ : syracuseStep 13298053 = 2493385) B2493385
theorem B6310345 : Blo 1555475 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B14191051 : Blo 1555475 14191051 := bstep (se 1 (by rfl) ⟨10643288, by rfl⟩ : syracuseStep 14191051 = 21286577) B21286577
theorem B5253767 : Blo 1555475 5253767 := bstep (se 1 (by rfl) ⟨3940325, by rfl⟩ : syracuseStep 5253767 = 7880651) B7880651
theorem B5253821 : Blo 1555475 5253821 := bstep (se 3 (by rfl) ⟨985091, by rfl⟩ : syracuseStep 5253821 = 1970183) B1970183
theorem B3992279 : Blo 1555475 3992279 := bstep (se 1 (by rfl) ⟨2994209, by rfl⟩ : syracuseStep 3992279 = 5988419) B5988419
theorem B2493175 : Blo 1555475 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B4983581 : Blo 1555475 4983581 := bstep (se 3 (by rfl) ⟨934421, by rfl⟩ : syracuseStep 4983581 = 1868843) B1868843
theorem B3500873 : Blo 1555475 3500873 := bstep (se 2 (by rfl) ⟨1312827, by rfl⟩ : syracuseStep 3500873 = 2625655) B2625655
theorem B5253983 : Blo 1555475 5253983 := bstep (se 1 (by rfl) ⟨3940487, by rfl⟩ : syracuseStep 5253983 = 7880975) B7880975
theorem B5254145 : Blo 1555475 5254145 := bstep (se 2 (by rfl) ⟨1970304, by rfl⟩ : syracuseStep 5254145 = 3940609) B3940609
theorem B5909699 : Blo 1555475 5909699 := bstep (se 1 (by rfl) ⟨4432274, by rfl⟩ : syracuseStep 5909699 = 8864549) B8864549
theorem B4984055 : Blo 1555475 4984055 := bstep (se 1 (by rfl) ⟨3738041, by rfl⟩ : syracuseStep 4984055 = 7476083) B7476083
theorem B6311159 : Blo 1555475 6311159 := bstep (se 1 (by rfl) ⟨4733369, by rfl⟩ : syracuseStep 6311159 = 9466739) B9466739
theorem B6647183 : Blo 1555475 6647183 := bstep (se 1 (by rfl) ⟨4985387, by rfl⟩ : syracuseStep 6647183 = 9970775) B9970775
theorem B7982509 : Blo 1555475 7982509 := bstep (se 3 (by rfl) ⟨1496720, by rfl⟩ : syracuseStep 7982509 = 2993441) B2993441
theorem B1969591 : Blo 1555475 1969591 := bstep (se 1 (by rfl) ⟨1477193, by rfl⟩ : syracuseStep 1969591 = 2954387) B2954387
theorem B2624987 : Blo 1555475 2624987 := bstep (se 1 (by rfl) ⟨1968740, by rfl⟩ : syracuseStep 2624987 = 3937481) B3937481
theorem B3501665 : Blo 1555475 3501665 := bstep (se 2 (by rfl) ⟨1313124, by rfl⟩ : syracuseStep 3501665 = 2626249) B2626249
theorem B5910155 : Blo 1555475 5910155 := bstep (se 1 (by rfl) ⟨4432616, by rfl⟩ : syracuseStep 5910155 = 8865233) B8865233
theorem B13299389 : Blo 1555475 13299389 := bstep (se 3 (by rfl) ⟨2493635, by rfl⟩ : syracuseStep 13299389 = 4987271) B4987271
theorem B2625223 : Blo 1555475 2625223 := bstep (se 1 (by rfl) ⟨1968917, by rfl⟩ : syracuseStep 2625223 = 3937835) B3937835
theorem B17739485 : Blo 1555475 17739485 := bstep (se 3 (by rfl) ⟨3326153, by rfl⟩ : syracuseStep 17739485 = 6652307) B6652307
theorem B5254955 : Blo 1555475 5254955 := bstep (se 1 (by rfl) ⟨3941216, by rfl⟩ : syracuseStep 5254955 = 7882433) B7882433
theorem B5607263 : Blo 1555475 5607263 := bstep (se 1 (by rfl) ⟨4205447, by rfl⟩ : syracuseStep 5607263 = 8410895) B8410895
theorem B5910367 : Blo 1555475 5910367 := bstep (se 1 (by rfl) ⟨4432775, by rfl⟩ : syracuseStep 5910367 = 8865551) B8865551
theorem B2625385 : Blo 1555475 2625385 := bstep (se 2 (by rfl) ⟨984519, by rfl⟩ : syracuseStep 2625385 = 1969039) B1969039
theorem B3502007 : Blo 1555475 3502007 := bstep (se 1 (by rfl) ⟨2626505, by rfl⟩ : syracuseStep 3502007 = 5253011) B5253011
theorem B4730899 : Blo 1555475 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B2953255 : Blo 1555475 2953255 := bstep (se 1 (by rfl) ⟨2214941, by rfl⟩ : syracuseStep 2953255 = 4429883) B4429883
theorem B5255225 : Blo 1555475 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B19935395 : Blo 1555475 19935395 := bstep (se 1 (by rfl) ⟨14951546, by rfl⟩ : syracuseStep 19935395 = 29903093) B29903093
theorem B2953415 : Blo 1555475 2953415 := bstep (se 1 (by rfl) ⟨2215061, by rfl⟩ : syracuseStep 2953415 = 4430123) B4430123
theorem B7876925 : Blo 1555475 7876925 := bstep (se 3 (by rfl) ⟨1476923, by rfl⟩ : syracuseStep 7876925 = 2953847) B2953847
theorem B25243973 : Blo 1555475 25243973 := bstep (se 4 (by rfl) ⟨2366622, by rfl⟩ : syracuseStep 25243973 = 4733245) B4733245
theorem B7475543 : Blo 1555475 7475543 := bstep (se 1 (by rfl) ⟨5606657, by rfl⟩ : syracuseStep 7475543 = 11213315) B11213315
theorem B5255549 : Blo 1555475 5255549 := bstep (se 3 (by rfl) ⟨985415, by rfl⟩ : syracuseStep 5255549 = 1970831) B1970831
theorem B2625979 : Blo 1555475 2625979 := bstep (se 1 (by rfl) ⟨1969484, by rfl⟩ : syracuseStep 2625979 = 3938969) B3938969
theorem B3371483 : Blo 1555475 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B3740147 : Blo 1555475 3740147 := bstep (se 1 (by rfl) ⟨2805110, by rfl⟩ : syracuseStep 3740147 = 5610221) B5610221
theorem B3502601 : Blo 1555475 3502601 := bstep (se 2 (by rfl) ⟨1313475, by rfl⟩ : syracuseStep 3502601 = 2626951) B2626951
theorem B2626087 : Blo 1555475 2626087 := bstep (se 1 (by rfl) ⟨1969565, by rfl⟩ : syracuseStep 2626087 = 3939131) B3939131
theorem B5255819 : Blo 1555475 5255819 := bstep (se 1 (by rfl) ⟨3941864, by rfl⟩ : syracuseStep 5255819 = 7883729) B7883729
theorem B11825837 : Blo 1555475 11825837 := bstep (se 3 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 11825837 = 4434689) B4434689
theorem B1970887 : Blo 1555475 1970887 := bstep (se 1 (by rfl) ⟨1478165, by rfl⟩ : syracuseStep 1970887 = 2956331) B2956331
theorem B4207319 : Blo 1555475 4207319 := bstep (se 1 (by rfl) ⟨3155489, by rfl⟩ : syracuseStep 4207319 = 6310979) B6310979
theorem B10646275 : Blo 1555475 10646275 := bstep (se 1 (by rfl) ⟨7984706, by rfl⟩ : syracuseStep 10646275 = 15969413) B15969413
theorem B9966365 : Blo 1555475 9966365 := bstep (se 3 (by rfl) ⟨1868693, by rfl⟩ : syracuseStep 9966365 = 3737387) B3737387
theorem B5911325 : Blo 1555475 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B5911339 : Blo 1555475 5911339 := bstep (se 1 (by rfl) ⟨4433504, by rfl⟩ : syracuseStep 5911339 = 8867009) B8867009
theorem B3502943 : Blo 1555475 3502943 := bstep (se 1 (by rfl) ⟨2627207, by rfl⟩ : syracuseStep 3502943 = 5254415) B5254415
theorem B2626411 : Blo 1555475 2626411 := bstep (se 1 (by rfl) ⟨1969808, by rfl⟩ : syracuseStep 2626411 = 3939617) B3939617
theorem B5124983 : Blo 1555475 5124983 := bstep (se 1 (by rfl) ⟨3843737, by rfl⟩ : syracuseStep 5124983 = 7687475) B7687475
theorem B3503123 : Blo 1555475 3503123 := bstep (se 1 (by rfl) ⟨2627342, by rfl⟩ : syracuseStep 3503123 = 5254685) B5254685
theorem B13300787 : Blo 1555475 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B2954569 : Blo 1555475 2954569 := bstep (se 2 (by rfl) ⟨1107963, by rfl⟩ : syracuseStep 2954569 = 2215927) B2215927
theorem B3503465 : Blo 1555475 3503465 := bstep (se 2 (by rfl) ⟨1313799, by rfl⟩ : syracuseStep 3503465 = 2627599) B2627599
theorem B7583149 : Blo 1555475 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B22435339 : Blo 1555475 22435339 := bstep (se 1 (by rfl) ⟨16826504, by rfl⟩ : syracuseStep 22435339 = 33653009) B33653009
theorem B14194187 : Blo 1555475 14194187 := bstep (se 1 (by rfl) ⟨10645640, by rfl⟩ : syracuseStep 14194187 = 21291281) B21291281
theorem B1750567 : Blo 1555475 1750567 := bstep (se 1 (by rfl) ⟨1312925, by rfl⟩ : syracuseStep 1750567 = 2625851) B2625851
theorem B3741223 : Blo 1555475 3741223 := bstep (se 1 (by rfl) ⟨2805917, by rfl⟩ : syracuseStep 3741223 = 5611835) B5611835
theorem B4986515 : Blo 1555475 4986515 := bstep (se 1 (by rfl) ⟨3739886, by rfl⟩ : syracuseStep 4986515 = 7479773) B7479773
theorem B6649559 : Blo 1555475 6649559 := bstep (se 1 (by rfl) ⟨4987169, by rfl⟩ : syracuseStep 6649559 = 9974339) B9974339
theorem B8419139 : Blo 1555475 8419139 := bstep (se 1 (by rfl) ⟨6314354, by rfl⟩ : syracuseStep 8419139 = 12628709) B12628709
theorem B2627471 : Blo 1555475 2627471 := bstep (se 1 (by rfl) ⟨1970603, by rfl⟩ : syracuseStep 2627471 = 3941207) B3941207
theorem B3504059 : Blo 1555475 3504059 := bstep (se 1 (by rfl) ⟨2628044, by rfl⟩ : syracuseStep 3504059 = 5256089) B5256089
theorem B8861633 : Blo 1555475 8861633 := bstep (se 2 (by rfl) ⟨3323112, by rfl⟩ : syracuseStep 8861633 = 6646225) B6646225
theorem B11220929 : Blo 1555475 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B16832519 : Blo 1555475 16832519 := bstep (se 1 (by rfl) ⟨12624389, by rfl⟩ : syracuseStep 16832519 = 25248779) B25248779
theorem B8869925 : Blo 1555475 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B13662265 : Blo 1555475 13662265 := bstep (se 2 (by rfl) ⟨5123349, by rfl⟩ : syracuseStep 13662265 = 10246699) B10246699
theorem B3504185 : Blo 1555475 3504185 := bstep (se 2 (by rfl) ⟨1314069, by rfl⟩ : syracuseStep 3504185 = 2628139) B2628139
theorem B2627707 : Blo 1555475 2627707 := bstep (se 1 (by rfl) ⟨1970780, by rfl⟩ : syracuseStep 2627707 = 3941561) B3941561
theorem B22452461 : Blo 1555475 22452461 := bstep (se 3 (by rfl) ⟨4209836, by rfl⟩ : syracuseStep 22452461 = 8419673) B8419673
theorem B3938665 : Blo 1555475 3938665 := bstep (se 2 (by rfl) ⟨1476999, by rfl⟩ : syracuseStep 3938665 = 2953999) B2953999
theorem B26589545 : Blo 1555475 26589545 := bstep (se 2 (by rfl) ⟨9971079, by rfl⟩ : syracuseStep 26589545 = 19942159) B19942159
theorem B5323151 : Blo 1555475 5323151 := bstep (se 1 (by rfl) ⟨3992363, by rfl⟩ : syracuseStep 5323151 = 7984727) B7984727
theorem B7879193 : Blo 1555475 7879193 := bstep (se 2 (by rfl) ⟨2954697, by rfl⟩ : syracuseStep 7879193 = 5909395) B5909395
theorem B34134605 : Blo 1555475 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B3938939 : Blo 1555475 3938939 := bstep (se 1 (by rfl) ⟨2954204, by rfl⟩ : syracuseStep 3938939 = 5908409) B5908409
theorem B4209275 : Blo 1555475 4209275 := bstep (se 1 (by rfl) ⟨3156956, by rfl⟩ : syracuseStep 4209275 = 6313913) B6313913
theorem B4209515 : Blo 1555475 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B2333615 : Blo 1555475 2333615 := bstep (se 1 (by rfl) ⟨1750211, by rfl⟩ : syracuseStep 2333615 = 3500423) B3500423
theorem B1661915 : Blo 1555475 1661915 := bstep (se 1 (by rfl) ⟨1246436, by rfl⟩ : syracuseStep 1661915 = 2492873) B2492873
theorem B11820005 : Blo 1555475 11820005 := bstep (se 4 (by rfl) ⟨1108125, by rfl⟩ : syracuseStep 11820005 = 2216251) B2216251
theorem B2333705 : Blo 1555475 2333705 := bstep (se 2 (by rfl) ⟨875139, by rfl⟩ : syracuseStep 2333705 = 1750279) B1750279
theorem B1555495 : Blo 1555475 1555495 := bstep (se 1 (by rfl) ⟨1166621, by rfl⟩ : syracuseStep 1555495 = 2333243) B2333243
theorem B2333735 : Blo 1555475 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B1555535 : Blo 1555475 1555535 := bstep (se 1 (by rfl) ⟨1166651, by rfl⟩ : syracuseStep 1555535 = 2333303) B2333303
theorem B1555551 : Blo 1555475 1555551 := bstep (se 1 (by rfl) ⟨1166663, by rfl⟩ : syracuseStep 1555551 = 2333327) B2333327
theorem B1555579 : Blo 1555475 1555579 := bstep (se 1 (by rfl) ⟨1166684, by rfl⟩ : syracuseStep 1555579 = 2333369) B2333369
theorem B2333819 : Blo 1555475 2333819 := bstep (se 1 (by rfl) ⟨1750364, by rfl⟩ : syracuseStep 2333819 = 3500729) B3500729
theorem B9977003 : Blo 1555475 9977003 := bstep (se 1 (by rfl) ⟨7482752, by rfl⟩ : syracuseStep 9977003 = 14965505) B14965505
theorem B1555631 : Blo 1555475 1555631 := bstep (se 1 (by rfl) ⟨1166723, by rfl⟩ : syracuseStep 1555631 = 2333447) B2333447
theorem B1555655 : Blo 1555475 1555655 := bstep (se 1 (by rfl) ⟨1166741, by rfl⟩ : syracuseStep 1555655 = 2333483) B2333483
theorem B1555675 : Blo 1555475 1555675 := bstep (se 1 (by rfl) ⟨1166756, by rfl⟩ : syracuseStep 1555675 = 2333513) B2333513
theorem B2333945 : Blo 1555475 2333945 := bstep (se 2 (by rfl) ⟨875229, by rfl⟩ : syracuseStep 2333945 = 1750459) B1750459
theorem B1555751 : Blo 1555475 1555751 := bstep (se 1 (by rfl) ⟨1166813, by rfl⟩ : syracuseStep 1555751 = 2333627) B2333627
theorem B5250365 : Blo 1555475 5250365 := bstep (se 3 (by rfl) ⟨984443, by rfl⟩ : syracuseStep 5250365 = 1968887) B1968887
theorem B1555791 : Blo 1555475 1555791 := bstep (se 1 (by rfl) ⟨1166843, by rfl⟩ : syracuseStep 1555791 = 2333687) B2333687
theorem B1555807 : Blo 1555475 1555807 := bstep (se 1 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 1555807 = 2333711) B2333711
theorem B2334047 : Blo 1555475 2334047 := bstep (se 1 (by rfl) ⟨1750535, by rfl⟩ : syracuseStep 2334047 = 3501071) B3501071
theorem B2334059 : Blo 1555475 2334059 := bstep (se 1 (by rfl) ⟨1750544, by rfl⟩ : syracuseStep 2334059 = 3501089) B3501089
theorem B1555835 : Blo 1555475 1555835 := bstep (se 1 (by rfl) ⟨1166876, by rfl⟩ : syracuseStep 1555835 = 2333753) B2333753
theorem B9977231 : Blo 1555475 9977231 := bstep (se 1 (by rfl) ⟨7482923, by rfl⟩ : syracuseStep 9977231 = 14965847) B14965847
theorem B8412581 : Blo 1555475 8412581 := bstep (se 4 (by rfl) ⟨788679, by rfl⟩ : syracuseStep 8412581 = 1577359) B1577359
theorem B1555887 : Blo 1555475 1555887 := bstep (se 1 (by rfl) ⟨1166915, by rfl⟩ : syracuseStep 1555887 = 2333831) B2333831
theorem B1555911 : Blo 1555475 1555911 := bstep (se 1 (by rfl) ⟨1166933, by rfl⟩ : syracuseStep 1555911 = 2333867) B2333867
theorem B1555931 : Blo 1555475 1555931 := bstep (se 1 (by rfl) ⟨1166948, by rfl⟩ : syracuseStep 1555931 = 2333897) B2333897
theorem B2366939 : Blo 1555475 2366939 := bstep (se 1 (by rfl) ⟨1775204, by rfl⟩ : syracuseStep 2366939 = 3550409) B3550409
theorem B2956763 : Blo 1555475 2956763 := bstep (se 1 (by rfl) ⟨2217572, by rfl⟩ : syracuseStep 2956763 = 4435145) B4435145
theorem B1556007 : Blo 1555475 1556007 := bstep (se 1 (by rfl) ⟨1167005, by rfl⟩ : syracuseStep 1556007 = 2334011) B2334011
theorem B5905979 : Blo 1555475 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B3153487 : Blo 1555475 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B1556047 : Blo 1555475 1556047 := bstep (se 1 (by rfl) ⟨1167035, by rfl⟩ : syracuseStep 1556047 = 2334071) B2334071
theorem B2334287 : Blo 1555475 2334287 := bstep (se 1 (by rfl) ⟨1750715, by rfl⟩ : syracuseStep 2334287 = 3501431) B3501431
theorem B1556063 : Blo 1555475 1556063 := bstep (se 1 (by rfl) ⟨1167047, by rfl⟩ : syracuseStep 1556063 = 2334095) B2334095
theorem B4988513 : Blo 1555475 4988513 := bstep (se 2 (by rfl) ⟨1870692, by rfl⟩ : syracuseStep 4988513 = 3741385) B3741385
theorem B1556091 : Blo 1555475 1556091 := bstep (se 1 (by rfl) ⟨1167068, by rfl⟩ : syracuseStep 1556091 = 2334137) B2334137
theorem B14204555 : Blo 1555475 14204555 := bstep (se 1 (by rfl) ⟨10653416, by rfl⟩ : syracuseStep 14204555 = 21306833) B21306833
theorem B9977489 : Blo 1555475 9977489 := bstep (se 2 (by rfl) ⟨3741558, by rfl⟩ : syracuseStep 9977489 = 7483117) B7483117
theorem B1556143 : Blo 1555475 1556143 := bstep (se 1 (by rfl) ⟨1167107, by rfl⟩ : syracuseStep 1556143 = 2334215) B2334215
theorem B14966461 : Blo 1555475 14966461 := bstep (se 3 (by rfl) ⟨2806211, by rfl⟩ : syracuseStep 14966461 = 5612423) B5612423
theorem B1556167 : Blo 1555475 1556167 := bstep (se 1 (by rfl) ⟨1167125, by rfl⟩ : syracuseStep 1556167 = 2334251) B2334251
theorem B2334407 : Blo 1555475 2334407 := bstep (se 1 (by rfl) ⟨1750805, by rfl⟩ : syracuseStep 2334407 = 3501611) B3501611
theorem B1556187 : Blo 1555475 1556187 := bstep (se 1 (by rfl) ⟨1167140, by rfl⟩ : syracuseStep 1556187 = 2334281) B2334281
theorem B17719073 : Blo 1555475 17719073 := bstep (se 2 (by rfl) ⟨6644652, by rfl⟩ : syracuseStep 17719073 = 13289305) B13289305
theorem B1556263 : Blo 1555475 1556263 := bstep (se 1 (by rfl) ⟨1167197, by rfl⟩ : syracuseStep 1556263 = 2334395) B2334395
theorem B1556303 : Blo 1555475 1556303 := bstep (se 1 (by rfl) ⟨1167227, by rfl⟩ : syracuseStep 1556303 = 2334455) B2334455
theorem B1556319 : Blo 1555475 1556319 := bstep (se 1 (by rfl) ⟨1167239, by rfl⟩ : syracuseStep 1556319 = 2334479) B2334479
theorem B2334569 : Blo 1555475 2334569 := bstep (se 2 (by rfl) ⟨875463, by rfl⟩ : syracuseStep 2334569 = 1750927) B1750927
theorem B9461623 : Blo 1555475 9461623 := bstep (se 1 (by rfl) ⟨7096217, by rfl⟩ : syracuseStep 9461623 = 14192435) B14192435
theorem B1556347 : Blo 1555475 1556347 := bstep (se 1 (by rfl) ⟨1167260, by rfl⟩ : syracuseStep 1556347 = 2334521) B2334521
theorem B1556399 : Blo 1555475 1556399 := bstep (se 1 (by rfl) ⟨1167299, by rfl⟩ : syracuseStep 1556399 = 2334599) B2334599
theorem B2334647 : Blo 1555475 2334647 := bstep (se 1 (by rfl) ⟨1750985, by rfl⟩ : syracuseStep 2334647 = 3501971) B3501971
theorem B7479233 : Blo 1555475 7479233 := bstep (se 2 (by rfl) ⟨2804712, by rfl⟩ : syracuseStep 7479233 = 5609425) B5609425
theorem B1556423 : Blo 1555475 1556423 := bstep (se 1 (by rfl) ⟨1167317, by rfl⟩ : syracuseStep 1556423 = 2334635) B2334635
theorem B1556443 : Blo 1555475 1556443 := bstep (se 1 (by rfl) ⟨1167332, by rfl⟩ : syracuseStep 1556443 = 2334665) B2334665
theorem B2334683 : Blo 1555475 2334683 := bstep (se 1 (by rfl) ⟨1751012, by rfl⟩ : syracuseStep 2334683 = 3502025) B3502025
theorem B6307865 : Blo 1555475 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B5251283 : Blo 1555475 5251283 := bstep (se 1 (by rfl) ⟨3938462, by rfl⟩ : syracuseStep 5251283 = 7876925) B7876925
theorem B1556767 : Blo 1555475 1556767 := bstep (se 1 (by rfl) ⟨1167575, by rfl⟩ : syracuseStep 1556767 = 2335151) B2335151
theorem B2335067 : Blo 1555475 2335067 := bstep (se 1 (by rfl) ⟨1751300, by rfl⟩ : syracuseStep 2335067 = 3502601) B3502601
theorem B1556827 : Blo 1555475 1556827 := bstep (se 1 (by rfl) ⟨1167620, by rfl⟩ : syracuseStep 1556827 = 2335241) B2335241
theorem B1556847 : Blo 1555475 1556847 := bstep (se 1 (by rfl) ⟨1167635, by rfl⟩ : syracuseStep 1556847 = 2335271) B2335271
theorem B1556903 : Blo 1555475 1556903 := bstep (se 1 (by rfl) ⟨1167677, by rfl⟩ : syracuseStep 1556903 = 2335355) B2335355
theorem B5251553 : Blo 1555475 5251553 := bstep (se 2 (by rfl) ⟨1969332, by rfl⟩ : syracuseStep 5251553 = 3938665) B3938665
theorem B1556987 : Blo 1555475 1556987 := bstep (se 1 (by rfl) ⟨1167740, by rfl⟩ : syracuseStep 1556987 = 2335481) B2335481
theorem B6644243 : Blo 1555475 6644243 := bstep (se 1 (by rfl) ⟨4983182, by rfl⟩ : syracuseStep 6644243 = 9966365) B9966365
theorem B3940883 : Blo 1555475 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B2335295 : Blo 1555475 2335295 := bstep (se 1 (by rfl) ⟨1751471, by rfl⟩ : syracuseStep 2335295 = 3502943) B3502943
theorem B1557055 : Blo 1555475 1557055 := bstep (se 1 (by rfl) ⟨1167791, by rfl⟩ : syracuseStep 1557055 = 2335583) B2335583
theorem B1557063 : Blo 1555475 1557063 := bstep (se 1 (by rfl) ⟨1167797, by rfl⟩ : syracuseStep 1557063 = 2335595) B2335595
theorem B8413793 : Blo 1555475 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B2335415 : Blo 1555475 2335415 := bstep (se 1 (by rfl) ⟨1751561, by rfl⟩ : syracuseStep 2335415 = 3503123) B3503123
theorem B1557215 : Blo 1555475 1557215 := bstep (se 1 (by rfl) ⟨1167911, by rfl⟩ : syracuseStep 1557215 = 2335823) B2335823
theorem B1557295 : Blo 1555475 1557295 := bstep (se 1 (by rfl) ⟨1167971, by rfl⟩ : syracuseStep 1557295 = 2335943) B2335943
theorem B2335643 : Blo 1555475 2335643 := bstep (se 1 (by rfl) ⟨1751732, by rfl⟩ : syracuseStep 2335643 = 3503465) B3503465
theorem B1557403 : Blo 1555475 1557403 := bstep (se 1 (by rfl) ⟨1168052, by rfl⟩ : syracuseStep 1557403 = 2336105) B2336105
theorem B1557455 : Blo 1555475 1557455 := bstep (se 1 (by rfl) ⟨1168091, by rfl⟩ : syracuseStep 1557455 = 2336183) B2336183
theorem B9462791 : Blo 1555475 9462791 := bstep (se 1 (by rfl) ⟨7097093, by rfl⟩ : syracuseStep 9462791 = 14194187) B14194187
theorem B7881785 : Blo 1555475 7881785 := bstep (se 2 (by rfl) ⟨2955669, by rfl⟩ : syracuseStep 7881785 = 5911339) B5911339
theorem B4433039 : Blo 1555475 4433039 := bstep (se 1 (by rfl) ⟨3324779, by rfl⟩ : syracuseStep 4433039 = 6649559) B6649559
theorem B5612759 : Blo 1555475 5612759 := bstep (se 1 (by rfl) ⟨4209569, by rfl⟩ : syracuseStep 5612759 = 8419139) B8419139
theorem B2336039 : Blo 1555475 2336039 := bstep (se 1 (by rfl) ⟨1752029, by rfl⟩ : syracuseStep 2336039 = 3504059) B3504059
theorem B5907755 : Blo 1555475 5907755 := bstep (se 1 (by rfl) ⟨4430816, by rfl⟩ : syracuseStep 5907755 = 8861633) B8861633
theorem B7480619 : Blo 1555475 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B2336123 : Blo 1555475 2336123 := bstep (se 1 (by rfl) ⟨1752092, by rfl⟩ : syracuseStep 2336123 = 3504185) B3504185
theorem B14968307 : Blo 1555475 14968307 := bstep (se 1 (by rfl) ⟨11226230, by rfl⟩ : syracuseStep 14968307 = 22452461) B22452461
theorem B3548767 : Blo 1555475 3548767 := bstep (se 1 (by rfl) ⟨2661575, by rfl⟩ : syracuseStep 3548767 = 5323151) B5323151
theorem B5252795 : Blo 1555475 5252795 := bstep (se 1 (by rfl) ⟨3939596, by rfl⟩ : syracuseStep 5252795 = 7879193) B7879193
theorem B2492201 : Blo 1555475 2492201 := bstep (se 2 (by rfl) ⟨934575, by rfl⟩ : syracuseStep 2492201 = 1869151) B1869151
theorem B10643345 : Blo 1555475 10643345 := bstep (se 2 (by rfl) ⟨3991254, by rfl⟩ : syracuseStep 10643345 = 7982509) B7982509
theorem B85231673 : Blo 1555475 85231673 := bstep (se 2 (by rfl) ⟨31961877, by rfl⟩ : syracuseStep 85231673 = 63923755) B63923755
theorem B4204649 : Blo 1555475 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B3500243 : Blo 1555475 3500243 := bstep (se 1 (by rfl) ⟨2625182, by rfl⟩ : syracuseStep 3500243 = 5250365) B5250365
theorem B14952701 : Blo 1555475 14952701 := bstep (se 3 (by rfl) ⟨2803631, by rfl⟩ : syracuseStep 14952701 = 5607263) B5607263
theorem B3500297 : Blo 1555475 3500297 := bstep (se 2 (by rfl) ⟨1312611, by rfl⟩ : syracuseStep 3500297 = 2625223) B2625223
theorem B13666621 : Blo 1555475 13666621 := bstep (se 3 (by rfl) ⟨2562491, by rfl⟩ : syracuseStep 13666621 = 5124983) B5124983
theorem B8866259 : Blo 1555475 8866259 := bstep (se 1 (by rfl) ⟨6649694, by rfl⟩ : syracuseStep 8866259 = 13299389) B13299389
theorem B3500513 : Blo 1555475 3500513 := bstep (se 2 (by rfl) ⟨1312692, by rfl⟩ : syracuseStep 3500513 = 2625385) B2625385
theorem B3738233 : Blo 1555475 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B19180241 : Blo 1555475 19180241 := bstep (se 2 (by rfl) ⟨7192590, by rfl⟩ : syracuseStep 19180241 = 14385181) B14385181
theorem B3500819 : Blo 1555475 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B13290263 : Blo 1555475 13290263 := bstep (se 1 (by rfl) ⟨9967697, by rfl⟩ : syracuseStep 13290263 = 19935395) B19935395
theorem B1968943 : Blo 1555475 1968943 := bstep (se 1 (by rfl) ⟨1476707, by rfl⟩ : syracuseStep 1968943 = 2953415) B2953415
theorem B16829315 : Blo 1555475 16829315 := bstep (se 1 (by rfl) ⟨12621986, by rfl⟩ : syracuseStep 16829315 = 25243973) B25243973
theorem B4983695 : Blo 1555475 4983695 := bstep (se 1 (by rfl) ⟨3737771, by rfl⟩ : syracuseStep 4983695 = 7475543) B7475543
theorem B2247655 : Blo 1555475 2247655 := bstep (se 1 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 2247655 = 3371483) B3371483
theorem B2493431 : Blo 1555475 2493431 := bstep (se 1 (by rfl) ⟨1870073, by rfl⟩ : syracuseStep 2493431 = 3740147) B3740147
theorem B7883891 : Blo 1555475 7883891 := bstep (se 1 (by rfl) ⟨5912918, by rfl⟩ : syracuseStep 7883891 = 11825837) B11825837
theorem B3501179 : Blo 1555475 3501179 := bstep (se 1 (by rfl) ⟨2625884, by rfl⟩ : syracuseStep 3501179 = 5251769) B5251769
theorem B2804879 : Blo 1555475 2804879 := bstep (se 1 (by rfl) ⟨2103659, by rfl⟩ : syracuseStep 2804879 = 4207319) B4207319
theorem B50490539 : Blo 1555475 50490539 := bstep (se 1 (by rfl) ⟨37867904, by rfl⟩ : syracuseStep 50490539 = 75735809) B75735809
theorem B26602667 : Blo 1555475 26602667 := bstep (se 1 (by rfl) ⟨19952000, by rfl⟩ : syracuseStep 26602667 = 39904001) B39904001
theorem B17730737 : Blo 1555475 17730737 := bstep (se 2 (by rfl) ⟨6649026, by rfl⟩ : syracuseStep 17730737 = 13298053) B13298053
theorem B5762267 : Blo 1555475 5762267 := bstep (se 1 (by rfl) ⟨4321700, by rfl⟩ : syracuseStep 5762267 = 8643401) B8643401
theorem B3501305 : Blo 1555475 3501305 := bstep (se 2 (by rfl) ⟨1312989, by rfl⟩ : syracuseStep 3501305 = 2625979) B2625979
theorem B10644767 : Blo 1555475 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B8867191 : Blo 1555475 8867191 := bstep (se 1 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 8867191 = 13300787) B13300787
theorem B3501449 : Blo 1555475 3501449 := bstep (se 2 (by rfl) ⟨1313043, by rfl⟩ : syracuseStep 3501449 = 2626087) B2626087
theorem B3501575 : Blo 1555475 3501575 := bstep (se 1 (by rfl) ⟨2626181, by rfl⟩ : syracuseStep 3501575 = 5252363) B5252363
theorem B5254739 : Blo 1555475 5254739 := bstep (se 1 (by rfl) ⟨3941054, by rfl⟩ : syracuseStep 5254739 = 7882109) B7882109
theorem B18460333 : Blo 1555475 18460333 := bstep (se 3 (by rfl) ⟨3461312, by rfl⟩ : syracuseStep 18460333 = 6922625) B6922625
theorem B3501755 : Blo 1555475 3501755 := bstep (se 1 (by rfl) ⟨2626316, by rfl⟩ : syracuseStep 3501755 = 5252633) B5252633
theorem B4206377 : Blo 1555475 4206377 := bstep (se 2 (by rfl) ⟨1577391, by rfl⟩ : syracuseStep 4206377 = 3154783) B3154783
theorem B3501881 : Blo 1555475 3501881 := bstep (se 2 (by rfl) ⟨1313205, by rfl⟩ : syracuseStep 3501881 = 2626411) B2626411
theorem B42594167 : Blo 1555475 42594167 := bstep (se 1 (by rfl) ⟨31945625, by rfl⟩ : syracuseStep 42594167 = 63891251) B63891251
theorem B6311837 : Blo 1555475 6311837 := bstep (se 3 (by rfl) ⟨1183469, by rfl⟩ : syracuseStep 6311837 = 2366939) B2366939
theorem B7884701 : Blo 1555475 7884701 := bstep (se 3 (by rfl) ⟨1478381, by rfl⟩ : syracuseStep 7884701 = 2956763) B2956763
theorem B2625959 : Blo 1555475 2625959 := bstep (se 1 (by rfl) ⟨1969469, by rfl⟩ : syracuseStep 2625959 = 3938939) B3938939
theorem B2806183 : Blo 1555475 2806183 := bstep (se 1 (by rfl) ⟨2104637, by rfl⟩ : syracuseStep 2806183 = 4209275) B4209275
theorem B3502511 : Blo 1555475 3502511 := bstep (se 1 (by rfl) ⟨2626883, by rfl⟩ : syracuseStep 3502511 = 5253767) B5253767
theorem B3502547 : Blo 1555475 3502547 := bstep (se 1 (by rfl) ⟨2626910, by rfl⟩ : syracuseStep 3502547 = 5253821) B5253821
theorem B3322387 : Blo 1555475 3322387 := bstep (se 1 (by rfl) ⟨2491790, by rfl⟩ : syracuseStep 3322387 = 4983581) B4983581
theorem B10646077 : Blo 1555475 10646077 := bstep (se 3 (by rfl) ⟨1996139, by rfl⟩ : syracuseStep 10646077 = 3992279) B3992279
theorem B3502655 : Blo 1555475 3502655 := bstep (se 1 (by rfl) ⟨2626991, by rfl⟩ : syracuseStep 3502655 = 5253983) B5253983
theorem B2806343 : Blo 1555475 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B2626121 : Blo 1555475 2626121 := bstep (se 2 (by rfl) ⟨984795, by rfl⟩ : syracuseStep 2626121 = 1969591) B1969591
theorem B3502763 : Blo 1555475 3502763 := bstep (se 1 (by rfl) ⟨2627072, by rfl⟩ : syracuseStep 3502763 = 5254145) B5254145
theorem B29913785 : Blo 1555475 29913785 := bstep (se 2 (by rfl) ⟨11217669, by rfl⟩ : syracuseStep 29913785 = 22435339) B22435339
theorem B3322703 : Blo 1555475 3322703 := bstep (se 1 (by rfl) ⟨2492027, by rfl⟩ : syracuseStep 3322703 = 4984055) B4984055
theorem B4207439 : Blo 1555475 4207439 := bstep (se 1 (by rfl) ⟨3155579, by rfl⟩ : syracuseStep 4207439 = 6311159) B6311159
theorem B5608387 : Blo 1555475 5608387 := bstep (se 1 (by rfl) ⟨4206290, by rfl⟩ : syracuseStep 5608387 = 8412581) B8412581
theorem B1749991 : Blo 1555475 1749991 := bstep (se 1 (by rfl) ⟨1312493, by rfl⟩ : syracuseStep 1749991 = 2624987) B2624987
theorem B3937319 : Blo 1555475 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B11826323 : Blo 1555475 11826323 := bstep (se 1 (by rfl) ⟨8869742, by rfl⟩ : syracuseStep 11826323 = 17739485) B17739485
theorem B3503303 : Blo 1555475 3503303 := bstep (se 1 (by rfl) ⟨2627477, by rfl⟩ : syracuseStep 3503303 = 5254955) B5254955
theorem B4986155 : Blo 1555475 4986155 := bstep (se 1 (by rfl) ⟨3739616, by rfl⟩ : syracuseStep 4986155 = 7479233) B7479233
theorem B3503483 : Blo 1555475 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B3937673 : Blo 1555475 3937673 := bstep (se 2 (by rfl) ⟨1476627, by rfl⟩ : syracuseStep 3937673 = 2953255) B2953255
theorem B7476619 : Blo 1555475 7476619 := bstep (se 1 (by rfl) ⟨5607464, by rfl⟩ : syracuseStep 7476619 = 11214929) B11214929
theorem B18216353 : Blo 1555475 18216353 := bstep (se 2 (by rfl) ⟨6831132, by rfl⟩ : syracuseStep 18216353 = 13662265) B13662265
theorem B3503609 : Blo 1555475 3503609 := bstep (se 2 (by rfl) ⟨1313853, by rfl⟩ : syracuseStep 3503609 = 2627707) B2627707
theorem B3503699 : Blo 1555475 3503699 := bstep (se 1 (by rfl) ⟨2627774, by rfl⟩ : syracuseStep 3503699 = 5255549) B5255549
theorem B2627167 : Blo 1555475 2627167 := bstep (se 1 (by rfl) ⟨1970375, by rfl⟩ : syracuseStep 2627167 = 3940751) B3940751
theorem B3503879 : Blo 1555475 3503879 := bstep (se 1 (by rfl) ⟨2627909, by rfl⟩ : syracuseStep 3503879 = 5255819) B5255819
theorem B2955055 : Blo 1555475 2955055 := bstep (se 1 (by rfl) ⟨2216291, by rfl⟩ : syracuseStep 2955055 = 4432583) B4432583
theorem B2627383 : Blo 1555475 2627383 := bstep (se 1 (by rfl) ⟨1970537, by rfl⟩ : syracuseStep 2627383 = 3941075) B3941075
theorem B18921401 : Blo 1555475 18921401 := bstep (se 2 (by rfl) ⟨7095525, by rfl⟩ : syracuseStep 18921401 = 14191051) B14191051
theorem B6739919 : Blo 1555475 6739919 := bstep (se 1 (by rfl) ⟨5054939, by rfl⟩ : syracuseStep 6739919 = 10109879) B10109879
theorem B2627849 : Blo 1555475 2627849 := bstep (se 2 (by rfl) ⟨985443, by rfl⟩ : syracuseStep 2627849 = 1970887) B1970887
theorem B3324233 : Blo 1555475 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B14195033 : Blo 1555475 14195033 := bstep (se 2 (by rfl) ⟨5323137, by rfl⟩ : syracuseStep 14195033 = 10646275) B10646275
theorem B3324343 : Blo 1555475 3324343 := bstep (se 1 (by rfl) ⟨2493257, by rfl⟩ : syracuseStep 3324343 = 4986515) B4986515
theorem B2333255 : Blo 1555475 2333255 := bstep (se 1 (by rfl) ⟨1749941, by rfl⟩ : syracuseStep 2333255 = 3499883) B3499883
theorem B1751647 : Blo 1555475 1751647 := bstep (se 1 (by rfl) ⟨1313735, by rfl⟩ : syracuseStep 1751647 = 2627471) B2627471
theorem B2333291 : Blo 1555475 2333291 := bstep (se 1 (by rfl) ⟨1749968, by rfl⟩ : syracuseStep 2333291 = 3499937) B3499937
theorem B11221679 : Blo 1555475 11221679 := bstep (se 1 (by rfl) ⟨8416259, by rfl⟩ : syracuseStep 11221679 = 16832519) B16832519
theorem B5913283 : Blo 1555475 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B2333519 : Blo 1555475 2333519 := bstep (se 1 (by rfl) ⟨1750139, by rfl⟩ : syracuseStep 2333519 = 3500279) B3500279
theorem B3939151 : Blo 1555475 3939151 := bstep (se 1 (by rfl) ⟨2954363, by rfl⟩ : syracuseStep 3939151 = 5908727) B5908727
theorem B17726363 : Blo 1555475 17726363 := bstep (se 1 (by rfl) ⟨13294772, by rfl⟩ : syracuseStep 17726363 = 26589545) B26589545
theorem B13302701 : Blo 1555475 13302701 := bstep (se 3 (by rfl) ⟨2494256, by rfl⟩ : syracuseStep 13302701 = 4988513) B4988513
theorem B22756403 : Blo 1555475 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B3939425 : Blo 1555475 3939425 := bstep (se 2 (by rfl) ⟨1477284, by rfl⟩ : syracuseStep 3939425 = 2954569) B2954569
theorem B2333915 : Blo 1555475 2333915 := bstep (se 1 (by rfl) ⟨1750436, by rfl⟩ : syracuseStep 2333915 = 3500873) B3500873
theorem B1555743 : Blo 1555475 1555743 := bstep (se 1 (by rfl) ⟨1166807, by rfl⟩ : syracuseStep 1555743 = 2333615) B2333615
theorem B7880003 : Blo 1555475 7880003 := bstep (se 1 (by rfl) ⟨5910002, by rfl⟩ : syracuseStep 7880003 = 11820005) B11820005
theorem B1555803 : Blo 1555475 1555803 := bstep (se 1 (by rfl) ⟨1166852, by rfl⟩ : syracuseStep 1555803 = 2333705) B2333705
theorem B1555823 : Blo 1555475 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B2334089 : Blo 1555475 2334089 := bstep (se 2 (by rfl) ⟨875283, by rfl⟩ : syracuseStep 2334089 = 1750567) B1750567
theorem B4988297 : Blo 1555475 4988297 := bstep (se 2 (by rfl) ⟨1870611, by rfl⟩ : syracuseStep 4988297 = 3741223) B3741223
theorem B1555879 : Blo 1555475 1555879 := bstep (se 1 (by rfl) ⟨1166909, by rfl⟩ : syracuseStep 1555879 = 2333819) B2333819
theorem B6651335 : Blo 1555475 6651335 := bstep (se 1 (by rfl) ⟨4988501, by rfl⟩ : syracuseStep 6651335 = 9977003) B9977003
theorem B3939799 : Blo 1555475 3939799 := bstep (se 1 (by rfl) ⟨2954849, by rfl⟩ : syracuseStep 3939799 = 5909699) B5909699
theorem B1555963 : Blo 1555475 1555963 := bstep (se 1 (by rfl) ⟨1166972, by rfl⟩ : syracuseStep 1555963 = 2333945) B2333945
theorem B1556031 : Blo 1555475 1556031 := bstep (se 1 (by rfl) ⟨1167023, by rfl⟩ : syracuseStep 1556031 = 2334047) B2334047
theorem B40443461 : Blo 1555475 40443461 := bstep (se 4 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 40443461 = 7583149) B7583149
theorem B1556039 : Blo 1555475 1556039 := bstep (se 1 (by rfl) ⟨1167029, by rfl⟩ : syracuseStep 1556039 = 2334059) B2334059
theorem B19955281 : Blo 1555475 19955281 := bstep (se 2 (by rfl) ⟨7483230, by rfl⟩ : syracuseStep 19955281 = 14966461) B14966461
theorem B4431455 : Blo 1555475 4431455 := bstep (se 1 (by rfl) ⟨3323591, by rfl⟩ : syracuseStep 4431455 = 6647183) B6647183
theorem B6651487 : Blo 1555475 6651487 := bstep (se 1 (by rfl) ⟨4988615, by rfl⟩ : syracuseStep 6651487 = 9977231) B9977231
theorem B1556191 : Blo 1555475 1556191 := bstep (se 1 (by rfl) ⟨1167143, by rfl⟩ : syracuseStep 1556191 = 2334287) B2334287
theorem B2334443 : Blo 1555475 2334443 := bstep (se 1 (by rfl) ⟨1750832, by rfl⟩ : syracuseStep 2334443 = 3501665) B3501665
theorem B3940103 : Blo 1555475 3940103 := bstep (se 1 (by rfl) ⟨2955077, by rfl⟩ : syracuseStep 3940103 = 5910155) B5910155
theorem B9469703 : Blo 1555475 9469703 := bstep (se 1 (by rfl) ⟨7102277, by rfl⟩ : syracuseStep 9469703 = 14204555) B14204555
theorem B6651659 : Blo 1555475 6651659 := bstep (se 1 (by rfl) ⟨4988744, by rfl⟩ : syracuseStep 6651659 = 9977489) B9977489
theorem B7880489 : Blo 1555475 7880489 := bstep (se 2 (by rfl) ⟨2955183, by rfl⟩ : syracuseStep 7880489 = 5910367) B5910367
theorem B1556271 : Blo 1555475 1556271 := bstep (se 1 (by rfl) ⟨1167203, by rfl⟩ : syracuseStep 1556271 = 2334407) B2334407
theorem B12615497 : Blo 1555475 12615497 := bstep (se 2 (by rfl) ⟨4730811, by rfl⟩ : syracuseStep 12615497 = 9461623) B9461623
theorem B11812715 : Blo 1555475 11812715 := bstep (se 1 (by rfl) ⟨8859536, by rfl⟩ : syracuseStep 11812715 = 17719073) B17719073
theorem B1556379 : Blo 1555475 1556379 := bstep (se 1 (by rfl) ⟨1167284, by rfl⟩ : syracuseStep 1556379 = 2334569) B2334569
theorem B4431773 : Blo 1555475 4431773 := bstep (se 3 (by rfl) ⟨830957, by rfl⟩ : syracuseStep 4431773 = 1661915) B1661915
theorem B1556431 : Blo 1555475 1556431 := bstep (se 1 (by rfl) ⟨1167323, by rfl⟩ : syracuseStep 1556431 = 2334647) B2334647
theorem B2334671 : Blo 1555475 2334671 := bstep (se 1 (by rfl) ⟨1751003, by rfl⟩ : syracuseStep 2334671 = 3502007) B3502007
theorem B1556455 : Blo 1555475 1556455 := bstep (se 1 (by rfl) ⟨1167341, by rfl⟩ : syracuseStep 1556455 = 2334683) B2334683
theorem B1556711 : Blo 1555475 1556711 := bstep (se 1 (by rfl) ⟨1167533, by rfl⟩ : syracuseStep 1556711 = 2335067) B2335067
theorem B2335007 : Blo 1555475 2335007 := bstep (se 1 (by rfl) ⟨1751255, by rfl⟩ : syracuseStep 2335007 = 3502511) B3502511
theorem B2335031 : Blo 1555475 2335031 := bstep (se 1 (by rfl) ⟨1751273, by rfl⟩ : syracuseStep 2335031 = 3502547) B3502547
theorem B7479677 : Blo 1555475 7479677 := bstep (se 3 (by rfl) ⟨1402439, by rfl⟩ : syracuseStep 7479677 = 2804879) B2804879
theorem B2335103 : Blo 1555475 2335103 := bstep (se 1 (by rfl) ⟨1751327, by rfl⟩ : syracuseStep 2335103 = 3502655) B3502655
theorem B1556863 : Blo 1555475 1556863 := bstep (se 1 (by rfl) ⟨1167647, by rfl⟩ : syracuseStep 1556863 = 2335295) B2335295
theorem B2335175 : Blo 1555475 2335175 := bstep (se 1 (by rfl) ⟨1751381, by rfl⟩ : syracuseStep 2335175 = 3502763) B3502763
theorem B1556943 : Blo 1555475 1556943 := bstep (se 1 (by rfl) ⟨1167707, by rfl⟩ : syracuseStep 1556943 = 2335415) B2335415
theorem B4432457 : Blo 1555475 4432457 := bstep (se 2 (by rfl) ⟨1662171, by rfl⟩ : syracuseStep 4432457 = 3324343) B3324343
theorem B1557095 : Blo 1555475 1557095 := bstep (se 1 (by rfl) ⟨1167821, by rfl⟩ : syracuseStep 1557095 = 2335643) B2335643
theorem B6308527 : Blo 1555475 6308527 := bstep (se 1 (by rfl) ⟨4731395, by rfl⟩ : syracuseStep 6308527 = 9462791) B9462791
theorem B13296413 : Blo 1555475 13296413 := bstep (se 3 (by rfl) ⟨2493077, by rfl⟩ : syracuseStep 13296413 = 4986155) B4986155
theorem B2335529 : Blo 1555475 2335529 := bstep (se 2 (by rfl) ⟨875823, by rfl⟩ : syracuseStep 2335529 = 1751647) B1751647
theorem B2335535 : Blo 1555475 2335535 := bstep (se 1 (by rfl) ⟨1751651, by rfl⟩ : syracuseStep 2335535 = 3503303) B3503303
theorem B1557359 : Blo 1555475 1557359 := bstep (se 1 (by rfl) ⟨1168019, by rfl⟩ : syracuseStep 1557359 = 2336039) B2336039
theorem B2335655 : Blo 1555475 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B1557415 : Blo 1555475 1557415 := bstep (se 1 (by rfl) ⟨1168061, by rfl⟩ : syracuseStep 1557415 = 2336123) B2336123
theorem B9978871 : Blo 1555475 9978871 := bstep (se 1 (by rfl) ⟨7484153, by rfl⟩ : syracuseStep 9978871 = 14968307) B14968307
theorem B2335739 : Blo 1555475 2335739 := bstep (se 1 (by rfl) ⟨1751804, by rfl⟩ : syracuseStep 2335739 = 3503609) B3503609
theorem B2335799 : Blo 1555475 2335799 := bstep (se 1 (by rfl) ⟨1751849, by rfl⟩ : syracuseStep 2335799 = 3503699) B3503699
theorem B5252201 : Blo 1555475 5252201 := bstep (se 2 (by rfl) ⟨1969575, by rfl⟩ : syracuseStep 5252201 = 3939151) B3939151
theorem B2335919 : Blo 1555475 2335919 := bstep (se 1 (by rfl) ⟨1751939, by rfl⟩ : syracuseStep 2335919 = 3503879) B3503879
theorem B7095563 : Blo 1555475 7095563 := bstep (se 1 (by rfl) ⟨5321672, by rfl⟩ : syracuseStep 7095563 = 10643345) B10643345
theorem B56821115 : Blo 1555475 56821115 := bstep (se 1 (by rfl) ⟨42615836, by rfl⟩ : syracuseStep 56821115 = 85231673) B85231673
theorem B2803099 : Blo 1555475 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B9463355 : Blo 1555475 9463355 := bstep (se 1 (by rfl) ⟨7097516, by rfl⟩ : syracuseStep 9463355 = 14195033) B14195033
theorem B2492155 : Blo 1555475 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B7481119 : Blo 1555475 7481119 := bstep (se 1 (by rfl) ⟨5610839, by rfl⟩ : syracuseStep 7481119 = 11221679) B11221679
theorem B11822921 : Blo 1555475 11822921 := bstep (se 2 (by rfl) ⟨4433595, by rfl⟩ : syracuseStep 11822921 = 8867191) B8867191
theorem B5253065 : Blo 1555475 5253065 := bstep (se 2 (by rfl) ⟨1969899, by rfl⟩ : syracuseStep 5253065 = 3939799) B3939799
theorem B11217005 : Blo 1555475 11217005 := bstep (se 3 (by rfl) ⟨2103188, by rfl⟩ : syracuseStep 11217005 = 4206377) B4206377
theorem B7096511 : Blo 1555475 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B5253335 : Blo 1555475 5253335 := bstep (se 1 (by rfl) ⟨3940001, by rfl⟩ : syracuseStep 5253335 = 7880003) B7880003
theorem B4434223 : Blo 1555475 4434223 := bstep (se 1 (by rfl) ⟨3325667, by rfl⟩ : syracuseStep 4434223 = 6651335) B6651335
theorem B26962307 : Blo 1555475 26962307 := bstep (se 1 (by rfl) ⟨20221730, by rfl⟩ : syracuseStep 26962307 = 40443461) B40443461
theorem B4434439 : Blo 1555475 4434439 := bstep (se 1 (by rfl) ⟨3325829, by rfl⟩ : syracuseStep 4434439 = 6651659) B6651659
theorem B5253659 : Blo 1555475 5253659 := bstep (se 1 (by rfl) ⟨3940244, by rfl⟩ : syracuseStep 5253659 = 7880489) B7880489
theorem B7875143 : Blo 1555475 7875143 := bstep (se 1 (by rfl) ⟨5906357, by rfl⟩ : syracuseStep 7875143 = 11812715) B11812715
theorem B28396111 : Blo 1555475 28396111 := bstep (se 1 (by rfl) ⟨21297083, by rfl⟩ : syracuseStep 28396111 = 42594167) B42594167
theorem B4205243 : Blo 1555475 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B3500855 : Blo 1555475 3500855 := bstep (se 1 (by rfl) ⟨2625641, by rfl⟩ : syracuseStep 3500855 = 5251283) B5251283
theorem B3501035 : Blo 1555475 3501035 := bstep (se 1 (by rfl) ⟨2625776, by rfl⟩ : syracuseStep 3501035 = 5251553) B5251553
theorem B1870895 : Blo 1555475 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B18222161 : Blo 1555475 18222161 := bstep (se 2 (by rfl) ⟨6833310, by rfl⟩ : syracuseStep 18222161 = 13666621) B13666621
theorem B19942523 : Blo 1555475 19942523 := bstep (se 1 (by rfl) ⟨14956892, by rfl⟩ : syracuseStep 19942523 = 29913785) B29913785
theorem B2215135 : Blo 1555475 2215135 := bstep (se 1 (by rfl) ⟨1661351, by rfl⟩ : syracuseStep 2215135 = 3322703) B3322703
theorem B2804959 : Blo 1555475 2804959 := bstep (se 1 (by rfl) ⟨2103719, by rfl⟩ : syracuseStep 2804959 = 4207439) B4207439
theorem B2624879 : Blo 1555475 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B5254523 : Blo 1555475 5254523 := bstep (se 1 (by rfl) ⟨3940892, by rfl⟩ : syracuseStep 5254523 = 7881785) B7881785
theorem B7884215 : Blo 1555475 7884215 := bstep (se 1 (by rfl) ⟨5913161, by rfl⟩ : syracuseStep 7884215 = 11826323) B11826323
theorem B7884377 : Blo 1555475 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B2625115 : Blo 1555475 2625115 := bstep (se 1 (by rfl) ⟨1968836, by rfl⟩ : syracuseStep 2625115 = 3937673) B3937673
theorem B12144235 : Blo 1555475 12144235 := bstep (se 1 (by rfl) ⟨9108176, by rfl⟩ : syracuseStep 12144235 = 18216353) B18216353
theorem B2625257 : Blo 1555475 2625257 := bstep (se 2 (by rfl) ⟨984471, by rfl⟩ : syracuseStep 2625257 = 1968943) B1968943
theorem B3501863 : Blo 1555475 3501863 := bstep (se 1 (by rfl) ⟨2626397, by rfl⟩ : syracuseStep 3501863 = 5252795) B5252795
theorem B4493279 : Blo 1555475 4493279 := bstep (se 1 (by rfl) ⟨3369959, by rfl⟩ : syracuseStep 4493279 = 6739919) B6739919
theorem B2216155 : Blo 1555475 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B5910839 : Blo 1555475 5910839 := bstep (se 1 (by rfl) ⟨4433129, by rfl⟩ : syracuseStep 5910839 = 8866259) B8866259
theorem B8860175 : Blo 1555475 8860175 := bstep (se 1 (by rfl) ⟨6645131, by rfl⟩ : syracuseStep 8860175 = 13290263) B13290263
theorem B11219543 : Blo 1555475 11219543 := bstep (se 1 (by rfl) ⟨8414657, by rfl⟩ : syracuseStep 11219543 = 16829315) B16829315
theorem B3322463 : Blo 1555475 3322463 := bstep (se 1 (by rfl) ⟨2491847, by rfl⟩ : syracuseStep 3322463 = 4983695) B4983695
theorem B11817575 : Blo 1555475 11817575 := bstep (se 1 (by rfl) ⟨8863181, by rfl⟩ : syracuseStep 11817575 = 17726363) B17726363
theorem B8868467 : Blo 1555475 8868467 := bstep (se 1 (by rfl) ⟨6651350, by rfl⟩ : syracuseStep 8868467 = 13302701) B13302701
theorem B2626283 : Blo 1555475 2626283 := bstep (se 1 (by rfl) ⟨1969712, by rfl⟩ : syracuseStep 2626283 = 3939425) B3939425
theorem B5255927 : Blo 1555475 5255927 := bstep (se 1 (by rfl) ⟨3941945, by rfl⟩ : syracuseStep 5255927 = 7883891) B7883891
theorem B4731689 : Blo 1555475 4731689 := bstep (se 2 (by rfl) ⟨1774383, by rfl⟩ : syracuseStep 4731689 = 3548767) B3548767
theorem B3502889 : Blo 1555475 3502889 := bstep (se 2 (by rfl) ⟨1313583, by rfl⟩ : syracuseStep 3502889 = 2627167) B2627167
theorem B8868649 : Blo 1555475 8868649 := bstep (se 2 (by rfl) ⟨3325743, by rfl⟩ : syracuseStep 8868649 = 6651487) B6651487
theorem B24613777 : Blo 1555475 24613777 := bstep (se 2 (by rfl) ⟨9230166, by rfl⟩ : syracuseStep 24613777 = 18460333) B18460333
theorem B3503159 : Blo 1555475 3503159 := bstep (se 1 (by rfl) ⟨2627369, by rfl⟩ : syracuseStep 3503159 = 5254739) B5254739
theorem B2954303 : Blo 1555475 2954303 := bstep (se 1 (by rfl) ⟨2215727, by rfl⟩ : syracuseStep 2954303 = 4431455) B4431455
theorem B3503177 : Blo 1555475 3503177 := bstep (se 2 (by rfl) ⟨1313691, by rfl⟩ : syracuseStep 3503177 = 2627383) B2627383
theorem B11818061 : Blo 1555475 11818061 := bstep (se 3 (by rfl) ⟨2215886, by rfl⟩ : syracuseStep 11818061 = 4431773) B4431773
theorem B2626735 : Blo 1555475 2626735 := bstep (se 1 (by rfl) ⟨1970051, by rfl⟩ : syracuseStep 2626735 = 3940103) B3940103
theorem B6313135 : Blo 1555475 6313135 := bstep (se 1 (by rfl) ⟨4734851, by rfl⟩ : syracuseStep 6313135 = 9469703) B9469703
theorem B8410331 : Blo 1555475 8410331 := bstep (se 1 (by rfl) ⟨6307748, by rfl⟩ : syracuseStep 8410331 = 12615497) B12615497
theorem B4207891 : Blo 1555475 4207891 := bstep (se 1 (by rfl) ⟨3155918, by rfl⟩ : syracuseStep 4207891 = 6311837) B6311837
theorem B5256467 : Blo 1555475 5256467 := bstep (se 1 (by rfl) ⟨3942350, by rfl⟩ : syracuseStep 5256467 = 7884701) B7884701
theorem B1750639 : Blo 1555475 1750639 := bstep (se 1 (by rfl) ⟨1312979, by rfl⟩ : syracuseStep 1750639 = 2625959) B2625959
theorem B4429495 : Blo 1555475 4429495 := bstep (se 1 (by rfl) ⟨3322121, by rfl⟩ : syracuseStep 4429495 = 6644243) B6644243
theorem B2627255 : Blo 1555475 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B1750747 : Blo 1555475 1750747 := bstep (se 1 (by rfl) ⟨1313060, by rfl⟩ : syracuseStep 1750747 = 2626121) B2626121
theorem B5609195 : Blo 1555475 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B4429849 : Blo 1555475 4429849 := bstep (se 2 (by rfl) ⟨1661193, by rfl⟩ : syracuseStep 4429849 = 3322387) B3322387
theorem B14194769 : Blo 1555475 14194769 := bstep (se 2 (by rfl) ⟨5323038, by rfl⟩ : syracuseStep 14194769 = 10646077) B10646077
theorem B2955359 : Blo 1555475 2955359 := bstep (se 1 (by rfl) ⟨2216519, by rfl⟩ : syracuseStep 2955359 = 4433039) B4433039
theorem B3741839 : Blo 1555475 3741839 := bstep (se 1 (by rfl) ⟨2806379, by rfl⟩ : syracuseStep 3741839 = 5612759) B5612759
theorem B3938503 : Blo 1555475 3938503 := bstep (se 1 (by rfl) ⟨2953877, by rfl⟩ : syracuseStep 3938503 = 5907755) B5907755
theorem B4987079 : Blo 1555475 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B1661467 : Blo 1555475 1661467 := bstep (se 1 (by rfl) ⟨1246100, by rfl⟩ : syracuseStep 1661467 = 2492201) B2492201
theorem B7477849 : Blo 1555475 7477849 := bstep (se 2 (by rfl) ⟨2804193, by rfl⟩ : syracuseStep 7477849 = 5608387) B5608387
theorem B12614267 : Blo 1555475 12614267 := bstep (se 1 (by rfl) ⟨9460700, by rfl⟩ : syracuseStep 12614267 = 18921401) B18921401
theorem B2333321 : Blo 1555475 2333321 := bstep (se 2 (by rfl) ⟨874995, by rfl⟩ : syracuseStep 2333321 = 1749991) B1749991
theorem B2996873 : Blo 1555475 2996873 := bstep (se 2 (by rfl) ⟨1123827, by rfl⟩ : syracuseStep 2996873 = 2247655) B2247655
theorem B2333495 : Blo 1555475 2333495 := bstep (se 1 (by rfl) ⟨1750121, by rfl⟩ : syracuseStep 2333495 = 3500243) B3500243
theorem B9968467 : Blo 1555475 9968467 := bstep (se 1 (by rfl) ⟨7476350, by rfl⟩ : syracuseStep 9968467 = 14952701) B14952701
theorem B2333531 : Blo 1555475 2333531 := bstep (se 1 (by rfl) ⟨1750148, by rfl⟩ : syracuseStep 2333531 = 3500297) B3500297
theorem B1751899 : Blo 1555475 1751899 := bstep (se 1 (by rfl) ⟨1313924, by rfl⟩ : syracuseStep 1751899 = 2627849) B2627849
theorem B2333675 : Blo 1555475 2333675 := bstep (se 1 (by rfl) ⟨1750256, by rfl⟩ : syracuseStep 2333675 = 3500513) B3500513
theorem B1555503 : Blo 1555475 1555503 := bstep (se 1 (by rfl) ⟨1166627, by rfl⟩ : syracuseStep 1555503 = 2333255) B2333255
theorem B1555527 : Blo 1555475 1555527 := bstep (se 1 (by rfl) ⟨1166645, by rfl⟩ : syracuseStep 1555527 = 2333291) B2333291
theorem B12786827 : Blo 1555475 12786827 := bstep (se 1 (by rfl) ⟨9590120, by rfl⟩ : syracuseStep 12786827 = 19180241) B19180241
theorem B2333879 : Blo 1555475 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B9968825 : Blo 1555475 9968825 := bstep (se 2 (by rfl) ⟨3738309, by rfl⟩ : syracuseStep 9968825 = 7476619) B7476619
theorem B1555679 : Blo 1555475 1555679 := bstep (se 1 (by rfl) ⟨1166759, by rfl⟩ : syracuseStep 1555679 = 2333519) B2333519
theorem B1662287 : Blo 1555475 1662287 := bstep (se 1 (by rfl) ⟨1246715, by rfl⟩ : syracuseStep 1662287 = 2493431) B2493431
theorem B15170935 : Blo 1555475 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B2334119 : Blo 1555475 2334119 := bstep (se 1 (by rfl) ⟨1750589, by rfl⟩ : syracuseStep 2334119 = 3501179) B3501179
theorem B26607041 : Blo 1555475 26607041 := bstep (se 2 (by rfl) ⟨9977640, by rfl⟩ : syracuseStep 26607041 = 19955281) B19955281
theorem B33660359 : Blo 1555475 33660359 := bstep (se 1 (by rfl) ⟨25245269, by rfl⟩ : syracuseStep 33660359 = 50490539) B50490539
theorem B17735111 : Blo 1555475 17735111 := bstep (se 1 (by rfl) ⟨13301333, by rfl⟩ : syracuseStep 17735111 = 26602667) B26602667
theorem B11820491 : Blo 1555475 11820491 := bstep (se 1 (by rfl) ⟨8865368, by rfl⟩ : syracuseStep 11820491 = 17730737) B17730737
theorem B1555943 : Blo 1555475 1555943 := bstep (se 1 (by rfl) ⟨1166957, by rfl⟩ : syracuseStep 1555943 = 2333915) B2333915
theorem B3841511 : Blo 1555475 3841511 := bstep (se 1 (by rfl) ⟨2881133, by rfl⟩ : syracuseStep 3841511 = 5762267) B5762267
theorem B2334203 : Blo 1555475 2334203 := bstep (se 1 (by rfl) ⟨1750652, by rfl⟩ : syracuseStep 2334203 = 3501305) B3501305
theorem B14966309 : Blo 1555475 14966309 := bstep (se 4 (by rfl) ⟨1403091, by rfl⟩ : syracuseStep 14966309 = 2806183) B2806183
theorem B1556059 : Blo 1555475 1556059 := bstep (se 1 (by rfl) ⟨1167044, by rfl⟩ : syracuseStep 1556059 = 2334089) B2334089
theorem B2334299 : Blo 1555475 2334299 := bstep (se 1 (by rfl) ⟨1750724, by rfl⟩ : syracuseStep 2334299 = 3501449) B3501449
theorem B3325531 : Blo 1555475 3325531 := bstep (se 1 (by rfl) ⟨2494148, by rfl⟩ : syracuseStep 3325531 = 4988297) B4988297
theorem B2334383 : Blo 1555475 2334383 := bstep (se 1 (by rfl) ⟨1750787, by rfl⟩ : syracuseStep 2334383 = 3501575) B3501575
theorem B3940073 : Blo 1555475 3940073 := bstep (se 2 (by rfl) ⟨1477527, by rfl⟩ : syracuseStep 3940073 = 2955055) B2955055
theorem B2334503 : Blo 1555475 2334503 := bstep (se 1 (by rfl) ⟨1750877, by rfl⟩ : syracuseStep 2334503 = 3501755) B3501755
theorem B1556295 : Blo 1555475 1556295 := bstep (se 1 (by rfl) ⟨1167221, by rfl⟩ : syracuseStep 1556295 = 2334443) B2334443
theorem B2334587 : Blo 1555475 2334587 := bstep (se 1 (by rfl) ⟨1750940, by rfl⟩ : syracuseStep 2334587 = 3501881) B3501881
theorem B1556447 : Blo 1555475 1556447 := bstep (se 1 (by rfl) ⟨1167335, by rfl⟩ : syracuseStep 1556447 = 2334671) B2334671
theorem B5906465 : Blo 1555475 5906465 := bstep (se 2 (by rfl) ⟨2214924, by rfl⟩ : syracuseStep 5906465 = 4429849) B4429849
theorem B4989053 : Blo 1555475 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1556671 : Blo 1555475 1556671 := bstep (se 1 (by rfl) ⟨1167503, by rfl⟩ : syracuseStep 1556671 = 2335007) B2335007
theorem B1556687 : Blo 1555475 1556687 := bstep (se 1 (by rfl) ⟨1167515, by rfl⟩ : syracuseStep 1556687 = 2335031) B2335031
theorem B3940559 : Blo 1555475 3940559 := bstep (se 1 (by rfl) ⟨2955419, by rfl⟩ : syracuseStep 3940559 = 5910839) B5910839
theorem B1556735 : Blo 1555475 1556735 := bstep (se 1 (by rfl) ⟨1167551, by rfl⟩ : syracuseStep 1556735 = 2335103) B2335103
theorem B5251337 : Blo 1555475 5251337 := bstep (se 2 (by rfl) ⟨1969251, by rfl⟩ : syracuseStep 5251337 = 3938503) B3938503
theorem B1556783 : Blo 1555475 1556783 := bstep (se 1 (by rfl) ⟨1167587, by rfl⟩ : syracuseStep 1556783 = 2335175) B2335175
theorem B5906783 : Blo 1555475 5906783 := bstep (se 1 (by rfl) ⟨4430087, by rfl⟩ : syracuseStep 5906783 = 8860175) B8860175
theorem B7479695 : Blo 1555475 7479695 := bstep (se 1 (by rfl) ⟨5609771, by rfl⟩ : syracuseStep 7479695 = 11219543) B11219543
theorem B18924029 : Blo 1555475 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B8864275 : Blo 1555475 8864275 := bstep (se 1 (by rfl) ⟨6648206, by rfl⟩ : syracuseStep 8864275 = 13296413) B13296413
theorem B3154459 : Blo 1555475 3154459 := bstep (se 1 (by rfl) ⟨2365844, by rfl⟩ : syracuseStep 3154459 = 4731689) B4731689
theorem B2335259 : Blo 1555475 2335259 := bstep (se 1 (by rfl) ⟨1751444, by rfl⟩ : syracuseStep 2335259 = 3502889) B3502889
theorem B1557019 : Blo 1555475 1557019 := bstep (se 1 (by rfl) ⟨1167764, by rfl⟩ : syracuseStep 1557019 = 2335529) B2335529
theorem B1557023 : Blo 1555475 1557023 := bstep (se 1 (by rfl) ⟨1167767, by rfl⟩ : syracuseStep 1557023 = 2335535) B2335535
theorem B1557103 : Blo 1555475 1557103 := bstep (se 1 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 1557103 = 2335655) B2335655
theorem B1557159 : Blo 1555475 1557159 := bstep (se 1 (by rfl) ⟨1167869, by rfl⟩ : syracuseStep 1557159 = 2335739) B2335739
theorem B2335439 : Blo 1555475 2335439 := bstep (se 1 (by rfl) ⟨1751579, by rfl⟩ : syracuseStep 2335439 = 3503159) B3503159
theorem B1557199 : Blo 1555475 1557199 := bstep (se 1 (by rfl) ⟨1167899, by rfl⟩ : syracuseStep 1557199 = 2335799) B2335799
theorem B2335451 : Blo 1555475 2335451 := bstep (se 1 (by rfl) ⟨1751588, by rfl⟩ : syracuseStep 2335451 = 3503177) B3503177
theorem B1557279 : Blo 1555475 1557279 := bstep (se 1 (by rfl) ⟨1167959, by rfl⟩ : syracuseStep 1557279 = 2335919) B2335919
theorem B9970465 : Blo 1555475 9970465 := bstep (se 2 (by rfl) ⟨3738924, by rfl⟩ : syracuseStep 9970465 = 7477849) B7477849
theorem B4432765 : Blo 1555475 4432765 := bstep (se 3 (by rfl) ⟨831143, by rfl⟩ : syracuseStep 4432765 = 1662287) B1662287
theorem B37880743 : Blo 1555475 37880743 := bstep (se 1 (by rfl) ⟨28410557, by rfl⟩ : syracuseStep 37880743 = 56821115) B56821115
theorem B6308903 : Blo 1555475 6308903 := bstep (se 1 (by rfl) ⟨4731677, by rfl⟩ : syracuseStep 6308903 = 9463355) B9463355
theorem B2335865 : Blo 1555475 2335865 := bstep (se 2 (by rfl) ⟨875949, by rfl⟩ : syracuseStep 2335865 = 1751899) B1751899
theorem B32818369 : Blo 1555475 32818369 := bstep (se 2 (by rfl) ⟨12306888, by rfl⟩ : syracuseStep 32818369 = 24613777) B24613777
theorem B7881947 : Blo 1555475 7881947 := bstep (se 1 (by rfl) ⟨5911460, by rfl⟩ : syracuseStep 7881947 = 11822921) B11822921
theorem B13305161 : Blo 1555475 13305161 := bstep (se 2 (by rfl) ⟨4989435, by rfl⟩ : syracuseStep 13305161 = 9978871) B9978871
theorem B31966645 : Blo 1555475 31966645 := bstep (se 5 (by rfl) ⟨1498436, by rfl⟩ : syracuseStep 31966645 = 2996873) B2996873
theorem B17974871 : Blo 1555475 17974871 := bstep (se 1 (by rfl) ⟨13481153, by rfl⟩ : syracuseStep 17974871 = 26962307) B26962307
theorem B2803495 : Blo 1555475 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B20227913 : Blo 1555475 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B3737465 : Blo 1555475 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B3500153 : Blo 1555475 3500153 := bstep (se 2 (by rfl) ⟨1312557, by rfl⟩ : syracuseStep 3500153 = 2625115) B2625115
theorem B4434041 : Blo 1555475 4434041 := bstep (se 2 (by rfl) ⟨1662765, by rfl⟩ : syracuseStep 4434041 = 3325531) B3325531
theorem B6645883 : Blo 1555475 6645883 := bstep (se 1 (by rfl) ⟨4984412, by rfl⟩ : syracuseStep 6645883 = 9968825) B9968825
theorem B17738027 : Blo 1555475 17738027 := bstep (se 1 (by rfl) ⟨13303520, by rfl⟩ : syracuseStep 17738027 = 26607041) B26607041
theorem B22440239 : Blo 1555475 22440239 := bstep (se 1 (by rfl) ⟨16830179, by rfl⟩ : syracuseStep 22440239 = 33660359) B33660359
theorem B11823407 : Blo 1555475 11823407 := bstep (se 1 (by rfl) ⟨8867555, by rfl⟩ : syracuseStep 11823407 = 17735111) B17735111
theorem B34098205 : Blo 1555475 34098205 := bstep (se 3 (by rfl) ⟨6393413, by rfl⟩ : syracuseStep 34098205 = 12786827) B12786827
theorem B2215289 : Blo 1555475 2215289 := bstep (se 2 (by rfl) ⟨830733, by rfl⟩ : syracuseStep 2215289 = 1661467) B1661467
theorem B1969535 : Blo 1555475 1969535 := bstep (se 1 (by rfl) ⟨1477151, by rfl⟩ : syracuseStep 1969535 = 2954303) B2954303
theorem B3501467 : Blo 1555475 3501467 := bstep (se 1 (by rfl) ⟨2626100, by rfl⟩ : syracuseStep 3501467 = 5252201) B5252201
theorem B4730375 : Blo 1555475 4730375 := bstep (se 1 (by rfl) ⟨3547781, by rfl⟩ : syracuseStep 4730375 = 7095563) B7095563
theorem B11824865 : Blo 1555475 11824865 := bstep (se 2 (by rfl) ⟨4434324, by rfl⟩ : syracuseStep 11824865 = 8868649) B8868649
theorem B13291289 : Blo 1555475 13291289 := bstep (se 2 (by rfl) ⟨4984233, by rfl⟩ : syracuseStep 13291289 = 9968467) B9968467
theorem B3739463 : Blo 1555475 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B10244029 : Blo 1555475 10244029 := bstep (se 3 (by rfl) ⟨1920755, by rfl⟩ : syracuseStep 10244029 = 3841511) B3841511
theorem B3502043 : Blo 1555475 3502043 := bstep (se 1 (by rfl) ⟨2626532, by rfl⟩ : syracuseStep 3502043 = 5253065) B5253065
theorem B1970239 : Blo 1555475 1970239 := bstep (se 1 (by rfl) ⟨1477679, by rfl⟩ : syracuseStep 1970239 = 2955359) B2955359
theorem B2494559 : Blo 1555475 2494559 := bstep (se 1 (by rfl) ⟨1870919, by rfl⟩ : syracuseStep 2494559 = 3741839) B3741839
theorem B3502223 : Blo 1555475 3502223 := bstep (se 1 (by rfl) ⟨2626667, by rfl⟩ : syracuseStep 3502223 = 5253335) B5253335
theorem B3502313 : Blo 1555475 3502313 := bstep (se 2 (by rfl) ⟨1313367, by rfl⟩ : syracuseStep 3502313 = 2626735) B2626735
theorem B8417513 : Blo 1555475 8417513 := bstep (se 2 (by rfl) ⟨3156567, by rfl⟩ : syracuseStep 8417513 = 6313135) B6313135
theorem B8859901 : Blo 1555475 8859901 := bstep (se 3 (by rfl) ⟨1661231, by rfl⟩ : syracuseStep 8859901 = 3322463) B3322463
theorem B2953513 : Blo 1555475 2953513 := bstep (se 2 (by rfl) ⟨1107567, by rfl⟩ : syracuseStep 2953513 = 2215135) B2215135
theorem B3739945 : Blo 1555475 3739945 := bstep (se 2 (by rfl) ⟨1402479, by rfl⟩ : syracuseStep 3739945 = 2804959) B2804959
theorem B3502439 : Blo 1555475 3502439 := bstep (se 1 (by rfl) ⟨2626829, by rfl⟩ : syracuseStep 3502439 = 5253659) B5253659
theorem B8409511 : Blo 1555475 8409511 := bstep (se 1 (by rfl) ⟨6307133, by rfl⟩ : syracuseStep 8409511 = 12614267) B12614267
theorem B16192313 : Blo 1555475 16192313 := bstep (se 2 (by rfl) ⟨6072117, by rfl⟩ : syracuseStep 16192313 = 12144235) B12144235
theorem B1749919 : Blo 1555475 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B3503015 : Blo 1555475 3503015 := bstep (se 1 (by rfl) ⟨2627261, by rfl⟩ : syracuseStep 3503015 = 5254523) B5254523
theorem B5256143 : Blo 1555475 5256143 := bstep (se 1 (by rfl) ⟨3942107, by rfl⟩ : syracuseStep 5256143 = 7884215) B7884215
theorem B3322873 : Blo 1555475 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B9974825 : Blo 1555475 9974825 := bstep (se 2 (by rfl) ⟨3740559, by rfl⟩ : syracuseStep 9974825 = 7481119) B7481119
theorem B5256251 : Blo 1555475 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B1750171 : Blo 1555475 1750171 := bstep (se 1 (by rfl) ⟨1312628, by rfl⟩ : syracuseStep 1750171 = 2625257) B2625257
theorem B2626715 : Blo 1555475 2626715 := bstep (se 1 (by rfl) ⟨1970036, by rfl⟩ : syracuseStep 2626715 = 3940073) B3940073
theorem B11982077 : Blo 1555475 11982077 := bstep (se 3 (by rfl) ⟨2246639, by rfl⟩ : syracuseStep 11982077 = 4493279) B4493279
theorem B37852717 : Blo 1555475 37852717 := bstep (se 3 (by rfl) ⟨7097384, by rfl⟩ : syracuseStep 37852717 = 14194769) B14194769
theorem B48592429 : Blo 1555475 48592429 := bstep (se 3 (by rfl) ⟨9111080, by rfl⟩ : syracuseStep 48592429 = 18222161) B18222161
theorem B4986451 : Blo 1555475 4986451 := bstep (se 1 (by rfl) ⟨3739838, by rfl⟩ : syracuseStep 4986451 = 7479677) B7479677
theorem B2954873 : Blo 1555475 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B2954971 : Blo 1555475 2954971 := bstep (se 1 (by rfl) ⟨2216228, by rfl⟩ : syracuseStep 2954971 = 4432457) B4432457
theorem B5912297 : Blo 1555475 5912297 := bstep (se 2 (by rfl) ⟨2217111, by rfl⟩ : syracuseStep 5912297 = 4434223) B4434223
theorem B7878383 : Blo 1555475 7878383 := bstep (se 1 (by rfl) ⟨5908787, by rfl⟩ : syracuseStep 7878383 = 11817575) B11817575
theorem B5912311 : Blo 1555475 5912311 := bstep (se 1 (by rfl) ⟨4434233, by rfl⟩ : syracuseStep 5912311 = 8868467) B8868467
theorem B1750855 : Blo 1555475 1750855 := bstep (se 1 (by rfl) ⟨1313141, by rfl⟩ : syracuseStep 1750855 = 2626283) B2626283
theorem B3503951 : Blo 1555475 3503951 := bstep (se 1 (by rfl) ⟨2627963, by rfl⟩ : syracuseStep 3503951 = 5255927) B5255927
theorem B22427549 : Blo 1555475 22427549 := bstep (se 3 (by rfl) ⟨4205165, by rfl⟩ : syracuseStep 22427549 = 8410331) B8410331
theorem B5912585 : Blo 1555475 5912585 := bstep (se 2 (by rfl) ⟨2217219, by rfl⟩ : syracuseStep 5912585 = 4434439) B4434439
theorem B7878707 : Blo 1555475 7878707 := bstep (se 1 (by rfl) ⟨5909030, by rfl⟩ : syracuseStep 7878707 = 11818061) B11818061
theorem B37861481 : Blo 1555475 37861481 := bstep (se 2 (by rfl) ⟨14198055, by rfl⟩ : syracuseStep 37861481 = 28396111) B28396111
theorem B3504311 : Blo 1555475 3504311 := bstep (se 1 (by rfl) ⟨2628233, by rfl⟩ : syracuseStep 3504311 = 5256467) B5256467
theorem B8411369 : Blo 1555475 8411369 := bstep (se 2 (by rfl) ⟨3154263, by rfl⟩ : syracuseStep 8411369 = 6308527) B6308527
theorem B1751503 : Blo 1555475 1751503 := bstep (se 1 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 1751503 = 2627255) B2627255
theorem B7478003 : Blo 1555475 7478003 := bstep (se 1 (by rfl) ⟨5608502, by rfl⟩ : syracuseStep 7478003 = 11217005) B11217005
theorem B3324719 : Blo 1555475 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B5610521 : Blo 1555475 5610521 := bstep (se 2 (by rfl) ⟨2103945, by rfl⟩ : syracuseStep 5610521 = 4207891) B4207891
theorem B5250095 : Blo 1555475 5250095 := bstep (se 1 (by rfl) ⟨3937571, by rfl⟩ : syracuseStep 5250095 = 7875143) B7875143
theorem B1555547 : Blo 1555475 1555547 := bstep (se 1 (by rfl) ⟨1166660, by rfl⟩ : syracuseStep 1555547 = 2333321) B2333321
theorem B1555663 : Blo 1555475 1555663 := bstep (se 1 (by rfl) ⟨1166747, by rfl⟩ : syracuseStep 1555663 = 2333495) B2333495
theorem B2333903 : Blo 1555475 2333903 := bstep (se 1 (by rfl) ⟨1750427, by rfl⟩ : syracuseStep 2333903 = 3500855) B3500855
theorem B1555687 : Blo 1555475 1555687 := bstep (se 1 (by rfl) ⟨1166765, by rfl⟩ : syracuseStep 1555687 = 2333531) B2333531
theorem B1555783 : Blo 1555475 1555783 := bstep (se 1 (by rfl) ⟨1166837, by rfl⟩ : syracuseStep 1555783 = 2333675) B2333675
theorem B2334023 : Blo 1555475 2334023 := bstep (se 1 (by rfl) ⟨1750517, by rfl⟩ : syracuseStep 2334023 = 3501035) B3501035
theorem B13295015 : Blo 1555475 13295015 := bstep (se 1 (by rfl) ⟨9971261, by rfl⟩ : syracuseStep 13295015 = 19942523) B19942523
theorem B1555919 : Blo 1555475 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B2334185 : Blo 1555475 2334185 := bstep (se 2 (by rfl) ⟨875319, by rfl⟩ : syracuseStep 2334185 = 1750639) B1750639
theorem B5905993 : Blo 1555475 5905993 := bstep (se 2 (by rfl) ⟨2214747, by rfl⟩ : syracuseStep 5905993 = 4429495) B4429495
theorem B1556079 : Blo 1555475 1556079 := bstep (se 1 (by rfl) ⟨1167059, by rfl⟩ : syracuseStep 1556079 = 2334119) B2334119
theorem B2334329 : Blo 1555475 2334329 := bstep (se 2 (by rfl) ⟨875373, by rfl⟩ : syracuseStep 2334329 = 1750747) B1750747
theorem B7880327 : Blo 1555475 7880327 := bstep (se 1 (by rfl) ⟨5910245, by rfl⟩ : syracuseStep 7880327 = 11820491) B11820491
theorem B1556135 : Blo 1555475 1556135 := bstep (se 1 (by rfl) ⟨1167101, by rfl⟩ : syracuseStep 1556135 = 2334203) B2334203
theorem B9977539 : Blo 1555475 9977539 := bstep (se 1 (by rfl) ⟨7483154, by rfl⟩ : syracuseStep 9977539 = 14966309) B14966309
theorem B1556199 : Blo 1555475 1556199 := bstep (se 1 (by rfl) ⟨1167149, by rfl⟩ : syracuseStep 1556199 = 2334299) B2334299
theorem B1556255 : Blo 1555475 1556255 := bstep (se 1 (by rfl) ⟨1167191, by rfl⟩ : syracuseStep 1556255 = 2334383) B2334383
theorem B1556335 : Blo 1555475 1556335 := bstep (se 1 (by rfl) ⟨1167251, by rfl⟩ : syracuseStep 1556335 = 2334503) B2334503
theorem B2334575 : Blo 1555475 2334575 := bstep (se 1 (by rfl) ⟨1750931, by rfl⟩ : syracuseStep 2334575 = 3501863) B3501863
theorem B1556391 : Blo 1555475 1556391 := bstep (se 1 (by rfl) ⟨1167293, by rfl⟩ : syracuseStep 1556391 = 2334587) B2334587
theorem B1663039 : Blo 1555475 1663039 := bstep (se 1 (by rfl) ⟨1247279, by rfl⟩ : syracuseStep 1663039 = 2494559) B2494559
theorem B3326035 : Blo 1555475 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B2334815 : Blo 1555475 2334815 := bstep (se 1 (by rfl) ⟨1751111, by rfl⟩ : syracuseStep 2334815 = 3502223) B3502223
theorem B2334875 : Blo 1555475 2334875 := bstep (se 1 (by rfl) ⟨1751156, by rfl⟩ : syracuseStep 2334875 = 3502313) B3502313
theorem B5611675 : Blo 1555475 5611675 := bstep (se 1 (by rfl) ⟨4208756, by rfl⟩ : syracuseStep 5611675 = 8417513) B8417513
theorem B2334959 : Blo 1555475 2334959 := bstep (se 1 (by rfl) ⟨1751219, by rfl⟩ : syracuseStep 2334959 = 3502439) B3502439
theorem B11813201 : Blo 1555475 11813201 := bstep (se 2 (by rfl) ⟨4429950, by rfl⟩ : syracuseStep 11813201 = 8859901) B8859901
theorem B12616019 : Blo 1555475 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B1556839 : Blo 1555475 1556839 := bstep (se 1 (by rfl) ⟨1167629, by rfl⟩ : syracuseStep 1556839 = 2335259) B2335259
theorem B1556959 : Blo 1555475 1556959 := bstep (se 1 (by rfl) ⟨1167719, by rfl⟩ : syracuseStep 1556959 = 2335439) B2335439
theorem B1556967 : Blo 1555475 1556967 := bstep (se 1 (by rfl) ⟨1167725, by rfl⟩ : syracuseStep 1556967 = 2335451) B2335451
theorem B2335337 : Blo 1555475 2335337 := bstep (se 2 (by rfl) ⟨875751, by rfl⟩ : syracuseStep 2335337 = 1751503) B1751503
theorem B22430317 : Blo 1555475 22430317 := bstep (se 3 (by rfl) ⟨4205684, by rfl⟩ : syracuseStep 22430317 = 8411369) B8411369
theorem B2335343 : Blo 1555475 2335343 := bstep (se 1 (by rfl) ⟨1751507, by rfl⟩ : syracuseStep 2335343 = 3503015) B3503015
theorem B1557243 : Blo 1555475 1557243 := bstep (se 1 (by rfl) ⟨1167932, by rfl⟩ : syracuseStep 1557243 = 2335865) B2335865
theorem B7988051 : Blo 1555475 7988051 := bstep (se 1 (by rfl) ⟨5991038, by rfl⟩ : syracuseStep 7988051 = 11982077) B11982077
theorem B5907437 : Blo 1555475 5907437 := bstep (se 3 (by rfl) ⟨1107644, by rfl⟩ : syracuseStep 5907437 = 2215289) B2215289
theorem B5252093 : Blo 1555475 5252093 := bstep (se 3 (by rfl) ⟨984767, by rfl⟩ : syracuseStep 5252093 = 1969535) B1969535
theorem B3941531 : Blo 1555475 3941531 := bstep (se 1 (by rfl) ⟨2956148, by rfl⟩ : syracuseStep 3941531 = 5912297) B5912297
theorem B5252255 : Blo 1555475 5252255 := bstep (se 1 (by rfl) ⟨3939191, by rfl⟩ : syracuseStep 5252255 = 7878383) B7878383
theorem B13485275 : Blo 1555475 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B2335967 : Blo 1555475 2335967 := bstep (se 1 (by rfl) ⟨1751975, by rfl⟩ : syracuseStep 2335967 = 3503951) B3503951
theorem B2491643 : Blo 1555475 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B14951699 : Blo 1555475 14951699 := bstep (se 1 (by rfl) ⟨11213774, by rfl⟩ : syracuseStep 14951699 = 22427549) B22427549
theorem B3941723 : Blo 1555475 3941723 := bstep (se 1 (by rfl) ⟨2956292, by rfl⟩ : syracuseStep 3941723 = 5912585) B5912585
theorem B5252471 : Blo 1555475 5252471 := bstep (se 1 (by rfl) ⟨3939353, by rfl⟩ : syracuseStep 5252471 = 7878707) B7878707
theorem B25240987 : Blo 1555475 25240987 := bstep (se 1 (by rfl) ⟨18930740, by rfl⟩ : syracuseStep 25240987 = 37861481) B37861481
theorem B2336207 : Blo 1555475 2336207 := bstep (se 1 (by rfl) ⟨1752155, by rfl⟩ : syracuseStep 2336207 = 3504311) B3504311
theorem B14960159 : Blo 1555475 14960159 := bstep (se 1 (by rfl) ⟨11220119, by rfl⟩ : syracuseStep 14960159 = 22440239) B22440239
theorem B7882271 : Blo 1555475 7882271 := bstep (se 1 (by rfl) ⟨5911703, by rfl⟩ : syracuseStep 7882271 = 11823407) B11823407
theorem B3500063 : Blo 1555475 3500063 := bstep (se 1 (by rfl) ⟨2625047, by rfl⟩ : syracuseStep 3500063 = 5250095) B5250095
theorem B7874657 : Blo 1555475 7874657 := bstep (se 2 (by rfl) ⟨2952996, by rfl⟩ : syracuseStep 7874657 = 5905993) B5905993
theorem B7883081 : Blo 1555475 7883081 := bstep (se 2 (by rfl) ⟨2956155, by rfl⟩ : syracuseStep 7883081 = 5912311) B5912311
theorem B3737993 : Blo 1555475 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B5253551 : Blo 1555475 5253551 := bstep (se 1 (by rfl) ⟨3940163, by rfl⟩ : syracuseStep 5253551 = 7880327) B7880327
theorem B7883243 : Blo 1555475 7883243 := bstep (se 1 (by rfl) ⟨5912432, by rfl⟩ : syracuseStep 7883243 = 11824865) B11824865
theorem B2492975 : Blo 1555475 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B13658705 : Blo 1555475 13658705 := bstep (se 2 (by rfl) ⟨5122014, by rfl⟩ : syracuseStep 13658705 = 10244029) B10244029
theorem B17721989 : Blo 1555475 17721989 := bstep (se 4 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 17721989 = 3322873) B3322873
theorem B3500891 : Blo 1555475 3500891 := bstep (se 1 (by rfl) ⟨2625668, by rfl⟩ : syracuseStep 3500891 = 5251337) B5251337
theorem B4205935 : Blo 1555475 4205935 := bstep (se 1 (by rfl) ⟨3154451, by rfl⟩ : syracuseStep 4205935 = 6308903) B6308903
theorem B4205945 : Blo 1555475 4205945 := bstep (se 2 (by rfl) ⟨1577229, by rfl⟩ : syracuseStep 4205945 = 3154459) B3154459
theorem B5254631 : Blo 1555475 5254631 := bstep (se 1 (by rfl) ⟨3940973, by rfl⟩ : syracuseStep 5254631 = 7881947) B7881947
theorem B1969915 : Blo 1555475 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B5910353 : Blo 1555475 5910353 := bstep (se 2 (by rfl) ⟨2216382, by rfl⟩ : syracuseStep 5910353 = 4432765) B4432765
theorem B50507657 : Blo 1555475 50507657 := bstep (se 2 (by rfl) ⟨18940371, by rfl⟩ : syracuseStep 50507657 = 37880743) B37880743
theorem B11825351 : Blo 1555475 11825351 := bstep (se 1 (by rfl) ⟨8869013, by rfl⟩ : syracuseStep 11825351 = 17738027) B17738027
theorem B43757825 : Blo 1555475 43757825 := bstep (se 2 (by rfl) ⟨16409184, by rfl⟩ : syracuseStep 43757825 = 32818369) B32818369
theorem B4985335 : Blo 1555475 4985335 := bstep (se 1 (by rfl) ⟨3739001, by rfl⟩ : syracuseStep 4985335 = 7478003) B7478003
theorem B2216479 : Blo 1555475 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B3740347 : Blo 1555475 3740347 := bstep (se 1 (by rfl) ⟨2805260, by rfl⟩ : syracuseStep 3740347 = 5610521) B5610521
theorem B6648601 : Blo 1555475 6648601 := bstep (se 2 (by rfl) ⟨2493225, by rfl⟩ : syracuseStep 6648601 = 4986451) B4986451
theorem B8860859 : Blo 1555475 8860859 := bstep (se 1 (by rfl) ⟨6645644, by rfl⟩ : syracuseStep 8860859 = 13291289) B13291289
theorem B3937643 : Blo 1555475 3937643 := bstep (se 1 (by rfl) ⟨2953232, by rfl⟩ : syracuseStep 3937643 = 5906465) B5906465
theorem B2626985 : Blo 1555475 2626985 := bstep (se 2 (by rfl) ⟨985119, by rfl⟩ : syracuseStep 2626985 = 1970239) B1970239
theorem B2627039 : Blo 1555475 2627039 := bstep (se 1 (by rfl) ⟨1970279, by rfl⟩ : syracuseStep 2627039 = 3940559) B3940559
theorem B8861177 : Blo 1555475 8861177 := bstep (se 2 (by rfl) ⟨3322941, by rfl⟩ : syracuseStep 8861177 = 6645883) B6645883
theorem B3937855 : Blo 1555475 3937855 := bstep (se 1 (by rfl) ⟨2953391, by rfl⟩ : syracuseStep 3937855 = 5906783) B5906783
theorem B259159621 : Blo 1555475 259159621 := bstep (se 4 (by rfl) ⟨24296214, by rfl⟩ : syracuseStep 259159621 = 48592429) B48592429
theorem B4986463 : Blo 1555475 4986463 := bstep (se 1 (by rfl) ⟨3739847, by rfl⟩ : syracuseStep 4986463 = 7479695) B7479695
theorem B3938017 : Blo 1555475 3938017 := bstep (se 2 (by rfl) ⟨1476756, by rfl⟩ : syracuseStep 3938017 = 2953513) B2953513
theorem B4986593 : Blo 1555475 4986593 := bstep (se 2 (by rfl) ⟨1869972, by rfl⟩ : syracuseStep 4986593 = 3739945) B3739945
theorem B10794875 : Blo 1555475 10794875 := bstep (se 1 (by rfl) ⟨8096156, by rfl⟩ : syracuseStep 10794875 = 16192313) B16192313
theorem B11212681 : Blo 1555475 11212681 := bstep (se 2 (by rfl) ⟨4204755, by rfl⟩ : syracuseStep 11212681 = 8409511) B8409511
theorem B3504095 : Blo 1555475 3504095 := bstep (se 1 (by rfl) ⟨2628071, by rfl⟩ : syracuseStep 3504095 = 5256143) B5256143
theorem B11819033 : Blo 1555475 11819033 := bstep (se 2 (by rfl) ⟨4432137, by rfl⟩ : syracuseStep 11819033 = 8864275) B8864275
theorem B6649883 : Blo 1555475 6649883 := bstep (se 1 (by rfl) ⟨4987412, by rfl⟩ : syracuseStep 6649883 = 9974825) B9974825
theorem B3504167 : Blo 1555475 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B1751143 : Blo 1555475 1751143 := bstep (se 1 (by rfl) ⟨1313357, by rfl⟩ : syracuseStep 1751143 = 2626715) B2626715
theorem B8870107 : Blo 1555475 8870107 := bstep (se 1 (by rfl) ⟨6652580, by rfl⟩ : syracuseStep 8870107 = 13305161) B13305161
theorem B13293953 : Blo 1555475 13293953 := bstep (se 2 (by rfl) ⟨4985232, by rfl⟩ : syracuseStep 13293953 = 9970465) B9970465
theorem B11983247 : Blo 1555475 11983247 := bstep (se 1 (by rfl) ⟨8987435, by rfl⟩ : syracuseStep 11983247 = 17974871) B17974871
theorem B2333225 : Blo 1555475 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B45464273 : Blo 1555475 45464273 := bstep (se 2 (by rfl) ⟨17049102, by rfl⟩ : syracuseStep 45464273 = 34098205) B34098205
theorem B2333435 : Blo 1555475 2333435 := bstep (se 1 (by rfl) ⟨1750076, by rfl⟩ : syracuseStep 2333435 = 3500153) B3500153
theorem B2956027 : Blo 1555475 2956027 := bstep (se 1 (by rfl) ⟨2217020, by rfl⟩ : syracuseStep 2956027 = 4434041) B4434041
theorem B2333561 : Blo 1555475 2333561 := bstep (se 2 (by rfl) ⟨875085, by rfl⟩ : syracuseStep 2333561 = 1750171) B1750171
theorem B42622193 : Blo 1555475 42622193 := bstep (se 2 (by rfl) ⟨15983322, by rfl⟩ : syracuseStep 42622193 = 31966645) B31966645
theorem B50470289 : Blo 1555475 50470289 := bstep (se 2 (by rfl) ⟨18926358, by rfl⟩ : syracuseStep 50470289 = 37852717) B37852717
theorem B1555935 : Blo 1555475 1555935 := bstep (se 1 (by rfl) ⟨1166951, by rfl⟩ : syracuseStep 1555935 = 2333903) B2333903
theorem B1556015 : Blo 1555475 1556015 := bstep (se 1 (by rfl) ⟨1167011, by rfl⟩ : syracuseStep 1556015 = 2334023) B2334023
theorem B13303385 : Blo 1555475 13303385 := bstep (se 2 (by rfl) ⟨4988769, by rfl⟩ : syracuseStep 13303385 = 9977539) B9977539
theorem B2334311 : Blo 1555475 2334311 := bstep (se 1 (by rfl) ⟨1750733, by rfl⟩ : syracuseStep 2334311 = 3501467) B3501467
theorem B8863343 : Blo 1555475 8863343 := bstep (se 1 (by rfl) ⟨6647507, by rfl⟩ : syracuseStep 8863343 = 13295015) B13295015
theorem B3939961 : Blo 1555475 3939961 := bstep (se 2 (by rfl) ⟨1477485, by rfl⟩ : syracuseStep 3939961 = 2954971) B2954971
theorem B1556123 : Blo 1555475 1556123 := bstep (se 1 (by rfl) ⟨1167092, by rfl⟩ : syracuseStep 1556123 = 2334185) B2334185
theorem B3153583 : Blo 1555475 3153583 := bstep (se 1 (by rfl) ⟨2365187, by rfl⟩ : syracuseStep 3153583 = 4730375) B4730375
theorem B1556219 : Blo 1555475 1556219 := bstep (se 1 (by rfl) ⟨1167164, by rfl⟩ : syracuseStep 1556219 = 2334329) B2334329
theorem B2334473 : Blo 1555475 2334473 := bstep (se 2 (by rfl) ⟨875427, by rfl⟩ : syracuseStep 2334473 = 1750855) B1750855
theorem B1556383 : Blo 1555475 1556383 := bstep (se 1 (by rfl) ⟨1167287, by rfl⟩ : syracuseStep 1556383 = 2334575) B2334575
theorem B2334695 : Blo 1555475 2334695 := bstep (se 1 (by rfl) ⟨1751021, by rfl⟩ : syracuseStep 2334695 = 3502043) B3502043
theorem B1556543 : Blo 1555475 1556543 := bstep (se 1 (by rfl) ⟨1167407, by rfl⟩ : syracuseStep 1556543 = 2334815) B2334815
theorem B1556583 : Blo 1555475 1556583 := bstep (se 1 (by rfl) ⟨1167437, by rfl⟩ : syracuseStep 1556583 = 2334875) B2334875
theorem B2334857 : Blo 1555475 2334857 := bstep (se 2 (by rfl) ⟨875571, by rfl⟩ : syracuseStep 2334857 = 1751143) B1751143
theorem B1556639 : Blo 1555475 1556639 := bstep (se 1 (by rfl) ⟨1167479, by rfl⟩ : syracuseStep 1556639 = 2334959) B2334959
theorem B1556891 : Blo 1555475 1556891 := bstep (se 1 (by rfl) ⟨1167668, by rfl⟩ : syracuseStep 1556891 = 2335337) B2335337
theorem B1556895 : Blo 1555475 1556895 := bstep (se 1 (by rfl) ⟨1167671, by rfl⟩ : syracuseStep 1556895 = 2335343) B2335343
theorem B5325367 : Blo 1555475 5325367 := bstep (se 1 (by rfl) ⟨3994025, by rfl⟩ : syracuseStep 5325367 = 7988051) B7988051
theorem B5907239 : Blo 1555475 5907239 := bstep (se 1 (by rfl) ⟨4430429, by rfl⟩ : syracuseStep 5907239 = 8860859) B8860859
theorem B1557311 : Blo 1555475 1557311 := bstep (se 1 (by rfl) ⟨1167983, by rfl⟩ : syracuseStep 1557311 = 2335967) B2335967
theorem B16819109 : Blo 1555475 16819109 := bstep (se 4 (by rfl) ⟨1576791, by rfl⟩ : syracuseStep 16819109 = 3153583) B3153583
theorem B1557471 : Blo 1555475 1557471 := bstep (se 1 (by rfl) ⟨1168103, by rfl⟩ : syracuseStep 1557471 = 2336207) B2336207
theorem B19948517 : Blo 1555475 19948517 := bstep (se 4 (by rfl) ⟨1870173, by rfl⟩ : syracuseStep 19948517 = 3740347) B3740347
theorem B11215853 : Blo 1555475 11215853 := bstep (se 3 (by rfl) ⟨2102972, by rfl⟩ : syracuseStep 11215853 = 4205945) B4205945
theorem B3941369 : Blo 1555475 3941369 := bstep (se 2 (by rfl) ⟨1478013, by rfl⟩ : syracuseStep 3941369 = 2956027) B2956027
theorem B5907451 : Blo 1555475 5907451 := bstep (se 1 (by rfl) ⟨4430588, by rfl⟩ : syracuseStep 5907451 = 8861177) B8861177
theorem B8864801 : Blo 1555475 8864801 := bstep (se 2 (by rfl) ⟨3324300, by rfl⟩ : syracuseStep 8864801 = 6648601) B6648601
theorem B2336063 : Blo 1555475 2336063 := bstep (se 1 (by rfl) ⟨1752047, by rfl⟩ : syracuseStep 2336063 = 3504095) B3504095
theorem B4433255 : Blo 1555475 4433255 := bstep (se 1 (by rfl) ⟨3324941, by rfl⟩ : syracuseStep 4433255 = 6649883) B6649883
theorem B2336111 : Blo 1555475 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B7988831 : Blo 1555475 7988831 := bstep (se 1 (by rfl) ⟨5991623, by rfl⟩ : syracuseStep 7988831 = 11983247) B11983247
theorem B11814659 : Blo 1555475 11814659 := bstep (se 1 (by rfl) ⟨8860994, by rfl⟩ : syracuseStep 11814659 = 17721989) B17721989
theorem B33654649 : Blo 1555475 33654649 := bstep (se 2 (by rfl) ⟨12620493, by rfl⟩ : syracuseStep 33654649 = 25240987) B25240987
theorem B5253281 : Blo 1555475 5253281 := bstep (se 2 (by rfl) ⟨1969980, by rfl⟩ : syracuseStep 5253281 = 3939961) B3939961
theorem B33646859 : Blo 1555475 33646859 := bstep (se 1 (by rfl) ⟨25235144, by rfl⟩ : syracuseStep 33646859 = 50470289) B50470289
theorem B5908895 : Blo 1555475 5908895 := bstep (se 1 (by rfl) ⟨4431671, by rfl⟩ : syracuseStep 5908895 = 8863343) B8863343
theorem B33671771 : Blo 1555475 33671771 := bstep (se 1 (by rfl) ⟨25253828, by rfl⟩ : syracuseStep 33671771 = 50507657) B50507657
theorem B466750133 : Blo 1555475 466750133 := bstep (se 5 (by rfl) ⟨21878912, by rfl⟩ : syracuseStep 466750133 = 43757825) B43757825
theorem B4434713 : Blo 1555475 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B7883567 : Blo 1555475 7883567 := bstep (se 1 (by rfl) ⟨5912675, by rfl⟩ : syracuseStep 7883567 = 11825351) B11825351
theorem B7482233 : Blo 1555475 7482233 := bstep (se 2 (by rfl) ⟨2805837, by rfl⟩ : syracuseStep 7482233 = 5611675) B5611675
theorem B7875467 : Blo 1555475 7875467 := bstep (se 1 (by rfl) ⟨5906600, by rfl⟩ : syracuseStep 7875467 = 11813201) B11813201
theorem B6647113 : Blo 1555475 6647113 := bstep (se 2 (by rfl) ⟨2492667, by rfl⟩ : syracuseStep 6647113 = 4985335) B4985335
theorem B3501395 : Blo 1555475 3501395 := bstep (se 1 (by rfl) ⟨2626046, by rfl⟩ : syracuseStep 3501395 = 5252093) B5252093
theorem B3501503 : Blo 1555475 3501503 := bstep (se 1 (by rfl) ⟨2626127, by rfl⟩ : syracuseStep 3501503 = 5252255) B5252255
theorem B8990183 : Blo 1555475 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B2625095 : Blo 1555475 2625095 := bstep (se 1 (by rfl) ⟨1968821, by rfl⟩ : syracuseStep 2625095 = 3937643) B3937643
theorem B3501647 : Blo 1555475 3501647 := bstep (se 1 (by rfl) ⟨2626235, by rfl⟩ : syracuseStep 3501647 = 5252471) B5252471
theorem B9973439 : Blo 1555475 9973439 := bstep (se 1 (by rfl) ⟨7480079, by rfl⟩ : syracuseStep 9973439 = 14960159) B14960159
theorem B5254847 : Blo 1555475 5254847 := bstep (se 1 (by rfl) ⟨3941135, by rfl⟩ : syracuseStep 5254847 = 7882271) B7882271
theorem B6647933 : Blo 1555475 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B5255387 : Blo 1555475 5255387 := bstep (se 1 (by rfl) ⟨3941540, by rfl⟩ : syracuseStep 5255387 = 7883081) B7883081
theorem B3502367 : Blo 1555475 3502367 := bstep (se 1 (by rfl) ⟨2626775, by rfl⟩ : syracuseStep 3502367 = 5253551) B5253551
theorem B5255495 : Blo 1555475 5255495 := bstep (se 1 (by rfl) ⟨3941621, by rfl⟩ : syracuseStep 5255495 = 7883243) B7883243
theorem B9105803 : Blo 1555475 9105803 := bstep (se 1 (by rfl) ⟨6829352, by rfl⟩ : syracuseStep 9105803 = 13658705) B13658705
theorem B5607913 : Blo 1555475 5607913 := bstep (se 2 (by rfl) ⟨2102967, by rfl⟩ : syracuseStep 5607913 = 4205935) B4205935
theorem B6648617 : Blo 1555475 6648617 := bstep (se 2 (by rfl) ⟨2493231, by rfl⟩ : syracuseStep 6648617 = 4986463) B4986463
theorem B28414795 : Blo 1555475 28414795 := bstep (se 1 (by rfl) ⟨21311096, by rfl⟩ : syracuseStep 28414795 = 42622193) B42622193
theorem B3503087 : Blo 1555475 3503087 := bstep (se 1 (by rfl) ⟨2627315, by rfl⟩ : syracuseStep 3503087 = 5254631) B5254631
theorem B2626553 : Blo 1555475 2626553 := bstep (se 2 (by rfl) ⟨984957, by rfl⟩ : syracuseStep 2626553 = 1969915) B1969915
theorem B8868923 : Blo 1555475 8868923 := bstep (se 1 (by rfl) ⟨6651692, by rfl⟩ : syracuseStep 8868923 = 13303385) B13303385
theorem B2217385 : Blo 1555475 2217385 := bstep (se 2 (by rfl) ⟨831519, by rfl⟩ : syracuseStep 2217385 = 1663039) B1663039
theorem B8410679 : Blo 1555475 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B11826809 : Blo 1555475 11826809 := bstep (se 2 (by rfl) ⟨4435053, by rfl⟩ : syracuseStep 11826809 = 8870107) B8870107
theorem B3938291 : Blo 1555475 3938291 := bstep (se 1 (by rfl) ⟨2953718, by rfl⟩ : syracuseStep 3938291 = 5907437) B5907437
theorem B2955305 : Blo 1555475 2955305 := bstep (se 2 (by rfl) ⟨1108239, by rfl⟩ : syracuseStep 2955305 = 2216479) B2216479
theorem B2627687 : Blo 1555475 2627687 := bstep (se 1 (by rfl) ⟨1970765, by rfl⟩ : syracuseStep 2627687 = 3941531) B3941531
theorem B29907089 : Blo 1555475 29907089 := bstep (se 2 (by rfl) ⟨11215158, by rfl⟩ : syracuseStep 29907089 = 22430317) B22430317
theorem B1661095 : Blo 1555475 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B9967799 : Blo 1555475 9967799 := bstep (se 1 (by rfl) ⟨7475849, by rfl⟩ : syracuseStep 9967799 = 14951699) B14951699
theorem B2627815 : Blo 1555475 2627815 := bstep (se 1 (by rfl) ⟨1970861, by rfl⟩ : syracuseStep 2627815 = 3941723) B3941723
theorem B1751323 : Blo 1555475 1751323 := bstep (se 1 (by rfl) ⟨1313492, by rfl⟩ : syracuseStep 1751323 = 2626985) B2626985
theorem B1751359 : Blo 1555475 1751359 := bstep (se 1 (by rfl) ⟨1313519, by rfl⟩ : syracuseStep 1751359 = 2627039) B2627039
theorem B9967981 : Blo 1555475 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B3324395 : Blo 1555475 3324395 := bstep (se 1 (by rfl) ⟨2493296, by rfl⟩ : syracuseStep 3324395 = 4986593) B4986593
theorem B7879355 : Blo 1555475 7879355 := bstep (se 1 (by rfl) ⟨5909516, by rfl⟩ : syracuseStep 7879355 = 11819033) B11819033
theorem B2333375 : Blo 1555475 2333375 := bstep (se 1 (by rfl) ⟨1750031, by rfl⟩ : syracuseStep 2333375 = 3500063) B3500063
theorem B5249771 : Blo 1555475 5249771 := bstep (se 1 (by rfl) ⟨3937328, by rfl⟩ : syracuseStep 5249771 = 7874657) B7874657
theorem B8862635 : Blo 1555475 8862635 := bstep (se 1 (by rfl) ⟨6646976, by rfl⟩ : syracuseStep 8862635 = 13293953) B13293953
theorem B1555483 : Blo 1555475 1555483 := bstep (se 1 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 1555483 = 2333225) B2333225
theorem B30309515 : Blo 1555475 30309515 := bstep (se 1 (by rfl) ⟨22732136, by rfl⟩ : syracuseStep 30309515 = 45464273) B45464273
theorem B1555623 : Blo 1555475 1555623 := bstep (se 1 (by rfl) ⟨1166717, by rfl⟩ : syracuseStep 1555623 = 2333435) B2333435
theorem B2333927 : Blo 1555475 2333927 := bstep (se 1 (by rfl) ⟨1750445, by rfl⟩ : syracuseStep 2333927 = 3500891) B3500891
theorem B1555707 : Blo 1555475 1555707 := bstep (se 1 (by rfl) ⟨1166780, by rfl⟩ : syracuseStep 1555707 = 2333561) B2333561
theorem B5250473 : Blo 1555475 5250473 := bstep (se 2 (by rfl) ⟨1968927, by rfl⟩ : syracuseStep 5250473 = 3937855) B3937855
theorem B345546161 : Blo 1555475 345546161 := bstep (se 2 (by rfl) ⟨129579810, by rfl⟩ : syracuseStep 345546161 = 259159621) B259159621
theorem B5250689 : Blo 1555475 5250689 := bstep (se 2 (by rfl) ⟨1969008, by rfl⟩ : syracuseStep 5250689 = 3938017) B3938017
theorem B28786333 : Blo 1555475 28786333 := bstep (se 3 (by rfl) ⟨5397437, by rfl⟩ : syracuseStep 28786333 = 10794875) B10794875
theorem B1556207 : Blo 1555475 1556207 := bstep (se 1 (by rfl) ⟨1167155, by rfl⟩ : syracuseStep 1556207 = 2334311) B2334311
theorem B1556315 : Blo 1555475 1556315 := bstep (se 1 (by rfl) ⟨1167236, by rfl⟩ : syracuseStep 1556315 = 2334473) B2334473
theorem B14950241 : Blo 1555475 14950241 := bstep (se 2 (by rfl) ⟨5606340, by rfl⟩ : syracuseStep 14950241 = 11212681) B11212681
theorem B3940235 : Blo 1555475 3940235 := bstep (se 1 (by rfl) ⟨2955176, by rfl⟩ : syracuseStep 3940235 = 5910353) B5910353
theorem B1556463 : Blo 1555475 1556463 := bstep (se 1 (by rfl) ⟨1167347, by rfl⟩ : syracuseStep 1556463 = 2334695) B2334695
theorem B1556571 : Blo 1555475 1556571 := bstep (se 1 (by rfl) ⟨1167428, by rfl⟩ : syracuseStep 1556571 = 2334857) B2334857
theorem B7880813 : Blo 1555475 7880813 := bstep (se 3 (by rfl) ⟨1477652, by rfl⟩ : syracuseStep 7880813 = 2955305) B2955305
theorem B2334911 : Blo 1555475 2334911 := bstep (se 1 (by rfl) ⟨1751183, by rfl⟩ : syracuseStep 2334911 = 3502367) B3502367
theorem B6070535 : Blo 1555475 6070535 := bstep (se 1 (by rfl) ⟨4552901, by rfl⟩ : syracuseStep 6070535 = 9105803) B9105803
theorem B17727821 : Blo 1555475 17727821 := bstep (se 3 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 17727821 = 6647933) B6647933
theorem B2335097 : Blo 1555475 2335097 := bstep (se 2 (by rfl) ⟨875661, by rfl⟩ : syracuseStep 2335097 = 1751323) B1751323
theorem B2335145 : Blo 1555475 2335145 := bstep (se 2 (by rfl) ⟨875679, by rfl⟩ : syracuseStep 2335145 = 1751359) B1751359
theorem B4432411 : Blo 1555475 4432411 := bstep (se 1 (by rfl) ⟨3324308, by rfl⟩ : syracuseStep 4432411 = 6648617) B6648617
theorem B2335391 : Blo 1555475 2335391 := bstep (se 1 (by rfl) ⟨1751543, by rfl⟩ : syracuseStep 2335391 = 3503087) B3503087
theorem B1557375 : Blo 1555475 1557375 := bstep (se 1 (by rfl) ⟨1168031, by rfl⟩ : syracuseStep 1557375 = 2336063) B2336063
theorem B1557407 : Blo 1555475 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B5325887 : Blo 1555475 5325887 := bstep (se 1 (by rfl) ⟨3994415, by rfl⟩ : syracuseStep 5325887 = 7988831) B7988831
theorem B22431239 : Blo 1555475 22431239 := bstep (se 1 (by rfl) ⟨16823429, by rfl⟩ : syracuseStep 22431239 = 33646859) B33646859
theorem B22447847 : Blo 1555475 22447847 := bstep (se 1 (by rfl) ⟨16835885, by rfl⟩ : syracuseStep 22447847 = 33671771) B33671771
theorem B311166755 : Blo 1555475 311166755 := bstep (se 1 (by rfl) ⟨233375066, by rfl⟩ : syracuseStep 311166755 = 466750133) B466750133
theorem B5252903 : Blo 1555475 5252903 := bstep (se 1 (by rfl) ⟨3939677, by rfl⟩ : syracuseStep 5252903 = 7879355) B7879355
theorem B3499847 : Blo 1555475 3499847 := bstep (se 1 (by rfl) ⟨2624885, by rfl⟩ : syracuseStep 3499847 = 5249771) B5249771
theorem B5908423 : Blo 1555475 5908423 := bstep (se 1 (by rfl) ⟨4431317, by rfl⟩ : syracuseStep 5908423 = 8862635) B8862635
theorem B38381777 : Blo 1555475 38381777 := bstep (se 2 (by rfl) ⟨14393166, by rfl⟩ : syracuseStep 38381777 = 28786333) B28786333
theorem B3500315 : Blo 1555475 3500315 := bstep (se 1 (by rfl) ⟨2625236, by rfl⟩ : syracuseStep 3500315 = 5250473) B5250473
theorem B3500459 : Blo 1555475 3500459 := bstep (se 1 (by rfl) ⟨2625344, by rfl⟩ : syracuseStep 3500459 = 5250689) B5250689
theorem B2214793 : Blo 1555475 2214793 := bstep (se 2 (by rfl) ⟨830547, by rfl⟩ : syracuseStep 2214793 = 1661095) B1661095
theorem B13290641 : Blo 1555475 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B13299011 : Blo 1555475 13299011 := bstep (se 1 (by rfl) ⟨9974258, by rfl⟩ : syracuseStep 13299011 = 19948517) B19948517
theorem B5909867 : Blo 1555475 5909867 := bstep (se 1 (by rfl) ⟨4432400, by rfl⟩ : syracuseStep 5909867 = 8864801) B8864801
theorem B5607119 : Blo 1555475 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B7884539 : Blo 1555475 7884539 := bstep (se 1 (by rfl) ⟨5913404, by rfl⟩ : syracuseStep 7884539 = 11826809) B11826809
theorem B7876439 : Blo 1555475 7876439 := bstep (se 1 (by rfl) ⟨5907329, by rfl⟩ : syracuseStep 7876439 = 11814659) B11814659
theorem B2625527 : Blo 1555475 2625527 := bstep (se 1 (by rfl) ⟨1969145, by rfl⟩ : syracuseStep 2625527 = 3938291) B3938291
theorem B7876601 : Blo 1555475 7876601 := bstep (se 2 (by rfl) ⟨2953725, by rfl⟩ : syracuseStep 7876601 = 5907451) B5907451
theorem B3502187 : Blo 1555475 3502187 := bstep (se 1 (by rfl) ⟨2626640, by rfl⟩ : syracuseStep 3502187 = 5253281) B5253281
theorem B2216263 : Blo 1555475 2216263 := bstep (se 1 (by rfl) ⟨1662197, by rfl⟩ : syracuseStep 2216263 = 3324395) B3324395
theorem B5255711 : Blo 1555475 5255711 := bstep (se 1 (by rfl) ⟨3941783, by rfl⟩ : syracuseStep 5255711 = 7883567) B7883567
theorem B20206343 : Blo 1555475 20206343 := bstep (se 1 (by rfl) ⟨15154757, by rfl⟩ : syracuseStep 20206343 = 30309515) B30309515
theorem B230364107 : Blo 1555475 230364107 := bstep (se 1 (by rfl) ⟨172773080, by rfl⟩ : syracuseStep 230364107 = 345546161) B345546161
theorem B5993455 : Blo 1555475 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B1750063 : Blo 1555475 1750063 := bstep (se 1 (by rfl) ⟨1312547, by rfl⟩ : syracuseStep 1750063 = 2625095) B2625095
theorem B6648959 : Blo 1555475 6648959 := bstep (se 1 (by rfl) ⟨4986719, by rfl⟩ : syracuseStep 6648959 = 9973439) B9973439
theorem B3503231 : Blo 1555475 3503231 := bstep (se 1 (by rfl) ⟨2627423, by rfl⟩ : syracuseStep 3503231 = 5254847) B5254847
theorem B44872865 : Blo 1555475 44872865 := bstep (se 2 (by rfl) ⟨16827324, by rfl⟩ : syracuseStep 44872865 = 33654649) B33654649
theorem B9966827 : Blo 1555475 9966827 := bstep (se 1 (by rfl) ⟨7475120, by rfl⟩ : syracuseStep 9966827 = 14950241) B14950241
theorem B2626823 : Blo 1555475 2626823 := bstep (se 1 (by rfl) ⟨1970117, by rfl⟩ : syracuseStep 2626823 = 3940235) B3940235
theorem B3503591 : Blo 1555475 3503591 := bstep (se 1 (by rfl) ⟨2627693, by rfl⟩ : syracuseStep 3503591 = 5255387) B5255387
theorem B3503663 : Blo 1555475 3503663 := bstep (se 1 (by rfl) ⟨2627747, by rfl⟩ : syracuseStep 3503663 = 5255495) B5255495
theorem B3503753 : Blo 1555475 3503753 := bstep (se 2 (by rfl) ⟨1313907, by rfl⟩ : syracuseStep 3503753 = 2627815) B2627815
theorem B26580797 : Blo 1555475 26580797 := bstep (se 3 (by rfl) ⟨4983899, by rfl⟩ : syracuseStep 26580797 = 9967799) B9967799
theorem B3938159 : Blo 1555475 3938159 := bstep (se 1 (by rfl) ⟨2953619, by rfl⟩ : syracuseStep 3938159 = 5907239) B5907239
theorem B11212739 : Blo 1555475 11212739 := bstep (se 1 (by rfl) ⟨8409554, by rfl⟩ : syracuseStep 11212739 = 16819109) B16819109
theorem B7477217 : Blo 1555475 7477217 := bstep (se 2 (by rfl) ⟨2803956, by rfl⟩ : syracuseStep 7477217 = 5607913) B5607913
theorem B7477235 : Blo 1555475 7477235 := bstep (se 1 (by rfl) ⟨5607926, by rfl⟩ : syracuseStep 7477235 = 11215853) B11215853
theorem B1751035 : Blo 1555475 1751035 := bstep (se 1 (by rfl) ⟨1313276, by rfl⟩ : syracuseStep 1751035 = 2626553) B2626553
theorem B2627579 : Blo 1555475 2627579 := bstep (se 1 (by rfl) ⟨1970684, by rfl⟩ : syracuseStep 2627579 = 3941369) B3941369
theorem B5912615 : Blo 1555475 5912615 := bstep (se 1 (by rfl) ⟨4434461, by rfl⟩ : syracuseStep 5912615 = 8868923) B8868923
theorem B7100489 : Blo 1555475 7100489 := bstep (se 2 (by rfl) ⟨2662683, by rfl⟩ : syracuseStep 7100489 = 5325367) B5325367
theorem B2955503 : Blo 1555475 2955503 := bstep (se 1 (by rfl) ⟨2216627, by rfl⟩ : syracuseStep 2955503 = 4433255) B4433255
theorem B37886393 : Blo 1555475 37886393 := bstep (se 2 (by rfl) ⟨14207397, by rfl⟩ : syracuseStep 37886393 = 28414795) B28414795
theorem B1751791 : Blo 1555475 1751791 := bstep (se 1 (by rfl) ⟨1313843, by rfl⟩ : syracuseStep 1751791 = 2627687) B2627687
theorem B19938059 : Blo 1555475 19938059 := bstep (se 1 (by rfl) ⟨14953544, by rfl⟩ : syracuseStep 19938059 = 29907089) B29907089
theorem B3939263 : Blo 1555475 3939263 := bstep (se 1 (by rfl) ⟨2954447, by rfl⟩ : syracuseStep 3939263 = 5908895) B5908895
theorem B8862817 : Blo 1555475 8862817 := bstep (se 2 (by rfl) ⟨3323556, by rfl⟩ : syracuseStep 8862817 = 6647113) B6647113
theorem B1555583 : Blo 1555475 1555583 := bstep (se 1 (by rfl) ⟨1166687, by rfl⟩ : syracuseStep 1555583 = 2333375) B2333375
theorem B2956475 : Blo 1555475 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B2956513 : Blo 1555475 2956513 := bstep (se 2 (by rfl) ⟨1108692, by rfl⟩ : syracuseStep 2956513 = 2217385) B2217385
theorem B4988155 : Blo 1555475 4988155 := bstep (se 1 (by rfl) ⟨3741116, by rfl⟩ : syracuseStep 4988155 = 7482233) B7482233
theorem B5250311 : Blo 1555475 5250311 := bstep (se 1 (by rfl) ⟨3937733, by rfl⟩ : syracuseStep 5250311 = 7875467) B7875467
theorem B1555951 : Blo 1555475 1555951 := bstep (se 1 (by rfl) ⟨1166963, by rfl⟩ : syracuseStep 1555951 = 2333927) B2333927
theorem B2334263 : Blo 1555475 2334263 := bstep (se 1 (by rfl) ⟨1750697, by rfl⟩ : syracuseStep 2334263 = 3501395) B3501395
theorem B2334335 : Blo 1555475 2334335 := bstep (se 1 (by rfl) ⟨1750751, by rfl⟩ : syracuseStep 2334335 = 3501503) B3501503
theorem B2334431 : Blo 1555475 2334431 := bstep (se 1 (by rfl) ⟨1750823, by rfl⟩ : syracuseStep 2334431 = 3501647) B3501647
theorem B2334791 : Blo 1555475 2334791 := bstep (se 1 (by rfl) ⟨1751093, by rfl⟩ : syracuseStep 2334791 = 3502187) B3502187
theorem B1556607 : Blo 1555475 1556607 := bstep (se 1 (by rfl) ⟨1167455, by rfl⟩ : syracuseStep 1556607 = 2334911) B2334911
theorem B4047023 : Blo 1555475 4047023 := bstep (se 1 (by rfl) ⟨3035267, by rfl⟩ : syracuseStep 4047023 = 6070535) B6070535
theorem B1556731 : Blo 1555475 1556731 := bstep (se 1 (by rfl) ⟨1167548, by rfl⟩ : syracuseStep 1556731 = 2335097) B2335097
theorem B1556763 : Blo 1555475 1556763 := bstep (se 1 (by rfl) ⟨1167572, by rfl⟩ : syracuseStep 1556763 = 2335145) B2335145
theorem B1556927 : Blo 1555475 1556927 := bstep (se 1 (by rfl) ⟨1167695, by rfl⟩ : syracuseStep 1556927 = 2335391) B2335391
theorem B153576071 : Blo 1555475 153576071 := bstep (se 1 (by rfl) ⟨115182053, by rfl⟩ : syracuseStep 153576071 = 230364107) B230364107
theorem B4432639 : Blo 1555475 4432639 := bstep (se 1 (by rfl) ⟨3324479, by rfl⟩ : syracuseStep 4432639 = 6648959) B6648959
theorem B2335487 : Blo 1555475 2335487 := bstep (se 1 (by rfl) ⟨1751615, by rfl⟩ : syracuseStep 2335487 = 3503231) B3503231
theorem B6644551 : Blo 1555475 6644551 := bstep (se 1 (by rfl) ⟨4983413, by rfl⟩ : syracuseStep 6644551 = 9966827) B9966827
theorem B2335721 : Blo 1555475 2335721 := bstep (se 2 (by rfl) ⟨875895, by rfl⟩ : syracuseStep 2335721 = 1751791) B1751791
theorem B2335727 : Blo 1555475 2335727 := bstep (se 1 (by rfl) ⟨1751795, by rfl⟩ : syracuseStep 2335727 = 3503591) B3503591
theorem B2335775 : Blo 1555475 2335775 := bstep (se 1 (by rfl) ⟨1751831, by rfl⟩ : syracuseStep 2335775 = 3503663) B3503663
theorem B2335835 : Blo 1555475 2335835 := bstep (se 1 (by rfl) ⟨1751876, by rfl⟩ : syracuseStep 2335835 = 3503753) B3503753
theorem B17720531 : Blo 1555475 17720531 := bstep (se 1 (by rfl) ⟨13290398, by rfl⟩ : syracuseStep 17720531 = 26580797) B26580797
theorem B3941743 : Blo 1555475 3941743 := bstep (se 1 (by rfl) ⟨2956307, by rfl⟩ : syracuseStep 3941743 = 5912615) B5912615
theorem B25257595 : Blo 1555475 25257595 := bstep (se 1 (by rfl) ⟨18943196, by rfl⟩ : syracuseStep 25257595 = 37886393) B37886393
theorem B3942017 : Blo 1555475 3942017 := bstep (se 2 (by rfl) ⟨1478256, by rfl⟩ : syracuseStep 3942017 = 2956513) B2956513
theorem B3500207 : Blo 1555475 3500207 := bstep (se 1 (by rfl) ⟨2625155, by rfl⟩ : syracuseStep 3500207 = 5250311) B5250311
theorem B8866007 : Blo 1555475 8866007 := bstep (se 1 (by rfl) ⟨6649505, by rfl⟩ : syracuseStep 8866007 = 13299011) B13299011
theorem B3738079 : Blo 1555475 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B5253875 : Blo 1555475 5253875 := bstep (se 1 (by rfl) ⟨3940406, by rfl⟩ : syracuseStep 5253875 = 7880813) B7880813
theorem B13470895 : Blo 1555475 13470895 := bstep (se 1 (by rfl) ⟨10103171, by rfl⟩ : syracuseStep 13470895 = 20206343) B20206343
theorem B5909881 : Blo 1555475 5909881 := bstep (se 2 (by rfl) ⟨2216205, by rfl⟩ : syracuseStep 5909881 = 4432411) B4432411
theorem B3550591 : Blo 1555475 3550591 := bstep (se 1 (by rfl) ⟨2662943, by rfl⟩ : syracuseStep 3550591 = 5325887) B5325887
theorem B14954159 : Blo 1555475 14954159 := bstep (se 1 (by rfl) ⟨11215619, by rfl⟩ : syracuseStep 14954159 = 22431239) B22431239
theorem B3501935 : Blo 1555475 3501935 := bstep (se 1 (by rfl) ⟨2626451, by rfl⟩ : syracuseStep 3501935 = 5252903) B5252903
theorem B2625439 : Blo 1555475 2625439 := bstep (se 1 (by rfl) ⟨1969079, by rfl⟩ : syracuseStep 2625439 = 3938159) B3938159
theorem B7475159 : Blo 1555475 7475159 := bstep (se 1 (by rfl) ⟨5606369, by rfl⟩ : syracuseStep 7475159 = 11212739) B11212739
theorem B7991273 : Blo 1555475 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B4984811 : Blo 1555475 4984811 := bstep (se 1 (by rfl) ⟨3738608, by rfl⟩ : syracuseStep 4984811 = 7477217) B7477217
theorem B4984823 : Blo 1555475 4984823 := bstep (se 1 (by rfl) ⟨3738617, by rfl⟩ : syracuseStep 4984823 = 7477235) B7477235
theorem B11817089 : Blo 1555475 11817089 := bstep (se 2 (by rfl) ⟨4431408, by rfl⟩ : syracuseStep 11817089 = 8862817) B8862817
theorem B25587851 : Blo 1555475 25587851 := bstep (se 1 (by rfl) ⟨19190888, by rfl⟩ : syracuseStep 25587851 = 38381777) B38381777
theorem B1970335 : Blo 1555475 1970335 := bstep (se 1 (by rfl) ⟨1477751, by rfl⟩ : syracuseStep 1970335 = 2955503) B2955503
theorem B13292039 : Blo 1555475 13292039 := bstep (se 1 (by rfl) ⟨9969029, by rfl⟩ : syracuseStep 13292039 = 19938059) B19938059
theorem B2626175 : Blo 1555475 2626175 := bstep (se 1 (by rfl) ⟨1969631, by rfl⟩ : syracuseStep 2626175 = 3939263) B3939263
theorem B8860427 : Blo 1555475 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B1970983 : Blo 1555475 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B5256359 : Blo 1555475 5256359 := bstep (se 1 (by rfl) ⟨3942269, by rfl⟩ : syracuseStep 5256359 = 7884539) B7884539
theorem B7877897 : Blo 1555475 7877897 := bstep (se 2 (by rfl) ⟨2954211, by rfl⟩ : syracuseStep 7877897 = 5908423) B5908423
theorem B1750351 : Blo 1555475 1750351 := bstep (se 1 (by rfl) ⟨1312763, by rfl⟩ : syracuseStep 1750351 = 2625527) B2625527
theorem B11818547 : Blo 1555475 11818547 := bstep (se 1 (by rfl) ⟨8863910, by rfl⟩ : syracuseStep 11818547 = 17727821) B17727821
theorem B3503807 : Blo 1555475 3503807 := bstep (se 1 (by rfl) ⟨2627855, by rfl⟩ : syracuseStep 3503807 = 5255711) B5255711
theorem B2955017 : Blo 1555475 2955017 := bstep (se 2 (by rfl) ⟨1108131, by rfl⟩ : syracuseStep 2955017 = 2216263) B2216263
theorem B29915243 : Blo 1555475 29915243 := bstep (se 1 (by rfl) ⟨22436432, by rfl⟩ : syracuseStep 29915243 = 44872865) B44872865
theorem B1751215 : Blo 1555475 1751215 := bstep (se 1 (by rfl) ⟨1313411, by rfl⟩ : syracuseStep 1751215 = 2626823) B2626823
theorem B14965231 : Blo 1555475 14965231 := bstep (se 1 (by rfl) ⟨11223923, by rfl⟩ : syracuseStep 14965231 = 22447847) B22447847
theorem B207444503 : Blo 1555475 207444503 := bstep (se 1 (by rfl) ⟨155583377, by rfl⟩ : syracuseStep 207444503 = 311166755) B311166755
theorem B2333231 : Blo 1555475 2333231 := bstep (se 1 (by rfl) ⟨1749923, by rfl⟩ : syracuseStep 2333231 = 3499847) B3499847
theorem B1751719 : Blo 1555475 1751719 := bstep (se 1 (by rfl) ⟨1313789, by rfl⟩ : syracuseStep 1751719 = 2627579) B2627579
theorem B4733659 : Blo 1555475 4733659 := bstep (se 1 (by rfl) ⟨3550244, by rfl⟩ : syracuseStep 4733659 = 7100489) B7100489
theorem B2333417 : Blo 1555475 2333417 := bstep (se 2 (by rfl) ⟨875031, by rfl⟩ : syracuseStep 2333417 = 1750063) B1750063
theorem B2333543 : Blo 1555475 2333543 := bstep (se 1 (by rfl) ⟨1750157, by rfl⟩ : syracuseStep 2333543 = 3500315) B3500315
theorem B2333639 : Blo 1555475 2333639 := bstep (se 1 (by rfl) ⟨1750229, by rfl⟩ : syracuseStep 2333639 = 3500459) B3500459
theorem B6650873 : Blo 1555475 6650873 := bstep (se 2 (by rfl) ⟨2494077, by rfl⟩ : syracuseStep 6650873 = 4988155) B4988155
theorem B11812229 : Blo 1555475 11812229 := bstep (se 4 (by rfl) ⟨1107396, by rfl⟩ : syracuseStep 11812229 = 2214793) B2214793
theorem B3939911 : Blo 1555475 3939911 := bstep (se 1 (by rfl) ⟨2954933, by rfl⟩ : syracuseStep 3939911 = 5909867) B5909867
theorem B1556175 : Blo 1555475 1556175 := bstep (se 1 (by rfl) ⟨1167131, by rfl⟩ : syracuseStep 1556175 = 2334263) B2334263
theorem B1556223 : Blo 1555475 1556223 := bstep (se 1 (by rfl) ⟨1167167, by rfl⟩ : syracuseStep 1556223 = 2334335) B2334335
theorem B1556287 : Blo 1555475 1556287 := bstep (se 1 (by rfl) ⟨1167215, by rfl⟩ : syracuseStep 1556287 = 2334431) B2334431
theorem B5250959 : Blo 1555475 5250959 := bstep (se 1 (by rfl) ⟨3938219, by rfl⟩ : syracuseStep 5250959 = 7876439) B7876439
theorem B2334713 : Blo 1555475 2334713 := bstep (se 2 (by rfl) ⟨875517, by rfl⟩ : syracuseStep 2334713 = 1751035) B1751035
theorem B5251067 : Blo 1555475 5251067 := bstep (se 1 (by rfl) ⟨3938300, by rfl⟩ : syracuseStep 5251067 = 7876601) B7876601
theorem B1556527 : Blo 1555475 1556527 := bstep (se 1 (by rfl) ⟨1167395, by rfl⟩ : syracuseStep 1556527 = 2334791) B2334791
theorem B2334953 : Blo 1555475 2334953 := bstep (se 2 (by rfl) ⟨875607, by rfl⟩ : syracuseStep 2334953 = 1751215) B1751215
theorem B102384047 : Blo 1555475 102384047 := bstep (se 1 (by rfl) ⟨76788035, by rfl⟩ : syracuseStep 102384047 = 153576071) B153576071
theorem B1556991 : Blo 1555475 1556991 := bstep (se 1 (by rfl) ⟨1167743, by rfl⟩ : syracuseStep 1556991 = 2335487) B2335487
theorem B5906951 : Blo 1555475 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B1557147 : Blo 1555475 1557147 := bstep (se 1 (by rfl) ⟨1167860, by rfl⟩ : syracuseStep 1557147 = 2335721) B2335721
theorem B1557151 : Blo 1555475 1557151 := bstep (se 1 (by rfl) ⟨1167863, by rfl⟩ : syracuseStep 1557151 = 2335727) B2335727
theorem B1557183 : Blo 1555475 1557183 := bstep (se 1 (by rfl) ⟨1167887, by rfl⟩ : syracuseStep 1557183 = 2335775) B2335775
theorem B1557223 : Blo 1555475 1557223 := bstep (se 1 (by rfl) ⟨1167917, by rfl⟩ : syracuseStep 1557223 = 2335835) B2335835
theorem B11813687 : Blo 1555475 11813687 := bstep (se 1 (by rfl) ⟨8860265, by rfl⟩ : syracuseStep 11813687 = 17720531) B17720531
theorem B5251931 : Blo 1555475 5251931 := bstep (se 1 (by rfl) ⟨3938948, by rfl⟩ : syracuseStep 5251931 = 7877897) B7877897
theorem B2335625 : Blo 1555475 2335625 := bstep (se 2 (by rfl) ⟨875859, by rfl⟩ : syracuseStep 2335625 = 1751719) B1751719
theorem B2335871 : Blo 1555475 2335871 := bstep (se 1 (by rfl) ⟨1751903, by rfl⟩ : syracuseStep 2335871 = 3503807) B3503807
theorem B4433915 : Blo 1555475 4433915 := bstep (se 1 (by rfl) ⟨3325436, by rfl⟩ : syracuseStep 4433915 = 6650873) B6650873
theorem B7874819 : Blo 1555475 7874819 := bstep (se 1 (by rfl) ⟨5906114, by rfl⟩ : syracuseStep 7874819 = 11812229) B11812229
theorem B3500585 : Blo 1555475 3500585 := bstep (se 2 (by rfl) ⟨1312719, by rfl⟩ : syracuseStep 3500585 = 2625439) B2625439
theorem B3500639 : Blo 1555475 3500639 := bstep (se 1 (by rfl) ⟨2625479, by rfl⟩ : syracuseStep 3500639 = 5250959) B5250959
theorem B4983439 : Blo 1555475 4983439 := bstep (se 1 (by rfl) ⟨3737579, by rfl⟩ : syracuseStep 4983439 = 7475159) B7475159
theorem B5327515 : Blo 1555475 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B3500711 : Blo 1555475 3500711 := bstep (se 1 (by rfl) ⟨2625533, by rfl⟩ : syracuseStep 3500711 = 5251067) B5251067
theorem B10792061 : Blo 1555475 10792061 := bstep (se 3 (by rfl) ⟨2023511, by rfl⟩ : syracuseStep 10792061 = 4047023) B4047023
theorem B4984105 : Blo 1555475 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B5910185 : Blo 1555475 5910185 := bstep (se 2 (by rfl) ⟨2216319, by rfl⟩ : syracuseStep 5910185 = 4432639) B4432639
theorem B8859401 : Blo 1555475 8859401 := bstep (se 2 (by rfl) ⟨3322275, by rfl⟩ : syracuseStep 8859401 = 6644551) B6644551
theorem B1970011 : Blo 1555475 1970011 := bstep (se 1 (by rfl) ⟨1477508, by rfl⟩ : syracuseStep 1970011 = 2955017) B2955017
theorem B19943495 : Blo 1555475 19943495 := bstep (se 1 (by rfl) ⟨14957621, by rfl⟩ : syracuseStep 19943495 = 29915243) B29915243
theorem B272937077 : Blo 1555475 272937077 := bstep (se 5 (by rfl) ⟨12793925, by rfl⟩ : syracuseStep 272937077 = 25587851) B25587851
theorem B5910671 : Blo 1555475 5910671 := bstep (se 1 (by rfl) ⟨4433003, by rfl⟩ : syracuseStep 5910671 = 8866007) B8866007
theorem B17961193 : Blo 1555475 17961193 := bstep (se 2 (by rfl) ⟨6735447, by rfl⟩ : syracuseStep 17961193 = 13470895) B13470895
theorem B5255657 : Blo 1555475 5255657 := bstep (se 2 (by rfl) ⟨1970871, by rfl⟩ : syracuseStep 5255657 = 3941743) B3941743
theorem B3502583 : Blo 1555475 3502583 := bstep (se 1 (by rfl) ⟨2626937, by rfl⟩ : syracuseStep 3502583 = 5253875) B5253875
theorem B2626607 : Blo 1555475 2626607 := bstep (se 1 (by rfl) ⟨1969955, by rfl⟩ : syracuseStep 2626607 = 3939911) B3939911
theorem B3323207 : Blo 1555475 3323207 := bstep (se 1 (by rfl) ⟨2492405, by rfl⟩ : syracuseStep 3323207 = 4984811) B4984811
theorem B3323215 : Blo 1555475 3323215 := bstep (se 1 (by rfl) ⟨2492411, by rfl⟩ : syracuseStep 3323215 = 4984823) B4984823
theorem B7878059 : Blo 1555475 7878059 := bstep (se 1 (by rfl) ⟨5908544, by rfl⟩ : syracuseStep 7878059 = 11817089) B11817089
theorem B2627113 : Blo 1555475 2627113 := bstep (se 2 (by rfl) ⟨985167, by rfl⟩ : syracuseStep 2627113 = 1970335) B1970335
theorem B8861359 : Blo 1555475 8861359 := bstep (se 1 (by rfl) ⟨6646019, by rfl⟩ : syracuseStep 8861359 = 13292039) B13292039
theorem B1750783 : Blo 1555475 1750783 := bstep (se 1 (by rfl) ⟨1313087, by rfl⟩ : syracuseStep 1750783 = 2626175) B2626175
theorem B19953641 : Blo 1555475 19953641 := bstep (se 2 (by rfl) ⟨7482615, by rfl⟩ : syracuseStep 19953641 = 14965231) B14965231
theorem B3504239 : Blo 1555475 3504239 := bstep (se 1 (by rfl) ⟨2628179, by rfl⟩ : syracuseStep 3504239 = 5256359) B5256359
theorem B7879031 : Blo 1555475 7879031 := bstep (se 1 (by rfl) ⟨5909273, by rfl⟩ : syracuseStep 7879031 = 11818547) B11818547
theorem B2627977 : Blo 1555475 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B2628011 : Blo 1555475 2628011 := bstep (se 1 (by rfl) ⟨1971008, by rfl⟩ : syracuseStep 2628011 = 3942017) B3942017
theorem B25246181 : Blo 1555475 25246181 := bstep (se 4 (by rfl) ⟨2366829, by rfl⟩ : syracuseStep 25246181 = 4733659) B4733659
theorem B2333471 : Blo 1555475 2333471 := bstep (se 1 (by rfl) ⟨1750103, by rfl⟩ : syracuseStep 2333471 = 3500207) B3500207
theorem B138296335 : Blo 1555475 138296335 := bstep (se 1 (by rfl) ⟨103722251, by rfl⟩ : syracuseStep 138296335 = 207444503) B207444503
theorem B1555487 : Blo 1555475 1555487 := bstep (se 1 (by rfl) ⟨1166615, by rfl⟩ : syracuseStep 1555487 = 2333231) B2333231
theorem B2333801 : Blo 1555475 2333801 := bstep (se 2 (by rfl) ⟨875175, by rfl⟩ : syracuseStep 2333801 = 1750351) B1750351
theorem B39877757 : Blo 1555475 39877757 := bstep (se 3 (by rfl) ⟨7477079, by rfl⟩ : syracuseStep 39877757 = 14954159) B14954159
theorem B1555611 : Blo 1555475 1555611 := bstep (se 1 (by rfl) ⟨1166708, by rfl⟩ : syracuseStep 1555611 = 2333417) B2333417
theorem B7879841 : Blo 1555475 7879841 := bstep (se 2 (by rfl) ⟨2954940, by rfl⟩ : syracuseStep 7879841 = 5909881) B5909881
theorem B4734121 : Blo 1555475 4734121 := bstep (se 2 (by rfl) ⟨1775295, by rfl⟩ : syracuseStep 4734121 = 3550591) B3550591
theorem B1555695 : Blo 1555475 1555695 := bstep (se 1 (by rfl) ⟨1166771, by rfl⟩ : syracuseStep 1555695 = 2333543) B2333543
theorem B1555759 : Blo 1555475 1555759 := bstep (se 1 (by rfl) ⟨1166819, by rfl⟩ : syracuseStep 1555759 = 2333639) B2333639
theorem B1556475 : Blo 1555475 1556475 := bstep (se 1 (by rfl) ⟨1167356, by rfl⟩ : syracuseStep 1556475 = 2334713) B2334713
theorem B33676793 : Blo 1555475 33676793 := bstep (se 2 (by rfl) ⟨12628797, by rfl⟩ : syracuseStep 33676793 = 25257595) B25257595
theorem B2334623 : Blo 1555475 2334623 := bstep (se 1 (by rfl) ⟨1750967, by rfl⟩ : syracuseStep 2334623 = 3501935) B3501935
theorem B13295663 : Blo 1555475 13295663 := bstep (se 1 (by rfl) ⟨9971747, by rfl⟩ : syracuseStep 13295663 = 19943495) B19943495
theorem B3940447 : Blo 1555475 3940447 := bstep (se 1 (by rfl) ⟨2955335, by rfl⟩ : syracuseStep 3940447 = 5910671) B5910671
theorem B1556635 : Blo 1555475 1556635 := bstep (se 1 (by rfl) ⟨1167476, by rfl⟩ : syracuseStep 1556635 = 2334953) B2334953
theorem B68256031 : Blo 1555475 68256031 := bstep (se 1 (by rfl) ⟨51192023, by rfl⟩ : syracuseStep 68256031 = 102384047) B102384047
theorem B2335055 : Blo 1555475 2335055 := bstep (se 1 (by rfl) ⟨1751291, by rfl⟩ : syracuseStep 2335055 = 3502583) B3502583
theorem B1557083 : Blo 1555475 1557083 := bstep (se 1 (by rfl) ⟨1167812, by rfl⟩ : syracuseStep 1557083 = 2335625) B2335625
theorem B1557247 : Blo 1555475 1557247 := bstep (se 1 (by rfl) ⟨1167935, by rfl⟩ : syracuseStep 1557247 = 2335871) B2335871
theorem B6644585 : Blo 1555475 6644585 := bstep (se 2 (by rfl) ⟨2491719, by rfl⟩ : syracuseStep 6644585 = 4983439) B4983439
theorem B5252039 : Blo 1555475 5252039 := bstep (se 1 (by rfl) ⟨3939029, by rfl⟩ : syracuseStep 5252039 = 7878059) B7878059
theorem B184395113 : Blo 1555475 184395113 := bstep (se 2 (by rfl) ⟨69148167, by rfl⟩ : syracuseStep 184395113 = 138296335) B138296335
theorem B2336159 : Blo 1555475 2336159 := bstep (se 1 (by rfl) ⟨1752119, by rfl⟩ : syracuseStep 2336159 = 3504239) B3504239
theorem B5252687 : Blo 1555475 5252687 := bstep (se 1 (by rfl) ⟨3939515, by rfl⟩ : syracuseStep 5252687 = 7879031) B7879031
theorem B6645473 : Blo 1555475 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B26585171 : Blo 1555475 26585171 := bstep (se 1 (by rfl) ⟨19938878, by rfl⟩ : syracuseStep 26585171 = 39877757) B39877757
theorem B7194707 : Blo 1555475 7194707 := bstep (se 1 (by rfl) ⟨5396030, by rfl⟩ : syracuseStep 7194707 = 10792061) B10792061
theorem B5253227 : Blo 1555475 5253227 := bstep (se 1 (by rfl) ⟨3939920, by rfl⟩ : syracuseStep 5253227 = 7879841) B7879841
theorem B11815145 : Blo 1555475 11815145 := bstep (se 2 (by rfl) ⟨4430679, by rfl⟩ : syracuseStep 11815145 = 8861359) B8861359
theorem B7875791 : Blo 1555475 7875791 := bstep (se 1 (by rfl) ⟨5906843, by rfl⟩ : syracuseStep 7875791 = 11813687) B11813687
theorem B3501287 : Blo 1555475 3501287 := bstep (se 1 (by rfl) ⟨2625965, by rfl⟩ : syracuseStep 3501287 = 5251931) B5251931
theorem B28413413 : Blo 1555475 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B95793029 : Blo 1555475 95793029 := bstep (se 4 (by rfl) ⟨8980596, by rfl⟩ : syracuseStep 95793029 = 17961193) B17961193
theorem B6312161 : Blo 1555475 6312161 := bstep (se 2 (by rfl) ⟨2367060, by rfl⟩ : syracuseStep 6312161 = 4734121) B4734121
theorem B16830787 : Blo 1555475 16830787 := bstep (se 1 (by rfl) ⟨12623090, by rfl⟩ : syracuseStep 16830787 = 25246181) B25246181
theorem B3502817 : Blo 1555475 3502817 := bstep (se 2 (by rfl) ⟨1313556, by rfl⟩ : syracuseStep 3502817 = 2627113) B2627113
theorem B22451195 : Blo 1555475 22451195 := bstep (se 1 (by rfl) ⟨16838396, by rfl⟩ : syracuseStep 22451195 = 33676793) B33676793
theorem B2626681 : Blo 1555475 2626681 := bstep (se 2 (by rfl) ⟨985005, by rfl⟩ : syracuseStep 2626681 = 1970011) B1970011
theorem B181958051 : Blo 1555475 181958051 := bstep (se 1 (by rfl) ⟨136468538, by rfl⟩ : syracuseStep 181958051 = 272937077) B272937077
theorem B3503771 : Blo 1555475 3503771 := bstep (se 1 (by rfl) ⟨2627828, by rfl⟩ : syracuseStep 3503771 = 5255657) B5255657
theorem B3937967 : Blo 1555475 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B3503969 : Blo 1555475 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B1751071 : Blo 1555475 1751071 := bstep (se 1 (by rfl) ⟨1313303, by rfl⟩ : syracuseStep 1751071 = 2626607) B2626607
theorem B8861885 : Blo 1555475 8861885 := bstep (se 3 (by rfl) ⟨1661603, by rfl⟩ : syracuseStep 8861885 = 3323207) B3323207
theorem B13302427 : Blo 1555475 13302427 := bstep (se 1 (by rfl) ⟨9976820, by rfl⟩ : syracuseStep 13302427 = 19953641) B19953641
theorem B2955943 : Blo 1555475 2955943 := bstep (se 1 (by rfl) ⟨2216957, by rfl⟩ : syracuseStep 2955943 = 4433915) B4433915
theorem B5249879 : Blo 1555475 5249879 := bstep (se 1 (by rfl) ⟨3937409, by rfl⟩ : syracuseStep 5249879 = 7874819) B7874819
theorem B1752007 : Blo 1555475 1752007 := bstep (se 1 (by rfl) ⟨1314005, by rfl⟩ : syracuseStep 1752007 = 2628011) B2628011
theorem B2333723 : Blo 1555475 2333723 := bstep (se 1 (by rfl) ⟨1750292, by rfl⟩ : syracuseStep 2333723 = 3500585) B3500585
theorem B2333759 : Blo 1555475 2333759 := bstep (se 1 (by rfl) ⟨1750319, by rfl⟩ : syracuseStep 2333759 = 3500639) B3500639
theorem B4430953 : Blo 1555475 4430953 := bstep (se 2 (by rfl) ⟨1661607, by rfl⟩ : syracuseStep 4430953 = 3323215) B3323215
theorem B2333807 : Blo 1555475 2333807 := bstep (se 1 (by rfl) ⟨1750355, by rfl⟩ : syracuseStep 2333807 = 3500711) B3500711
theorem B1555647 : Blo 1555475 1555647 := bstep (se 1 (by rfl) ⟨1166735, by rfl⟩ : syracuseStep 1555647 = 2333471) B2333471
theorem B1555867 : Blo 1555475 1555867 := bstep (se 1 (by rfl) ⟨1166900, by rfl⟩ : syracuseStep 1555867 = 2333801) B2333801
theorem B2334377 : Blo 1555475 2334377 := bstep (se 2 (by rfl) ⟨875391, by rfl⟩ : syracuseStep 2334377 = 1750783) B1750783
theorem B3940123 : Blo 1555475 3940123 := bstep (se 1 (by rfl) ⟨2955092, by rfl⟩ : syracuseStep 3940123 = 5910185) B5910185
theorem B5906267 : Blo 1555475 5906267 := bstep (se 1 (by rfl) ⟨4429700, by rfl⟩ : syracuseStep 5906267 = 8859401) B8859401
theorem B1556415 : Blo 1555475 1556415 := bstep (se 1 (by rfl) ⟨1167311, by rfl⟩ : syracuseStep 1556415 = 2334623) B2334623
theorem B8863775 : Blo 1555475 8863775 := bstep (se 1 (by rfl) ⟨6647831, by rfl⟩ : syracuseStep 8863775 = 13295663) B13295663
theorem B2334761 : Blo 1555475 2334761 := bstep (se 2 (by rfl) ⟨875535, by rfl⟩ : syracuseStep 2334761 = 1751071) B1751071
theorem B1556703 : Blo 1555475 1556703 := bstep (se 1 (by rfl) ⟨1167527, by rfl⟩ : syracuseStep 1556703 = 2335055) B2335055
theorem B2335211 : Blo 1555475 2335211 := bstep (se 1 (by rfl) ⟨1751408, by rfl⟩ : syracuseStep 2335211 = 3502817) B3502817
theorem B14967463 : Blo 1555475 14967463 := bstep (se 1 (by rfl) ⟨11225597, by rfl⟩ : syracuseStep 14967463 = 22451195) B22451195
theorem B17736569 : Blo 1555475 17736569 := bstep (se 2 (by rfl) ⟨6651213, by rfl⟩ : syracuseStep 17736569 = 13302427) B13302427
theorem B3941257 : Blo 1555475 3941257 := bstep (se 2 (by rfl) ⟨1477971, by rfl⟩ : syracuseStep 3941257 = 2955943) B2955943
theorem B122930075 : Blo 1555475 122930075 := bstep (se 1 (by rfl) ⟨92197556, by rfl⟩ : syracuseStep 122930075 = 184395113) B184395113
theorem B1557439 : Blo 1555475 1557439 := bstep (se 1 (by rfl) ⟨1168079, by rfl⟩ : syracuseStep 1557439 = 2336159) B2336159
theorem B2335847 : Blo 1555475 2335847 := bstep (se 1 (by rfl) ⟨1751885, by rfl⟩ : syracuseStep 2335847 = 3503771) B3503771
theorem B2335979 : Blo 1555475 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B2336009 : Blo 1555475 2336009 := bstep (se 2 (by rfl) ⟨876003, by rfl⟩ : syracuseStep 2336009 = 1752007) B1752007
theorem B5907923 : Blo 1555475 5907923 := bstep (se 1 (by rfl) ⟨4430942, by rfl⟩ : syracuseStep 5907923 = 8861885) B8861885
theorem B5907937 : Blo 1555475 5907937 := bstep (se 2 (by rfl) ⟨2215476, by rfl⟩ : syracuseStep 5907937 = 4430953) B4430953
theorem B3499919 : Blo 1555475 3499919 := bstep (se 1 (by rfl) ⟨2624939, by rfl⟩ : syracuseStep 3499919 = 5249879) B5249879
theorem B18942275 : Blo 1555475 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B5253497 : Blo 1555475 5253497 := bstep (se 2 (by rfl) ⟨1970061, by rfl⟩ : syracuseStep 5253497 = 3940123) B3940123
theorem B5253929 : Blo 1555475 5253929 := bstep (se 2 (by rfl) ⟨1970223, by rfl⟩ : syracuseStep 5253929 = 3940447) B3940447
theorem B91008041 : Blo 1555475 91008041 := bstep (se 2 (by rfl) ⟨34128015, by rfl⟩ : syracuseStep 91008041 = 68256031) B68256031
theorem B22441049 : Blo 1555475 22441049 := bstep (se 2 (by rfl) ⟨8415393, by rfl⟩ : syracuseStep 22441049 = 16830787) B16830787
theorem B3501359 : Blo 1555475 3501359 := bstep (se 1 (by rfl) ⟨2626019, by rfl⟩ : syracuseStep 3501359 = 5252039) B5252039
theorem B3501791 : Blo 1555475 3501791 := bstep (se 1 (by rfl) ⟨2626343, by rfl⟩ : syracuseStep 3501791 = 5252687) B5252687
theorem B2625311 : Blo 1555475 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B17723447 : Blo 1555475 17723447 := bstep (se 1 (by rfl) ⟨13292585, by rfl⟩ : syracuseStep 17723447 = 26585171) B26585171
theorem B4796471 : Blo 1555475 4796471 := bstep (se 1 (by rfl) ⟨3597353, by rfl⟩ : syracuseStep 4796471 = 7194707) B7194707
theorem B3502151 : Blo 1555475 3502151 := bstep (se 1 (by rfl) ⟨2626613, by rfl⟩ : syracuseStep 3502151 = 5253227) B5253227
theorem B7876763 : Blo 1555475 7876763 := bstep (se 1 (by rfl) ⟨5907572, by rfl⟩ : syracuseStep 7876763 = 11815145) B11815145
theorem B3502241 : Blo 1555475 3502241 := bstep (se 2 (by rfl) ⟨1313340, by rfl⟩ : syracuseStep 3502241 = 2626681) B2626681
theorem B3937511 : Blo 1555475 3937511 := bstep (se 1 (by rfl) ⟨2953133, by rfl⟩ : syracuseStep 3937511 = 5906267) B5906267
theorem B63862019 : Blo 1555475 63862019 := bstep (se 1 (by rfl) ⟨47896514, by rfl⟩ : syracuseStep 63862019 = 95793029) B95793029
theorem B4208107 : Blo 1555475 4208107 := bstep (se 1 (by rfl) ⟨3156080, by rfl⟩ : syracuseStep 4208107 = 6312161) B6312161
theorem B4429723 : Blo 1555475 4429723 := bstep (se 1 (by rfl) ⟨3322292, by rfl⟩ : syracuseStep 4429723 = 6644585) B6644585
theorem B121305367 : Blo 1555475 121305367 := bstep (se 1 (by rfl) ⟨90979025, by rfl⟩ : syracuseStep 121305367 = 181958051) B181958051
theorem B4430315 : Blo 1555475 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B1555815 : Blo 1555475 1555815 := bstep (se 1 (by rfl) ⟨1166861, by rfl⟩ : syracuseStep 1555815 = 2333723) B2333723
theorem B1555839 : Blo 1555475 1555839 := bstep (se 1 (by rfl) ⟨1166879, by rfl⟩ : syracuseStep 1555839 = 2333759) B2333759
theorem B1555871 : Blo 1555475 1555871 := bstep (se 1 (by rfl) ⟨1166903, by rfl⟩ : syracuseStep 1555871 = 2333807) B2333807
theorem B5250527 : Blo 1555475 5250527 := bstep (se 1 (by rfl) ⟨3937895, by rfl⟩ : syracuseStep 5250527 = 7875791) B7875791
theorem B2334191 : Blo 1555475 2334191 := bstep (se 1 (by rfl) ⟨1750643, by rfl⟩ : syracuseStep 2334191 = 3501287) B3501287
theorem B1556251 : Blo 1555475 1556251 := bstep (se 1 (by rfl) ⟨1167188, by rfl⟩ : syracuseStep 1556251 = 2334377) B2334377
theorem B1556507 : Blo 1555475 1556507 := bstep (se 1 (by rfl) ⟨1167380, by rfl⟩ : syracuseStep 1556507 = 2334761) B2334761
theorem B2334767 : Blo 1555475 2334767 := bstep (se 1 (by rfl) ⟨1751075, by rfl⟩ : syracuseStep 2334767 = 3502151) B3502151
theorem B5251175 : Blo 1555475 5251175 := bstep (se 1 (by rfl) ⟨3938381, by rfl⟩ : syracuseStep 5251175 = 7876763) B7876763
theorem B2334827 : Blo 1555475 2334827 := bstep (se 1 (by rfl) ⟨1751120, by rfl⟩ : syracuseStep 2334827 = 3502241) B3502241
theorem B242688109 : Blo 1555475 242688109 := bstep (se 3 (by rfl) ⟨45504020, by rfl⟩ : syracuseStep 242688109 = 91008041) B91008041
theorem B1556807 : Blo 1555475 1556807 := bstep (se 1 (by rfl) ⟨1167605, by rfl⟩ : syracuseStep 1556807 = 2335211) B2335211
theorem B81953383 : Blo 1555475 81953383 := bstep (se 1 (by rfl) ⟨61465037, by rfl⟩ : syracuseStep 81953383 = 122930075) B122930075
theorem B1557231 : Blo 1555475 1557231 := bstep (se 1 (by rfl) ⟨1167923, by rfl⟩ : syracuseStep 1557231 = 2335847) B2335847
theorem B1557319 : Blo 1555475 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B42574679 : Blo 1555475 42574679 := bstep (se 1 (by rfl) ⟨31931009, by rfl⟩ : syracuseStep 42574679 = 63862019) B63862019
theorem B1557339 : Blo 1555475 1557339 := bstep (se 1 (by rfl) ⟨1168004, by rfl⟩ : syracuseStep 1557339 = 2336009) B2336009
theorem B19956617 : Blo 1555475 19956617 := bstep (se 2 (by rfl) ⟨7483731, by rfl⟩ : syracuseStep 19956617 = 14967463) B14967463
theorem B11814173 : Blo 1555475 11814173 := bstep (se 3 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 11814173 = 4430315) B4430315
theorem B14960699 : Blo 1555475 14960699 := bstep (se 1 (by rfl) ⟨11220524, by rfl⟩ : syracuseStep 14960699 = 22441049) B22441049
theorem B3500351 : Blo 1555475 3500351 := bstep (se 1 (by rfl) ⟨2625263, by rfl⟩ : syracuseStep 3500351 = 5250527) B5250527
theorem B5909183 : Blo 1555475 5909183 := bstep (se 1 (by rfl) ⟨4431887, by rfl⟩ : syracuseStep 5909183 = 8863775) B8863775
theorem B11815631 : Blo 1555475 11815631 := bstep (se 1 (by rfl) ⟨8861723, by rfl⟩ : syracuseStep 11815631 = 17723447) B17723447
theorem B3197647 : Blo 1555475 3197647 := bstep (se 1 (by rfl) ⟨2398235, by rfl⟩ : syracuseStep 3197647 = 4796471) B4796471
theorem B11824379 : Blo 1555475 11824379 := bstep (se 1 (by rfl) ⟨8868284, by rfl⟩ : syracuseStep 11824379 = 17736569) B17736569
theorem B2625007 : Blo 1555475 2625007 := bstep (se 1 (by rfl) ⟨1968755, by rfl⟩ : syracuseStep 2625007 = 3937511) B3937511
theorem B5255009 : Blo 1555475 5255009 := bstep (se 2 (by rfl) ⟨1970628, by rfl⟩ : syracuseStep 5255009 = 3941257) B3941257
theorem B12628183 : Blo 1555475 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B3502331 : Blo 1555475 3502331 := bstep (se 1 (by rfl) ⟨2626748, by rfl⟩ : syracuseStep 3502331 = 5253497) B5253497
theorem B3502619 : Blo 1555475 3502619 := bstep (se 1 (by rfl) ⟨2626964, by rfl⟩ : syracuseStep 3502619 = 5253929) B5253929
theorem B7877249 : Blo 1555475 7877249 := bstep (se 2 (by rfl) ⟨2953968, by rfl⟩ : syracuseStep 7877249 = 5907937) B5907937
theorem B1750207 : Blo 1555475 1750207 := bstep (se 1 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 1750207 = 2625311) B2625311
theorem B161740489 : Blo 1555475 161740489 := bstep (se 2 (by rfl) ⟨60652683, by rfl⟩ : syracuseStep 161740489 = 121305367) B121305367
theorem B3938615 : Blo 1555475 3938615 := bstep (se 1 (by rfl) ⟨2953961, by rfl⟩ : syracuseStep 3938615 = 5907923) B5907923
theorem B2333279 : Blo 1555475 2333279 := bstep (se 1 (by rfl) ⟨1749959, by rfl⟩ : syracuseStep 2333279 = 3499919) B3499919
theorem B5610809 : Blo 1555475 5610809 := bstep (se 2 (by rfl) ⟨2104053, by rfl⟩ : syracuseStep 5610809 = 4208107) B4208107
theorem B2334239 : Blo 1555475 2334239 := bstep (se 1 (by rfl) ⟨1750679, by rfl⟩ : syracuseStep 2334239 = 3501359) B3501359
theorem B1556127 : Blo 1555475 1556127 := bstep (se 1 (by rfl) ⟨1167095, by rfl⟩ : syracuseStep 1556127 = 2334191) B2334191
theorem B2334527 : Blo 1555475 2334527 := bstep (se 1 (by rfl) ⟨1750895, by rfl⟩ : syracuseStep 2334527 = 3501791) B3501791
theorem B5906297 : Blo 1555475 5906297 := bstep (se 2 (by rfl) ⟨2214861, by rfl⟩ : syracuseStep 5906297 = 4429723) B4429723
theorem B1556511 : Blo 1555475 1556511 := bstep (se 1 (by rfl) ⟨1167383, by rfl⟩ : syracuseStep 1556511 = 2334767) B2334767
theorem B1556551 : Blo 1555475 1556551 := bstep (se 1 (by rfl) ⟨1167413, by rfl⟩ : syracuseStep 1556551 = 2334827) B2334827
theorem B323584145 : Blo 1555475 323584145 := bstep (se 2 (by rfl) ⟨121344054, by rfl⟩ : syracuseStep 323584145 = 242688109) B242688109
theorem B2334887 : Blo 1555475 2334887 := bstep (se 1 (by rfl) ⟨1751165, by rfl⟩ : syracuseStep 2334887 = 3502331) B3502331
theorem B2335079 : Blo 1555475 2335079 := bstep (se 1 (by rfl) ⟨1751309, by rfl⟩ : syracuseStep 2335079 = 3502619) B3502619
theorem B5251499 : Blo 1555475 5251499 := bstep (se 1 (by rfl) ⟨3938624, by rfl⟩ : syracuseStep 5251499 = 7877249) B7877249
theorem B13304411 : Blo 1555475 13304411 := bstep (se 1 (by rfl) ⟨9978308, by rfl⟩ : syracuseStep 13304411 = 19956617) B19956617
theorem B3500009 : Blo 1555475 3500009 := bstep (se 2 (by rfl) ⟨1312503, by rfl⟩ : syracuseStep 3500009 = 2625007) B2625007
theorem B7882919 : Blo 1555475 7882919 := bstep (se 1 (by rfl) ⟨5912189, by rfl⟩ : syracuseStep 7882919 = 11824379) B11824379
theorem B3500783 : Blo 1555475 3500783 := bstep (se 1 (by rfl) ⟨2625587, by rfl⟩ : syracuseStep 3500783 = 5251175) B5251175
theorem B16837577 : Blo 1555475 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B14962157 : Blo 1555475 14962157 := bstep (se 3 (by rfl) ⟨2805404, by rfl⟩ : syracuseStep 14962157 = 5610809) B5610809
theorem B7876115 : Blo 1555475 7876115 := bstep (se 1 (by rfl) ⟨5907086, by rfl⟩ : syracuseStep 7876115 = 11814173) B11814173
theorem B4263529 : Blo 1555475 4263529 := bstep (se 2 (by rfl) ⟨1598823, by rfl⟩ : syracuseStep 4263529 = 3197647) B3197647
theorem B9973799 : Blo 1555475 9973799 := bstep (se 1 (by rfl) ⟨7480349, by rfl⟩ : syracuseStep 9973799 = 14960699) B14960699
theorem B2625743 : Blo 1555475 2625743 := bstep (se 1 (by rfl) ⟨1969307, by rfl⟩ : syracuseStep 2625743 = 3938615) B3938615
theorem B7877087 : Blo 1555475 7877087 := bstep (se 1 (by rfl) ⟨5907815, by rfl⟩ : syracuseStep 7877087 = 11815631) B11815631
theorem B3503339 : Blo 1555475 3503339 := bstep (se 1 (by rfl) ⟨2627504, by rfl⟩ : syracuseStep 3503339 = 5255009) B5255009
theorem B3937531 : Blo 1555475 3937531 := bstep (se 1 (by rfl) ⟨2953148, by rfl⟩ : syracuseStep 3937531 = 5906297) B5906297
theorem B28383119 : Blo 1555475 28383119 := bstep (se 1 (by rfl) ⟨21287339, by rfl⟩ : syracuseStep 28383119 = 42574679) B42574679
theorem B109271177 : Blo 1555475 109271177 := bstep (se 2 (by rfl) ⟨40976691, by rfl⟩ : syracuseStep 109271177 = 81953383) B81953383
theorem B2333567 : Blo 1555475 2333567 := bstep (se 1 (by rfl) ⟨1750175, by rfl⟩ : syracuseStep 2333567 = 3500351) B3500351
theorem B2333609 : Blo 1555475 2333609 := bstep (se 2 (by rfl) ⟨875103, by rfl⟩ : syracuseStep 2333609 = 1750207) B1750207
theorem B1555519 : Blo 1555475 1555519 := bstep (se 1 (by rfl) ⟨1166639, by rfl⟩ : syracuseStep 1555519 = 2333279) B2333279
theorem B3939455 : Blo 1555475 3939455 := bstep (se 1 (by rfl) ⟨2954591, by rfl⟩ : syracuseStep 3939455 = 5909183) B5909183
theorem B215653985 : Blo 1555475 215653985 := bstep (se 2 (by rfl) ⟨80870244, by rfl⟩ : syracuseStep 215653985 = 161740489) B161740489
theorem B1556159 : Blo 1555475 1556159 := bstep (se 1 (by rfl) ⟨1167119, by rfl⟩ : syracuseStep 1556159 = 2334239) B2334239
theorem B1556351 : Blo 1555475 1556351 := bstep (se 1 (by rfl) ⟨1167263, by rfl⟩ : syracuseStep 1556351 = 2334527) B2334527
theorem B1556591 : Blo 1555475 1556591 := bstep (se 1 (by rfl) ⟨1167443, by rfl⟩ : syracuseStep 1556591 = 2334887) B2334887
theorem B1556719 : Blo 1555475 1556719 := bstep (se 1 (by rfl) ⟨1167539, by rfl⟩ : syracuseStep 1556719 = 2335079) B2335079
theorem B5251391 : Blo 1555475 5251391 := bstep (se 1 (by rfl) ⟨3938543, by rfl⟩ : syracuseStep 5251391 = 7877087) B7877087
theorem B2335559 : Blo 1555475 2335559 := bstep (se 1 (by rfl) ⟨1751669, by rfl⟩ : syracuseStep 2335559 = 3503339) B3503339
theorem B11225051 : Blo 1555475 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B215722763 : Blo 1555475 215722763 := bstep (se 1 (by rfl) ⟨161792072, by rfl⟩ : syracuseStep 215722763 = 323584145) B323584145
theorem B3500999 : Blo 1555475 3500999 := bstep (se 1 (by rfl) ⟨2625749, by rfl⟩ : syracuseStep 3500999 = 5251499) B5251499
theorem B72847451 : Blo 1555475 72847451 := bstep (se 1 (by rfl) ⟨54635588, by rfl⟩ : syracuseStep 72847451 = 109271177) B109271177
theorem B5255279 : Blo 1555475 5255279 := bstep (se 1 (by rfl) ⟨3941459, by rfl⟩ : syracuseStep 5255279 = 7882919) B7882919
theorem B2626303 : Blo 1555475 2626303 := bstep (se 1 (by rfl) ⟨1969727, by rfl⟩ : syracuseStep 2626303 = 3939455) B3939455
theorem B9974771 : Blo 1555475 9974771 := bstep (se 1 (by rfl) ⟨7481078, by rfl⟩ : syracuseStep 9974771 = 14962157) B14962157
theorem B6649199 : Blo 1555475 6649199 := bstep (se 1 (by rfl) ⟨4986899, by rfl⟩ : syracuseStep 6649199 = 9973799) B9973799
theorem B1750495 : Blo 1555475 1750495 := bstep (se 1 (by rfl) ⟨1312871, by rfl⟩ : syracuseStep 1750495 = 2625743) B2625743
theorem B8869607 : Blo 1555475 8869607 := bstep (se 1 (by rfl) ⟨6652205, by rfl⟩ : syracuseStep 8869607 = 13304411) B13304411
theorem B18922079 : Blo 1555475 18922079 := bstep (se 1 (by rfl) ⟨14191559, by rfl⟩ : syracuseStep 18922079 = 28383119) B28383119
theorem B2333339 : Blo 1555475 2333339 := bstep (se 1 (by rfl) ⟨1750004, by rfl⟩ : syracuseStep 2333339 = 3500009) B3500009
theorem B5250041 : Blo 1555475 5250041 := bstep (se 2 (by rfl) ⟨1968765, by rfl⟩ : syracuseStep 5250041 = 3937531) B3937531
theorem B2333855 : Blo 1555475 2333855 := bstep (se 1 (by rfl) ⟨1750391, by rfl⟩ : syracuseStep 2333855 = 3500783) B3500783
theorem B1555711 : Blo 1555475 1555711 := bstep (se 1 (by rfl) ⟨1166783, by rfl⟩ : syracuseStep 1555711 = 2333567) B2333567
theorem B1555739 : Blo 1555475 1555739 := bstep (se 1 (by rfl) ⟨1166804, by rfl⟩ : syracuseStep 1555739 = 2333609) B2333609
theorem B5684705 : Blo 1555475 5684705 := bstep (se 2 (by rfl) ⟨2131764, by rfl⟩ : syracuseStep 5684705 = 4263529) B4263529
theorem B5250743 : Blo 1555475 5250743 := bstep (se 1 (by rfl) ⟨3938057, by rfl⟩ : syracuseStep 5250743 = 7876115) B7876115
theorem B143769323 : Blo 1555475 143769323 := bstep (se 1 (by rfl) ⟨107826992, by rfl⟩ : syracuseStep 143769323 = 215653985) B215653985
theorem B1557039 : Blo 1555475 1557039 := bstep (se 1 (by rfl) ⟨1167779, by rfl⟩ : syracuseStep 1557039 = 2335559) B2335559
theorem B4432799 : Blo 1555475 4432799 := bstep (se 1 (by rfl) ⟨3324599, by rfl⟩ : syracuseStep 4432799 = 6649199) B6649199
theorem B3500027 : Blo 1555475 3500027 := bstep (se 1 (by rfl) ⟨2625020, by rfl⟩ : syracuseStep 3500027 = 5250041) B5250041
theorem B3500495 : Blo 1555475 3500495 := bstep (se 1 (by rfl) ⟨2625371, by rfl⟩ : syracuseStep 3500495 = 5250743) B5250743
theorem B48564967 : Blo 1555475 48564967 := bstep (se 1 (by rfl) ⟨36423725, by rfl⟩ : syracuseStep 48564967 = 72847451) B72847451
theorem B3500927 : Blo 1555475 3500927 := bstep (se 1 (by rfl) ⟨2625695, by rfl⟩ : syracuseStep 3500927 = 5251391) B5251391
theorem B3501737 : Blo 1555475 3501737 := bstep (se 2 (by rfl) ⟨1313151, by rfl⟩ : syracuseStep 3501737 = 2626303) B2626303
theorem B7483367 : Blo 1555475 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B143815175 : Blo 1555475 143815175 := bstep (se 1 (by rfl) ⟨107861381, by rfl⟩ : syracuseStep 143815175 = 215722763) B215722763
theorem B3789803 : Blo 1555475 3789803 := bstep (se 1 (by rfl) ⟨2842352, by rfl⟩ : syracuseStep 3789803 = 5684705) B5684705
theorem B3503519 : Blo 1555475 3503519 := bstep (se 1 (by rfl) ⟨2627639, by rfl⟩ : syracuseStep 3503519 = 5255279) B5255279
theorem B6649847 : Blo 1555475 6649847 := bstep (se 1 (by rfl) ⟨4987385, by rfl⟩ : syracuseStep 6649847 = 9974771) B9974771
theorem B5913071 : Blo 1555475 5913071 := bstep (se 1 (by rfl) ⟨4434803, by rfl⟩ : syracuseStep 5913071 = 8869607) B8869607
theorem B12614719 : Blo 1555475 12614719 := bstep (se 1 (by rfl) ⟨9461039, by rfl⟩ : syracuseStep 12614719 = 18922079) B18922079
theorem B1555559 : Blo 1555475 1555559 := bstep (se 1 (by rfl) ⟨1166669, by rfl⟩ : syracuseStep 1555559 = 2333339) B2333339
theorem B2333993 : Blo 1555475 2333993 := bstep (se 2 (by rfl) ⟨875247, by rfl⟩ : syracuseStep 2333993 = 1750495) B1750495
theorem B2333999 : Blo 1555475 2333999 := bstep (se 1 (by rfl) ⟨1750499, by rfl⟩ : syracuseStep 2333999 = 3500999) B3500999
theorem B1555903 : Blo 1555475 1555903 := bstep (se 1 (by rfl) ⟨1166927, by rfl⟩ : syracuseStep 1555903 = 2333855) B2333855
theorem B95846215 : Blo 1555475 95846215 := bstep (se 1 (by rfl) ⟨71884661, by rfl⟩ : syracuseStep 95846215 = 143769323) B143769323
theorem B2335679 : Blo 1555475 2335679 := bstep (se 1 (by rfl) ⟨1751759, by rfl⟩ : syracuseStep 2335679 = 3503519) B3503519
theorem B4433231 : Blo 1555475 4433231 := bstep (se 1 (by rfl) ⟨3324923, by rfl⟩ : syracuseStep 4433231 = 6649847) B6649847
theorem B16819625 : Blo 1555475 16819625 := bstep (se 2 (by rfl) ⟨6307359, by rfl⟩ : syracuseStep 16819625 = 12614719) B12614719
theorem B3942047 : Blo 1555475 3942047 := bstep (se 1 (by rfl) ⟨2956535, by rfl⟩ : syracuseStep 3942047 = 5913071) B5913071
theorem B2526535 : Blo 1555475 2526535 := bstep (se 1 (by rfl) ⟨1894901, by rfl⟩ : syracuseStep 2526535 = 3789803) B3789803
theorem B64753289 : Blo 1555475 64753289 := bstep (se 2 (by rfl) ⟨24282483, by rfl⟩ : syracuseStep 64753289 = 48564967) B48564967
theorem B95876783 : Blo 1555475 95876783 := bstep (se 1 (by rfl) ⟨71907587, by rfl⟩ : syracuseStep 95876783 = 143815175) B143815175
theorem B2955199 : Blo 1555475 2955199 := bstep (se 1 (by rfl) ⟨2216399, by rfl⟩ : syracuseStep 2955199 = 4432799) B4432799
theorem B2333351 : Blo 1555475 2333351 := bstep (se 1 (by rfl) ⟨1750013, by rfl⟩ : syracuseStep 2333351 = 3500027) B3500027
theorem B2333663 : Blo 1555475 2333663 := bstep (se 1 (by rfl) ⟨1750247, by rfl⟩ : syracuseStep 2333663 = 3500495) B3500495
theorem B2333951 : Blo 1555475 2333951 := bstep (se 1 (by rfl) ⟨1750463, by rfl⟩ : syracuseStep 2333951 = 3500927) B3500927
theorem B1555995 : Blo 1555475 1555995 := bstep (se 1 (by rfl) ⟨1166996, by rfl⟩ : syracuseStep 1555995 = 2333993) B2333993
theorem B1555999 : Blo 1555475 1555999 := bstep (se 1 (by rfl) ⟨1166999, by rfl⟩ : syracuseStep 1555999 = 2333999) B2333999
theorem B127794953 : Blo 1555475 127794953 := bstep (se 2 (by rfl) ⟨47923107, by rfl⟩ : syracuseStep 127794953 = 95846215) B95846215
theorem B2334491 : Blo 1555475 2334491 := bstep (se 1 (by rfl) ⟨1750868, by rfl⟩ : syracuseStep 2334491 = 3501737) B3501737
theorem B19955645 : Blo 1555475 19955645 := bstep (se 3 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 19955645 = 7483367) B7483367
theorem B1557119 : Blo 1555475 1557119 := bstep (se 1 (by rfl) ⟨1167839, by rfl⟩ : syracuseStep 1557119 = 2335679) B2335679
theorem B11821949 : Blo 1555475 11821949 := bstep (se 3 (by rfl) ⟨2216615, by rfl⟩ : syracuseStep 11821949 = 4433231) B4433231
theorem B3368713 : Blo 1555475 3368713 := bstep (se 2 (by rfl) ⟨1263267, by rfl⟩ : syracuseStep 3368713 = 2526535) B2526535
theorem B63917855 : Blo 1555475 63917855 := bstep (se 1 (by rfl) ⟨47938391, by rfl⟩ : syracuseStep 63917855 = 95876783) B95876783
theorem B43168859 : Blo 1555475 43168859 := bstep (se 1 (by rfl) ⟨32376644, by rfl⟩ : syracuseStep 43168859 = 64753289) B64753289
theorem B11213083 : Blo 1555475 11213083 := bstep (se 1 (by rfl) ⟨8409812, by rfl⟩ : syracuseStep 11213083 = 16819625) B16819625
theorem B2628031 : Blo 1555475 2628031 := bstep (se 1 (by rfl) ⟨1971023, by rfl⟩ : syracuseStep 2628031 = 3942047) B3942047
theorem B1555567 : Blo 1555475 1555567 := bstep (se 1 (by rfl) ⟨1166675, by rfl⟩ : syracuseStep 1555567 = 2333351) B2333351
theorem B1555775 : Blo 1555475 1555775 := bstep (se 1 (by rfl) ⟨1166831, by rfl⟩ : syracuseStep 1555775 = 2333663) B2333663
theorem B340786541 : Blo 1555475 340786541 := bstep (se 3 (by rfl) ⟨63897476, by rfl⟩ : syracuseStep 340786541 = 127794953) B127794953
theorem B1555967 : Blo 1555475 1555967 := bstep (se 1 (by rfl) ⟨1166975, by rfl⟩ : syracuseStep 1555967 = 2333951) B2333951
theorem B1556327 : Blo 1555475 1556327 := bstep (se 1 (by rfl) ⟨1167245, by rfl⟩ : syracuseStep 1556327 = 2334491) B2334491
theorem B3940265 : Blo 1555475 3940265 := bstep (se 2 (by rfl) ⟨1477599, by rfl⟩ : syracuseStep 3940265 = 2955199) B2955199
theorem B13303763 : Blo 1555475 13303763 := bstep (se 1 (by rfl) ⟨9977822, by rfl⟩ : syracuseStep 13303763 = 19955645) B19955645
theorem B14950777 : Blo 1555475 14950777 := bstep (se 2 (by rfl) ⟨5606541, by rfl⟩ : syracuseStep 14950777 = 11213083) B11213083
theorem B7881299 : Blo 1555475 7881299 := bstep (se 1 (by rfl) ⟨5910974, by rfl⟩ : syracuseStep 7881299 = 11821949) B11821949
theorem B28779239 : Blo 1555475 28779239 := bstep (se 1 (by rfl) ⟨21584429, by rfl⟩ : syracuseStep 28779239 = 43168859) B43168859
theorem B227191027 : Blo 1555475 227191027 := bstep (se 1 (by rfl) ⟨170393270, by rfl⟩ : syracuseStep 227191027 = 340786541) B340786541
theorem B4491617 : Blo 1555475 4491617 := bstep (se 2 (by rfl) ⟨1684356, by rfl⟩ : syracuseStep 4491617 = 3368713) B3368713
theorem B42611903 : Blo 1555475 42611903 := bstep (se 1 (by rfl) ⟨31958927, by rfl⟩ : syracuseStep 42611903 = 63917855) B63917855
theorem B2626843 : Blo 1555475 2626843 := bstep (se 1 (by rfl) ⟨1970132, by rfl⟩ : syracuseStep 2626843 = 3940265) B3940265
theorem B8869175 : Blo 1555475 8869175 := bstep (se 1 (by rfl) ⟨6651881, by rfl⟩ : syracuseStep 8869175 = 13303763) B13303763
theorem B3504041 : Blo 1555475 3504041 := bstep (se 2 (by rfl) ⟨1314015, by rfl⟩ : syracuseStep 3504041 = 2628031) B2628031
theorem B19186159 : Blo 1555475 19186159 := bstep (se 1 (by rfl) ⟨14389619, by rfl⟩ : syracuseStep 19186159 = 28779239) B28779239
theorem B11977645 : Blo 1555475 11977645 := bstep (se 3 (by rfl) ⟨2245808, by rfl⟩ : syracuseStep 11977645 = 4491617) B4491617
theorem B2336027 : Blo 1555475 2336027 := bstep (se 1 (by rfl) ⟨1752020, by rfl⟩ : syracuseStep 2336027 = 3504041) B3504041
theorem B5254199 : Blo 1555475 5254199 := bstep (se 1 (by rfl) ⟨3940649, by rfl⟩ : syracuseStep 5254199 = 7881299) B7881299
theorem B19934369 : Blo 1555475 19934369 := bstep (se 2 (by rfl) ⟨7475388, by rfl⟩ : syracuseStep 19934369 = 14950777) B14950777
theorem B3502457 : Blo 1555475 3502457 := bstep (se 2 (by rfl) ⟨1313421, by rfl⟩ : syracuseStep 3502457 = 2626843) B2626843
theorem B302921369 : Blo 1555475 302921369 := bstep (se 2 (by rfl) ⟨113595513, by rfl⟩ : syracuseStep 302921369 = 227191027) B227191027
theorem B28407935 : Blo 1555475 28407935 := bstep (se 1 (by rfl) ⟨21305951, by rfl⟩ : syracuseStep 28407935 = 42611903) B42611903
theorem B5912783 : Blo 1555475 5912783 := bstep (se 1 (by rfl) ⟨4434587, by rfl⟩ : syracuseStep 5912783 = 8869175) B8869175
theorem B2334971 : Blo 1555475 2334971 := bstep (se 1 (by rfl) ⟨1751228, by rfl⟩ : syracuseStep 2334971 = 3502457) B3502457
theorem B1557351 : Blo 1555475 1557351 := bstep (se 1 (by rfl) ⟨1168013, by rfl⟩ : syracuseStep 1557351 = 2336027) B2336027
theorem B3941855 : Blo 1555475 3941855 := bstep (se 1 (by rfl) ⟨2956391, by rfl⟩ : syracuseStep 3941855 = 5912783) B5912783
theorem B13289579 : Blo 1555475 13289579 := bstep (se 1 (by rfl) ⟨9967184, by rfl⟩ : syracuseStep 13289579 = 19934369) B19934369
theorem B15970193 : Blo 1555475 15970193 := bstep (se 2 (by rfl) ⟨5988822, by rfl⟩ : syracuseStep 15970193 = 11977645) B11977645
theorem B3502799 : Blo 1555475 3502799 := bstep (se 1 (by rfl) ⟨2627099, by rfl⟩ : syracuseStep 3502799 = 5254199) B5254199
theorem B25581545 : Blo 1555475 25581545 := bstep (se 2 (by rfl) ⟨9593079, by rfl⟩ : syracuseStep 25581545 = 19186159) B19186159
theorem B201947579 : Blo 1555475 201947579 := bstep (se 1 (by rfl) ⟨151460684, by rfl⟩ : syracuseStep 201947579 = 302921369) B302921369
theorem B18938623 : Blo 1555475 18938623 := bstep (se 1 (by rfl) ⟨14203967, by rfl⟩ : syracuseStep 18938623 = 28407935) B28407935
theorem B1556647 : Blo 1555475 1556647 := bstep (se 1 (by rfl) ⟨1167485, by rfl⟩ : syracuseStep 1556647 = 2334971) B2334971
theorem B2335199 : Blo 1555475 2335199 := bstep (se 1 (by rfl) ⟨1751399, by rfl⟩ : syracuseStep 2335199 = 3502799) B3502799
theorem B25251497 : Blo 1555475 25251497 := bstep (se 2 (by rfl) ⟨9469311, by rfl⟩ : syracuseStep 25251497 = 18938623) B18938623
theorem B8859719 : Blo 1555475 8859719 := bstep (se 1 (by rfl) ⟨6644789, by rfl⟩ : syracuseStep 8859719 = 13289579) B13289579
theorem B134631719 : Blo 1555475 134631719 := bstep (se 1 (by rfl) ⟨100973789, by rfl⟩ : syracuseStep 134631719 = 201947579) B201947579
theorem B10646795 : Blo 1555475 10646795 := bstep (se 1 (by rfl) ⟨7985096, by rfl⟩ : syracuseStep 10646795 = 15970193) B15970193
theorem B2627903 : Blo 1555475 2627903 := bstep (se 1 (by rfl) ⟨1970927, by rfl⟩ : syracuseStep 2627903 = 3941855) B3941855
theorem B17054363 : Blo 1555475 17054363 := bstep (se 1 (by rfl) ⟨12790772, by rfl⟩ : syracuseStep 17054363 = 25581545) B25581545
theorem B5906479 : Blo 1555475 5906479 := bstep (se 1 (by rfl) ⟨4429859, by rfl⟩ : syracuseStep 5906479 = 8859719) B8859719
theorem B1556799 : Blo 1555475 1556799 := bstep (se 1 (by rfl) ⟨1167599, by rfl⟩ : syracuseStep 1556799 = 2335199) B2335199
theorem B89754479 : Blo 1555475 89754479 := bstep (se 1 (by rfl) ⟨67315859, by rfl⟩ : syracuseStep 89754479 = 134631719) B134631719
theorem B7097863 : Blo 1555475 7097863 := bstep (se 1 (by rfl) ⟨5323397, by rfl⟩ : syracuseStep 7097863 = 10646795) B10646795
theorem B1751935 : Blo 1555475 1751935 := bstep (se 1 (by rfl) ⟨1313951, by rfl⟩ : syracuseStep 1751935 = 2627903) B2627903
theorem B11369575 : Blo 1555475 11369575 := bstep (se 1 (by rfl) ⟨8527181, by rfl⟩ : syracuseStep 11369575 = 17054363) B17054363
theorem B16834331 : Blo 1555475 16834331 := bstep (se 1 (by rfl) ⟨12625748, by rfl⟩ : syracuseStep 16834331 = 25251497) B25251497
theorem B2335913 : Blo 1555475 2335913 := bstep (se 2 (by rfl) ⟨875967, by rfl⟩ : syracuseStep 2335913 = 1751935) B1751935
theorem B59836319 : Blo 1555475 59836319 := bstep (se 1 (by rfl) ⟨44877239, by rfl⟩ : syracuseStep 59836319 = 89754479) B89754479
theorem B9463817 : Blo 1555475 9463817 := bstep (se 2 (by rfl) ⟨3548931, by rfl⟩ : syracuseStep 9463817 = 7097863) B7097863
theorem B7875305 : Blo 1555475 7875305 := bstep (se 2 (by rfl) ⟨2953239, by rfl⟩ : syracuseStep 7875305 = 5906479) B5906479
theorem B15159433 : Blo 1555475 15159433 := bstep (se 2 (by rfl) ⟨5684787, by rfl⟩ : syracuseStep 15159433 = 11369575) B11369575
theorem B11222887 : Blo 1555475 11222887 := bstep (se 1 (by rfl) ⟨8417165, by rfl⟩ : syracuseStep 11222887 = 16834331) B16834331
theorem B1557275 : Blo 1555475 1557275 := bstep (se 1 (by rfl) ⟨1167956, by rfl⟩ : syracuseStep 1557275 = 2335913) B2335913
theorem B6309211 : Blo 1555475 6309211 := bstep (se 1 (by rfl) ⟨4731908, by rfl⟩ : syracuseStep 6309211 = 9463817) B9463817
theorem B20212577 : Blo 1555475 20212577 := bstep (se 2 (by rfl) ⟨7579716, by rfl⟩ : syracuseStep 20212577 = 15159433) B15159433
theorem B39890879 : Blo 1555475 39890879 := bstep (se 1 (by rfl) ⟨29918159, by rfl⟩ : syracuseStep 39890879 = 59836319) B59836319
theorem B14963849 : Blo 1555475 14963849 := bstep (se 2 (by rfl) ⟨5611443, by rfl⟩ : syracuseStep 14963849 = 11222887) B11222887
theorem B5250203 : Blo 1555475 5250203 := bstep (se 1 (by rfl) ⟨3937652, by rfl⟩ : syracuseStep 5250203 = 7875305) B7875305
theorem B3500135 : Blo 1555475 3500135 := bstep (se 1 (by rfl) ⟨2625101, by rfl⟩ : syracuseStep 3500135 = 5250203) B5250203
theorem B26593919 : Blo 1555475 26593919 := bstep (se 1 (by rfl) ⟨19945439, by rfl⟩ : syracuseStep 26593919 = 39890879) B39890879
theorem B9975899 : Blo 1555475 9975899 := bstep (se 1 (by rfl) ⟨7481924, by rfl⟩ : syracuseStep 9975899 = 14963849) B14963849
theorem B8412281 : Blo 1555475 8412281 := bstep (se 2 (by rfl) ⟨3154605, by rfl⟩ : syracuseStep 8412281 = 6309211) B6309211
theorem B13475051 : Blo 1555475 13475051 := bstep (se 1 (by rfl) ⟨10106288, by rfl⟩ : syracuseStep 13475051 = 20212577) B20212577
theorem B17729279 : Blo 1555475 17729279 := bstep (se 1 (by rfl) ⟨13296959, by rfl⟩ : syracuseStep 17729279 = 26593919) B26593919
theorem B5608187 : Blo 1555475 5608187 := bstep (se 1 (by rfl) ⟨4206140, by rfl⟩ : syracuseStep 5608187 = 8412281) B8412281
theorem B8983367 : Blo 1555475 8983367 := bstep (se 1 (by rfl) ⟨6737525, by rfl⟩ : syracuseStep 8983367 = 13475051) B13475051
theorem B6650599 : Blo 1555475 6650599 := bstep (se 1 (by rfl) ⟨4987949, by rfl⟩ : syracuseStep 6650599 = 9975899) B9975899
theorem B2333423 : Blo 1555475 2333423 := bstep (se 1 (by rfl) ⟨1750067, by rfl⟩ : syracuseStep 2333423 = 3500135) B3500135
theorem B5988911 : Blo 1555475 5988911 := bstep (se 1 (by rfl) ⟨4491683, by rfl⟩ : syracuseStep 5988911 = 8983367) B8983367
theorem B3738791 : Blo 1555475 3738791 := bstep (se 1 (by rfl) ⟨2804093, by rfl⟩ : syracuseStep 3738791 = 5608187) B5608187
theorem B8867465 : Blo 1555475 8867465 := bstep (se 2 (by rfl) ⟨3325299, by rfl⟩ : syracuseStep 8867465 = 6650599) B6650599
theorem B11819519 : Blo 1555475 11819519 := bstep (se 1 (by rfl) ⟨8864639, by rfl⟩ : syracuseStep 11819519 = 17729279) B17729279
theorem B1555615 : Blo 1555475 1555615 := bstep (se 1 (by rfl) ⟨1166711, by rfl⟩ : syracuseStep 1555615 = 2333423) B2333423
theorem B2492527 : Blo 1555475 2492527 := bstep (se 1 (by rfl) ⟨1869395, by rfl⟩ : syracuseStep 2492527 = 3738791) B3738791
theorem B15970429 : Blo 1555475 15970429 := bstep (se 3 (by rfl) ⟨2994455, by rfl⟩ : syracuseStep 15970429 = 5988911) B5988911
theorem B5911643 : Blo 1555475 5911643 := bstep (se 1 (by rfl) ⟨4433732, by rfl⟩ : syracuseStep 5911643 = 8867465) B8867465
theorem B7879679 : Blo 1555475 7879679 := bstep (se 1 (by rfl) ⟨5909759, by rfl⟩ : syracuseStep 7879679 = 11819519) B11819519
theorem B3941095 : Blo 1555475 3941095 := bstep (se 1 (by rfl) ⟨2955821, by rfl⟩ : syracuseStep 3941095 = 5911643) B5911643
theorem B5253119 : Blo 1555475 5253119 := bstep (se 1 (by rfl) ⟨3939839, by rfl⟩ : syracuseStep 5253119 = 7879679) B7879679
theorem B85175621 : Blo 1555475 85175621 := bstep (se 4 (by rfl) ⟨7985214, by rfl⟩ : syracuseStep 85175621 = 15970429) B15970429
theorem B3323369 : Blo 1555475 3323369 := bstep (se 2 (by rfl) ⟨1246263, by rfl⟩ : syracuseStep 3323369 = 2492527) B2492527
theorem B5254793 : Blo 1555475 5254793 := bstep (se 2 (by rfl) ⟨1970547, by rfl⟩ : syracuseStep 5254793 = 3941095) B3941095
theorem B3502079 : Blo 1555475 3502079 := bstep (se 1 (by rfl) ⟨2626559, by rfl⟩ : syracuseStep 3502079 = 5253119) B5253119
theorem B56783747 : Blo 1555475 56783747 := bstep (se 1 (by rfl) ⟨42587810, by rfl⟩ : syracuseStep 56783747 = 85175621) B85175621
theorem B8862317 : Blo 1555475 8862317 := bstep (se 3 (by rfl) ⟨1661684, by rfl⟩ : syracuseStep 8862317 = 3323369) B3323369
theorem B37855831 : Blo 1555475 37855831 := bstep (se 1 (by rfl) ⟨28391873, by rfl⟩ : syracuseStep 37855831 = 56783747) B56783747
theorem B5908211 : Blo 1555475 5908211 := bstep (se 1 (by rfl) ⟨4431158, by rfl⟩ : syracuseStep 5908211 = 8862317) B8862317
theorem B3503195 : Blo 1555475 3503195 := bstep (se 1 (by rfl) ⟨2627396, by rfl⟩ : syracuseStep 3503195 = 5254793) B5254793
theorem B2334719 : Blo 1555475 2334719 := bstep (se 1 (by rfl) ⟨1751039, by rfl⟩ : syracuseStep 2334719 = 3502079) B3502079
theorem B2335463 : Blo 1555475 2335463 := bstep (se 1 (by rfl) ⟨1751597, by rfl⟩ : syracuseStep 2335463 = 3503195) B3503195
theorem B50474441 : Blo 1555475 50474441 := bstep (se 2 (by rfl) ⟨18927915, by rfl⟩ : syracuseStep 50474441 = 37855831) B37855831
theorem B3938807 : Blo 1555475 3938807 := bstep (se 1 (by rfl) ⟨2954105, by rfl⟩ : syracuseStep 3938807 = 5908211) B5908211
theorem B1556479 : Blo 1555475 1556479 := bstep (se 1 (by rfl) ⟨1167359, by rfl⟩ : syracuseStep 1556479 = 2334719) B2334719
theorem B1556975 : Blo 1555475 1556975 := bstep (se 1 (by rfl) ⟨1167731, by rfl⟩ : syracuseStep 1556975 = 2335463) B2335463
theorem B2625871 : Blo 1555475 2625871 := bstep (se 1 (by rfl) ⟨1969403, by rfl⟩ : syracuseStep 2625871 = 3938807) B3938807
theorem B33649627 : Blo 1555475 33649627 := bstep (se 1 (by rfl) ⟨25237220, by rfl⟩ : syracuseStep 33649627 = 50474441) B50474441
theorem B3501161 : Blo 1555475 3501161 := bstep (se 2 (by rfl) ⟨1312935, by rfl⟩ : syracuseStep 3501161 = 2625871) B2625871
theorem B44866169 : Blo 1555475 44866169 := bstep (se 2 (by rfl) ⟨16824813, by rfl⟩ : syracuseStep 44866169 = 33649627) B33649627
theorem B29910779 : Blo 1555475 29910779 := bstep (se 1 (by rfl) ⟨22433084, by rfl⟩ : syracuseStep 29910779 = 44866169) B44866169
theorem B2334107 : Blo 1555475 2334107 := bstep (se 1 (by rfl) ⟨1750580, by rfl⟩ : syracuseStep 2334107 = 3501161) B3501161
theorem B19940519 : Blo 1555475 19940519 := bstep (se 1 (by rfl) ⟨14955389, by rfl⟩ : syracuseStep 19940519 = 29910779) B29910779
theorem B1556071 : Blo 1555475 1556071 := bstep (se 1 (by rfl) ⟨1167053, by rfl⟩ : syracuseStep 1556071 = 2334107) B2334107
theorem B13293679 : Blo 1555475 13293679 := bstep (se 1 (by rfl) ⟨9970259, by rfl⟩ : syracuseStep 13293679 = 19940519) B19940519
theorem B17724905 : Blo 1555475 17724905 := bstep (se 2 (by rfl) ⟨6646839, by rfl⟩ : syracuseStep 17724905 = 13293679) B13293679
theorem B11816603 : Blo 1555475 11816603 := bstep (se 1 (by rfl) ⟨8862452, by rfl⟩ : syracuseStep 11816603 = 17724905) B17724905
theorem B7877735 : Blo 1555475 7877735 := bstep (se 1 (by rfl) ⟨5908301, by rfl⟩ : syracuseStep 7877735 = 11816603) B11816603
theorem B5251823 : Blo 1555475 5251823 := bstep (se 1 (by rfl) ⟨3938867, by rfl⟩ : syracuseStep 5251823 = 7877735) B7877735
theorem B3501215 : Blo 1555475 3501215 := bstep (se 1 (by rfl) ⟨2625911, by rfl⟩ : syracuseStep 3501215 = 5251823) B5251823
theorem B2334143 : Blo 1555475 2334143 := bstep (se 1 (by rfl) ⟨1750607, by rfl⟩ : syracuseStep 2334143 = 3501215) B3501215
theorem B1556095 : Blo 1555475 1556095 := bstep (se 1 (by rfl) ⟨1167071, by rfl⟩ : syracuseStep 1556095 = 2334143) B2334143

theorem C0 (j : ℕ) (h1 : 388868 ≤ j) (h2 : j ≤ 389368) : Blo 1555475 (4 * j + 3) := by
  interval_cases j
  · exact B1555475
  · exact B1555479
  · exact B1555483
  · exact B1555487
  · exact B1555491
  · exact B1555495
  · exact B1555499
  · exact B1555503
  · exact B1555507
  · exact B1555511
  · exact B1555515
  · exact B1555519
  · exact B1555523
  · exact B1555527
  · exact B1555531
  · exact B1555535
  · exact B1555539
  · exact B1555543
  · exact B1555547
  · exact B1555551
  · exact B1555555
  · exact B1555559
  · exact B1555563
  · exact B1555567
  · exact B1555571
  · exact B1555575
  · exact B1555579
  · exact B1555583
  · exact B1555587
  · exact B1555591
  · exact B1555595
  · exact B1555599
  · exact B1555603
  · exact B1555607
  · exact B1555611
  · exact B1555615
  · exact B1555619
  · exact B1555623
  · exact B1555627
  · exact B1555631
  · exact B1555635
  · exact B1555639
  · exact B1555643
  · exact B1555647
  · exact B1555651
  · exact B1555655
  · exact B1555659
  · exact B1555663
  · exact B1555667
  · exact B1555671
  · exact B1555675
  · exact B1555679
  · exact B1555683
  · exact B1555687
  · exact B1555691
  · exact B1555695
  · exact B1555699
  · exact B1555703
  · exact B1555707
  · exact B1555711
  · exact B1555715
  · exact B1555719
  · exact B1555723
  · exact B1555727
  · exact B1555731
  · exact B1555735
  · exact B1555739
  · exact B1555743
  · exact B1555747
  · exact B1555751
  · exact B1555755
  · exact B1555759
  · exact B1555763
  · exact B1555767
  · exact B1555771
  · exact B1555775
  · exact B1555779
  · exact B1555783
  · exact B1555787
  · exact B1555791
  · exact B1555795
  · exact B1555799
  · exact B1555803
  · exact B1555807
  · exact B1555811
  · exact B1555815
  · exact B1555819
  · exact B1555823
  · exact B1555827
  · exact B1555831
  · exact B1555835
  · exact B1555839
  · exact B1555843
  · exact B1555847
  · exact B1555851
  · exact B1555855
  · exact B1555859
  · exact B1555863
  · exact B1555867
  · exact B1555871
  · exact B1555875
  · exact B1555879
  · exact B1555883
  · exact B1555887
  · exact B1555891
  · exact B1555895
  · exact B1555899
  · exact B1555903
  · exact B1555907
  · exact B1555911
  · exact B1555915
  · exact B1555919
  · exact B1555923
  · exact B1555927
  · exact B1555931
  · exact B1555935
  · exact B1555939
  · exact B1555943
  · exact B1555947
  · exact B1555951
  · exact B1555955
  · exact B1555959
  · exact B1555963
  · exact B1555967
  · exact B1555971
  · exact B1555975
  · exact B1555979
  · exact B1555983
  · exact B1555987
  · exact B1555991
  · exact B1555995
  · exact B1555999
  · exact B1556003
  · exact B1556007
  · exact B1556011
  · exact B1556015
  · exact B1556019
  · exact B1556023
  · exact B1556027
  · exact B1556031
  · exact B1556035
  · exact B1556039
  · exact B1556043
  · exact B1556047
  · exact B1556051
  · exact B1556055
  · exact B1556059
  · exact B1556063
  · exact B1556067
  · exact B1556071
  · exact B1556075
  · exact B1556079
  · exact B1556083
  · exact B1556087
  · exact B1556091
  · exact B1556095
  · exact B1556099
  · exact B1556103
  · exact B1556107
  · exact B1556111
  · exact B1556115
  · exact B1556119
  · exact B1556123
  · exact B1556127
  · exact B1556131
  · exact B1556135
  · exact B1556139
  · exact B1556143
  · exact B1556147
  · exact B1556151
  · exact B1556155
  · exact B1556159
  · exact B1556163
  · exact B1556167
  · exact B1556171
  · exact B1556175
  · exact B1556179
  · exact B1556183
  · exact B1556187
  · exact B1556191
  · exact B1556195
  · exact B1556199
  · exact B1556203
  · exact B1556207
  · exact B1556211
  · exact B1556215
  · exact B1556219
  · exact B1556223
  · exact B1556227
  · exact B1556231
  · exact B1556235
  · exact B1556239
  · exact B1556243
  · exact B1556247
  · exact B1556251
  · exact B1556255
  · exact B1556259
  · exact B1556263
  · exact B1556267
  · exact B1556271
  · exact B1556275
  · exact B1556279
  · exact B1556283
  · exact B1556287
  · exact B1556291
  · exact B1556295
  · exact B1556299
  · exact B1556303
  · exact B1556307
  · exact B1556311
  · exact B1556315
  · exact B1556319
  · exact B1556323
  · exact B1556327
  · exact B1556331
  · exact B1556335
  · exact B1556339
  · exact B1556343
  · exact B1556347
  · exact B1556351
  · exact B1556355
  · exact B1556359
  · exact B1556363
  · exact B1556367
  · exact B1556371
  · exact B1556375
  · exact B1556379
  · exact B1556383
  · exact B1556387
  · exact B1556391
  · exact B1556395
  · exact B1556399
  · exact B1556403
  · exact B1556407
  · exact B1556411
  · exact B1556415
  · exact B1556419
  · exact B1556423
  · exact B1556427
  · exact B1556431
  · exact B1556435
  · exact B1556439
  · exact B1556443
  · exact B1556447
  · exact B1556451
  · exact B1556455
  · exact B1556459
  · exact B1556463
  · exact B1556467
  · exact B1556471
  · exact B1556475
  · exact B1556479
  · exact B1556483
  · exact B1556487
  · exact B1556491
  · exact B1556495
  · exact B1556499
  · exact B1556503
  · exact B1556507
  · exact B1556511
  · exact B1556515
  · exact B1556519
  · exact B1556523
  · exact B1556527
  · exact B1556531
  · exact B1556535
  · exact B1556539
  · exact B1556543
  · exact B1556547
  · exact B1556551
  · exact B1556555
  · exact B1556559
  · exact B1556563
  · exact B1556567
  · exact B1556571
  · exact B1556575
  · exact B1556579
  · exact B1556583
  · exact B1556587
  · exact B1556591
  · exact B1556595
  · exact B1556599
  · exact B1556603
  · exact B1556607
  · exact B1556611
  · exact B1556615
  · exact B1556619
  · exact B1556623
  · exact B1556627
  · exact B1556631
  · exact B1556635
  · exact B1556639
  · exact B1556643
  · exact B1556647
  · exact B1556651
  · exact B1556655
  · exact B1556659
  · exact B1556663
  · exact B1556667
  · exact B1556671
  · exact B1556675
  · exact B1556679
  · exact B1556683
  · exact B1556687
  · exact B1556691
  · exact B1556695
  · exact B1556699
  · exact B1556703
  · exact B1556707
  · exact B1556711
  · exact B1556715
  · exact B1556719
  · exact B1556723
  · exact B1556727
  · exact B1556731
  · exact B1556735
  · exact B1556739
  · exact B1556743
  · exact B1556747
  · exact B1556751
  · exact B1556755
  · exact B1556759
  · exact B1556763
  · exact B1556767
  · exact B1556771
  · exact B1556775
  · exact B1556779
  · exact B1556783
  · exact B1556787
  · exact B1556791
  · exact B1556795
  · exact B1556799
  · exact B1556803
  · exact B1556807
  · exact B1556811
  · exact B1556815
  · exact B1556819
  · exact B1556823
  · exact B1556827
  · exact B1556831
  · exact B1556835
  · exact B1556839
  · exact B1556843
  · exact B1556847
  · exact B1556851
  · exact B1556855
  · exact B1556859
  · exact B1556863
  · exact B1556867
  · exact B1556871
  · exact B1556875
  · exact B1556879
  · exact B1556883
  · exact B1556887
  · exact B1556891
  · exact B1556895
  · exact B1556899
  · exact B1556903
  · exact B1556907
  · exact B1556911
  · exact B1556915
  · exact B1556919
  · exact B1556923
  · exact B1556927
  · exact B1556931
  · exact B1556935
  · exact B1556939
  · exact B1556943
  · exact B1556947
  · exact B1556951
  · exact B1556955
  · exact B1556959
  · exact B1556963
  · exact B1556967
  · exact B1556971
  · exact B1556975
  · exact B1556979
  · exact B1556983
  · exact B1556987
  · exact B1556991
  · exact B1556995
  · exact B1556999
  · exact B1557003
  · exact B1557007
  · exact B1557011
  · exact B1557015
  · exact B1557019
  · exact B1557023
  · exact B1557027
  · exact B1557031
  · exact B1557035
  · exact B1557039
  · exact B1557043
  · exact B1557047
  · exact B1557051
  · exact B1557055
  · exact B1557059
  · exact B1557063
  · exact B1557067
  · exact B1557071
  · exact B1557075
  · exact B1557079
  · exact B1557083
  · exact B1557087
  · exact B1557091
  · exact B1557095
  · exact B1557099
  · exact B1557103
  · exact B1557107
  · exact B1557111
  · exact B1557115
  · exact B1557119
  · exact B1557123
  · exact B1557127
  · exact B1557131
  · exact B1557135
  · exact B1557139
  · exact B1557143
  · exact B1557147
  · exact B1557151
  · exact B1557155
  · exact B1557159
  · exact B1557163
  · exact B1557167
  · exact B1557171
  · exact B1557175
  · exact B1557179
  · exact B1557183
  · exact B1557187
  · exact B1557191
  · exact B1557195
  · exact B1557199
  · exact B1557203
  · exact B1557207
  · exact B1557211
  · exact B1557215
  · exact B1557219
  · exact B1557223
  · exact B1557227
  · exact B1557231
  · exact B1557235
  · exact B1557239
  · exact B1557243
  · exact B1557247
  · exact B1557251
  · exact B1557255
  · exact B1557259
  · exact B1557263
  · exact B1557267
  · exact B1557271
  · exact B1557275
  · exact B1557279
  · exact B1557283
  · exact B1557287
  · exact B1557291
  · exact B1557295
  · exact B1557299
  · exact B1557303
  · exact B1557307
  · exact B1557311
  · exact B1557315
  · exact B1557319
  · exact B1557323
  · exact B1557327
  · exact B1557331
  · exact B1557335
  · exact B1557339
  · exact B1557343
  · exact B1557347
  · exact B1557351
  · exact B1557355
  · exact B1557359
  · exact B1557363
  · exact B1557367
  · exact B1557371
  · exact B1557375
  · exact B1557379
  · exact B1557383
  · exact B1557387
  · exact B1557391
  · exact B1557395
  · exact B1557399
  · exact B1557403
  · exact B1557407
  · exact B1557411
  · exact B1557415
  · exact B1557419
  · exact B1557423
  · exact B1557427
  · exact B1557431
  · exact B1557435
  · exact B1557439
  · exact B1557443
  · exact B1557447
  · exact B1557451
  · exact B1557455
  · exact B1557459
  · exact B1557463
  · exact B1557467
  · exact B1557471
  · exact B1557475

theorem solution (m : ℕ) (hlo : 1555475 ≤ m) (hhi : m ≤ 1557475) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 388868 ≤ j := by omega
    have hj2 : j ≤ 389368 := by omega
    have hb : Blo 1555475 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
