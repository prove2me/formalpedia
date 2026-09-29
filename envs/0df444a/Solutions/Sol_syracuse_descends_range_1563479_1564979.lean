-- Prove2me | solution 1 for syracuse_descends_range_1563479_1564979
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:30.877231+00:00
-- url     : https://prove2.me/submissions/4e62e1fc-5a8a-419e-81de-f12a805e7840

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


theorem B1671193 : Blo 1563479 1671193 := bbase (se 2 (by rfl) ⟨626697, by rfl⟩ : syracuseStep 1671193 = 1253395) (by norm_num)
theorem B2711677 : Blo 1563479 2711677 := bbase (se 3 (by rfl) ⟨508439, by rfl⟩ : syracuseStep 2711677 = 1016879) (by norm_num)
theorem B8904917 : Blo 1563479 8904917 := bbase (se 7 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 8904917 = 208709) (by norm_num)
theorem B33497429 : Blo 1563479 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B13541813 : Blo 1563479 13541813 := bbase (se 5 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 13541813 = 1269545) (by norm_num)
theorem B8249813 : Blo 1563479 8249813 := bbase (se 7 (by rfl) ⟨96677, by rfl⟩ : syracuseStep 8249813 = 193355) (by norm_num)
theorem B2638453 : Blo 1563479 2638453 := bbase (se 5 (by rfl) ⟨123677, by rfl⟩ : syracuseStep 2638453 = 247355) (by norm_num)
theorem B2638541 : Blo 1563479 2638541 := bbase (se 3 (by rfl) ⟨494726, by rfl⟩ : syracuseStep 2638541 = 989453) (by norm_num)
theorem B2638669 : Blo 1563479 2638669 := bbase (se 3 (by rfl) ⟨494750, by rfl⟩ : syracuseStep 2638669 = 989501) (by norm_num)
theorem B1606541 : Blo 1563479 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B2638757 : Blo 1563479 2638757 := bbase (se 4 (by rfl) ⟨247383, by rfl⟩ : syracuseStep 2638757 = 494767) (by norm_num)
theorem B3957781 : Blo 1563479 3957781 := bbase (se 6 (by rfl) ⟨92760, by rfl⟩ : syracuseStep 3957781 = 185521) (by norm_num)
theorem B2638885 : Blo 1563479 2638885 := bbase (se 4 (by rfl) ⟨247395, by rfl⟩ : syracuseStep 2638885 = 494791) (by norm_num)
theorem B52864085 : Blo 1563479 52864085 := bbase (se 8 (by rfl) ⟨309750, by rfl⟩ : syracuseStep 52864085 = 619501) (by norm_num)
theorem B5637221 : Blo 1563479 5637221 := bbase (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) (by norm_num)
theorem B2638973 : Blo 1563479 2638973 := bbase (se 3 (by rfl) ⟨494807, by rfl⟩ : syracuseStep 2638973 = 989615) (by norm_num)
theorem B3957893 : Blo 1563479 3957893 := bbase (se 4 (by rfl) ⟨371052, by rfl⟩ : syracuseStep 3957893 = 742105) (by norm_num)
theorem B2819245 : Blo 1563479 2819245 := bbase (se 3 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 2819245 = 1057217) (by norm_num)
theorem B2639101 : Blo 1563479 2639101 := bbase (se 3 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 2639101 = 989663) (by norm_num)
theorem B5276933 : Blo 1563479 5276933 := bbase (se 4 (by rfl) ⟨494712, by rfl⟩ : syracuseStep 5276933 = 989425) (by norm_num)
theorem B5940485 : Blo 1563479 5940485 := bbase (se 4 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 5940485 = 1113841) (by norm_num)
theorem B3958085 : Blo 1563479 3958085 := bbase (se 4 (by rfl) ⟨371070, by rfl⟩ : syracuseStep 3958085 = 742141) (by norm_num)
theorem B2639189 : Blo 1563479 2639189 := bbase (se 12 (by rfl) ⟨966, by rfl⟩ : syracuseStep 2639189 = 1933) (by norm_num)
theorem B5637509 : Blo 1563479 5637509 := bbase (se 4 (by rfl) ⟨528516, by rfl⟩ : syracuseStep 5637509 = 1057033) (by norm_num)
theorem B2639317 : Blo 1563479 2639317 := bbase (se 7 (by rfl) ⟨30929, by rfl⟩ : syracuseStep 2639317 = 61859) (by norm_num)
theorem B6342133 : Blo 1563479 6342133 := bbase (se 5 (by rfl) ⟨297287, by rfl⟩ : syracuseStep 6342133 = 594575) (by norm_num)
theorem B3171845 : Blo 1563479 3171845 := bbase (se 4 (by rfl) ⟨297360, by rfl⟩ : syracuseStep 3171845 = 594721) (by norm_num)
theorem B2115077 : Blo 1563479 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B5940773 : Blo 1563479 5940773 := bbase (se 4 (by rfl) ⟨556947, by rfl⟩ : syracuseStep 5940773 = 1113895) (by norm_num)
theorem B2639405 : Blo 1563479 2639405 := bbase (se 3 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 2639405 = 989777) (by norm_num)
theorem B11429429 : Blo 1563479 11429429 := bbase (se 5 (by rfl) ⟨535754, by rfl⟩ : syracuseStep 11429429 = 1071509) (by norm_num)
theorem B10298933 : Blo 1563479 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B10020469 : Blo 1563479 10020469 := bbase (se 5 (by rfl) ⟨469709, by rfl⟩ : syracuseStep 10020469 = 939419) (by norm_num)
theorem B7915157 : Blo 1563479 7915157 := bbase (se 6 (by rfl) ⟨185511, by rfl⟩ : syracuseStep 7915157 = 371023) (by norm_num)
theorem B3958429 : Blo 1563479 3958429 := bbase (se 3 (by rfl) ⟨742205, by rfl⟩ : syracuseStep 3958429 = 1484411) (by norm_num)
theorem B2639533 : Blo 1563479 2639533 := bbase (se 3 (by rfl) ⟨494912, by rfl⟩ : syracuseStep 2639533 = 989825) (by norm_num)
theorem B5277365 : Blo 1563479 5277365 := bbase (se 5 (by rfl) ⟨247376, by rfl⟩ : syracuseStep 5277365 = 494753) (by norm_num)
theorem B2819821 : Blo 1563479 2819821 := bbase (se 3 (by rfl) ⟨528716, by rfl⟩ : syracuseStep 2819821 = 1057433) (by norm_num)
theorem B2639621 : Blo 1563479 2639621 := bbase (se 4 (by rfl) ⟨247464, by rfl⟩ : syracuseStep 2639621 = 494929) (by norm_num)
theorem B3958541 : Blo 1563479 3958541 := bbase (se 3 (by rfl) ⟨742226, by rfl⟩ : syracuseStep 3958541 = 1484453) (by norm_num)
theorem B2639749 : Blo 1563479 2639749 := bbase (se 4 (by rfl) ⟨247476, by rfl⟩ : syracuseStep 2639749 = 494953) (by norm_num)
theorem B3958733 : Blo 1563479 3958733 := bbase (se 3 (by rfl) ⟨742262, by rfl⟩ : syracuseStep 3958733 = 1484525) (by norm_num)
theorem B2639837 : Blo 1563479 2639837 := bbase (se 3 (by rfl) ⟨494969, by rfl⟩ : syracuseStep 2639837 = 989939) (by norm_num)
theorem B2377765 : Blo 1563479 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B2639965 : Blo 1563479 2639965 := bbase (se 3 (by rfl) ⟨494993, by rfl⟩ : syracuseStep 2639965 = 989987) (by norm_num)
theorem B5277797 : Blo 1563479 5277797 := bbase (se 4 (by rfl) ⟨494793, by rfl⟩ : syracuseStep 5277797 = 989587) (by norm_num)
theorem B2640053 : Blo 1563479 2640053 := bbase (se 5 (by rfl) ⟨123752, by rfl⟩ : syracuseStep 2640053 = 247505) (by norm_num)
theorem B2345237 : Blo 1563479 2345237 := bbase (se 6 (by rfl) ⟨54966, by rfl⟩ : syracuseStep 2345237 = 109933) (by norm_num)
theorem B3959077 : Blo 1563479 3959077 := bbase (se 4 (by rfl) ⟨371163, by rfl⟩ : syracuseStep 3959077 = 742327) (by norm_num)
theorem B2345261 : Blo 1563479 2345261 := bbase (se 3 (by rfl) ⟨439736, by rfl⟩ : syracuseStep 2345261 = 879473) (by norm_num)
theorem B2640181 : Blo 1563479 2640181 := bbase (se 5 (by rfl) ⟨123758, by rfl⟩ : syracuseStep 2640181 = 247517) (by norm_num)
theorem B2345285 : Blo 1563479 2345285 := bbase (se 4 (by rfl) ⟨219870, by rfl⟩ : syracuseStep 2345285 = 439741) (by norm_num)
theorem B2345309 : Blo 1563479 2345309 := bbase (se 3 (by rfl) ⟨439745, by rfl⟩ : syracuseStep 2345309 = 879491) (by norm_num)
theorem B2345333 : Blo 1563479 2345333 := bbase (se 5 (by rfl) ⟨109937, by rfl⟩ : syracuseStep 2345333 = 219875) (by norm_num)
theorem B14264693 : Blo 1563479 14264693 := bbase (se 5 (by rfl) ⟨668657, by rfl⟩ : syracuseStep 14264693 = 1337315) (by norm_num)
theorem B2378101 : Blo 1563479 2378101 := bbase (se 5 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 2378101 = 222947) (by norm_num)
theorem B2345357 : Blo 1563479 2345357 := bbase (se 3 (by rfl) ⟨439754, by rfl⟩ : syracuseStep 2345357 = 879509) (by norm_num)
theorem B2640269 : Blo 1563479 2640269 := bbase (se 3 (by rfl) ⟨495050, by rfl⟩ : syracuseStep 2640269 = 990101) (by norm_num)
theorem B3959189 : Blo 1563479 3959189 := bbase (se 6 (by rfl) ⟨92793, by rfl⟩ : syracuseStep 3959189 = 185587) (by norm_num)
theorem B2345381 : Blo 1563479 2345381 := bbase (se 4 (by rfl) ⟨219879, by rfl⟩ : syracuseStep 2345381 = 439759) (by norm_num)
theorem B2345405 : Blo 1563479 2345405 := bbase (se 3 (by rfl) ⟨439763, by rfl⟩ : syracuseStep 2345405 = 879527) (by norm_num)
theorem B2345429 : Blo 1563479 2345429 := bbase (se 7 (by rfl) ⟨27485, by rfl⟩ : syracuseStep 2345429 = 54971) (by norm_num)
theorem B1878493 : Blo 1563479 1878493 := bbase (se 3 (by rfl) ⟨352217, by rfl⟩ : syracuseStep 1878493 = 704435) (by norm_num)
theorem B2345453 : Blo 1563479 2345453 := bbase (se 3 (by rfl) ⟨439772, by rfl⟩ : syracuseStep 2345453 = 879545) (by norm_num)
theorem B2345477 : Blo 1563479 2345477 := bbase (se 4 (by rfl) ⟨219888, by rfl⟩ : syracuseStep 2345477 = 439777) (by norm_num)
theorem B2411021 : Blo 1563479 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B2640397 : Blo 1563479 2640397 := bbase (se 3 (by rfl) ⟨495074, by rfl⟩ : syracuseStep 2640397 = 990149) (by norm_num)
theorem B5278229 : Blo 1563479 5278229 := bbase (se 6 (by rfl) ⟨123708, by rfl⟩ : syracuseStep 5278229 = 247417) (by norm_num)
theorem B2345501 : Blo 1563479 2345501 := bbase (se 3 (by rfl) ⟨439781, by rfl⟩ : syracuseStep 2345501 = 879563) (by norm_num)
theorem B15026741 : Blo 1563479 15026741 := bbase (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) (by norm_num)
theorem B2345525 : Blo 1563479 2345525 := bbase (se 5 (by rfl) ⟨109946, by rfl⟩ : syracuseStep 2345525 = 219893) (by norm_num)
theorem B2345549 : Blo 1563479 2345549 := bbase (se 3 (by rfl) ⟨439790, by rfl⟩ : syracuseStep 2345549 = 879581) (by norm_num)
theorem B3959381 : Blo 1563479 3959381 := bbase (se 8 (by rfl) ⟨23199, by rfl⟩ : syracuseStep 3959381 = 46399) (by norm_num)
theorem B2345573 : Blo 1563479 2345573 := bbase (se 4 (by rfl) ⟨219897, by rfl⟩ : syracuseStep 2345573 = 439795) (by norm_num)
theorem B2640485 : Blo 1563479 2640485 := bbase (se 4 (by rfl) ⟨247545, by rfl⟩ : syracuseStep 2640485 = 495091) (by norm_num)
theorem B2345597 : Blo 1563479 2345597 := bbase (se 3 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 2345597 = 879599) (by norm_num)
theorem B2345621 : Blo 1563479 2345621 := bbase (se 6 (by rfl) ⟨54975, by rfl⟩ : syracuseStep 2345621 = 109951) (by norm_num)
theorem B2345645 : Blo 1563479 2345645 := bbase (se 3 (by rfl) ⟨439808, by rfl⟩ : syracuseStep 2345645 = 879617) (by norm_num)
theorem B2345669 : Blo 1563479 2345669 := bbase (se 4 (by rfl) ⟨219906, by rfl⟩ : syracuseStep 2345669 = 439813) (by norm_num)
theorem B5941957 : Blo 1563479 5941957 := bbase (se 4 (by rfl) ⟨557058, by rfl⟩ : syracuseStep 5941957 = 1114117) (by norm_num)
theorem B2345693 : Blo 1563479 2345693 := bbase (se 3 (by rfl) ⟨439817, by rfl⟩ : syracuseStep 2345693 = 879635) (by norm_num)
theorem B2640613 : Blo 1563479 2640613 := bbase (se 4 (by rfl) ⟨247557, by rfl⟩ : syracuseStep 2640613 = 495115) (by norm_num)
theorem B2345717 : Blo 1563479 2345717 := bbase (se 5 (by rfl) ⟨109955, by rfl⟩ : syracuseStep 2345717 = 219911) (by norm_num)
theorem B2345741 : Blo 1563479 2345741 := bbase (se 3 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 2345741 = 879653) (by norm_num)
theorem B2345765 : Blo 1563479 2345765 := bbase (se 4 (by rfl) ⟨219915, by rfl⟩ : syracuseStep 2345765 = 439831) (by norm_num)
theorem B2345789 : Blo 1563479 2345789 := bbase (se 3 (by rfl) ⟨439835, by rfl⟩ : syracuseStep 2345789 = 879671) (by norm_num)
theorem B2640701 : Blo 1563479 2640701 := bbase (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) (by norm_num)
theorem B3861317 : Blo 1563479 3861317 := bbase (se 4 (by rfl) ⟨361998, by rfl⟩ : syracuseStep 3861317 = 723997) (by norm_num)
theorem B2968397 : Blo 1563479 2968397 := bbase (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) (by norm_num)
theorem B2345813 : Blo 1563479 2345813 := bbase (se 9 (by rfl) ⟨6872, by rfl⟩ : syracuseStep 2345813 = 13745) (by norm_num)
theorem B1878881 : Blo 1563479 1878881 := bbase (se 2 (by rfl) ⟨704580, by rfl⟩ : syracuseStep 1878881 = 1409161) (by norm_num)
theorem B2345837 : Blo 1563479 2345837 := bbase (se 3 (by rfl) ⟨439844, by rfl⟩ : syracuseStep 2345837 = 879689) (by norm_num)
theorem B2345861 : Blo 1563479 2345861 := bbase (se 4 (by rfl) ⟨219924, by rfl⟩ : syracuseStep 2345861 = 439849) (by norm_num)
theorem B2345885 : Blo 1563479 2345885 := bbase (se 3 (by rfl) ⟨439853, by rfl⟩ : syracuseStep 2345885 = 879707) (by norm_num)
theorem B7916453 : Blo 1563479 7916453 := bbase (se 4 (by rfl) ⟨742167, by rfl⟩ : syracuseStep 7916453 = 1484335) (by norm_num)
theorem B3566501 : Blo 1563479 3566501 := bbase (se 4 (by rfl) ⟨334359, by rfl⟩ : syracuseStep 3566501 = 668719) (by norm_num)
theorem B3959725 : Blo 1563479 3959725 := bbase (se 3 (by rfl) ⟨742448, by rfl⟩ : syracuseStep 3959725 = 1484897) (by norm_num)
theorem B2345909 : Blo 1563479 2345909 := bbase (se 5 (by rfl) ⟨109964, by rfl⟩ : syracuseStep 2345909 = 219929) (by norm_num)
theorem B2640829 : Blo 1563479 2640829 := bbase (se 3 (by rfl) ⟨495155, by rfl⟩ : syracuseStep 2640829 = 990311) (by norm_num)
theorem B6679493 : Blo 1563479 6679493 := bbase (se 4 (by rfl) ⟨626202, by rfl⟩ : syracuseStep 6679493 = 1252405) (by norm_num)
theorem B5278661 : Blo 1563479 5278661 := bbase (se 4 (by rfl) ⟨494874, by rfl⟩ : syracuseStep 5278661 = 989749) (by norm_num)
theorem B2345933 : Blo 1563479 2345933 := bbase (se 3 (by rfl) ⟨439862, by rfl⟩ : syracuseStep 2345933 = 879725) (by norm_num)
theorem B2345957 : Blo 1563479 2345957 := bbase (se 4 (by rfl) ⟨219933, by rfl⟩ : syracuseStep 2345957 = 439867) (by norm_num)
theorem B2345981 : Blo 1563479 2345981 := bbase (se 3 (by rfl) ⟨439871, by rfl⟩ : syracuseStep 2345981 = 879743) (by norm_num)
theorem B2346005 : Blo 1563479 2346005 := bbase (se 6 (by rfl) ⟨54984, by rfl⟩ : syracuseStep 2346005 = 109969) (by norm_num)
theorem B3959837 : Blo 1563479 3959837 := bbase (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) (by norm_num)
theorem B2346029 : Blo 1563479 2346029 := bbase (se 3 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 2346029 = 879761) (by norm_num)
theorem B2346053 : Blo 1563479 2346053 := bbase (se 4 (by rfl) ⟨219942, by rfl⟩ : syracuseStep 2346053 = 439885) (by norm_num)
theorem B2346077 : Blo 1563479 2346077 := bbase (se 3 (by rfl) ⟨439889, by rfl⟩ : syracuseStep 2346077 = 879779) (by norm_num)
theorem B2346101 : Blo 1563479 2346101 := bbase (se 5 (by rfl) ⟨109973, by rfl⟩ : syracuseStep 2346101 = 219947) (by norm_num)
theorem B2346125 : Blo 1563479 2346125 := bbase (se 3 (by rfl) ⟨439898, by rfl⟩ : syracuseStep 2346125 = 879797) (by norm_num)
theorem B2346149 : Blo 1563479 2346149 := bbase (se 4 (by rfl) ⟨219951, by rfl⟩ : syracuseStep 2346149 = 439903) (by norm_num)
theorem B2346173 : Blo 1563479 2346173 := bbase (se 3 (by rfl) ⟨439907, by rfl⟩ : syracuseStep 2346173 = 879815) (by norm_num)
theorem B1879237 : Blo 1563479 1879237 := bbase (se 4 (by rfl) ⟨176178, by rfl⟩ : syracuseStep 1879237 = 352357) (by norm_num)
theorem B2346197 : Blo 1563479 2346197 := bbase (se 7 (by rfl) ⟨27494, by rfl⟩ : syracuseStep 2346197 = 54989) (by norm_num)
theorem B3960029 : Blo 1563479 3960029 := bbase (se 3 (by rfl) ⟨742505, by rfl⟩ : syracuseStep 3960029 = 1485011) (by norm_num)
theorem B2346221 : Blo 1563479 2346221 := bbase (se 3 (by rfl) ⟨439916, by rfl⟩ : syracuseStep 2346221 = 879833) (by norm_num)
theorem B2346245 : Blo 1563479 2346245 := bbase (se 4 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 2346245 = 439921) (by norm_num)
theorem B2346269 : Blo 1563479 2346269 := bbase (se 3 (by rfl) ⟨439925, by rfl⟩ : syracuseStep 2346269 = 879851) (by norm_num)
theorem B2346293 : Blo 1563479 2346293 := bbase (se 5 (by rfl) ⟨109982, by rfl⟩ : syracuseStep 2346293 = 219965) (by norm_num)
theorem B2346317 : Blo 1563479 2346317 := bbase (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) (by norm_num)
theorem B2346341 : Blo 1563479 2346341 := bbase (se 4 (by rfl) ⟨219969, by rfl⟩ : syracuseStep 2346341 = 439939) (by norm_num)
theorem B5279093 : Blo 1563479 5279093 := bbase (se 5 (by rfl) ⟨247457, by rfl⟩ : syracuseStep 5279093 = 494915) (by norm_num)
theorem B2346365 : Blo 1563479 2346365 := bbase (se 3 (by rfl) ⟨439943, by rfl⟩ : syracuseStep 2346365 = 879887) (by norm_num)
theorem B3517829 : Blo 1563479 3517829 := bbase (se 4 (by rfl) ⟨329796, by rfl⟩ : syracuseStep 3517829 = 659593) (by norm_num)
theorem B2346389 : Blo 1563479 2346389 := bbase (se 6 (by rfl) ⟨54993, by rfl⟩ : syracuseStep 2346389 = 109987) (by norm_num)
theorem B2346413 : Blo 1563479 2346413 := bbase (se 3 (by rfl) ⟨439952, by rfl⟩ : syracuseStep 2346413 = 879905) (by norm_num)
theorem B2346437 : Blo 1563479 2346437 := bbase (se 4 (by rfl) ⟨219978, by rfl⟩ : syracuseStep 2346437 = 439957) (by norm_num)
theorem B3517901 : Blo 1563479 3517901 := bbase (se 3 (by rfl) ⟨659606, by rfl⟩ : syracuseStep 3517901 = 1319213) (by norm_num)
theorem B2346461 : Blo 1563479 2346461 := bbase (se 3 (by rfl) ⟨439961, by rfl⟩ : syracuseStep 2346461 = 879923) (by norm_num)
theorem B2346485 : Blo 1563479 2346485 := bbase (se 5 (by rfl) ⟨109991, by rfl⟩ : syracuseStep 2346485 = 219983) (by norm_num)
theorem B3526141 : Blo 1563479 3526141 := bbase (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) (by norm_num)
theorem B2379269 : Blo 1563479 2379269 := bbase (se 4 (by rfl) ⟨223056, by rfl⟩ : syracuseStep 2379269 = 446113) (by norm_num)
theorem B2346509 : Blo 1563479 2346509 := bbase (se 3 (by rfl) ⟨439970, by rfl⟩ : syracuseStep 2346509 = 879941) (by norm_num)
theorem B3517973 : Blo 1563479 3517973 := bbase (se 6 (by rfl) ⟨82452, by rfl⟩ : syracuseStep 3517973 = 164905) (by norm_num)
theorem B1879573 : Blo 1563479 1879573 := bbase (se 6 (by rfl) ⟨44052, by rfl⟩ : syracuseStep 1879573 = 88105) (by norm_num)
theorem B2346533 : Blo 1563479 2346533 := bbase (se 4 (by rfl) ⟨219987, by rfl⟩ : syracuseStep 2346533 = 439975) (by norm_num)
theorem B3960373 : Blo 1563479 3960373 := bbase (se 5 (by rfl) ⟨185642, by rfl⟩ : syracuseStep 3960373 = 371285) (by norm_num)
theorem B2969149 : Blo 1563479 2969149 := bbase (se 3 (by rfl) ⟨556715, by rfl⟩ : syracuseStep 2969149 = 1113431) (by norm_num)
theorem B2346557 : Blo 1563479 2346557 := bbase (se 3 (by rfl) ⟨439979, by rfl⟩ : syracuseStep 2346557 = 879959) (by norm_num)
theorem B2346581 : Blo 1563479 2346581 := bbase (se 8 (by rfl) ⟨13749, by rfl⟩ : syracuseStep 2346581 = 27499) (by norm_num)
theorem B3518045 : Blo 1563479 3518045 := bbase (se 3 (by rfl) ⟨659633, by rfl⟩ : syracuseStep 3518045 = 1319267) (by norm_num)
theorem B2346605 : Blo 1563479 2346605 := bbase (se 3 (by rfl) ⟨439988, by rfl⟩ : syracuseStep 2346605 = 879977) (by norm_num)
theorem B2346629 : Blo 1563479 2346629 := bbase (se 4 (by rfl) ⟨219996, by rfl⟩ : syracuseStep 2346629 = 439993) (by norm_num)
theorem B2346653 : Blo 1563479 2346653 := bbase (se 3 (by rfl) ⟨439997, by rfl⟩ : syracuseStep 2346653 = 879995) (by norm_num)
theorem B3518117 : Blo 1563479 3518117 := bbase (se 4 (by rfl) ⟨329823, by rfl⟩ : syracuseStep 3518117 = 659647) (by norm_num)
theorem B3960485 : Blo 1563479 3960485 := bbase (se 4 (by rfl) ⟨371295, by rfl⟩ : syracuseStep 3960485 = 742591) (by norm_num)
theorem B2346677 : Blo 1563479 2346677 := bbase (se 5 (by rfl) ⟨110000, by rfl⟩ : syracuseStep 2346677 = 220001) (by norm_num)
theorem B2969293 : Blo 1563479 2969293 := bbase (se 3 (by rfl) ⟨556742, by rfl⟩ : syracuseStep 2969293 = 1113485) (by norm_num)
theorem B2346701 : Blo 1563479 2346701 := bbase (se 3 (by rfl) ⟨440006, by rfl⟩ : syracuseStep 2346701 = 880013) (by norm_num)
theorem B3010277 : Blo 1563479 3010277 := bbase (se 4 (by rfl) ⟨282213, by rfl⟩ : syracuseStep 3010277 = 564427) (by norm_num)
theorem B2346725 : Blo 1563479 2346725 := bbase (se 4 (by rfl) ⟨220005, by rfl⟩ : syracuseStep 2346725 = 440011) (by norm_num)
theorem B3518189 : Blo 1563479 3518189 := bbase (se 3 (by rfl) ⟨659660, by rfl⟩ : syracuseStep 3518189 = 1319321) (by norm_num)
theorem B3567341 : Blo 1563479 3567341 := bbase (se 3 (by rfl) ⟨668876, by rfl⟩ : syracuseStep 3567341 = 1337753) (by norm_num)
theorem B2346749 : Blo 1563479 2346749 := bbase (se 3 (by rfl) ⟨440015, by rfl⟩ : syracuseStep 2346749 = 880031) (by norm_num)
theorem B6344453 : Blo 1563479 6344453 := bbase (se 4 (by rfl) ⟨594792, by rfl⟩ : syracuseStep 6344453 = 1189585) (by norm_num)
theorem B2346773 : Blo 1563479 2346773 := bbase (se 6 (by rfl) ⟨55002, by rfl⟩ : syracuseStep 2346773 = 110005) (by norm_num)
theorem B5279525 : Blo 1563479 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B2346797 : Blo 1563479 2346797 := bbase (se 3 (by rfl) ⟨440024, by rfl⟩ : syracuseStep 2346797 = 880049) (by norm_num)
theorem B3518261 : Blo 1563479 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B5639989 : Blo 1563479 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B2346821 : Blo 1563479 2346821 := bbase (se 4 (by rfl) ⟨220014, by rfl⟩ : syracuseStep 2346821 = 440029) (by norm_num)
theorem B2346845 : Blo 1563479 2346845 := bbase (se 3 (by rfl) ⟨440033, by rfl⟩ : syracuseStep 2346845 = 880067) (by norm_num)
theorem B3960677 : Blo 1563479 3960677 := bbase (se 4 (by rfl) ⟨371313, by rfl⟩ : syracuseStep 3960677 = 742627) (by norm_num)
theorem B2969453 : Blo 1563479 2969453 := bbase (se 3 (by rfl) ⟨556772, by rfl⟩ : syracuseStep 2969453 = 1113545) (by norm_num)
theorem B2346869 : Blo 1563479 2346869 := bbase (se 5 (by rfl) ⟨110009, by rfl⟩ : syracuseStep 2346869 = 220019) (by norm_num)
theorem B3518333 : Blo 1563479 3518333 := bbase (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) (by norm_num)
theorem B2346893 : Blo 1563479 2346893 := bbase (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) (by norm_num)
theorem B2748325 : Blo 1563479 2748325 := bbase (se 4 (by rfl) ⟨257655, by rfl⟩ : syracuseStep 2748325 = 515311) (by norm_num)
theorem B2346917 : Blo 1563479 2346917 := bbase (se 4 (by rfl) ⟨220023, by rfl⟩ : syracuseStep 2346917 = 440047) (by norm_num)
theorem B6680501 : Blo 1563479 6680501 := bbase (se 5 (by rfl) ⟨313148, by rfl⟩ : syracuseStep 6680501 = 626297) (by norm_num)
theorem B2346941 : Blo 1563479 2346941 := bbase (se 3 (by rfl) ⟨440051, by rfl⟩ : syracuseStep 2346941 = 880103) (by norm_num)
theorem B3518405 : Blo 1563479 3518405 := bbase (se 4 (by rfl) ⟨329850, by rfl⟩ : syracuseStep 3518405 = 659701) (by norm_num)
theorem B2346965 : Blo 1563479 2346965 := bbase (se 7 (by rfl) ⟨27503, by rfl⟩ : syracuseStep 2346965 = 55007) (by norm_num)
theorem B2346989 : Blo 1563479 2346989 := bbase (se 3 (by rfl) ⟨440060, by rfl⟩ : syracuseStep 2346989 = 880121) (by norm_num)
theorem B2969597 : Blo 1563479 2969597 := bbase (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) (by norm_num)
theorem B2347013 : Blo 1563479 2347013 := bbase (se 4 (by rfl) ⟨220032, by rfl⟩ : syracuseStep 2347013 = 440065) (by norm_num)
theorem B3518477 : Blo 1563479 3518477 := bbase (se 3 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 3518477 = 1319429) (by norm_num)
theorem B2347037 : Blo 1563479 2347037 := bbase (se 3 (by rfl) ⟨440069, by rfl⟩ : syracuseStep 2347037 = 880139) (by norm_num)
theorem B2347061 : Blo 1563479 2347061 := bbase (se 5 (by rfl) ⟨110018, by rfl⟩ : syracuseStep 2347061 = 220037) (by norm_num)
theorem B1585225 : Blo 1563479 1585225 := bbase (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) (by norm_num)
theorem B2347085 : Blo 1563479 2347085 := bbase (se 3 (by rfl) ⟨440078, by rfl⟩ : syracuseStep 2347085 = 880157) (by norm_num)
theorem B3518549 : Blo 1563479 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B2347109 : Blo 1563479 2347109 := bbase (se 4 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 2347109 = 440083) (by norm_num)
theorem B2347133 : Blo 1563479 2347133 := bbase (se 3 (by rfl) ⟨440087, by rfl⟩ : syracuseStep 2347133 = 880175) (by norm_num)
theorem B2347157 : Blo 1563479 2347157 := bbase (se 6 (by rfl) ⟨55011, by rfl⟩ : syracuseStep 2347157 = 110023) (by norm_num)
theorem B3518621 : Blo 1563479 3518621 := bbase (se 3 (by rfl) ⟨659741, by rfl⟩ : syracuseStep 3518621 = 1319483) (by norm_num)
theorem B2347181 : Blo 1563479 2347181 := bbase (se 3 (by rfl) ⟨440096, by rfl⟩ : syracuseStep 2347181 = 880193) (by norm_num)
theorem B7917749 : Blo 1563479 7917749 := bbase (se 5 (by rfl) ⟨371144, by rfl⟩ : syracuseStep 7917749 = 742289) (by norm_num)
theorem B3961021 : Blo 1563479 3961021 := bbase (se 3 (by rfl) ⟨742691, by rfl⟩ : syracuseStep 3961021 = 1485383) (by norm_num)
theorem B2347205 : Blo 1563479 2347205 := bbase (se 4 (by rfl) ⟨220050, by rfl⟩ : syracuseStep 2347205 = 440101) (by norm_num)
theorem B5279957 : Blo 1563479 5279957 := bbase (se 7 (by rfl) ⟨61874, by rfl⟩ : syracuseStep 5279957 = 123749) (by norm_num)
theorem B2347229 : Blo 1563479 2347229 := bbase (se 3 (by rfl) ⟨440105, by rfl⟩ : syracuseStep 2347229 = 880211) (by norm_num)
theorem B3518693 : Blo 1563479 3518693 := bbase (se 4 (by rfl) ⟨329877, by rfl⟩ : syracuseStep 3518693 = 659755) (by norm_num)
theorem B2347253 : Blo 1563479 2347253 := bbase (se 5 (by rfl) ⟨110027, by rfl⟩ : syracuseStep 2347253 = 220055) (by norm_num)
theorem B2347277 : Blo 1563479 2347277 := bbase (se 3 (by rfl) ⟨440114, by rfl⟩ : syracuseStep 2347277 = 880229) (by norm_num)
theorem B2969885 : Blo 1563479 2969885 := bbase (se 3 (by rfl) ⟨556853, by rfl⟩ : syracuseStep 2969885 = 1113707) (by norm_num)
theorem B2347301 : Blo 1563479 2347301 := bbase (se 4 (by rfl) ⟨220059, by rfl⟩ : syracuseStep 2347301 = 440119) (by norm_num)
theorem B3518765 : Blo 1563479 3518765 := bbase (se 3 (by rfl) ⟨659768, by rfl⟩ : syracuseStep 3518765 = 1319537) (by norm_num)
theorem B3961133 : Blo 1563479 3961133 := bbase (se 3 (by rfl) ⟨742712, by rfl⟩ : syracuseStep 3961133 = 1485425) (by norm_num)
theorem B2347325 : Blo 1563479 2347325 := bbase (se 3 (by rfl) ⟨440123, by rfl⟩ : syracuseStep 2347325 = 880247) (by norm_num)
theorem B2347349 : Blo 1563479 2347349 := bbase (se 10 (by rfl) ⟨3438, by rfl⟩ : syracuseStep 2347349 = 6877) (by norm_num)
theorem B2347373 : Blo 1563479 2347373 := bbase (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) (by norm_num)
theorem B3518837 : Blo 1563479 3518837 := bbase (se 5 (by rfl) ⟨164945, by rfl⟩ : syracuseStep 3518837 = 329891) (by norm_num)
theorem B2347397 : Blo 1563479 2347397 := bbase (se 4 (by rfl) ⟨220068, by rfl⟩ : syracuseStep 2347397 = 440137) (by norm_num)
theorem B2347421 : Blo 1563479 2347421 := bbase (se 3 (by rfl) ⟨440141, by rfl⟩ : syracuseStep 2347421 = 880283) (by norm_num)
theorem B1905061 : Blo 1563479 1905061 := bbase (se 4 (by rfl) ⟨178599, by rfl⟩ : syracuseStep 1905061 = 357199) (by norm_num)
theorem B2970037 : Blo 1563479 2970037 := bbase (se 5 (by rfl) ⟨139220, by rfl⟩ : syracuseStep 2970037 = 278441) (by norm_num)
theorem B2347445 : Blo 1563479 2347445 := bbase (se 5 (by rfl) ⟨110036, by rfl⟩ : syracuseStep 2347445 = 220073) (by norm_num)
theorem B3518909 : Blo 1563479 3518909 := bbase (se 3 (by rfl) ⟨659795, by rfl⟩ : syracuseStep 3518909 = 1319591) (by norm_num)
theorem B1978825 : Blo 1563479 1978825 := bbase (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) (by norm_num)
theorem B2347469 : Blo 1563479 2347469 := bbase (se 3 (by rfl) ⟨440150, by rfl⟩ : syracuseStep 2347469 = 880301) (by norm_num)
theorem B3961325 : Blo 1563479 3961325 := bbase (se 3 (by rfl) ⟨742748, by rfl⟩ : syracuseStep 3961325 = 1485497) (by norm_num)
theorem B4452869 : Blo 1563479 4452869 := bbase (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) (by norm_num)
theorem B3518981 : Blo 1563479 3518981 := bbase (se 4 (by rfl) ⟨329904, by rfl⟩ : syracuseStep 3518981 = 659809) (by norm_num)
theorem B1978921 : Blo 1563479 1978921 := bbase (se 2 (by rfl) ⟨742095, by rfl⟩ : syracuseStep 1978921 = 1484191) (by norm_num)
theorem B3519053 : Blo 1563479 3519053 := bbase (se 3 (by rfl) ⟨659822, by rfl⟩ : syracuseStep 3519053 = 1319645) (by norm_num)
theorem B5280389 : Blo 1563479 5280389 := bbase (se 4 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 5280389 = 990073) (by norm_num)
theorem B3519125 : Blo 1563479 3519125 := bbase (se 6 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 3519125 = 164959) (by norm_num)
theorem B1979093 : Blo 1563479 1979093 := bbase (se 7 (by rfl) ⟨23192, by rfl⟩ : syracuseStep 1979093 = 46385) (by norm_num)
theorem B5010133 : Blo 1563479 5010133 := bbase (se 7 (by rfl) ⟨58712, by rfl⟩ : syracuseStep 5010133 = 117425) (by norm_num)
theorem B3519197 : Blo 1563479 3519197 := bbase (se 3 (by rfl) ⟨659849, by rfl⟩ : syracuseStep 3519197 = 1319699) (by norm_num)
theorem B2970341 : Blo 1563479 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B1979149 : Blo 1563479 1979149 := bbase (se 3 (by rfl) ⟨371090, by rfl⟩ : syracuseStep 1979149 = 742181) (by norm_num)
theorem B3519269 : Blo 1563479 3519269 := bbase (se 4 (by rfl) ⟨329931, by rfl⟩ : syracuseStep 3519269 = 659863) (by norm_num)
theorem B1586017 : Blo 1563479 1586017 := bbase (se 2 (by rfl) ⟨594756, by rfl⟩ : syracuseStep 1586017 = 1189513) (by norm_num)
theorem B1979245 : Blo 1563479 1979245 := bbase (se 3 (by rfl) ⟨371108, by rfl⟩ : syracuseStep 1979245 = 742217) (by norm_num)
theorem B3519341 : Blo 1563479 3519341 := bbase (se 3 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 3519341 = 1319753) (by norm_num)
theorem B3756917 : Blo 1563479 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B4576117 : Blo 1563479 4576117 := bbase (se 5 (by rfl) ⟨214505, by rfl⟩ : syracuseStep 4576117 = 429011) (by norm_num)
theorem B2675581 : Blo 1563479 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B6607781 : Blo 1563479 6607781 := bbase (se 4 (by rfl) ⟨619479, by rfl⟩ : syracuseStep 6607781 = 1238959) (by norm_num)
theorem B3519413 : Blo 1563479 3519413 := bbase (se 5 (by rfl) ⟨164972, by rfl⟩ : syracuseStep 3519413 = 329945) (by norm_num)
theorem B2118637 : Blo 1563479 2118637 := bbase (se 3 (by rfl) ⟨397244, by rfl⟩ : syracuseStep 2118637 = 794489) (by norm_num)
theorem B3519485 : Blo 1563479 3519485 := bbase (se 3 (by rfl) ⟨659903, by rfl⟩ : syracuseStep 3519485 = 1319807) (by norm_num)
theorem B3757061 : Blo 1563479 3757061 := bbase (se 4 (by rfl) ⟨352224, by rfl⟩ : syracuseStep 3757061 = 704449) (by norm_num)
theorem B4756501 : Blo 1563479 4756501 := bbase (se 6 (by rfl) ⟨111480, by rfl⟩ : syracuseStep 4756501 = 222961) (by norm_num)
theorem B1979417 : Blo 1563479 1979417 := bbase (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) (by norm_num)
theorem B5280821 : Blo 1563479 5280821 := bbase (se 5 (by rfl) ⟨247538, by rfl⟩ : syracuseStep 5280821 = 495077) (by norm_num)
theorem B3519557 : Blo 1563479 3519557 := bbase (se 4 (by rfl) ⟨329958, by rfl⟩ : syracuseStep 3519557 = 659917) (by norm_num)
theorem B1979473 : Blo 1563479 1979473 := bbase (se 2 (by rfl) ⟨742302, by rfl⟩ : syracuseStep 1979473 = 1484605) (by norm_num)
theorem B3519629 : Blo 1563479 3519629 := bbase (se 3 (by rfl) ⟨659930, by rfl⟩ : syracuseStep 3519629 = 1319861) (by norm_num)
theorem B1979569 : Blo 1563479 1979569 := bbase (se 2 (by rfl) ⟨742338, by rfl⟩ : syracuseStep 1979569 = 1484677) (by norm_num)
theorem B3519701 : Blo 1563479 3519701 := bbase (se 7 (by rfl) ⟨41246, by rfl⟩ : syracuseStep 3519701 = 82493) (by norm_num)
theorem B3568909 : Blo 1563479 3568909 := bbase (se 3 (by rfl) ⟨669170, by rfl⟩ : syracuseStep 3568909 = 1338341) (by norm_num)
theorem B3519773 : Blo 1563479 3519773 := bbase (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) (by norm_num)
theorem B1979741 : Blo 1563479 1979741 := bbase (se 3 (by rfl) ⟨371201, by rfl⟩ : syracuseStep 1979741 = 742403) (by norm_num)
theorem B3519845 : Blo 1563479 3519845 := bbase (se 4 (by rfl) ⟨329985, by rfl⟩ : syracuseStep 3519845 = 659971) (by norm_num)
theorem B1979797 : Blo 1563479 1979797 := bbase (se 6 (by rfl) ⟨46401, by rfl⟩ : syracuseStep 1979797 = 92803) (by norm_num)
theorem B3519917 : Blo 1563479 3519917 := bbase (se 3 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 3519917 = 1319969) (by norm_num)
theorem B2676149 : Blo 1563479 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B7919045 : Blo 1563479 7919045 := bbase (se 4 (by rfl) ⟨742410, by rfl⟩ : syracuseStep 7919045 = 1484821) (by norm_num)
theorem B3569093 : Blo 1563479 3569093 := bbase (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) (by norm_num)
theorem B5936597 : Blo 1563479 5936597 := bbase (se 7 (by rfl) ⟨69569, by rfl⟩ : syracuseStep 5936597 = 139139) (by norm_num)
theorem B5281253 : Blo 1563479 5281253 := bbase (se 4 (by rfl) ⟨495117, by rfl⟩ : syracuseStep 5281253 = 990235) (by norm_num)
theorem B1979893 : Blo 1563479 1979893 := bbase (se 5 (by rfl) ⟨92807, by rfl⟩ : syracuseStep 1979893 = 185615) (by norm_num)
theorem B3519989 : Blo 1563479 3519989 := bbase (se 5 (by rfl) ⟨164999, by rfl⟩ : syracuseStep 3519989 = 329999) (by norm_num)
theorem B3520061 : Blo 1563479 3520061 := bbase (se 3 (by rfl) ⟨660011, by rfl⟩ : syracuseStep 3520061 = 1320023) (by norm_num)
theorem B3520133 : Blo 1563479 3520133 := bbase (se 4 (by rfl) ⟨330012, by rfl⟩ : syracuseStep 3520133 = 660025) (by norm_num)
theorem B1980065 : Blo 1563479 1980065 := bbase (se 2 (by rfl) ⟨742524, by rfl⟩ : syracuseStep 1980065 = 1485049) (by norm_num)
theorem B6682277 : Blo 1563479 6682277 := bbase (se 4 (by rfl) ⟨626463, by rfl⟩ : syracuseStep 6682277 = 1252927) (by norm_num)
theorem B3520205 : Blo 1563479 3520205 := bbase (se 3 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 3520205 = 1320077) (by norm_num)
theorem B1758937 : Blo 1563479 1758937 := bbase (se 2 (by rfl) ⟨659601, by rfl⟩ : syracuseStep 1758937 = 1319203) (by norm_num)
theorem B1980121 : Blo 1563479 1980121 := bbase (se 2 (by rfl) ⟨742545, by rfl⟩ : syracuseStep 1980121 = 1485091) (by norm_num)
theorem B5936885 : Blo 1563479 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B1758973 : Blo 1563479 1758973 := bbase (se 3 (by rfl) ⟨329807, by rfl⟩ : syracuseStep 1758973 = 659615) (by norm_num)
theorem B3340045 : Blo 1563479 3340045 := bbase (se 3 (by rfl) ⟨626258, by rfl⟩ : syracuseStep 3340045 = 1252517) (by norm_num)
theorem B20035349 : Blo 1563479 20035349 := bbase (se 6 (by rfl) ⟨469578, by rfl⟩ : syracuseStep 20035349 = 939157) (by norm_num)
theorem B3520277 : Blo 1563479 3520277 := bbase (se 6 (by rfl) ⟨82506, by rfl⟩ : syracuseStep 3520277 = 165013) (by norm_num)
theorem B1759009 : Blo 1563479 1759009 := bbase (se 2 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 1759009 = 1319257) (by norm_num)
theorem B1980217 : Blo 1563479 1980217 := bbase (se 2 (by rfl) ⟨742581, by rfl⟩ : syracuseStep 1980217 = 1485163) (by norm_num)
theorem B1759045 : Blo 1563479 1759045 := bbase (se 4 (by rfl) ⟨164910, by rfl⟩ : syracuseStep 1759045 = 329821) (by norm_num)
theorem B3520349 : Blo 1563479 3520349 := bbase (se 3 (by rfl) ⟨660065, by rfl⟩ : syracuseStep 3520349 = 1320131) (by norm_num)
theorem B1759081 : Blo 1563479 1759081 := bbase (se 2 (by rfl) ⟨659655, by rfl⟩ : syracuseStep 1759081 = 1319311) (by norm_num)
theorem B1759117 : Blo 1563479 1759117 := bbase (se 3 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 1759117 = 659669) (by norm_num)
theorem B5281685 : Blo 1563479 5281685 := bbase (se 6 (by rfl) ⟨123789, by rfl⟩ : syracuseStep 5281685 = 247579) (by norm_num)
theorem B3520421 : Blo 1563479 3520421 := bbase (se 4 (by rfl) ⟨330039, by rfl⟩ : syracuseStep 3520421 = 660079) (by norm_num)
theorem B1759153 : Blo 1563479 1759153 := bbase (se 2 (by rfl) ⟨659682, by rfl⟩ : syracuseStep 1759153 = 1319365) (by norm_num)
theorem B2226133 : Blo 1563479 2226133 := bbase (se 7 (by rfl) ⟨26087, by rfl⟩ : syracuseStep 2226133 = 52175) (by norm_num)
theorem B1759189 : Blo 1563479 1759189 := bbase (se 7 (by rfl) ⟨20615, by rfl⟩ : syracuseStep 1759189 = 41231) (by norm_num)
theorem B1980389 : Blo 1563479 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B3520493 : Blo 1563479 3520493 := bbase (se 3 (by rfl) ⟨660092, by rfl⟩ : syracuseStep 3520493 = 1320185) (by norm_num)
theorem B1759225 : Blo 1563479 1759225 := bbase (se 2 (by rfl) ⟨659709, by rfl⟩ : syracuseStep 1759225 = 1319419) (by norm_num)
theorem B1759261 : Blo 1563479 1759261 := bbase (se 3 (by rfl) ⟨329861, by rfl⟩ : syracuseStep 1759261 = 659723) (by norm_num)
theorem B1980445 : Blo 1563479 1980445 := bbase (se 3 (by rfl) ⟨371333, by rfl⟩ : syracuseStep 1980445 = 742667) (by norm_num)
theorem B4454453 : Blo 1563479 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B3520565 : Blo 1563479 3520565 := bbase (se 5 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 3520565 = 330053) (by norm_num)
theorem B2504765 : Blo 1563479 2504765 := bbase (se 3 (by rfl) ⟨469643, by rfl⟩ : syracuseStep 2504765 = 939287) (by norm_num)
theorem B1759297 : Blo 1563479 1759297 := bbase (se 2 (by rfl) ⟨659736, by rfl⟩ : syracuseStep 1759297 = 1319473) (by norm_num)
theorem B1759333 : Blo 1563479 1759333 := bbase (se 4 (by rfl) ⟨164937, by rfl⟩ : syracuseStep 1759333 = 329875) (by norm_num)
theorem B3520637 : Blo 1563479 3520637 := bbase (se 3 (by rfl) ⟨660119, by rfl⟩ : syracuseStep 3520637 = 1320239) (by norm_num)
theorem B1980541 : Blo 1563479 1980541 := bbase (se 3 (by rfl) ⟨371351, by rfl⟩ : syracuseStep 1980541 = 742703) (by norm_num)
theorem B1759369 : Blo 1563479 1759369 := bbase (se 2 (by rfl) ⟨659763, by rfl⟩ : syracuseStep 1759369 = 1319527) (by norm_num)
theorem B1759405 : Blo 1563479 1759405 := bbase (se 3 (by rfl) ⟨329888, by rfl⟩ : syracuseStep 1759405 = 659777) (by norm_num)
theorem B3520709 : Blo 1563479 3520709 := bbase (se 4 (by rfl) ⟨330066, by rfl⟩ : syracuseStep 3520709 = 660133) (by norm_num)
theorem B1759441 : Blo 1563479 1759441 := bbase (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) (by norm_num)
theorem B1759477 : Blo 1563479 1759477 := bbase (se 5 (by rfl) ⟨82475, by rfl⟩ : syracuseStep 1759477 = 164951) (by norm_num)
theorem B3340541 : Blo 1563479 3340541 := bbase (se 3 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 3340541 = 1252703) (by norm_num)
theorem B3520781 : Blo 1563479 3520781 := bbase (se 3 (by rfl) ⟨660146, by rfl⟩ : syracuseStep 3520781 = 1320293) (by norm_num)
theorem B5011733 : Blo 1563479 5011733 := bbase (se 6 (by rfl) ⟨117462, by rfl⟩ : syracuseStep 5011733 = 234925) (by norm_num)
theorem B12687637 : Blo 1563479 12687637 := bbase (se 6 (by rfl) ⟨297366, by rfl⟩ : syracuseStep 12687637 = 594733) (by norm_num)
theorem B1759513 : Blo 1563479 1759513 := bbase (se 2 (by rfl) ⟨659817, by rfl⟩ : syracuseStep 1759513 = 1319635) (by norm_num)
theorem B2226469 : Blo 1563479 2226469 := bbase (se 4 (by rfl) ⟨208731, by rfl⟩ : syracuseStep 2226469 = 417463) (by norm_num)
theorem B1759549 : Blo 1563479 1759549 := bbase (se 3 (by rfl) ⟨329915, by rfl⟩ : syracuseStep 1759549 = 659831) (by norm_num)
theorem B3520853 : Blo 1563479 3520853 := bbase (se 10 (by rfl) ⟨5157, by rfl⟩ : syracuseStep 3520853 = 10315) (by norm_num)
theorem B1759585 : Blo 1563479 1759585 := bbase (se 2 (by rfl) ⟨659844, by rfl⟩ : syracuseStep 1759585 = 1319689) (by norm_num)
theorem B11278709 : Blo 1563479 11278709 := bbase (se 5 (by rfl) ⟨528689, by rfl⟩ : syracuseStep 11278709 = 1057379) (by norm_num)
theorem B1759621 : Blo 1563479 1759621 := bbase (se 4 (by rfl) ⟨164964, by rfl⟩ : syracuseStep 1759621 = 329929) (by norm_num)
theorem B3520925 : Blo 1563479 3520925 := bbase (se 3 (by rfl) ⟨660173, by rfl⟩ : syracuseStep 3520925 = 1320347) (by norm_num)
theorem B1759657 : Blo 1563479 1759657 := bbase (se 2 (by rfl) ⟨659871, by rfl⟩ : syracuseStep 1759657 = 1319743) (by norm_num)
theorem B1759693 : Blo 1563479 1759693 := bbase (se 3 (by rfl) ⟨329942, by rfl⟩ : syracuseStep 1759693 = 659885) (by norm_num)
theorem B3520997 : Blo 1563479 3520997 := bbase (se 4 (by rfl) ⟨330093, by rfl⟩ : syracuseStep 3520997 = 660187) (by norm_num)
theorem B1759729 : Blo 1563479 1759729 := bbase (se 2 (by rfl) ⟨659898, by rfl⟩ : syracuseStep 1759729 = 1319797) (by norm_num)
theorem B1784305 : Blo 1563479 1784305 := bbase (se 2 (by rfl) ⟨669114, by rfl⟩ : syracuseStep 1784305 = 1338229) (by norm_num)
theorem B1669621 : Blo 1563479 1669621 := bbase (se 5 (by rfl) ⟨78263, by rfl⟩ : syracuseStep 1669621 = 156527) (by norm_num)
theorem B2226685 : Blo 1563479 2226685 := bbase (se 3 (by rfl) ⟨417503, by rfl⟩ : syracuseStep 2226685 = 835007) (by norm_num)
theorem B2857477 : Blo 1563479 2857477 := bbase (se 4 (by rfl) ⟨267888, by rfl⟩ : syracuseStep 2857477 = 535777) (by norm_num)
theorem B1759765 : Blo 1563479 1759765 := bbase (se 6 (by rfl) ⟨41244, by rfl⟩ : syracuseStep 1759765 = 82489) (by norm_num)
theorem B3521069 : Blo 1563479 3521069 := bbase (se 3 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 3521069 = 1320401) (by norm_num)
theorem B1669681 : Blo 1563479 1669681 := bbase (se 2 (by rfl) ⟨626130, by rfl⟩ : syracuseStep 1669681 = 1252261) (by norm_num)
theorem B1759801 : Blo 1563479 1759801 := bbase (se 2 (by rfl) ⟨659925, by rfl⟩ : syracuseStep 1759801 = 1319851) (by norm_num)
theorem B2505277 : Blo 1563479 2505277 := bbase (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) (by norm_num)
theorem B1759837 : Blo 1563479 1759837 := bbase (se 3 (by rfl) ⟨329969, by rfl⟩ : syracuseStep 1759837 = 659939) (by norm_num)
theorem B3521141 : Blo 1563479 3521141 := bbase (se 5 (by rfl) ⟨165053, by rfl⟩ : syracuseStep 3521141 = 330107) (by norm_num)
theorem B1759873 : Blo 1563479 1759873 := bbase (se 2 (by rfl) ⟨659952, by rfl⟩ : syracuseStep 1759873 = 1319905) (by norm_num)
theorem B1759909 : Blo 1563479 1759909 := bbase (se 4 (by rfl) ⟨164991, by rfl⟩ : syracuseStep 1759909 = 329983) (by norm_num)
theorem B1759945 : Blo 1563479 1759945 := bbase (se 2 (by rfl) ⟨659979, by rfl⟩ : syracuseStep 1759945 = 1319959) (by norm_num)
theorem B4455125 : Blo 1563479 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B7920341 : Blo 1563479 7920341 := bbase (se 7 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 7920341 = 185633) (by norm_num)
theorem B1759981 : Blo 1563479 1759981 := bbase (se 3 (by rfl) ⟨329996, by rfl⟩ : syracuseStep 1759981 = 659993) (by norm_num)
theorem B1760017 : Blo 1563479 1760017 := bbase (se 2 (by rfl) ⟨660006, by rfl⟩ : syracuseStep 1760017 = 1320013) (by norm_num)
theorem B1760053 : Blo 1563479 1760053 := bbase (se 5 (by rfl) ⟨82502, by rfl⟩ : syracuseStep 1760053 = 165005) (by norm_num)
theorem B7519061 : Blo 1563479 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B1760089 : Blo 1563479 1760089 := bbase (se 2 (by rfl) ⟨660033, by rfl⟩ : syracuseStep 1760089 = 1320067) (by norm_num)
theorem B1669997 : Blo 1563479 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B2227061 : Blo 1563479 2227061 := bbase (se 5 (by rfl) ⟨104393, by rfl⟩ : syracuseStep 2227061 = 208787) (by norm_num)
theorem B1760125 : Blo 1563479 1760125 := bbase (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) (by norm_num)
theorem B5938069 : Blo 1563479 5938069 := bbase (se 6 (by rfl) ⟨139173, by rfl⟩ : syracuseStep 5938069 = 278347) (by norm_num)
theorem B1760161 : Blo 1563479 1760161 := bbase (se 2 (by rfl) ⟨660060, by rfl⟩ : syracuseStep 1760161 = 1320121) (by norm_num)
theorem B1760197 : Blo 1563479 1760197 := bbase (se 4 (by rfl) ⟨165018, by rfl⟩ : syracuseStep 1760197 = 330037) (by norm_num)
theorem B3759061 : Blo 1563479 3759061 := bbase (se 7 (by rfl) ⟨44051, by rfl⟩ : syracuseStep 3759061 = 88103) (by norm_num)
theorem B1760233 : Blo 1563479 1760233 := bbase (se 2 (by rfl) ⟨660087, by rfl⟩ : syracuseStep 1760233 = 1320175) (by norm_num)
theorem B1760269 : Blo 1563479 1760269 := bbase (se 3 (by rfl) ⟨330050, by rfl⟩ : syracuseStep 1760269 = 660101) (by norm_num)
theorem B1760305 : Blo 1563479 1760305 := bbase (se 2 (by rfl) ⟨660114, by rfl⟩ : syracuseStep 1760305 = 1320229) (by norm_num)
theorem B1760341 : Blo 1563479 1760341 := bbase (se 8 (by rfl) ⟨10314, by rfl⟩ : syracuseStep 1760341 = 20629) (by norm_num)
theorem B3341429 : Blo 1563479 3341429 := bbase (se 5 (by rfl) ⟨156629, by rfl⟩ : syracuseStep 3341429 = 313259) (by norm_num)
theorem B2006137 : Blo 1563479 2006137 := bbase (se 2 (by rfl) ⟨752301, by rfl⟩ : syracuseStep 2006137 = 1504603) (by norm_num)
theorem B1760377 : Blo 1563479 1760377 := bbase (se 2 (by rfl) ⟨660141, by rfl⟩ : syracuseStep 1760377 = 1320283) (by norm_num)
theorem B4455557 : Blo 1563479 4455557 := bbase (se 4 (by rfl) ⟨417708, by rfl⟩ : syracuseStep 4455557 = 835417) (by norm_num)
theorem B1760413 : Blo 1563479 1760413 := bbase (se 3 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 1760413 = 660155) (by norm_num)
theorem B2006209 : Blo 1563479 2006209 := bbase (se 2 (by rfl) ⟨752328, by rfl⟩ : syracuseStep 2006209 = 1504657) (by norm_num)
theorem B1760449 : Blo 1563479 1760449 := bbase (se 2 (by rfl) ⟨660168, by rfl⟩ : syracuseStep 1760449 = 1320337) (by norm_num)
theorem B5938373 : Blo 1563479 5938373 := bbase (se 4 (by rfl) ⟨556722, by rfl⟩ : syracuseStep 5938373 = 1113445) (by norm_num)
theorem B1760485 : Blo 1563479 1760485 := bbase (se 4 (by rfl) ⟨165045, by rfl⟩ : syracuseStep 1760485 = 330091) (by norm_num)
theorem B3341549 : Blo 1563479 3341549 := bbase (se 3 (by rfl) ⟨626540, by rfl⟩ : syracuseStep 3341549 = 1253081) (by norm_num)
theorem B1760521 : Blo 1563479 1760521 := bbase (se 2 (by rfl) ⟨660195, by rfl⟩ : syracuseStep 1760521 = 1320391) (by norm_num)
theorem B1670441 : Blo 1563479 1670441 := bbase (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) (by norm_num)
theorem B1760557 : Blo 1563479 1760557 := bbase (se 3 (by rfl) ⟨330104, by rfl⟩ : syracuseStep 1760557 = 660209) (by norm_num)
theorem B1760593 : Blo 1563479 1760593 := bbase (se 2 (by rfl) ⟨660222, by rfl⟩ : syracuseStep 1760593 = 1320445) (by norm_num)
theorem B1670501 : Blo 1563479 1670501 := bbase (se 4 (by rfl) ⟨156609, by rfl⟩ : syracuseStep 1670501 = 313219) (by norm_num)
theorem B5012837 : Blo 1563479 5012837 := bbase (se 4 (by rfl) ⟨469953, by rfl⟩ : syracuseStep 5012837 = 939907) (by norm_num)
theorem B1670629 : Blo 1563479 1670629 := bbase (se 4 (by rfl) ⟨156621, by rfl⟩ : syracuseStep 1670629 = 313243) (by norm_num)
theorem B2506277 : Blo 1563479 2506277 := bbase (se 4 (by rfl) ⟨234963, by rfl⟩ : syracuseStep 2506277 = 469927) (by norm_num)
theorem B26738261 : Blo 1563479 26738261 := bbase (se 8 (by rfl) ⟨156669, by rfl⟩ : syracuseStep 26738261 = 313339) (by norm_num)
theorem B2506405 : Blo 1563479 2506405 := bbase (se 4 (by rfl) ⟨234975, by rfl⟩ : syracuseStep 2506405 = 469951) (by norm_num)
theorem B2506469 : Blo 1563479 2506469 := bbase (se 4 (by rfl) ⟨234981, by rfl⟩ : syracuseStep 2506469 = 469963) (by norm_num)
theorem B3170029 : Blo 1563479 3170029 := bbase (se 3 (by rfl) ⟨594380, by rfl⟩ : syracuseStep 3170029 = 1188761) (by norm_num)
theorem B11280181 : Blo 1563479 11280181 := bbase (se 5 (by rfl) ⟨528758, by rfl⟩ : syracuseStep 11280181 = 1057517) (by norm_num)
theorem B3342181 : Blo 1563479 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B4456309 : Blo 1563479 4456309 := bbase (se 5 (by rfl) ⟨208889, by rfl⟩ : syracuseStep 4456309 = 417779) (by norm_num)
theorem B2236285 : Blo 1563479 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B1671073 : Blo 1563479 1671073 := bbase (se 2 (by rfl) ⟨626652, by rfl⟩ : syracuseStep 1671073 = 1253305) (by norm_num)
theorem B11878325 : Blo 1563479 11878325 := bbase (se 5 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 11878325 = 1113593) (by norm_num)
theorem B4014029 : Blo 1563479 4014029 := bbase (se 3 (by rfl) ⟨752630, by rfl⟩ : syracuseStep 4014029 = 1505261) (by norm_num)
theorem B7921637 : Blo 1563479 7921637 := bbase (se 4 (by rfl) ⟨742653, by rfl⟩ : syracuseStep 7921637 = 1485307) (by norm_num)
theorem B2113525 : Blo 1563479 2113525 := bbase (se 5 (by rfl) ⟨99071, by rfl⟩ : syracuseStep 2113525 = 198143) (by norm_num)
theorem B1564675 : Blo 1563479 1564675 := bstep (se 1 (by rfl) ⟨1173506, by rfl⟩ : syracuseStep 1564675 = 2347013) B2347013
theorem B10018829 : Blo 1563479 10018829 := bstep (se 3 (by rfl) ⟨1878530, by rfl⟩ : syracuseStep 10018829 = 3757061) B3757061
theorem B1564691 : Blo 1563479 1564691 := bstep (se 1 (by rfl) ⟨1173518, by rfl⟩ : syracuseStep 1564691 = 2347037) B2347037
theorem B2228257 : Blo 1563479 2228257 := bstep (se 2 (by rfl) ⟨835596, by rfl⟩ : syracuseStep 2228257 = 1671193) B1671193
theorem B1564707 : Blo 1563479 1564707 := bstep (se 1 (by rfl) ⟨1173530, by rfl⟩ : syracuseStep 1564707 = 2347061) B2347061
theorem B3170353 : Blo 1563479 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B1564723 : Blo 1563479 1564723 := bstep (se 1 (by rfl) ⟨1173542, by rfl⟩ : syracuseStep 1564723 = 2347085) B2347085
theorem B1564739 : Blo 1563479 1564739 := bstep (se 1 (by rfl) ⟨1173554, by rfl⟩ : syracuseStep 1564739 = 2347109) B2347109
theorem B1564755 : Blo 1563479 1564755 := bstep (se 1 (by rfl) ⟨1173566, by rfl⟩ : syracuseStep 1564755 = 2347133) B2347133
theorem B2113633 : Blo 1563479 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B1564771 : Blo 1563479 1564771 := bstep (se 1 (by rfl) ⟨1173578, by rfl⟩ : syracuseStep 1564771 = 2347157) B2347157
theorem B1564787 : Blo 1563479 1564787 := bstep (se 1 (by rfl) ⟨1173590, by rfl⟩ : syracuseStep 1564787 = 2347181) B2347181
theorem B1564803 : Blo 1563479 1564803 := bstep (se 1 (by rfl) ⟨1173602, by rfl⟩ : syracuseStep 1564803 = 2347205) B2347205
theorem B1564819 : Blo 1563479 1564819 := bstep (se 1 (by rfl) ⟨1173614, by rfl⟩ : syracuseStep 1564819 = 2347229) B2347229
theorem B1564835 : Blo 1563479 1564835 := bstep (se 1 (by rfl) ⟨1173626, by rfl⟩ : syracuseStep 1564835 = 2347253) B2347253
theorem B1564851 : Blo 1563479 1564851 := bstep (se 1 (by rfl) ⟨1173638, by rfl⟩ : syracuseStep 1564851 = 2347277) B2347277
theorem B1564867 : Blo 1563479 1564867 := bstep (se 1 (by rfl) ⟨1173650, by rfl⟩ : syracuseStep 1564867 = 2347301) B2347301
theorem B1564883 : Blo 1563479 1564883 := bstep (se 1 (by rfl) ⟨1173662, by rfl⟩ : syracuseStep 1564883 = 2347325) B2347325
theorem B1564899 : Blo 1563479 1564899 := bstep (se 1 (by rfl) ⟨1173674, by rfl⟩ : syracuseStep 1564899 = 2347349) B2347349
theorem B1564915 : Blo 1563479 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B1564931 : Blo 1563479 1564931 := bstep (se 1 (by rfl) ⟨1173698, by rfl⟩ : syracuseStep 1564931 = 2347397) B2347397
theorem B1564947 : Blo 1563479 1564947 := bstep (se 1 (by rfl) ⟨1173710, by rfl⟩ : syracuseStep 1564947 = 2347421) B2347421
theorem B9027875 : Blo 1563479 9027875 := bstep (se 1 (by rfl) ⟨6770906, by rfl⟩ : syracuseStep 9027875 = 13541813) B13541813
theorem B1564963 : Blo 1563479 1564963 := bstep (se 1 (by rfl) ⟨1173722, by rfl⟩ : syracuseStep 1564963 = 2347445) B2347445
theorem B1564979 : Blo 1563479 1564979 := bstep (se 1 (by rfl) ⟨1173734, by rfl⟩ : syracuseStep 1564979 = 2347469) B2347469
theorem B16916849 : Blo 1563479 16916849 := bstep (se 2 (by rfl) ⟨6343818, by rfl⟩ : syracuseStep 16916849 = 12687637) B12687637
theorem B3170801 : Blo 1563479 3170801 := bstep (se 2 (by rfl) ⟨1189050, by rfl⟩ : syracuseStep 3170801 = 2378101) B2378101
theorem B2540081 : Blo 1563479 2540081 := bstep (se 2 (by rfl) ⟨952530, by rfl⟩ : syracuseStep 2540081 = 1905061) B1905061
theorem B2638433 : Blo 1563479 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B10699397 : Blo 1563479 10699397 := bstep (se 4 (by rfl) ⟨1003068, by rfl⟩ : syracuseStep 10699397 = 2006137) B2006137
theorem B3809969 : Blo 1563479 3809969 := bstep (se 2 (by rfl) ⟨1428738, by rfl⟩ : syracuseStep 3809969 = 2857477) B2857477
theorem B2638561 : Blo 1563479 2638561 := bstep (se 2 (by rfl) ⟨989460, by rfl⟩ : syracuseStep 2638561 = 1978921) B1978921
theorem B35242723 : Blo 1563479 35242723 := bstep (se 1 (by rfl) ⟨26432042, by rfl⟩ : syracuseStep 35242723 = 52864085) B52864085
theorem B2638595 : Blo 1563479 2638595 := bstep (se 1 (by rfl) ⟨1978946, by rfl⟩ : syracuseStep 2638595 = 3957893) B3957893
theorem B2638723 : Blo 1563479 2638723 := bstep (se 1 (by rfl) ⟨1979042, by rfl⟩ : syracuseStep 2638723 = 3958085) B3958085
theorem B7922609 : Blo 1563479 7922609 := bstep (se 2 (by rfl) ⟨2970978, by rfl⟩ : syracuseStep 7922609 = 5941957) B5941957
theorem B3957731 : Blo 1563479 3957731 := bstep (se 1 (by rfl) ⟨2968298, by rfl⟩ : syracuseStep 3957731 = 5936597) B5936597
theorem B2638865 : Blo 1563479 2638865 := bstep (se 2 (by rfl) ⟨989574, by rfl⟩ : syracuseStep 2638865 = 1979149) B1979149
theorem B6865955 : Blo 1563479 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B5276771 : Blo 1563479 5276771 := bstep (se 1 (by rfl) ⟨3957578, by rfl⟩ : syracuseStep 5276771 = 7915157) B7915157
theorem B2114689 : Blo 1563479 2114689 := bstep (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) B1586017
theorem B2638993 : Blo 1563479 2638993 := bstep (se 2 (by rfl) ⟨989622, by rfl⟩ : syracuseStep 2638993 = 1979245) B1979245
theorem B3957923 : Blo 1563479 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B2639027 : Blo 1563479 2639027 := bstep (se 1 (by rfl) ⟨1979270, by rfl⟩ : syracuseStep 2639027 = 3958541) B3958541
theorem B2639155 : Blo 1563479 2639155 := bstep (se 1 (by rfl) ⟨1979366, by rfl⟩ : syracuseStep 2639155 = 3958733) B3958733
theorem B5277041 : Blo 1563479 5277041 := bstep (se 2 (by rfl) ⟨1978890, by rfl⟩ : syracuseStep 5277041 = 3957781) B3957781
theorem B2639297 : Blo 1563479 2639297 := bstep (se 2 (by rfl) ⟨989736, by rfl⟩ : syracuseStep 2639297 = 1979473) B1979473
theorem B2639425 : Blo 1563479 2639425 := bstep (se 2 (by rfl) ⟨989784, by rfl⟩ : syracuseStep 2639425 = 1979569) B1979569
theorem B2639459 : Blo 1563479 2639459 := bstep (se 1 (by rfl) ⟨1979594, by rfl⟩ : syracuseStep 2639459 = 3959189) B3959189
theorem B1607347 : Blo 1563479 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B2639587 : Blo 1563479 2639587 := bstep (se 1 (by rfl) ⟨1979690, by rfl⟩ : syracuseStep 2639587 = 3959381) B3959381
theorem B2639729 : Blo 1563479 2639729 := bstep (se 2 (by rfl) ⟨989898, by rfl⟩ : syracuseStep 2639729 = 1979797) B1979797
theorem B5277581 : Blo 1563479 5277581 := bstep (se 3 (by rfl) ⟨989546, by rfl⟩ : syracuseStep 5277581 = 1979093) B1979093
theorem B5277635 : Blo 1563479 5277635 := bstep (se 1 (by rfl) ⟨3958226, by rfl⟩ : syracuseStep 5277635 = 7916453) B7916453
theorem B2377667 : Blo 1563479 2377667 := bstep (se 1 (by rfl) ⟨1783250, by rfl⟩ : syracuseStep 2377667 = 3566501) B3566501
theorem B9512909 : Blo 1563479 9512909 := bstep (se 3 (by rfl) ⟨1783670, by rfl⟩ : syracuseStep 9512909 = 3567341) B3567341
theorem B8456177 : Blo 1563479 8456177 := bstep (se 2 (by rfl) ⟨3171066, by rfl⟩ : syracuseStep 8456177 = 6342133) B6342133
theorem B2639857 : Blo 1563479 2639857 := bstep (se 2 (by rfl) ⟨989946, by rfl⟩ : syracuseStep 2639857 = 1979893) B1979893
theorem B16918541 : Blo 1563479 16918541 := bstep (se 3 (by rfl) ⟨3172226, by rfl⟩ : syracuseStep 16918541 = 6344453) B6344453
theorem B2639891 : Blo 1563479 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B3958865 : Blo 1563479 3958865 := bstep (se 2 (by rfl) ⟨1484574, by rfl⟩ : syracuseStep 3958865 = 2969149) B2969149
theorem B3958915 : Blo 1563479 3958915 := bstep (se 1 (by rfl) ⟨2969186, by rfl⟩ : syracuseStep 3958915 = 5938373) B5938373
theorem B2640019 : Blo 1563479 2640019 := bstep (se 1 (by rfl) ⟨1980014, by rfl⟩ : syracuseStep 2640019 = 3960029) B3960029
theorem B5277905 : Blo 1563479 5277905 := bstep (se 2 (by rfl) ⟨1979214, by rfl⟩ : syracuseStep 5277905 = 3958429) B3958429
theorem B2345219 : Blo 1563479 2345219 := bstep (se 1 (by rfl) ⟨1758914, by rfl⟩ : syracuseStep 2345219 = 3517829) B3517829
theorem B3959057 : Blo 1563479 3959057 := bstep (se 2 (by rfl) ⟨1484646, by rfl⟩ : syracuseStep 3959057 = 2969293) B2969293
theorem B2345249 : Blo 1563479 2345249 := bstep (se 2 (by rfl) ⟨879468, by rfl⟩ : syracuseStep 2345249 = 1758937) B1758937
theorem B2640161 : Blo 1563479 2640161 := bstep (se 2 (by rfl) ⟨990060, by rfl⟩ : syracuseStep 2640161 = 1980121) B1980121
theorem B2345267 : Blo 1563479 2345267 := bstep (se 1 (by rfl) ⟨1758950, by rfl⟩ : syracuseStep 2345267 = 3517901) B3517901
theorem B2345297 : Blo 1563479 2345297 := bstep (se 2 (by rfl) ⟨879486, by rfl⟩ : syracuseStep 2345297 = 1758973) B1758973
theorem B2345315 : Blo 1563479 2345315 := bstep (se 1 (by rfl) ⟨1758986, by rfl⟩ : syracuseStep 2345315 = 3517973) B3517973
theorem B2345345 : Blo 1563479 2345345 := bstep (se 2 (by rfl) ⟨879504, by rfl⟩ : syracuseStep 2345345 = 1759009) B1759009
theorem B2345363 : Blo 1563479 2345363 := bstep (se 1 (by rfl) ⟨1759022, by rfl⟩ : syracuseStep 2345363 = 3518045) B3518045
theorem B2640289 : Blo 1563479 2640289 := bstep (se 2 (by rfl) ⟨990108, by rfl⟩ : syracuseStep 2640289 = 1980217) B1980217
theorem B2345393 : Blo 1563479 2345393 := bstep (se 2 (by rfl) ⟨879522, by rfl⟩ : syracuseStep 2345393 = 1759045) B1759045
theorem B2345411 : Blo 1563479 2345411 := bstep (se 1 (by rfl) ⟨1759058, by rfl⟩ : syracuseStep 2345411 = 3518117) B3518117
theorem B2640323 : Blo 1563479 2640323 := bstep (se 1 (by rfl) ⟨1980242, by rfl⟩ : syracuseStep 2640323 = 3960485) B3960485
theorem B2345441 : Blo 1563479 2345441 := bstep (se 2 (by rfl) ⟨879540, by rfl⟩ : syracuseStep 2345441 = 1759081) B1759081
theorem B5941745 : Blo 1563479 5941745 := bstep (se 2 (by rfl) ⟨2228154, by rfl⟩ : syracuseStep 5941745 = 4456309) B4456309
theorem B2345459 : Blo 1563479 2345459 := bstep (se 1 (by rfl) ⟨1759094, by rfl⟩ : syracuseStep 2345459 = 3518189) B3518189
theorem B2345489 : Blo 1563479 2345489 := bstep (se 2 (by rfl) ⟨879558, by rfl⟩ : syracuseStep 2345489 = 1759117) B1759117
theorem B2345507 : Blo 1563479 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B3664433 : Blo 1563479 3664433 := bstep (se 2 (by rfl) ⟨1374162, by rfl⟩ : syracuseStep 3664433 = 2748325) B2748325
theorem B2345537 : Blo 1563479 2345537 := bstep (se 2 (by rfl) ⟨879576, by rfl⟩ : syracuseStep 2345537 = 1759153) B1759153
theorem B2640451 : Blo 1563479 2640451 := bstep (se 1 (by rfl) ⟨1980338, by rfl⟩ : syracuseStep 2640451 = 3960677) B3960677
theorem B2345555 : Blo 1563479 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B2968177 : Blo 1563479 2968177 := bstep (se 2 (by rfl) ⟨1113066, by rfl⟩ : syracuseStep 2968177 = 2226133) B2226133
theorem B2345585 : Blo 1563479 2345585 := bstep (se 2 (by rfl) ⟨879594, by rfl⟩ : syracuseStep 2345585 = 1759189) B1759189
theorem B2345603 : Blo 1563479 2345603 := bstep (se 1 (by rfl) ⟨1759202, by rfl⟩ : syracuseStep 2345603 = 3518405) B3518405
theorem B2345633 : Blo 1563479 2345633 := bstep (se 2 (by rfl) ⟨879612, by rfl⟩ : syracuseStep 2345633 = 1759225) B1759225
theorem B2345651 : Blo 1563479 2345651 := bstep (se 1 (by rfl) ⟨1759238, by rfl⟩ : syracuseStep 2345651 = 3518477) B3518477
theorem B2345681 : Blo 1563479 2345681 := bstep (se 2 (by rfl) ⟨879630, by rfl⟩ : syracuseStep 2345681 = 1759261) B1759261
theorem B2640593 : Blo 1563479 2640593 := bstep (se 2 (by rfl) ⟨990222, by rfl⟩ : syracuseStep 2640593 = 1980445) B1980445
theorem B2345699 : Blo 1563479 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B5278445 : Blo 1563479 5278445 := bstep (se 3 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 5278445 = 1979417) B1979417
theorem B2345729 : Blo 1563479 2345729 := bstep (se 2 (by rfl) ⟨879648, by rfl⟩ : syracuseStep 2345729 = 1759297) B1759297
theorem B2345747 : Blo 1563479 2345747 := bstep (se 1 (by rfl) ⟨1759310, by rfl⟩ : syracuseStep 2345747 = 3518621) B3518621
theorem B5278499 : Blo 1563479 5278499 := bstep (se 1 (by rfl) ⟨3958874, by rfl⟩ : syracuseStep 5278499 = 7917749) B7917749
theorem B2345777 : Blo 1563479 2345777 := bstep (se 2 (by rfl) ⟨879666, by rfl⟩ : syracuseStep 2345777 = 1759333) B1759333
theorem B2345795 : Blo 1563479 2345795 := bstep (se 1 (by rfl) ⟨1759346, by rfl⟩ : syracuseStep 2345795 = 3518693) B3518693
theorem B3615569 : Blo 1563479 3615569 := bstep (se 2 (by rfl) ⟨1355838, by rfl⟩ : syracuseStep 3615569 = 2711677) B2711677
theorem B2640721 : Blo 1563479 2640721 := bstep (se 2 (by rfl) ⟨990270, by rfl⟩ : syracuseStep 2640721 = 1980541) B1980541
theorem B2345825 : Blo 1563479 2345825 := bstep (se 2 (by rfl) ⟨879684, by rfl⟩ : syracuseStep 2345825 = 1759369) B1759369
theorem B2345843 : Blo 1563479 2345843 := bstep (se 1 (by rfl) ⟨1759382, by rfl⟩ : syracuseStep 2345843 = 3518765) B3518765
theorem B2640755 : Blo 1563479 2640755 := bstep (se 1 (by rfl) ⟨1980566, by rfl⟩ : syracuseStep 2640755 = 3961133) B3961133
theorem B2345873 : Blo 1563479 2345873 := bstep (se 2 (by rfl) ⟨879702, by rfl⟩ : syracuseStep 2345873 = 1759405) B1759405
theorem B2345891 : Blo 1563479 2345891 := bstep (se 1 (by rfl) ⟨1759418, by rfl⟩ : syracuseStep 2345891 = 3518837) B3518837
theorem B2345921 : Blo 1563479 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B2345939 : Blo 1563479 2345939 := bstep (se 1 (by rfl) ⟨1759454, by rfl⟩ : syracuseStep 2345939 = 3518909) B3518909
theorem B5499875 : Blo 1563479 5499875 := bstep (se 1 (by rfl) ⟨4124906, by rfl⟩ : syracuseStep 5499875 = 8249813) B8249813
theorem B2345969 : Blo 1563479 2345969 := bstep (se 2 (by rfl) ⟨879738, by rfl⟩ : syracuseStep 2345969 = 1759477) B1759477
theorem B2640883 : Blo 1563479 2640883 := bstep (se 1 (by rfl) ⟨1980662, by rfl⟩ : syracuseStep 2640883 = 3961325) B3961325
theorem B2968579 : Blo 1563479 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B2345987 : Blo 1563479 2345987 := bstep (se 1 (by rfl) ⟨1759490, by rfl⟩ : syracuseStep 2345987 = 3518981) B3518981
theorem B2346017 : Blo 1563479 2346017 := bstep (se 2 (by rfl) ⟨879756, by rfl⟩ : syracuseStep 2346017 = 1759513) B1759513
theorem B2968625 : Blo 1563479 2968625 := bstep (se 2 (by rfl) ⟨1113234, by rfl⟩ : syracuseStep 2968625 = 2226469) B2226469
theorem B5278769 : Blo 1563479 5278769 := bstep (se 2 (by rfl) ⟨1979538, by rfl⟩ : syracuseStep 5278769 = 3959077) B3959077
theorem B2346035 : Blo 1563479 2346035 := bstep (se 1 (by rfl) ⟨1759526, by rfl⟩ : syracuseStep 2346035 = 3519053) B3519053
theorem B2346065 : Blo 1563479 2346065 := bstep (se 2 (by rfl) ⟨879774, by rfl⟩ : syracuseStep 2346065 = 1759549) B1759549
theorem B2346083 : Blo 1563479 2346083 := bstep (se 1 (by rfl) ⟨1759562, by rfl⟩ : syracuseStep 2346083 = 3519125) B3519125
theorem B2346113 : Blo 1563479 2346113 := bstep (se 2 (by rfl) ⟨879792, by rfl⟩ : syracuseStep 2346113 = 1759585) B1759585
theorem B2346131 : Blo 1563479 2346131 := bstep (se 1 (by rfl) ⟨1759598, by rfl⟩ : syracuseStep 2346131 = 3519197) B3519197
theorem B2346161 : Blo 1563479 2346161 := bstep (se 2 (by rfl) ⟨879810, by rfl⟩ : syracuseStep 2346161 = 1759621) B1759621
theorem B2346179 : Blo 1563479 2346179 := bstep (se 1 (by rfl) ⟨1759634, by rfl⟩ : syracuseStep 2346179 = 3519269) B3519269
theorem B2346209 : Blo 1563479 2346209 := bstep (se 2 (by rfl) ⟨879828, by rfl⟩ : syracuseStep 2346209 = 1759657) B1759657
theorem B3960049 : Blo 1563479 3960049 := bstep (se 2 (by rfl) ⟨1485018, by rfl⟩ : syracuseStep 3960049 = 2970037) B2970037
theorem B2346227 : Blo 1563479 2346227 := bstep (se 1 (by rfl) ⟨1759670, by rfl⟩ : syracuseStep 2346227 = 3519341) B3519341
theorem B2346257 : Blo 1563479 2346257 := bstep (se 2 (by rfl) ⟨879846, by rfl⟩ : syracuseStep 2346257 = 1759693) B1759693
theorem B2346275 : Blo 1563479 2346275 := bstep (se 1 (by rfl) ⟨1759706, by rfl⟩ : syracuseStep 2346275 = 3519413) B3519413
theorem B2346305 : Blo 1563479 2346305 := bstep (se 2 (by rfl) ⟨879864, by rfl⟩ : syracuseStep 2346305 = 1759729) B1759729
theorem B2379073 : Blo 1563479 2379073 := bstep (se 2 (by rfl) ⟨892152, by rfl⟩ : syracuseStep 2379073 = 1784305) B1784305
theorem B2968913 : Blo 1563479 2968913 := bstep (se 2 (by rfl) ⟨1113342, by rfl⟩ : syracuseStep 2968913 = 2226685) B2226685
theorem B2346323 : Blo 1563479 2346323 := bstep (se 1 (by rfl) ⟨1759742, by rfl⟩ : syracuseStep 2346323 = 3519485) B3519485
theorem B2346353 : Blo 1563479 2346353 := bstep (se 2 (by rfl) ⟨879882, by rfl⟩ : syracuseStep 2346353 = 1759765) B1759765
theorem B2346371 : Blo 1563479 2346371 := bstep (se 1 (by rfl) ⟨1759778, by rfl⟩ : syracuseStep 2346371 = 3519557) B3519557
theorem B13364621 : Blo 1563479 13364621 := bstep (se 3 (by rfl) ⟨2505866, by rfl⟩ : syracuseStep 13364621 = 5011733) B5011733
theorem B2346401 : Blo 1563479 2346401 := bstep (se 2 (by rfl) ⟨879900, by rfl⟩ : syracuseStep 2346401 = 1759801) B1759801
theorem B2346419 : Blo 1563479 2346419 := bstep (se 1 (by rfl) ⟨1759814, by rfl⟩ : syracuseStep 2346419 = 3519629) B3519629
theorem B2346449 : Blo 1563479 2346449 := bstep (se 2 (by rfl) ⟨879918, by rfl⟩ : syracuseStep 2346449 = 1759837) B1759837
theorem B2346467 : Blo 1563479 2346467 := bstep (se 1 (by rfl) ⟨1759850, by rfl⟩ : syracuseStep 2346467 = 3519701) B3519701
theorem B3517937 : Blo 1563479 3517937 := bstep (se 2 (by rfl) ⟨1319226, by rfl⟩ : syracuseStep 3517937 = 2638453) B2638453
theorem B2346497 : Blo 1563479 2346497 := bstep (se 2 (by rfl) ⟨879936, by rfl⟩ : syracuseStep 2346497 = 1759873) B1759873
theorem B3517955 : Blo 1563479 3517955 := bstep (se 1 (by rfl) ⟨2638466, by rfl⟩ : syracuseStep 3517955 = 5276933) B5276933
theorem B3960323 : Blo 1563479 3960323 := bstep (se 1 (by rfl) ⟨2970242, by rfl⟩ : syracuseStep 3960323 = 5940485) B5940485
theorem B2346515 : Blo 1563479 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B2346545 : Blo 1563479 2346545 := bstep (se 2 (by rfl) ⟨879954, by rfl⟩ : syracuseStep 2346545 = 1759909) B1759909
theorem B357305909 : Blo 1563479 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B2346563 : Blo 1563479 2346563 := bstep (se 1 (by rfl) ⟨1759922, by rfl⟩ : syracuseStep 2346563 = 3519845) B3519845
theorem B5279309 : Blo 1563479 5279309 := bstep (se 3 (by rfl) ⟨989870, by rfl⟩ : syracuseStep 5279309 = 1979741) B1979741
theorem B2346593 : Blo 1563479 2346593 := bstep (se 2 (by rfl) ⟨879972, by rfl⟩ : syracuseStep 2346593 = 1759945) B1759945
theorem B6680177 : Blo 1563479 6680177 := bstep (se 2 (by rfl) ⟨2505066, by rfl⟩ : syracuseStep 6680177 = 5010133) B5010133
theorem B2346611 : Blo 1563479 2346611 := bstep (se 1 (by rfl) ⟨1759958, by rfl⟩ : syracuseStep 2346611 = 3519917) B3519917
theorem B5279363 : Blo 1563479 5279363 := bstep (se 1 (by rfl) ⟨3959522, by rfl⟩ : syracuseStep 5279363 = 7919045) B7919045
theorem B2379395 : Blo 1563479 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B2346641 : Blo 1563479 2346641 := bstep (se 2 (by rfl) ⟨879990, by rfl⟩ : syracuseStep 2346641 = 1759981) B1759981
theorem B2346659 : Blo 1563479 2346659 := bstep (se 1 (by rfl) ⟨1759994, by rfl⟩ : syracuseStep 2346659 = 3519989) B3519989
theorem B2346689 : Blo 1563479 2346689 := bstep (se 2 (by rfl) ⟨880008, by rfl⟩ : syracuseStep 2346689 = 1760017) B1760017
theorem B3960515 : Blo 1563479 3960515 := bstep (se 1 (by rfl) ⟨2970386, by rfl⟩ : syracuseStep 3960515 = 5940773) B5940773
theorem B2346707 : Blo 1563479 2346707 := bstep (se 1 (by rfl) ⟨1760030, by rfl⟩ : syracuseStep 2346707 = 3520061) B3520061
theorem B2346737 : Blo 1563479 2346737 := bstep (se 2 (by rfl) ⟨880026, by rfl⟩ : syracuseStep 2346737 = 1760053) B1760053
theorem B2346755 : Blo 1563479 2346755 := bstep (se 1 (by rfl) ⟨1760066, by rfl⟩ : syracuseStep 2346755 = 3520133) B3520133
theorem B3518225 : Blo 1563479 3518225 := bstep (se 2 (by rfl) ⟨1319334, by rfl⟩ : syracuseStep 3518225 = 2638669) B2638669
theorem B2346785 : Blo 1563479 2346785 := bstep (se 2 (by rfl) ⟨880044, by rfl⟩ : syracuseStep 2346785 = 1760089) B1760089
theorem B3518243 : Blo 1563479 3518243 := bstep (se 1 (by rfl) ⟨2638682, by rfl⟩ : syracuseStep 3518243 = 5277365) B5277365
theorem B2346803 : Blo 1563479 2346803 := bstep (se 1 (by rfl) ⟨1760102, by rfl⟩ : syracuseStep 2346803 = 3520205) B3520205
theorem B2346833 : Blo 1563479 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B13356899 : Blo 1563479 13356899 := bstep (se 1 (by rfl) ⟨10017674, by rfl⟩ : syracuseStep 13356899 = 20035349) B20035349
theorem B2346851 : Blo 1563479 2346851 := bstep (se 1 (by rfl) ⟨1760138, by rfl⟩ : syracuseStep 2346851 = 3520277) B3520277
theorem B7917425 : Blo 1563479 7917425 := bstep (se 2 (by rfl) ⟨2969034, by rfl⟩ : syracuseStep 7917425 = 5938069) B5938069
theorem B2346881 : Blo 1563479 2346881 := bstep (se 2 (by rfl) ⟨880080, by rfl⟩ : syracuseStep 2346881 = 1760161) B1760161
theorem B5279633 : Blo 1563479 5279633 := bstep (se 2 (by rfl) ⟨1979862, by rfl⟩ : syracuseStep 5279633 = 3959725) B3959725
theorem B2346899 : Blo 1563479 2346899 := bstep (se 1 (by rfl) ⟨1760174, by rfl⟩ : syracuseStep 2346899 = 3520349) B3520349
theorem B2346929 : Blo 1563479 2346929 := bstep (se 2 (by rfl) ⟨880098, by rfl⟩ : syracuseStep 2346929 = 1760197) B1760197
theorem B2346947 : Blo 1563479 2346947 := bstep (se 1 (by rfl) ⟨1760210, by rfl⟩ : syracuseStep 2346947 = 3520421) B3520421
theorem B2346977 : Blo 1563479 2346977 := bstep (se 2 (by rfl) ⟨880116, by rfl⟩ : syracuseStep 2346977 = 1760233) B1760233
theorem B2346995 : Blo 1563479 2346995 := bstep (se 1 (by rfl) ⟨1760246, by rfl⟩ : syracuseStep 2346995 = 3520493) B3520493
theorem B8458253 : Blo 1563479 8458253 := bstep (se 3 (by rfl) ⟨1585922, by rfl⟩ : syracuseStep 8458253 = 3171845) B3171845
theorem B2347025 : Blo 1563479 2347025 := bstep (se 2 (by rfl) ⟨880134, by rfl⟩ : syracuseStep 2347025 = 1760269) B1760269
theorem B5640205 : Blo 1563479 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B2969635 : Blo 1563479 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B2347043 : Blo 1563479 2347043 := bstep (se 1 (by rfl) ⟨1760282, by rfl⟩ : syracuseStep 2347043 = 3520565) B3520565
theorem B3518513 : Blo 1563479 3518513 := bstep (se 2 (by rfl) ⟨1319442, by rfl⟩ : syracuseStep 3518513 = 2638885) B2638885
theorem B2347073 : Blo 1563479 2347073 := bstep (se 2 (by rfl) ⟨880152, by rfl⟩ : syracuseStep 2347073 = 1760305) B1760305
theorem B3518531 : Blo 1563479 3518531 := bstep (se 1 (by rfl) ⟨2638898, by rfl⟩ : syracuseStep 3518531 = 5277797) B5277797
theorem B2347091 : Blo 1563479 2347091 := bstep (se 1 (by rfl) ⟨1760318, by rfl⟩ : syracuseStep 2347091 = 3520637) B3520637
theorem B2347121 : Blo 1563479 2347121 := bstep (se 2 (by rfl) ⟨880170, by rfl⟩ : syracuseStep 2347121 = 1760341) B1760341
theorem B2347139 : Blo 1563479 2347139 := bstep (se 1 (by rfl) ⟨1760354, by rfl⟩ : syracuseStep 2347139 = 3520709) B3520709
theorem B30478477 : Blo 1563479 30478477 := bstep (se 3 (by rfl) ⟨5714714, by rfl⟩ : syracuseStep 30478477 = 11429429) B11429429
theorem B2347169 : Blo 1563479 2347169 := bstep (se 2 (by rfl) ⟨880188, by rfl⟩ : syracuseStep 2347169 = 1760377) B1760377
theorem B2347187 : Blo 1563479 2347187 := bstep (se 1 (by rfl) ⟨1760390, by rfl⟩ : syracuseStep 2347187 = 3520781) B3520781
theorem B2347217 : Blo 1563479 2347217 := bstep (se 2 (by rfl) ⟨880206, by rfl⟩ : syracuseStep 2347217 = 1760413) B1760413
theorem B2347235 : Blo 1563479 2347235 := bstep (se 1 (by rfl) ⟨1760426, by rfl⟩ : syracuseStep 2347235 = 3520853) B3520853
theorem B2674945 : Blo 1563479 2674945 := bstep (se 2 (by rfl) ⟨1003104, by rfl⟩ : syracuseStep 2674945 = 2006209) B2006209
theorem B2347265 : Blo 1563479 2347265 := bstep (se 2 (by rfl) ⟨880224, by rfl⟩ : syracuseStep 2347265 = 1760449) B1760449
theorem B2347283 : Blo 1563479 2347283 := bstep (se 1 (by rfl) ⟨1760462, by rfl⟩ : syracuseStep 2347283 = 3520925) B3520925
theorem B2347313 : Blo 1563479 2347313 := bstep (se 2 (by rfl) ⟨880242, by rfl⟩ : syracuseStep 2347313 = 1760485) B1760485
theorem B2347331 : Blo 1563479 2347331 := bstep (se 1 (by rfl) ⟨1760498, by rfl⟩ : syracuseStep 2347331 = 3520997) B3520997
theorem B3518801 : Blo 1563479 3518801 := bstep (se 2 (by rfl) ⟨1319550, by rfl⟩ : syracuseStep 3518801 = 2639101) B2639101
theorem B2347361 : Blo 1563479 2347361 := bstep (se 2 (by rfl) ⟨880260, by rfl⟩ : syracuseStep 2347361 = 1760521) B1760521
theorem B3518819 : Blo 1563479 3518819 := bstep (se 1 (by rfl) ⟨2639114, by rfl⟩ : syracuseStep 3518819 = 5278229) B5278229
theorem B2347379 : Blo 1563479 2347379 := bstep (se 1 (by rfl) ⟨1760534, by rfl⟩ : syracuseStep 2347379 = 3521069) B3521069
theorem B2347409 : Blo 1563479 2347409 := bstep (se 2 (by rfl) ⟨880278, by rfl⟩ : syracuseStep 2347409 = 1760557) B1760557
theorem B2347427 : Blo 1563479 2347427 := bstep (se 1 (by rfl) ⟨1760570, by rfl⟩ : syracuseStep 2347427 = 3521141) B3521141
theorem B5280173 : Blo 1563479 5280173 := bstep (se 3 (by rfl) ⟨990032, by rfl⟩ : syracuseStep 5280173 = 1980065) B1980065
theorem B2347457 : Blo 1563479 2347457 := bstep (se 2 (by rfl) ⟨880296, by rfl⟩ : syracuseStep 2347457 = 1760593) B1760593
theorem B2970083 : Blo 1563479 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B5280227 : Blo 1563479 5280227 := bstep (se 1 (by rfl) ⟨3960170, by rfl⟩ : syracuseStep 5280227 = 7920341) B7920341
theorem B1978931 : Blo 1563479 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B3519089 : Blo 1563479 3519089 := bstep (se 2 (by rfl) ⟨1319658, by rfl⟩ : syracuseStep 3519089 = 2639317) B2639317
theorem B4452995 : Blo 1563479 4452995 := bstep (se 1 (by rfl) ⟨3339746, by rfl⟩ : syracuseStep 4452995 = 6679493) B6679493
theorem B3519107 : Blo 1563479 3519107 := bstep (se 1 (by rfl) ⟨2639330, by rfl⟩ : syracuseStep 3519107 = 5278661) B5278661
theorem B5280497 : Blo 1563479 5280497 := bstep (se 2 (by rfl) ⟨1980186, by rfl⟩ : syracuseStep 5280497 = 3960373) B3960373
theorem B2970371 : Blo 1563479 2970371 := bstep (se 1 (by rfl) ⟨2227778, by rfl⟩ : syracuseStep 2970371 = 4455557) B4455557
theorem B3519377 : Blo 1563479 3519377 := bstep (se 2 (by rfl) ⟨1319766, by rfl⟩ : syracuseStep 3519377 = 2639533) B2639533
theorem B3519395 : Blo 1563479 3519395 := bstep (se 1 (by rfl) ⟨2639546, by rfl⟩ : syracuseStep 3519395 = 5279093) B5279093
theorem B5010349 : Blo 1563479 5010349 := bstep (se 3 (by rfl) ⟨939440, by rfl⟩ : syracuseStep 5010349 = 1878881) B1878881
theorem B4453325 : Blo 1563479 4453325 := bstep (se 3 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 4453325 = 1669997) B1669997
theorem B1586179 : Blo 1563479 1586179 := bstep (se 1 (by rfl) ⟨1189634, by rfl⟩ : syracuseStep 1586179 = 2379269) B2379269
theorem B4453393 : Blo 1563479 4453393 := bstep (se 2 (by rfl) ⟨1670022, by rfl⟩ : syracuseStep 4453393 = 3340045) B3340045
theorem B3519665 : Blo 1563479 3519665 := bstep (se 2 (by rfl) ⟨1319874, by rfl⟩ : syracuseStep 3519665 = 2639749) B2639749
theorem B3519683 : Blo 1563479 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B1979635 : Blo 1563479 1979635 := bstep (se 1 (by rfl) ⟨1484726, by rfl⟩ : syracuseStep 1979635 = 2969453) B2969453
theorem B5281037 : Blo 1563479 5281037 := bstep (se 3 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 5281037 = 1980389) B1980389
theorem B4453667 : Blo 1563479 4453667 := bstep (se 1 (by rfl) ⟨3340250, by rfl⟩ : syracuseStep 4453667 = 6680501) B6680501
theorem B7918883 : Blo 1563479 7918883 := bstep (se 1 (by rfl) ⟨5939162, by rfl⟩ : syracuseStep 7918883 = 11878325) B11878325
theorem B2676019 : Blo 1563479 2676019 := bstep (se 1 (by rfl) ⟨2007014, by rfl⟩ : syracuseStep 2676019 = 4014029) B4014029
theorem B5281091 : Blo 1563479 5281091 := bstep (se 1 (by rfl) ⟨3960818, by rfl⟩ : syracuseStep 5281091 = 7921637) B7921637
theorem B1979731 : Blo 1563479 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B25368005 : Blo 1563479 25368005 := bstep (se 4 (by rfl) ⟨2378250, by rfl⟩ : syracuseStep 25368005 = 4756501) B4756501
theorem B3519953 : Blo 1563479 3519953 := bstep (se 2 (by rfl) ⟨1319982, by rfl⟩ : syracuseStep 3519953 = 2639965) B2639965
theorem B5936611 : Blo 1563479 5936611 := bstep (se 1 (by rfl) ⟨4452458, by rfl⟩ : syracuseStep 5936611 = 8904917) B8904917
theorem B3519971 : Blo 1563479 3519971 := bstep (se 1 (by rfl) ⟨2639978, by rfl⟩ : syracuseStep 3519971 = 5279957) B5279957
theorem B5281361 : Blo 1563479 5281361 := bstep (se 2 (by rfl) ⟨1980510, by rfl⟩ : syracuseStep 5281361 = 3961021) B3961021
theorem B3520241 : Blo 1563479 3520241 := bstep (se 2 (by rfl) ⟨1320090, by rfl⟩ : syracuseStep 3520241 = 2640181) B2640181
theorem B3520259 : Blo 1563479 3520259 := bstep (se 1 (by rfl) ⟨2640194, by rfl⟩ : syracuseStep 3520259 = 5280389) B5280389
theorem B1759027 : Blo 1563479 1759027 := bstep (se 1 (by rfl) ⟨1319270, by rfl⟩ : syracuseStep 1759027 = 2638541) B2638541
theorem B1980227 : Blo 1563479 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B2504611 : Blo 1563479 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B1759171 : Blo 1563479 1759171 := bstep (se 1 (by rfl) ⟨1319378, by rfl⟩ : syracuseStep 1759171 = 2638757) B2638757
theorem B4405187 : Blo 1563479 4405187 := bstep (se 1 (by rfl) ⟨3303890, by rfl⟩ : syracuseStep 4405187 = 6607781) B6607781
theorem B2504657 : Blo 1563479 2504657 := bstep (se 2 (by rfl) ⟨939246, by rfl⟩ : syracuseStep 2504657 = 1878493) B1878493
theorem B2226161 : Blo 1563479 2226161 := bstep (se 2 (by rfl) ⟨834810, by rfl⟩ : syracuseStep 2226161 = 1669621) B1669621
theorem B3520529 : Blo 1563479 3520529 := bstep (se 2 (by rfl) ⟨1320198, by rfl⟩ : syracuseStep 3520529 = 2640397) B2640397
theorem B3520547 : Blo 1563479 3520547 := bstep (se 1 (by rfl) ⟨2640410, by rfl⟩ : syracuseStep 3520547 = 5280821) B5280821
theorem B2226241 : Blo 1563479 2226241 := bstep (se 2 (by rfl) ⟨834840, by rfl⟩ : syracuseStep 2226241 = 1669681) B1669681
theorem B3758147 : Blo 1563479 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B7919693 : Blo 1563479 7919693 := bstep (se 3 (by rfl) ⟨1484942, by rfl⟩ : syracuseStep 7919693 = 2969885) B2969885
theorem B3340369 : Blo 1563479 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B1759315 : Blo 1563479 1759315 := bstep (se 1 (by rfl) ⟨1319486, by rfl⟩ : syracuseStep 1759315 = 2638973) B2638973
theorem B4454509 : Blo 1563479 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B1759459 : Blo 1563479 1759459 := bstep (se 1 (by rfl) ⟨1319594, by rfl⟩ : syracuseStep 1759459 = 2639189) B2639189
theorem B3758339 : Blo 1563479 3758339 := bstep (se 1 (by rfl) ⟨2818754, by rfl⟩ : syracuseStep 3758339 = 5637509) B5637509
theorem B4454669 : Blo 1563479 4454669 := bstep (se 3 (by rfl) ⟨835250, by rfl⟩ : syracuseStep 4454669 = 1670501) B1670501
theorem B1784099 : Blo 1563479 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B3520817 : Blo 1563479 3520817 := bstep (se 2 (by rfl) ⟨1320306, by rfl⟩ : syracuseStep 3520817 = 2640613) B2640613
theorem B3520835 : Blo 1563479 3520835 := bstep (se 1 (by rfl) ⟨2640626, by rfl⟩ : syracuseStep 3520835 = 5281253) B5281253
theorem B1759603 : Blo 1563479 1759603 := bstep (se 1 (by rfl) ⟨1319702, by rfl⟩ : syracuseStep 1759603 = 2639405) B2639405
theorem B4454851 : Blo 1563479 4454851 := bstep (se 1 (by rfl) ⟨3341138, by rfl⟩ : syracuseStep 4454851 = 6682277) B6682277
theorem B6101489 : Blo 1563479 6101489 := bstep (se 2 (by rfl) ⟨2288058, by rfl⟩ : syracuseStep 6101489 = 4576117) B4576117
theorem B1759747 : Blo 1563479 1759747 := bstep (se 1 (by rfl) ⟨1319810, by rfl⟩ : syracuseStep 1759747 = 2639621) B2639621
theorem B3521105 : Blo 1563479 3521105 := bstep (se 2 (by rfl) ⟨1320414, by rfl⟩ : syracuseStep 3521105 = 2640829) B2640829
theorem B3521123 : Blo 1563479 3521123 := bstep (se 1 (by rfl) ⟨2640842, by rfl⟩ : syracuseStep 3521123 = 5281685) B5281685
theorem B5012081 : Blo 1563479 5012081 := bstep (se 2 (by rfl) ⟨1879530, by rfl⟩ : syracuseStep 5012081 = 3759061) B3759061
theorem B2824849 : Blo 1563479 2824849 := bstep (se 2 (by rfl) ⟨1059318, by rfl⟩ : syracuseStep 2824849 = 2118637) B2118637
theorem B1759891 : Blo 1563479 1759891 := bstep (se 1 (by rfl) ⟨1319918, by rfl⟩ : syracuseStep 1759891 = 2639837) B2639837
theorem B1669843 : Blo 1563479 1669843 := bstep (se 1 (by rfl) ⟨1252382, by rfl⟩ : syracuseStep 1669843 = 2504765) B2504765
theorem B1760035 : Blo 1563479 1760035 := bstep (se 1 (by rfl) ⟨1320026, by rfl⟩ : syracuseStep 1760035 = 2640053) B2640053
theorem B2227027 : Blo 1563479 2227027 := bstep (se 1 (by rfl) ⟨1670270, by rfl⟩ : syracuseStep 2227027 = 3340541) B3340541
theorem B1563491 : Blo 1563479 1563491 := bstep (se 1 (by rfl) ⟨1172618, by rfl⟩ : syracuseStep 1563491 = 2345237) B2345237
theorem B1563507 : Blo 1563479 1563507 := bstep (se 1 (by rfl) ⟨1172630, by rfl⟩ : syracuseStep 1563507 = 2345261) B2345261
theorem B1563523 : Blo 1563479 1563523 := bstep (se 1 (by rfl) ⟨1172642, by rfl⟩ : syracuseStep 1563523 = 2345285) B2345285
theorem B3758993 : Blo 1563479 3758993 := bstep (se 2 (by rfl) ⟨1409622, by rfl⟩ : syracuseStep 3758993 = 2819245) B2819245
theorem B1563539 : Blo 1563479 1563539 := bstep (se 1 (by rfl) ⟨1172654, by rfl⟩ : syracuseStep 1563539 = 2345309) B2345309
theorem B1563555 : Blo 1563479 1563555 := bstep (se 1 (by rfl) ⟨1172666, by rfl⟩ : syracuseStep 1563555 = 2345333) B2345333
theorem B9509795 : Blo 1563479 9509795 := bstep (se 1 (by rfl) ⟨7132346, by rfl⟩ : syracuseStep 9509795 = 14264693) B14264693
theorem B7519139 : Blo 1563479 7519139 := bstep (se 1 (by rfl) ⟨5639354, by rfl⟩ : syracuseStep 7519139 = 11278709) B11278709
theorem B2505649 : Blo 1563479 2505649 := bstep (se 2 (by rfl) ⟨939618, by rfl⟩ : syracuseStep 2505649 = 1879237) B1879237
theorem B1563571 : Blo 1563479 1563571 := bstep (se 1 (by rfl) ⟨1172678, by rfl⟩ : syracuseStep 1563571 = 2345357) B2345357
theorem B1760179 : Blo 1563479 1760179 := bstep (se 1 (by rfl) ⟨1320134, by rfl⟩ : syracuseStep 1760179 = 2640269) B2640269
theorem B1563587 : Blo 1563479 1563587 := bstep (se 1 (by rfl) ⟨1172690, by rfl⟩ : syracuseStep 1563587 = 2345381) B2345381
theorem B1563603 : Blo 1563479 1563603 := bstep (se 1 (by rfl) ⟨1172702, by rfl⟩ : syracuseStep 1563603 = 2345405) B2345405
theorem B1563619 : Blo 1563479 1563619 := bstep (se 1 (by rfl) ⟨1172714, by rfl⟩ : syracuseStep 1563619 = 2345429) B2345429
theorem B1563635 : Blo 1563479 1563635 := bstep (se 1 (by rfl) ⟨1172726, by rfl⟩ : syracuseStep 1563635 = 2345453) B2345453
theorem B1563651 : Blo 1563479 1563651 := bstep (se 1 (by rfl) ⟨1172738, by rfl⟩ : syracuseStep 1563651 = 2345477) B2345477
theorem B4758545 : Blo 1563479 4758545 := bstep (se 2 (by rfl) ⟨1784454, by rfl⟩ : syracuseStep 4758545 = 3568909) B3568909
theorem B1563667 : Blo 1563479 1563667 := bstep (se 1 (by rfl) ⟨1172750, by rfl⟩ : syracuseStep 1563667 = 2345501) B2345501
theorem B10017827 : Blo 1563479 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B1563683 : Blo 1563479 1563683 := bstep (se 1 (by rfl) ⟨1172762, by rfl⟩ : syracuseStep 1563683 = 2345525) B2345525
theorem B1563699 : Blo 1563479 1563699 := bstep (se 1 (by rfl) ⟨1172774, by rfl⟩ : syracuseStep 1563699 = 2345549) B2345549
theorem B1563715 : Blo 1563479 1563715 := bstep (se 1 (by rfl) ⟨1172786, by rfl⟩ : syracuseStep 1563715 = 2345573) B2345573
theorem B1760323 : Blo 1563479 1760323 := bstep (se 1 (by rfl) ⟨1320242, by rfl⟩ : syracuseStep 1760323 = 2640485) B2640485
theorem B1563731 : Blo 1563479 1563731 := bstep (se 1 (by rfl) ⟨1172798, by rfl⟩ : syracuseStep 1563731 = 2345597) B2345597
theorem B1563747 : Blo 1563479 1563747 := bstep (se 1 (by rfl) ⟨1172810, by rfl⟩ : syracuseStep 1563747 = 2345621) B2345621
theorem B1563763 : Blo 1563479 1563763 := bstep (se 1 (by rfl) ⟨1172822, by rfl⟩ : syracuseStep 1563763 = 2345645) B2345645
theorem B1563779 : Blo 1563479 1563779 := bstep (se 1 (by rfl) ⟨1172834, by rfl⟩ : syracuseStep 1563779 = 2345669) B2345669
theorem B1563795 : Blo 1563479 1563795 := bstep (se 1 (by rfl) ⟨1172846, by rfl⟩ : syracuseStep 1563795 = 2345693) B2345693
theorem B1563811 : Blo 1563479 1563811 := bstep (se 1 (by rfl) ⟨1172858, by rfl⟩ : syracuseStep 1563811 = 2345717) B2345717
theorem B1563827 : Blo 1563479 1563827 := bstep (se 1 (by rfl) ⟨1172870, by rfl⟩ : syracuseStep 1563827 = 2345741) B2345741
theorem B1563843 : Blo 1563479 1563843 := bstep (se 1 (by rfl) ⟨1172882, by rfl⟩ : syracuseStep 1563843 = 2345765) B2345765
theorem B1563859 : Blo 1563479 1563859 := bstep (se 1 (by rfl) ⟨1172894, by rfl⟩ : syracuseStep 1563859 = 2345789) B2345789
theorem B1760467 : Blo 1563479 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B1563875 : Blo 1563479 1563875 := bstep (se 1 (by rfl) ⟨1172906, by rfl⟩ : syracuseStep 1563875 = 2345813) B2345813
theorem B5012707 : Blo 1563479 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B1563891 : Blo 1563479 1563891 := bstep (se 1 (by rfl) ⟨1172918, by rfl⟩ : syracuseStep 1563891 = 2345837) B2345837
theorem B1563907 : Blo 1563479 1563907 := bstep (se 1 (by rfl) ⟨1172930, by rfl⟩ : syracuseStep 1563907 = 2345861) B2345861
theorem B6683917 : Blo 1563479 6683917 := bstep (se 3 (by rfl) ⟨1253234, by rfl⟩ : syracuseStep 6683917 = 2506469) B2506469
theorem B1563923 : Blo 1563479 1563923 := bstep (se 1 (by rfl) ⟨1172942, by rfl⟩ : syracuseStep 1563923 = 2345885) B2345885
theorem B1563939 : Blo 1563479 1563939 := bstep (se 1 (by rfl) ⟨1172954, by rfl⟩ : syracuseStep 1563939 = 2345909) B2345909
theorem B2227505 : Blo 1563479 2227505 := bstep (se 2 (by rfl) ⟨835314, by rfl⟩ : syracuseStep 2227505 = 1670629) B1670629
theorem B1563955 : Blo 1563479 1563955 := bstep (se 1 (by rfl) ⟨1172966, by rfl⟩ : syracuseStep 1563955 = 2345933) B2345933
theorem B1563971 : Blo 1563479 1563971 := bstep (se 1 (by rfl) ⟨1172978, by rfl⟩ : syracuseStep 1563971 = 2345957) B2345957
theorem B14269765 : Blo 1563479 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B4701521 : Blo 1563479 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B1563987 : Blo 1563479 1563987 := bstep (se 1 (by rfl) ⟨1172990, by rfl⟩ : syracuseStep 1563987 = 2345981) B2345981
theorem B1564003 : Blo 1563479 1564003 := bstep (se 1 (by rfl) ⟨1173002, by rfl⟩ : syracuseStep 1564003 = 2346005) B2346005
theorem B2506097 : Blo 1563479 2506097 := bstep (se 2 (by rfl) ⟨939786, by rfl⟩ : syracuseStep 2506097 = 1879573) B1879573
theorem B1564019 : Blo 1563479 1564019 := bstep (se 1 (by rfl) ⟨1173014, by rfl⟩ : syracuseStep 1564019 = 2346029) B2346029
theorem B1564035 : Blo 1563479 1564035 := bstep (se 1 (by rfl) ⟨1173026, by rfl⟩ : syracuseStep 1564035 = 2346053) B2346053
theorem B1564051 : Blo 1563479 1564051 := bstep (se 1 (by rfl) ⟨1173038, by rfl⟩ : syracuseStep 1564051 = 2346077) B2346077
theorem B1564067 : Blo 1563479 1564067 := bstep (se 1 (by rfl) ⟨1173050, by rfl⟩ : syracuseStep 1564067 = 2346101) B2346101
theorem B2227619 : Blo 1563479 2227619 := bstep (se 1 (by rfl) ⟨1670714, by rfl⟩ : syracuseStep 2227619 = 3341429) B3341429
theorem B1564083 : Blo 1563479 1564083 := bstep (se 1 (by rfl) ⟨1173062, by rfl⟩ : syracuseStep 1564083 = 2346125) B2346125
theorem B1564099 : Blo 1563479 1564099 := bstep (se 1 (by rfl) ⟨1173074, by rfl⟩ : syracuseStep 1564099 = 2346149) B2346149
theorem B1564115 : Blo 1563479 1564115 := bstep (se 1 (by rfl) ⟨1173086, by rfl⟩ : syracuseStep 1564115 = 2346173) B2346173
theorem B1564131 : Blo 1563479 1564131 := bstep (se 1 (by rfl) ⟨1173098, by rfl⟩ : syracuseStep 1564131 = 2346197) B2346197
theorem B13360625 : Blo 1563479 13360625 := bstep (se 2 (by rfl) ⟨5010234, by rfl⟩ : syracuseStep 13360625 = 10020469) B10020469
theorem B1564147 : Blo 1563479 1564147 := bstep (se 1 (by rfl) ⟨1173110, by rfl⟩ : syracuseStep 1564147 = 2346221) B2346221
theorem B2227699 : Blo 1563479 2227699 := bstep (se 1 (by rfl) ⟨1670774, by rfl⟩ : syracuseStep 2227699 = 3341549) B3341549
theorem B1564163 : Blo 1563479 1564163 := bstep (se 1 (by rfl) ⟨1173122, by rfl⟩ : syracuseStep 1564163 = 2346245) B2346245
theorem B8912389 : Blo 1563479 8912389 := bstep (se 4 (by rfl) ⟨835536, by rfl⟩ : syracuseStep 8912389 = 1671073) B1671073
theorem B10296845 : Blo 1563479 10296845 := bstep (se 3 (by rfl) ⟨1930658, by rfl⟩ : syracuseStep 10296845 = 3861317) B3861317
theorem B1564179 : Blo 1563479 1564179 := bstep (se 1 (by rfl) ⟨1173134, by rfl⟩ : syracuseStep 1564179 = 2346269) B2346269
theorem B1564195 : Blo 1563479 1564195 := bstep (se 1 (by rfl) ⟨1173146, by rfl⟩ : syracuseStep 1564195 = 2346293) B2346293
theorem B3341873 : Blo 1563479 3341873 := bstep (se 2 (by rfl) ⟨1253202, by rfl⟩ : syracuseStep 3341873 = 2506405) B2506405
theorem B1564211 : Blo 1563479 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B1564227 : Blo 1563479 1564227 := bstep (se 1 (by rfl) ⟨1173170, by rfl⟩ : syracuseStep 1564227 = 2346341) B2346341
theorem B3341891 : Blo 1563479 3341891 := bstep (se 1 (by rfl) ⟨2506418, by rfl⟩ : syracuseStep 3341891 = 5012837) B5012837
theorem B1564243 : Blo 1563479 1564243 := bstep (se 1 (by rfl) ⟨1173182, by rfl⟩ : syracuseStep 1564243 = 2346365) B2346365
theorem B1564259 : Blo 1563479 1564259 := bstep (se 1 (by rfl) ⟨1173194, by rfl⟩ : syracuseStep 1564259 = 2346389) B2346389
theorem B1564275 : Blo 1563479 1564275 := bstep (se 1 (by rfl) ⟨1173206, by rfl⟩ : syracuseStep 1564275 = 2346413) B2346413
theorem B1564291 : Blo 1563479 1564291 := bstep (se 1 (by rfl) ⟨1173218, by rfl⟩ : syracuseStep 1564291 = 2346437) B2346437
theorem B5938829 : Blo 1563479 5938829 := bstep (se 3 (by rfl) ⟨1113530, by rfl⟩ : syracuseStep 5938829 = 2227061) B2227061
theorem B4226705 : Blo 1563479 4226705 := bstep (se 2 (by rfl) ⟨1585014, by rfl⟩ : syracuseStep 4226705 = 3170029) B3170029
theorem B3759761 : Blo 1563479 3759761 := bstep (se 2 (by rfl) ⟨1409910, by rfl⟩ : syracuseStep 3759761 = 2819821) B2819821
theorem B1564307 : Blo 1563479 1564307 := bstep (se 1 (by rfl) ⟨1173230, by rfl⟩ : syracuseStep 1564307 = 2346461) B2346461
theorem B1564323 : Blo 1563479 1564323 := bstep (se 1 (by rfl) ⟨1173242, by rfl⟩ : syracuseStep 1564323 = 2346485) B2346485
theorem B1564339 : Blo 1563479 1564339 := bstep (se 1 (by rfl) ⟨1173254, by rfl⟩ : syracuseStep 1564339 = 2346509) B2346509
theorem B1564355 : Blo 1563479 1564355 := bstep (se 1 (by rfl) ⟨1173266, by rfl⟩ : syracuseStep 1564355 = 2346533) B2346533
theorem B1670851 : Blo 1563479 1670851 := bstep (se 1 (by rfl) ⟨1253138, by rfl⟩ : syracuseStep 1670851 = 2506277) B2506277
theorem B4284109 : Blo 1563479 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B1564371 : Blo 1563479 1564371 := bstep (se 1 (by rfl) ⟨1173278, by rfl⟩ : syracuseStep 1564371 = 2346557) B2346557
theorem B1564387 : Blo 1563479 1564387 := bstep (se 1 (by rfl) ⟨1173290, by rfl⟩ : syracuseStep 1564387 = 2346581) B2346581
theorem B17825507 : Blo 1563479 17825507 := bstep (se 1 (by rfl) ⟨13369130, by rfl⟩ : syracuseStep 17825507 = 26738261) B26738261
theorem B7519985 : Blo 1563479 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B15040241 : Blo 1563479 15040241 := bstep (se 2 (by rfl) ⟨5640090, by rfl⟩ : syracuseStep 15040241 = 11280181) B11280181
theorem B1564403 : Blo 1563479 1564403 := bstep (se 1 (by rfl) ⟨1173302, by rfl⟩ : syracuseStep 1564403 = 2346605) B2346605
theorem B1564419 : Blo 1563479 1564419 := bstep (se 1 (by rfl) ⟨1173314, by rfl⟩ : syracuseStep 1564419 = 2346629) B2346629
theorem B1564435 : Blo 1563479 1564435 := bstep (se 1 (by rfl) ⟨1173326, by rfl⟩ : syracuseStep 1564435 = 2346653) B2346653
theorem B1564451 : Blo 1563479 1564451 := bstep (se 1 (by rfl) ⟨1173338, by rfl⟩ : syracuseStep 1564451 = 2346677) B2346677
theorem B4456241 : Blo 1563479 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B1564467 : Blo 1563479 1564467 := bstep (se 1 (by rfl) ⟨1173350, by rfl⟩ : syracuseStep 1564467 = 2346701) B2346701
theorem B2006851 : Blo 1563479 2006851 := bstep (se 1 (by rfl) ⟨1505138, by rfl⟩ : syracuseStep 2006851 = 3010277) B3010277
theorem B1564483 : Blo 1563479 1564483 := bstep (se 1 (by rfl) ⟨1173362, by rfl⟩ : syracuseStep 1564483 = 2346725) B2346725
theorem B2981713 : Blo 1563479 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B1564499 : Blo 1563479 1564499 := bstep (se 1 (by rfl) ⟨1173374, by rfl⟩ : syracuseStep 1564499 = 2346749) B2346749
theorem B1564515 : Blo 1563479 1564515 := bstep (se 1 (by rfl) ⟨1173386, by rfl⟩ : syracuseStep 1564515 = 2346773) B2346773
theorem B1564531 : Blo 1563479 1564531 := bstep (se 1 (by rfl) ⟨1173398, by rfl⟩ : syracuseStep 1564531 = 2346797) B2346797
theorem B1564547 : Blo 1563479 1564547 := bstep (se 1 (by rfl) ⟨1173410, by rfl⟩ : syracuseStep 1564547 = 2346821) B2346821
theorem B1564563 : Blo 1563479 1564563 := bstep (se 1 (by rfl) ⟨1173422, by rfl⟩ : syracuseStep 1564563 = 2346845) B2346845
theorem B1564579 : Blo 1563479 1564579 := bstep (se 1 (by rfl) ⟨1173434, by rfl⟩ : syracuseStep 1564579 = 2346869) B2346869
theorem B1564595 : Blo 1563479 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B1564611 : Blo 1563479 1564611 := bstep (se 1 (by rfl) ⟨1173458, by rfl⟩ : syracuseStep 1564611 = 2346917) B2346917
theorem B1564627 : Blo 1563479 1564627 := bstep (se 1 (by rfl) ⟨1173470, by rfl⟩ : syracuseStep 1564627 = 2346941) B2346941
theorem B1564643 : Blo 1563479 1564643 := bstep (se 1 (by rfl) ⟨1173482, by rfl⟩ : syracuseStep 1564643 = 2346965) B2346965
theorem B2818033 : Blo 1563479 2818033 := bstep (se 2 (by rfl) ⟨1056762, by rfl⟩ : syracuseStep 2818033 = 2113525) B2113525
theorem B1564659 : Blo 1563479 1564659 := bstep (se 1 (by rfl) ⟨1173494, by rfl⟩ : syracuseStep 1564659 = 2346989) B2346989
theorem B1564683 : Blo 1563479 1564683 := bstep (se 1 (by rfl) ⟨1173512, by rfl⟩ : syracuseStep 1564683 = 2347025) B2347025
theorem B7520273 : Blo 1563479 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B1564695 : Blo 1563479 1564695 := bstep (se 1 (by rfl) ⟨1173521, by rfl⟩ : syracuseStep 1564695 = 2347043) B2347043
theorem B1564715 : Blo 1563479 1564715 := bstep (se 1 (by rfl) ⟨1173536, by rfl⟩ : syracuseStep 1564715 = 2347073) B2347073
theorem B12689453 : Blo 1563479 12689453 := bstep (se 3 (by rfl) ⟨2379272, by rfl⟩ : syracuseStep 12689453 = 4758545) B4758545
theorem B1564727 : Blo 1563479 1564727 := bstep (se 1 (by rfl) ⟨1173545, by rfl⟩ : syracuseStep 1564727 = 2347091) B2347091
theorem B4227137 : Blo 1563479 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B1564747 : Blo 1563479 1564747 := bstep (se 1 (by rfl) ⟨1173560, by rfl⟩ : syracuseStep 1564747 = 2347121) B2347121
theorem B1564759 : Blo 1563479 1564759 := bstep (se 1 (by rfl) ⟨1173569, by rfl⟩ : syracuseStep 1564759 = 2347139) B2347139
theorem B1564779 : Blo 1563479 1564779 := bstep (se 1 (by rfl) ⟨1173584, by rfl⟩ : syracuseStep 1564779 = 2347169) B2347169
theorem B1564791 : Blo 1563479 1564791 := bstep (se 1 (by rfl) ⟨1173593, by rfl⟩ : syracuseStep 1564791 = 2347187) B2347187
theorem B1564811 : Blo 1563479 1564811 := bstep (se 1 (by rfl) ⟨1173608, by rfl⟩ : syracuseStep 1564811 = 2347217) B2347217
theorem B5939345 : Blo 1563479 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B1564823 : Blo 1563479 1564823 := bstep (se 1 (by rfl) ⟨1173617, by rfl⟩ : syracuseStep 1564823 = 2347235) B2347235
theorem B1564843 : Blo 1563479 1564843 := bstep (se 1 (by rfl) ⟨1173632, by rfl⟩ : syracuseStep 1564843 = 2347265) B2347265
theorem B1564855 : Blo 1563479 1564855 := bstep (se 1 (by rfl) ⟨1173641, by rfl⟩ : syracuseStep 1564855 = 2347283) B2347283
theorem B1564875 : Blo 1563479 1564875 := bstep (se 1 (by rfl) ⟨1173656, by rfl⟩ : syracuseStep 1564875 = 2347313) B2347313
theorem B1564887 : Blo 1563479 1564887 := bstep (se 1 (by rfl) ⟨1173665, by rfl⟩ : syracuseStep 1564887 = 2347331) B2347331
theorem B1564907 : Blo 1563479 1564907 := bstep (se 1 (by rfl) ⟨1173680, by rfl⟩ : syracuseStep 1564907 = 2347361) B2347361
theorem B1564919 : Blo 1563479 1564919 := bstep (se 1 (by rfl) ⟨1173689, by rfl⟩ : syracuseStep 1564919 = 2347379) B2347379
theorem B1564939 : Blo 1563479 1564939 := bstep (se 1 (by rfl) ⟨1173704, by rfl⟩ : syracuseStep 1564939 = 2347409) B2347409
theorem B1564951 : Blo 1563479 1564951 := bstep (se 1 (by rfl) ⟨1173713, by rfl⟩ : syracuseStep 1564951 = 2347427) B2347427
theorem B1564971 : Blo 1563479 1564971 := bstep (se 1 (by rfl) ⟨1173728, by rfl⟩ : syracuseStep 1564971 = 2347457) B2347457
theorem B2113867 : Blo 1563479 2113867 := bstep (se 1 (by rfl) ⟨1585400, by rfl⟩ : syracuseStep 2113867 = 3170801) B3170801
theorem B2539979 : Blo 1563479 2539979 := bstep (se 1 (by rfl) ⟨1904984, by rfl⟩ : syracuseStep 2539979 = 3809969) B3809969
theorem B11272709 : Blo 1563479 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B3811263029 : Blo 1563479 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B5939801 : Blo 1563479 5939801 := bstep (se 2 (by rfl) ⟨2227425, by rfl⟩ : syracuseStep 5939801 = 4454851) B4454851
theorem B2638487 : Blo 1563479 2638487 := bstep (se 1 (by rfl) ⟨1978865, by rfl⟩ : syracuseStep 2638487 = 3957731) B3957731
theorem B15065861 : Blo 1563479 15065861 := bstep (se 4 (by rfl) ⟨1412424, by rfl⟩ : syracuseStep 15065861 = 2824849) B2824849
theorem B2638615 : Blo 1563479 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B5940013 : Blo 1563479 5940013 := bstep (se 3 (by rfl) ⟨1113752, by rfl⟩ : syracuseStep 5940013 = 2227505) B2227505
theorem B3957569 : Blo 1563479 3957569 := bstep (se 2 (by rfl) ⟨1484088, by rfl⟩ : syracuseStep 3957569 = 2968177) B2968177
theorem B46990297 : Blo 1563479 46990297 := bstep (se 2 (by rfl) ⟨17621361, by rfl⟩ : syracuseStep 46990297 = 35242723) B35242723
theorem B22848581 : Blo 1563479 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B5940317 : Blo 1563479 5940317 := bstep (se 3 (by rfl) ⟨1113809, by rfl⟩ : syracuseStep 5940317 = 2227619) B2227619
theorem B6341939 : Blo 1563479 6341939 := bstep (se 1 (by rfl) ⟨4756454, by rfl⟩ : syracuseStep 6341939 = 9512909) B9512909
theorem B5637451 : Blo 1563479 5637451 := bstep (se 1 (by rfl) ⟨4228088, by rfl⟩ : syracuseStep 5637451 = 8456177) B8456177
theorem B3958105 : Blo 1563479 3958105 := bstep (se 2 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 3958105 = 2968579) B2968579
theorem B2114905 : Blo 1563479 2114905 := bstep (se 2 (by rfl) ⟨793089, by rfl⟩ : syracuseStep 2114905 = 1586179) B1586179
theorem B2639243 : Blo 1563479 2639243 := bstep (se 1 (by rfl) ⟨1979432, by rfl⟩ : syracuseStep 2639243 = 3958865) B3958865
theorem B5277149 : Blo 1563479 5277149 := bstep (se 3 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 5277149 = 1978931) B1978931
theorem B2819585 : Blo 1563479 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B2639371 : Blo 1563479 2639371 := bstep (se 1 (by rfl) ⟨1979528, by rfl⟩ : syracuseStep 2639371 = 3959057) B3959057
theorem B2639513 : Blo 1563479 2639513 := bstep (se 2 (by rfl) ⟨989817, by rfl⟩ : syracuseStep 2639513 = 1979635) B1979635
theorem B2442955 : Blo 1563479 2442955 := bstep (se 1 (by rfl) ⟨1832216, by rfl⟩ : syracuseStep 2442955 = 3664433) B3664433
theorem B3172097 : Blo 1563479 3172097 := bstep (se 2 (by rfl) ⟨1189536, by rfl⟩ : syracuseStep 3172097 = 2379073) B2379073
theorem B2639641 : Blo 1563479 2639641 := bstep (se 2 (by rfl) ⟨989865, by rfl⟩ : syracuseStep 2639641 = 1979731) B1979731
theorem B2410379 : Blo 1563479 2410379 := bstep (se 1 (by rfl) ⟨1807784, by rfl⟩ : syracuseStep 2410379 = 3615569) B3615569
theorem B7915481 : Blo 1563479 7915481 := bstep (se 2 (by rfl) ⟨2968305, by rfl⟩ : syracuseStep 7915481 = 5936611) B5936611
theorem B6678551 : Blo 1563479 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B2345291 : Blo 1563479 2345291 := bstep (se 1 (by rfl) ⟨1758968, by rfl⟩ : syracuseStep 2345291 = 3517937) B3517937
theorem B8907083 : Blo 1563479 8907083 := bstep (se 1 (by rfl) ⟨6680312, by rfl⟩ : syracuseStep 8907083 = 13360625) B13360625
theorem B2345303 : Blo 1563479 2345303 := bstep (se 1 (by rfl) ⟨1758977, by rfl⟩ : syracuseStep 2345303 = 3517955) B3517955
theorem B2640215 : Blo 1563479 2640215 := bstep (se 1 (by rfl) ⟨1980161, by rfl⟩ : syracuseStep 2640215 = 3960323) B3960323
theorem B2345369 : Blo 1563479 2345369 := bstep (se 2 (by rfl) ⟨879513, by rfl⟩ : syracuseStep 2345369 = 1759027) B1759027
theorem B3959219 : Blo 1563479 3959219 := bstep (se 1 (by rfl) ⟨2969414, by rfl⟩ : syracuseStep 3959219 = 5938829) B5938829
theorem B3975617 : Blo 1563479 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B2640343 : Blo 1563479 2640343 := bstep (se 1 (by rfl) ⟨1980257, by rfl⟩ : syracuseStep 2640343 = 3960515) B3960515
theorem B2345483 : Blo 1563479 2345483 := bstep (se 1 (by rfl) ⟨1759112, by rfl⟩ : syracuseStep 2345483 = 3518225) B3518225
theorem B2345495 : Blo 1563479 2345495 := bstep (se 1 (by rfl) ⟨1759121, by rfl⟩ : syracuseStep 2345495 = 3518243) B3518243
theorem B5278283 : Blo 1563479 5278283 := bstep (se 1 (by rfl) ⟨3958712, by rfl⟩ : syracuseStep 5278283 = 7917425) B7917425
theorem B2345561 : Blo 1563479 2345561 := bstep (se 2 (by rfl) ⟨879585, by rfl⟩ : syracuseStep 2345561 = 1759171) B1759171
theorem B6679219 : Blo 1563479 6679219 := bstep (se 1 (by rfl) ⟨5009414, by rfl⟩ : syracuseStep 6679219 = 10018829) B10018829
theorem B5638835 : Blo 1563479 5638835 := bstep (se 1 (by rfl) ⟨4229126, by rfl⟩ : syracuseStep 5638835 = 8458253) B8458253
theorem B2345675 : Blo 1563479 2345675 := bstep (se 1 (by rfl) ⟨1759256, by rfl⟩ : syracuseStep 2345675 = 3518513) B3518513
theorem B2345687 : Blo 1563479 2345687 := bstep (se 1 (by rfl) ⟨1759265, by rfl⟩ : syracuseStep 2345687 = 3518531) B3518531
theorem B3959513 : Blo 1563479 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B2968321 : Blo 1563479 2968321 := bstep (se 2 (by rfl) ⟨1113120, by rfl⟩ : syracuseStep 2968321 = 2226241) B2226241
theorem B2345753 : Blo 1563479 2345753 := bstep (se 2 (by rfl) ⟨879657, by rfl⟩ : syracuseStep 2345753 = 1759315) B1759315
theorem B5278553 : Blo 1563479 5278553 := bstep (se 2 (by rfl) ⟨1979457, by rfl⟩ : syracuseStep 5278553 = 3958915) B3958915
theorem B2345867 : Blo 1563479 2345867 := bstep (se 1 (by rfl) ⟨1759400, by rfl⟩ : syracuseStep 2345867 = 3518801) B3518801
theorem B2345879 : Blo 1563479 2345879 := bstep (se 1 (by rfl) ⟨1759409, by rfl⟩ : syracuseStep 2345879 = 3518819) B3518819
theorem B2345945 : Blo 1563479 2345945 := bstep (se 2 (by rfl) ⟨879729, by rfl⟩ : syracuseStep 2345945 = 1759459) B1759459
theorem B3566593 : Blo 1563479 3566593 := bstep (se 2 (by rfl) ⟨1337472, by rfl⟩ : syracuseStep 3566593 = 2674945) B2674945
theorem B2346059 : Blo 1563479 2346059 := bstep (se 1 (by rfl) ⟨1759544, by rfl⟩ : syracuseStep 2346059 = 3519089) B3519089
theorem B2968663 : Blo 1563479 2968663 := bstep (se 1 (by rfl) ⟨2226497, by rfl⟩ : syracuseStep 2968663 = 4452995) B4452995
theorem B2346071 : Blo 1563479 2346071 := bstep (se 1 (by rfl) ⟨1759553, by rfl⟩ : syracuseStep 2346071 = 3519107) B3519107
theorem B2346137 : Blo 1563479 2346137 := bstep (se 2 (by rfl) ⟨879801, by rfl⟩ : syracuseStep 2346137 = 1759603) B1759603
theorem B2346251 : Blo 1563479 2346251 := bstep (se 1 (by rfl) ⟨1759688, by rfl⟩ : syracuseStep 2346251 = 3519377) B3519377
theorem B2346263 : Blo 1563479 2346263 := bstep (se 1 (by rfl) ⟨1759697, by rfl⟩ : syracuseStep 2346263 = 3519395) B3519395
theorem B2968883 : Blo 1563479 2968883 := bstep (se 1 (by rfl) ⟨2226662, by rfl⟩ : syracuseStep 2968883 = 4453325) B4453325
theorem B2346329 : Blo 1563479 2346329 := bstep (se 2 (by rfl) ⟨879873, by rfl⟩ : syracuseStep 2346329 = 1759747) B1759747
theorem B10022237 : Blo 1563479 10022237 := bstep (se 3 (by rfl) ⟨1879169, by rfl⟩ : syracuseStep 10022237 = 3758339) B3758339
theorem B3517847 : Blo 1563479 3517847 := bstep (se 1 (by rfl) ⟨2638385, by rfl⟩ : syracuseStep 3517847 = 5276771) B5276771
theorem B2346443 : Blo 1563479 2346443 := bstep (se 1 (by rfl) ⟨1759832, by rfl⟩ : syracuseStep 2346443 = 3519665) B3519665
theorem B2346455 : Blo 1563479 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B2969111 : Blo 1563479 2969111 := bstep (se 1 (by rfl) ⟨2226833, by rfl⟩ : syracuseStep 2969111 = 4453667) B4453667
theorem B5279255 : Blo 1563479 5279255 := bstep (se 1 (by rfl) ⟨3959441, by rfl⟩ : syracuseStep 5279255 = 7918883) B7918883
theorem B2346521 : Blo 1563479 2346521 := bstep (se 2 (by rfl) ⟨879945, by rfl⟩ : syracuseStep 2346521 = 1759891) B1759891
theorem B7917101 : Blo 1563479 7917101 := bstep (se 3 (by rfl) ⟨1484456, by rfl⟩ : syracuseStep 7917101 = 2968913) B2968913
theorem B12537389 : Blo 1563479 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B3518027 : Blo 1563479 3518027 := bstep (se 1 (by rfl) ⟨2638520, by rfl⟩ : syracuseStep 3518027 = 5277041) B5277041
theorem B8572517 : Blo 1563479 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B3518081 : Blo 1563479 3518081 := bstep (se 2 (by rfl) ⟨1319280, by rfl⟩ : syracuseStep 3518081 = 2638561) B2638561
theorem B16912003 : Blo 1563479 16912003 := bstep (se 1 (by rfl) ⟨12684002, by rfl⟩ : syracuseStep 16912003 = 25368005) B25368005
theorem B2346635 : Blo 1563479 2346635 := bstep (se 1 (by rfl) ⟨1759976, by rfl⟩ : syracuseStep 2346635 = 3519953) B3519953
theorem B2346647 : Blo 1563479 2346647 := bstep (se 1 (by rfl) ⟨1759985, by rfl⟩ : syracuseStep 2346647 = 3519971) B3519971
theorem B2346713 : Blo 1563479 2346713 := bstep (se 2 (by rfl) ⟨880017, by rfl⟩ : syracuseStep 2346713 = 1760035) B1760035
theorem B2969369 : Blo 1563479 2969369 := bstep (se 2 (by rfl) ⟨1113513, by rfl⟩ : syracuseStep 2969369 = 2227027) B2227027
theorem B2346827 : Blo 1563479 2346827 := bstep (se 1 (by rfl) ⟨1760120, by rfl⟩ : syracuseStep 2346827 = 3520241) B3520241
theorem B3518297 : Blo 1563479 3518297 := bstep (se 2 (by rfl) ⟨1319361, by rfl⟩ : syracuseStep 3518297 = 2638723) B2638723
theorem B2346839 : Blo 1563479 2346839 := bstep (se 1 (by rfl) ⟨1760129, by rfl⟩ : syracuseStep 2346839 = 3520259) B3520259
theorem B6680465 : Blo 1563479 6680465 := bstep (se 2 (by rfl) ⟨2505174, by rfl⟩ : syracuseStep 6680465 = 5010349) B5010349
theorem B2346905 : Blo 1563479 2346905 := bstep (se 2 (by rfl) ⟨880089, by rfl⟩ : syracuseStep 2346905 = 1760179) B1760179
theorem B3518387 : Blo 1563479 3518387 := bstep (se 1 (by rfl) ⟨2638790, by rfl⟩ : syracuseStep 3518387 = 5277581) B5277581
theorem B3518423 : Blo 1563479 3518423 := bstep (se 1 (by rfl) ⟨2638817, by rfl⟩ : syracuseStep 3518423 = 5277635) B5277635
theorem B2936791 : Blo 1563479 2936791 := bstep (se 1 (by rfl) ⟨2202593, by rfl⟩ : syracuseStep 2936791 = 4405187) B4405187
theorem B2347019 : Blo 1563479 2347019 := bstep (se 1 (by rfl) ⟨1760264, by rfl⟩ : syracuseStep 2347019 = 3520529) B3520529
theorem B2347031 : Blo 1563479 2347031 := bstep (se 1 (by rfl) ⟨1760273, by rfl⟩ : syracuseStep 2347031 = 3520547) B3520547
theorem B5279795 : Blo 1563479 5279795 := bstep (se 1 (by rfl) ⟨3959846, by rfl⟩ : syracuseStep 5279795 = 7919693) B7919693
theorem B2347097 : Blo 1563479 2347097 := bstep (se 2 (by rfl) ⟨880161, by rfl⟩ : syracuseStep 2347097 = 1760323) B1760323
theorem B3518603 : Blo 1563479 3518603 := bstep (se 1 (by rfl) ⟨2638952, by rfl⟩ : syracuseStep 3518603 = 5277905) B5277905
theorem B2969779 : Blo 1563479 2969779 := bstep (se 1 (by rfl) ⟨2227334, by rfl⟩ : syracuseStep 2969779 = 4454669) B4454669
theorem B3518657 : Blo 1563479 3518657 := bstep (se 2 (by rfl) ⟨1319496, by rfl⟩ : syracuseStep 3518657 = 2638993) B2638993
theorem B2347211 : Blo 1563479 2347211 := bstep (se 1 (by rfl) ⟨1760408, by rfl⟩ : syracuseStep 2347211 = 3520817) B3520817
theorem B2347223 : Blo 1563479 2347223 := bstep (se 1 (by rfl) ⟨1760417, by rfl⟩ : syracuseStep 2347223 = 3520835) B3520835
theorem B2347289 : Blo 1563479 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B5280065 : Blo 1563479 5280065 := bstep (se 2 (by rfl) ⟨1980024, by rfl⟩ : syracuseStep 5280065 = 3960049) B3960049
theorem B4067659 : Blo 1563479 4067659 := bstep (se 1 (by rfl) ⟨3050744, by rfl⟩ : syracuseStep 4067659 = 6101489) B6101489
theorem B3961163 : Blo 1563479 3961163 := bstep (se 1 (by rfl) ⟨2970872, by rfl⟩ : syracuseStep 3961163 = 5941745) B5941745
theorem B6345053 : Blo 1563479 6345053 := bstep (se 3 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 6345053 = 2379395) B2379395
theorem B2347403 : Blo 1563479 2347403 := bstep (se 1 (by rfl) ⟨1760552, by rfl⟩ : syracuseStep 2347403 = 3521105) B3521105
theorem B2347415 : Blo 1563479 2347415 := bstep (se 1 (by rfl) ⟨1760561, by rfl⟩ : syracuseStep 2347415 = 3521123) B3521123
theorem B3518873 : Blo 1563479 3518873 := bstep (se 2 (by rfl) ⟨1319577, by rfl⟩ : syracuseStep 3518873 = 2639155) B2639155
theorem B3568025 : Blo 1563479 3568025 := bstep (se 2 (by rfl) ⟨1338009, by rfl⟩ : syracuseStep 3568025 = 2676019) B2676019
theorem B19026353 : Blo 1563479 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B3518963 : Blo 1563479 3518963 := bstep (se 1 (by rfl) ⟨2639222, by rfl⟩ : syracuseStep 3518963 = 5278445) B5278445
theorem B3518999 : Blo 1563479 3518999 := bstep (se 1 (by rfl) ⟨2639249, by rfl⟩ : syracuseStep 3518999 = 5278499) B5278499
theorem B3666583 : Blo 1563479 3666583 := bstep (se 1 (by rfl) ⟨2749937, by rfl⟩ : syracuseStep 3666583 = 5499875) B5499875
theorem B2970265 : Blo 1563479 2970265 := bstep (se 2 (by rfl) ⟨1113849, by rfl⟩ : syracuseStep 2970265 = 2227699) B2227699
theorem B11883185 : Blo 1563479 11883185 := bstep (se 2 (by rfl) ⟨4456194, by rfl⟩ : syracuseStep 11883185 = 8912389) B8912389
theorem B1979083 : Blo 1563479 1979083 := bstep (se 1 (by rfl) ⟨1484312, by rfl⟩ : syracuseStep 1979083 = 2968625) B2968625
theorem B3519179 : Blo 1563479 3519179 := bstep (se 1 (by rfl) ⟨2639384, by rfl⟩ : syracuseStep 3519179 = 5278769) B5278769
theorem B3519233 : Blo 1563479 3519233 := bstep (se 2 (by rfl) ⟨1319712, by rfl⟩ : syracuseStep 3519233 = 2639425) B2639425
theorem B5280605 : Blo 1563479 5280605 := bstep (se 3 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 5280605 = 1980227) B1980227
theorem B8909747 : Blo 1563479 8909747 := bstep (se 1 (by rfl) ⟨6682310, by rfl⟩ : syracuseStep 8909747 = 13364621) B13364621
theorem B3519449 : Blo 1563479 3519449 := bstep (se 2 (by rfl) ⟨1319793, by rfl⟩ : syracuseStep 3519449 = 2639587) B2639587
theorem B3519539 : Blo 1563479 3519539 := bstep (se 1 (by rfl) ⟨2639654, by rfl⟩ : syracuseStep 3519539 = 5279309) B5279309
theorem B4453451 : Blo 1563479 4453451 := bstep (se 1 (by rfl) ⟨3340088, by rfl⟩ : syracuseStep 4453451 = 6680177) B6680177
theorem B3519575 : Blo 1563479 3519575 := bstep (se 1 (by rfl) ⟨2639681, by rfl⟩ : syracuseStep 3519575 = 5279363) B5279363
theorem B2675801 : Blo 1563479 2675801 := bstep (se 2 (by rfl) ⟨1003425, by rfl⟩ : syracuseStep 2675801 = 2006851) B2006851
theorem B11883671 : Blo 1563479 11883671 := bstep (se 1 (by rfl) ⟨8912753, by rfl⟩ : syracuseStep 11883671 = 17825507) B17825507
theorem B2970827 : Blo 1563479 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B3339481 : Blo 1563479 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B15029509 : Blo 1563479 15029509 := bstep (se 4 (by rfl) ⟨1409016, by rfl⟩ : syracuseStep 15029509 = 2818033) B2818033
theorem B3519755 : Blo 1563479 3519755 := bstep (se 1 (by rfl) ⟨2639816, by rfl⟩ : syracuseStep 3519755 = 5279633) B5279633
theorem B5936429 : Blo 1563479 5936429 := bstep (se 3 (by rfl) ⟨1113080, by rfl⟩ : syracuseStep 5936429 = 2226161) B2226161
theorem B3519809 : Blo 1563479 3519809 := bstep (se 2 (by rfl) ⟨1319928, by rfl⟩ : syracuseStep 3519809 = 2639857) B2639857
theorem B2971009 : Blo 1563479 2971009 := bstep (se 2 (by rfl) ⟨1114128, by rfl⟩ : syracuseStep 2971009 = 2228257) B2228257
theorem B40637969 : Blo 1563479 40637969 := bstep (se 2 (by rfl) ⟨15239238, by rfl⟩ : syracuseStep 40637969 = 30478477) B30478477
theorem B6018583 : Blo 1563479 6018583 := bstep (se 1 (by rfl) ⟨4513937, by rfl⟩ : syracuseStep 6018583 = 9027875) B9027875
theorem B3520025 : Blo 1563479 3520025 := bstep (se 2 (by rfl) ⟨1320009, by rfl⟩ : syracuseStep 3520025 = 2640019) B2640019
theorem B11277899 : Blo 1563479 11277899 := bstep (se 1 (by rfl) ⟨8458424, by rfl⟩ : syracuseStep 11277899 = 16916849) B16916849
theorem B3520115 : Blo 1563479 3520115 := bstep (se 1 (by rfl) ⟨2640086, by rfl⟩ : syracuseStep 3520115 = 5280173) B5280173
theorem B1980055 : Blo 1563479 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B3520151 : Blo 1563479 3520151 := bstep (se 1 (by rfl) ⟨2640113, by rfl⟩ : syracuseStep 3520151 = 5280227) B5280227
theorem B1758955 : Blo 1563479 1758955 := bstep (se 1 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 1758955 = 2638433) B2638433
theorem B7132931 : Blo 1563479 7132931 := bstep (se 1 (by rfl) ⟨5349698, by rfl⟩ : syracuseStep 7132931 = 10699397) B10699397
theorem B17815301 : Blo 1563479 17815301 := bstep (se 4 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 17815301 = 3340369) B3340369
theorem B3520331 : Blo 1563479 3520331 := bstep (se 1 (by rfl) ⟨2640248, by rfl⟩ : syracuseStep 3520331 = 5280497) B5280497
theorem B1759063 : Blo 1563479 1759063 := bstep (se 1 (by rfl) ⟨1319297, by rfl⟩ : syracuseStep 1759063 = 2638595) B2638595
theorem B3520385 : Blo 1563479 3520385 := bstep (se 2 (by rfl) ⟨1320144, by rfl⟩ : syracuseStep 3520385 = 2640289) B2640289
theorem B5281739 : Blo 1563479 5281739 := bstep (se 1 (by rfl) ⟨3961304, by rfl⟩ : syracuseStep 5281739 = 7922609) B7922609
theorem B1759243 : Blo 1563479 1759243 := bstep (se 1 (by rfl) ⟨1319432, by rfl⟩ : syracuseStep 1759243 = 2638865) B2638865
theorem B4577303 : Blo 1563479 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B3520601 : Blo 1563479 3520601 := bstep (se 2 (by rfl) ⟨1320225, by rfl⟩ : syracuseStep 3520601 = 2640451) B2640451
theorem B4757597 : Blo 1563479 4757597 := bstep (se 3 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 4757597 = 1784099) B1784099
theorem B1759351 : Blo 1563479 1759351 := bstep (se 1 (by rfl) ⟨1319513, by rfl⟩ : syracuseStep 1759351 = 2639027) B2639027
theorem B3520691 : Blo 1563479 3520691 := bstep (se 1 (by rfl) ⟨2640518, by rfl⟩ : syracuseStep 3520691 = 5281037) B5281037
theorem B3520727 : Blo 1563479 3520727 := bstep (se 1 (by rfl) ⟨2640545, by rfl⟩ : syracuseStep 3520727 = 5281091) B5281091
theorem B2226457 : Blo 1563479 2226457 := bstep (se 2 (by rfl) ⟨834921, by rfl⟩ : syracuseStep 2226457 = 1669843) B1669843
theorem B1759531 : Blo 1563479 1759531 := bstep (se 1 (by rfl) ⟨1319648, by rfl⟩ : syracuseStep 1759531 = 2639297) B2639297
theorem B6682925 : Blo 1563479 6682925 := bstep (se 3 (by rfl) ⟨1253048, by rfl⟩ : syracuseStep 6682925 = 2506097) B2506097
theorem B8911205 : Blo 1563479 8911205 := bstep (se 4 (by rfl) ⟨835425, by rfl⟩ : syracuseStep 8911205 = 1670851) B1670851
theorem B3520907 : Blo 1563479 3520907 := bstep (se 1 (by rfl) ⟨2640680, by rfl⟩ : syracuseStep 3520907 = 5281361) B5281361
theorem B1759639 : Blo 1563479 1759639 := bstep (se 1 (by rfl) ⟨1319729, by rfl⟩ : syracuseStep 1759639 = 2639459) B2639459
theorem B3520961 : Blo 1563479 3520961 := bstep (se 2 (by rfl) ⟨1320360, by rfl⟩ : syracuseStep 3520961 = 2640721) B2640721
theorem B3340865 : Blo 1563479 3340865 := bstep (se 2 (by rfl) ⟨1252824, by rfl⟩ : syracuseStep 3340865 = 2505649) B2505649
theorem B1759819 : Blo 1563479 1759819 := bstep (se 1 (by rfl) ⟨1319864, by rfl⟩ : syracuseStep 1759819 = 2639729) B2639729
theorem B1669771 : Blo 1563479 1669771 := bstep (se 1 (by rfl) ⟨1252328, by rfl⟩ : syracuseStep 1669771 = 2504657) B2504657
theorem B3521177 : Blo 1563479 3521177 := bstep (se 2 (by rfl) ⟨1320441, by rfl⟩ : syracuseStep 3521177 = 2640883) B2640883
theorem B11279027 : Blo 1563479 11279027 := bstep (se 1 (by rfl) ⟨8459270, by rfl⟩ : syracuseStep 11279027 = 16918541) B16918541
theorem B1759927 : Blo 1563479 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B5937857 : Blo 1563479 5937857 := bstep (se 2 (by rfl) ⟨2226696, by rfl⟩ : syracuseStep 5937857 = 4453393) B4453393
theorem B2505431 : Blo 1563479 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B6773549 : Blo 1563479 6773549 := bstep (se 3 (by rfl) ⟨1270040, by rfl⟩ : syracuseStep 6773549 = 2540081) B2540081
theorem B1563479 : Blo 1563479 1563479 := bstep (se 1 (by rfl) ⟨1172609, by rfl⟩ : syracuseStep 1563479 = 2345219) B2345219
theorem B1563499 : Blo 1563479 1563499 := bstep (se 1 (by rfl) ⟨1172624, by rfl⟩ : syracuseStep 1563499 = 2345249) B2345249
theorem B1760107 : Blo 1563479 1760107 := bstep (se 1 (by rfl) ⟨1320080, by rfl⟩ : syracuseStep 1760107 = 2640161) B2640161
theorem B1563511 : Blo 1563479 1563511 := bstep (se 1 (by rfl) ⟨1172633, by rfl⟩ : syracuseStep 1563511 = 2345267) B2345267
theorem B1563531 : Blo 1563479 1563531 := bstep (se 1 (by rfl) ⟨1172648, by rfl⟩ : syracuseStep 1563531 = 2345297) B2345297
theorem B1563543 : Blo 1563479 1563543 := bstep (se 1 (by rfl) ⟨1172657, by rfl⟩ : syracuseStep 1563543 = 2345315) B2345315
theorem B1563563 : Blo 1563479 1563563 := bstep (se 1 (by rfl) ⟨1172672, by rfl⟩ : syracuseStep 1563563 = 2345345) B2345345
theorem B1563575 : Blo 1563479 1563575 := bstep (se 1 (by rfl) ⟨1172681, by rfl⟩ : syracuseStep 1563575 = 2345363) B2345363
theorem B1563595 : Blo 1563479 1563595 := bstep (se 1 (by rfl) ⟨1172696, by rfl⟩ : syracuseStep 1563595 = 2345393) B2345393
theorem B1563607 : Blo 1563479 1563607 := bstep (se 1 (by rfl) ⟨1172705, by rfl⟩ : syracuseStep 1563607 = 2345411) B2345411
theorem B1760215 : Blo 1563479 1760215 := bstep (se 1 (by rfl) ⟨1320161, by rfl⟩ : syracuseStep 1760215 = 2640323) B2640323
theorem B6683609 : Blo 1563479 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B1563627 : Blo 1563479 1563627 := bstep (se 1 (by rfl) ⟨1172720, by rfl⟩ : syracuseStep 1563627 = 2345441) B2345441
theorem B1563639 : Blo 1563479 1563639 := bstep (se 1 (by rfl) ⟨1172729, by rfl⟩ : syracuseStep 1563639 = 2345459) B2345459
theorem B1563659 : Blo 1563479 1563659 := bstep (se 1 (by rfl) ⟨1172744, by rfl⟩ : syracuseStep 1563659 = 2345489) B2345489
theorem B8911889 : Blo 1563479 8911889 := bstep (se 2 (by rfl) ⟨3341958, by rfl⟩ : syracuseStep 8911889 = 6683917) B6683917
theorem B1563671 : Blo 1563479 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B1563691 : Blo 1563479 1563691 := bstep (se 1 (by rfl) ⟨1172768, by rfl⟩ : syracuseStep 1563691 = 2345537) B2345537
theorem B1563703 : Blo 1563479 1563703 := bstep (se 1 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 1563703 = 2345555) B2345555
theorem B1563723 : Blo 1563479 1563723 := bstep (se 1 (by rfl) ⟨1172792, by rfl⟩ : syracuseStep 1563723 = 2345585) B2345585
theorem B3341387 : Blo 1563479 3341387 := bstep (se 1 (by rfl) ⟨2506040, by rfl⟩ : syracuseStep 3341387 = 5012081) B5012081
theorem B1563735 : Blo 1563479 1563735 := bstep (se 1 (by rfl) ⟨1172801, by rfl⟩ : syracuseStep 1563735 = 2345603) B2345603
theorem B1563755 : Blo 1563479 1563755 := bstep (se 1 (by rfl) ⟨1172816, by rfl⟩ : syracuseStep 1563755 = 2345633) B2345633
theorem B1563767 : Blo 1563479 1563767 := bstep (se 1 (by rfl) ⟨1172825, by rfl⟩ : syracuseStep 1563767 = 2345651) B2345651
theorem B1563787 : Blo 1563479 1563787 := bstep (se 1 (by rfl) ⟨1172840, by rfl⟩ : syracuseStep 1563787 = 2345681) B2345681
theorem B1760395 : Blo 1563479 1760395 := bstep (se 1 (by rfl) ⟨1320296, by rfl⟩ : syracuseStep 1760395 = 2640593) B2640593
theorem B1563799 : Blo 1563479 1563799 := bstep (se 1 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 1563799 = 2345699) B2345699
theorem B1563819 : Blo 1563479 1563819 := bstep (se 1 (by rfl) ⟨1172864, by rfl⟩ : syracuseStep 1563819 = 2345729) B2345729
theorem B1563831 : Blo 1563479 1563831 := bstep (se 1 (by rfl) ⟨1172873, by rfl⟩ : syracuseStep 1563831 = 2345747) B2345747
theorem B1563851 : Blo 1563479 1563851 := bstep (se 1 (by rfl) ⟨1172888, by rfl⟩ : syracuseStep 1563851 = 2345777) B2345777
theorem B1563863 : Blo 1563479 1563863 := bstep (se 1 (by rfl) ⟨1172897, by rfl⟩ : syracuseStep 1563863 = 2345795) B2345795
theorem B1563883 : Blo 1563479 1563883 := bstep (se 1 (by rfl) ⟨1172912, by rfl⟩ : syracuseStep 1563883 = 2345825) B2345825
theorem B1563895 : Blo 1563479 1563895 := bstep (se 1 (by rfl) ⟨1172921, by rfl⟩ : syracuseStep 1563895 = 2345843) B2345843
theorem B1760503 : Blo 1563479 1760503 := bstep (se 1 (by rfl) ⟨1320377, by rfl⟩ : syracuseStep 1760503 = 2640755) B2640755
theorem B1563915 : Blo 1563479 1563915 := bstep (se 1 (by rfl) ⟨1172936, by rfl⟩ : syracuseStep 1563915 = 2345873) B2345873
theorem B2505995 : Blo 1563479 2505995 := bstep (se 1 (by rfl) ⟨1879496, by rfl⟩ : syracuseStep 2505995 = 3758993) B3758993
theorem B6339863 : Blo 1563479 6339863 := bstep (se 1 (by rfl) ⟨4754897, by rfl⟩ : syracuseStep 6339863 = 9509795) B9509795
theorem B1563927 : Blo 1563479 1563927 := bstep (se 1 (by rfl) ⟨1172945, by rfl⟩ : syracuseStep 1563927 = 2345891) B2345891
theorem B5012759 : Blo 1563479 5012759 := bstep (se 1 (by rfl) ⟨3759569, by rfl⟩ : syracuseStep 5012759 = 7519139) B7519139
theorem B1563947 : Blo 1563479 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B1563959 : Blo 1563479 1563959 := bstep (se 1 (by rfl) ⟨1172969, by rfl⟩ : syracuseStep 1563959 = 2345939) B2345939
theorem B1563979 : Blo 1563479 1563979 := bstep (se 1 (by rfl) ⟨1172984, by rfl⟩ : syracuseStep 1563979 = 2345969) B2345969
theorem B1563991 : Blo 1563479 1563991 := bstep (se 1 (by rfl) ⟨1172993, by rfl⟩ : syracuseStep 1563991 = 2345987) B2345987
theorem B7920989 : Blo 1563479 7920989 := bstep (se 3 (by rfl) ⟨1485185, by rfl⟩ : syracuseStep 7920989 = 2970371) B2970371
theorem B1564011 : Blo 1563479 1564011 := bstep (se 1 (by rfl) ⟨1173008, by rfl⟩ : syracuseStep 1564011 = 2346017) B2346017
theorem B1564023 : Blo 1563479 1564023 := bstep (se 1 (by rfl) ⟨1173017, by rfl⟩ : syracuseStep 1564023 = 2346035) B2346035
theorem B1564043 : Blo 1563479 1564043 := bstep (se 1 (by rfl) ⟨1173032, by rfl⟩ : syracuseStep 1564043 = 2346065) B2346065
theorem B1564055 : Blo 1563479 1564055 := bstep (se 1 (by rfl) ⟨1173041, by rfl⟩ : syracuseStep 1564055 = 2346083) B2346083
theorem B1564075 : Blo 1563479 1564075 := bstep (se 1 (by rfl) ⟨1173056, by rfl⟩ : syracuseStep 1564075 = 2346113) B2346113
theorem B1564087 : Blo 1563479 1564087 := bstep (se 1 (by rfl) ⟨1173065, by rfl⟩ : syracuseStep 1564087 = 2346131) B2346131
theorem B1564107 : Blo 1563479 1564107 := bstep (se 1 (by rfl) ⟨1173080, by rfl⟩ : syracuseStep 1564107 = 2346161) B2346161
theorem B1564119 : Blo 1563479 1564119 := bstep (se 1 (by rfl) ⟨1173089, by rfl⟩ : syracuseStep 1564119 = 2346179) B2346179
theorem B1564139 : Blo 1563479 1564139 := bstep (se 1 (by rfl) ⟨1173104, by rfl⟩ : syracuseStep 1564139 = 2346209) B2346209
theorem B1564151 : Blo 1563479 1564151 := bstep (se 1 (by rfl) ⟨1173113, by rfl⟩ : syracuseStep 1564151 = 2346227) B2346227
theorem B1564171 : Blo 1563479 1564171 := bstep (se 1 (by rfl) ⟨1173128, by rfl⟩ : syracuseStep 1564171 = 2346257) B2346257
theorem B1564183 : Blo 1563479 1564183 := bstep (se 1 (by rfl) ⟨1173137, by rfl⟩ : syracuseStep 1564183 = 2346275) B2346275
theorem B1564203 : Blo 1563479 1564203 := bstep (se 1 (by rfl) ⟨1173152, by rfl⟩ : syracuseStep 1564203 = 2346305) B2346305
theorem B1564215 : Blo 1563479 1564215 := bstep (se 1 (by rfl) ⟨1173161, by rfl⟩ : syracuseStep 1564215 = 2346323) B2346323
theorem B1564235 : Blo 1563479 1564235 := bstep (se 1 (by rfl) ⟨1173176, by rfl⟩ : syracuseStep 1564235 = 2346353) B2346353
theorem B1564247 : Blo 1563479 1564247 := bstep (se 1 (by rfl) ⟨1173185, by rfl⟩ : syracuseStep 1564247 = 2346371) B2346371
theorem B1564267 : Blo 1563479 1564267 := bstep (se 1 (by rfl) ⟨1173200, by rfl⟩ : syracuseStep 1564267 = 2346401) B2346401
theorem B1564279 : Blo 1563479 1564279 := bstep (se 1 (by rfl) ⟨1173209, by rfl⟩ : syracuseStep 1564279 = 2346419) B2346419
theorem B1564299 : Blo 1563479 1564299 := bstep (se 1 (by rfl) ⟨1173224, by rfl⟩ : syracuseStep 1564299 = 2346449) B2346449
theorem B1564311 : Blo 1563479 1564311 := bstep (se 1 (by rfl) ⟨1173233, by rfl⟩ : syracuseStep 1564311 = 2346467) B2346467
theorem B1564331 : Blo 1563479 1564331 := bstep (se 1 (by rfl) ⟨1173248, by rfl⟩ : syracuseStep 1564331 = 2346497) B2346497
theorem B6864563 : Blo 1563479 6864563 := bstep (se 1 (by rfl) ⟨5148422, by rfl⟩ : syracuseStep 6864563 = 10296845) B10296845
theorem B1564343 : Blo 1563479 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B1564363 : Blo 1563479 1564363 := bstep (se 1 (by rfl) ⟨1173272, by rfl⟩ : syracuseStep 1564363 = 2346545) B2346545
theorem B2227915 : Blo 1563479 2227915 := bstep (se 1 (by rfl) ⟨1670936, by rfl⟩ : syracuseStep 2227915 = 3341873) B3341873
theorem B1564375 : Blo 1563479 1564375 := bstep (se 1 (by rfl) ⟨1173281, by rfl⟩ : syracuseStep 1564375 = 2346563) B2346563
theorem B2227927 : Blo 1563479 2227927 := bstep (se 1 (by rfl) ⟨1670945, by rfl⟩ : syracuseStep 2227927 = 3341891) B3341891
theorem B1564395 : Blo 1563479 1564395 := bstep (se 1 (by rfl) ⟨1173296, by rfl⟩ : syracuseStep 1564395 = 2346593) B2346593
theorem B1564407 : Blo 1563479 1564407 := bstep (se 1 (by rfl) ⟨1173305, by rfl⟩ : syracuseStep 1564407 = 2346611) B2346611
theorem B2817803 : Blo 1563479 2817803 := bstep (se 1 (by rfl) ⟨2113352, by rfl⟩ : syracuseStep 2817803 = 4226705) B4226705
theorem B1564427 : Blo 1563479 1564427 := bstep (se 1 (by rfl) ⟨1173320, by rfl⟩ : syracuseStep 1564427 = 2346641) B2346641
theorem B2506507 : Blo 1563479 2506507 := bstep (se 1 (by rfl) ⟨1879880, by rfl⟩ : syracuseStep 2506507 = 3759761) B3759761
theorem B1564439 : Blo 1563479 1564439 := bstep (se 1 (by rfl) ⟨1173329, by rfl⟩ : syracuseStep 1564439 = 2346659) B2346659
theorem B1564459 : Blo 1563479 1564459 := bstep (se 1 (by rfl) ⟨1173344, by rfl⟩ : syracuseStep 1564459 = 2346689) B2346689
theorem B1564471 : Blo 1563479 1564471 := bstep (se 1 (by rfl) ⟨1173353, by rfl⟩ : syracuseStep 1564471 = 2346707) B2346707
theorem B1564491 : Blo 1563479 1564491 := bstep (se 1 (by rfl) ⟨1173368, by rfl⟩ : syracuseStep 1564491 = 2346737) B2346737
theorem B5013323 : Blo 1563479 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B10026827 : Blo 1563479 10026827 := bstep (se 1 (by rfl) ⟨7520120, by rfl⟩ : syracuseStep 10026827 = 15040241) B15040241
theorem B1564503 : Blo 1563479 1564503 := bstep (se 1 (by rfl) ⟨1173377, by rfl⟩ : syracuseStep 1564503 = 2346755) B2346755
theorem B6340445 : Blo 1563479 6340445 := bstep (se 3 (by rfl) ⟨1188833, by rfl⟩ : syracuseStep 6340445 = 2377667) B2377667
theorem B1564523 : Blo 1563479 1564523 := bstep (se 1 (by rfl) ⟨1173392, by rfl⟩ : syracuseStep 1564523 = 2346785) B2346785
theorem B1564535 : Blo 1563479 1564535 := bstep (se 1 (by rfl) ⟨1173401, by rfl⟩ : syracuseStep 1564535 = 2346803) B2346803
theorem B1564555 : Blo 1563479 1564555 := bstep (se 1 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 1564555 = 2346833) B2346833
theorem B8904599 : Blo 1563479 8904599 := bstep (se 1 (by rfl) ⟨6678449, by rfl⟩ : syracuseStep 8904599 = 13356899) B13356899
theorem B1564567 : Blo 1563479 1564567 := bstep (se 1 (by rfl) ⟨1173425, by rfl⟩ : syracuseStep 1564567 = 2346851) B2346851
theorem B1564587 : Blo 1563479 1564587 := bstep (se 1 (by rfl) ⟨1173440, by rfl⟩ : syracuseStep 1564587 = 2346881) B2346881
theorem B1564599 : Blo 1563479 1564599 := bstep (se 1 (by rfl) ⟨1173449, by rfl⟩ : syracuseStep 1564599 = 2346899) B2346899
theorem B1564619 : Blo 1563479 1564619 := bstep (se 1 (by rfl) ⟨1173464, by rfl⟩ : syracuseStep 1564619 = 2346929) B2346929
theorem B1564631 : Blo 1563479 1564631 := bstep (se 1 (by rfl) ⟨1173473, by rfl⟩ : syracuseStep 1564631 = 2346947) B2346947
theorem B1564651 : Blo 1563479 1564651 := bstep (se 1 (by rfl) ⟨1173488, by rfl⟩ : syracuseStep 1564651 = 2346977) B2346977
theorem B1564663 : Blo 1563479 1564663 := bstep (se 1 (by rfl) ⟨1173497, by rfl⟩ : syracuseStep 1564663 = 2346995) B2346995
theorem B1564679 : Blo 1563479 1564679 := bstep (se 1 (by rfl) ⟨1173509, by rfl⟩ : syracuseStep 1564679 = 2347019) B2347019
theorem B5013515 : Blo 1563479 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B1564687 : Blo 1563479 1564687 := bstep (se 1 (by rfl) ⟨1173515, by rfl⟩ : syracuseStep 1564687 = 2347031) B2347031
theorem B2818091 : Blo 1563479 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B160702517 : Blo 1563479 160702517 := bstep (se 5 (by rfl) ⟨7532930, by rfl⟩ : syracuseStep 160702517 = 15065861) B15065861
theorem B1564731 : Blo 1563479 1564731 := bstep (se 1 (by rfl) ⟨1173548, by rfl⟩ : syracuseStep 1564731 = 2347097) B2347097
theorem B17809469 : Blo 1563479 17809469 := bstep (se 3 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 17809469 = 6678551) B6678551
theorem B1564807 : Blo 1563479 1564807 := bstep (se 1 (by rfl) ⟨1173605, by rfl⟩ : syracuseStep 1564807 = 2347211) B2347211
theorem B1564815 : Blo 1563479 1564815 := bstep (se 1 (by rfl) ⟨1173611, by rfl⟩ : syracuseStep 1564815 = 2347223) B2347223
theorem B1564859 : Blo 1563479 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B1564935 : Blo 1563479 1564935 := bstep (se 1 (by rfl) ⟨1173701, by rfl⟩ : syracuseStep 1564935 = 2347403) B2347403
theorem B1564943 : Blo 1563479 1564943 := bstep (se 1 (by rfl) ⟨1173707, by rfl⟩ : syracuseStep 1564943 = 2347415) B2347415
theorem B5423545 : Blo 1563479 5423545 := bstep (se 2 (by rfl) ⟨2033829, by rfl⟩ : syracuseStep 5423545 = 4067659) B4067659
theorem B2818489 : Blo 1563479 2818489 := bstep (se 2 (by rfl) ⟨1056933, by rfl⟩ : syracuseStep 2818489 = 2113867) B2113867
theorem B7922123 : Blo 1563479 7922123 := bstep (se 1 (by rfl) ⟨5941592, by rfl⟩ : syracuseStep 7922123 = 11883185) B11883185
theorem B2638379 : Blo 1563479 2638379 := bstep (se 1 (by rfl) ⟨1978784, by rfl⟩ : syracuseStep 2638379 = 3957569) B3957569
theorem B5939831 : Blo 1563479 5939831 := bstep (se 1 (by rfl) ⟨4454873, by rfl⟩ : syracuseStep 5939831 = 8909747) B8909747
theorem B7922447 : Blo 1563479 7922447 := bstep (se 1 (by rfl) ⟨5941835, by rfl⟩ : syracuseStep 7922447 = 11883671) B11883671
theorem B3957619 : Blo 1563479 3957619 := bstep (se 1 (by rfl) ⟨2968214, by rfl⟩ : syracuseStep 3957619 = 5936429) B5936429
theorem B4227959 : Blo 1563479 4227959 := bstep (se 1 (by rfl) ⟨3170969, by rfl⟩ : syracuseStep 4227959 = 6341939) B6341939
theorem B8905625 : Blo 1563479 8905625 := bstep (se 2 (by rfl) ⟨3339609, by rfl⟩ : syracuseStep 8905625 = 6679219) B6679219
theorem B2638777 : Blo 1563479 2638777 := bstep (se 2 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 2638777 = 1979083) B1979083
theorem B3957761 : Blo 1563479 3957761 := bstep (se 2 (by rfl) ⟨1484160, by rfl⟩ : syracuseStep 3957761 = 2968321) B2968321
theorem B27091979 : Blo 1563479 27091979 := bstep (se 1 (by rfl) ⟨20318984, by rfl⟩ : syracuseStep 27091979 = 40637969) B40637969
theorem B2114731 : Blo 1563479 2114731 := bstep (se 1 (by rfl) ⟨1586048, by rfl⟩ : syracuseStep 2114731 = 3172097) B3172097
theorem B62653729 : Blo 1563479 62653729 := bstep (se 2 (by rfl) ⟨23495148, by rfl⟩ : syracuseStep 62653729 = 46990297) B46990297
theorem B5276987 : Blo 1563479 5276987 := bstep (se 1 (by rfl) ⟨3957740, by rfl⟩ : syracuseStep 5276987 = 7915481) B7915481
theorem B3171731 : Blo 1563479 3171731 := bstep (se 1 (by rfl) ⟨2378798, by rfl⟩ : syracuseStep 3171731 = 4757597) B4757597
theorem B3958217 : Blo 1563479 3958217 := bstep (se 2 (by rfl) ⟨1484331, by rfl⟩ : syracuseStep 3958217 = 2968663) B2968663
theorem B33433037 : Blo 1563479 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B5940803 : Blo 1563479 5940803 := bstep (se 1 (by rfl) ⟨4455602, by rfl⟩ : syracuseStep 5940803 = 8911205) B8911205
theorem B2639479 : Blo 1563479 2639479 := bstep (se 1 (by rfl) ⟨1979609, by rfl⟩ : syracuseStep 2639479 = 3959219) B3959219
theorem B20039345 : Blo 1563479 20039345 := bstep (se 2 (by rfl) ⟨7514754, by rfl⟩ : syracuseStep 20039345 = 15029509) B15029509
theorem B5277473 : Blo 1563479 5277473 := bstep (se 2 (by rfl) ⟨1979052, by rfl⟩ : syracuseStep 5277473 = 3958105) B3958105
theorem B2819873 : Blo 1563479 2819873 := bstep (se 2 (by rfl) ⟨1057452, by rfl⟩ : syracuseStep 2819873 = 2114905) B2114905
theorem B3958571 : Blo 1563479 3958571 := bstep (se 1 (by rfl) ⟨2968928, by rfl⟩ : syracuseStep 3958571 = 5937857) B5937857
theorem B2639675 : Blo 1563479 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B5941259 : Blo 1563479 5941259 := bstep (se 1 (by rfl) ⟨4455944, by rfl⟩ : syracuseStep 5941259 = 8911889) B8911889
theorem B2640073 : Blo 1563479 2640073 := bstep (se 2 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 2640073 = 1980055) B1980055
theorem B2345231 : Blo 1563479 2345231 := bstep (se 1 (by rfl) ⟨1758923, by rfl⟩ : syracuseStep 2345231 = 3517847) B3517847
theorem B2345273 : Blo 1563479 2345273 := bstep (se 2 (by rfl) ⟨879477, by rfl⟩ : syracuseStep 2345273 = 1758955) B1758955
theorem B5278067 : Blo 1563479 5278067 := bstep (se 1 (by rfl) ⟨3958550, by rfl⟩ : syracuseStep 5278067 = 7917101) B7917101
theorem B2345351 : Blo 1563479 2345351 := bstep (se 1 (by rfl) ⟨1759013, by rfl⟩ : syracuseStep 2345351 = 3518027) B3518027
theorem B2345387 : Blo 1563479 2345387 := bstep (se 1 (by rfl) ⟨1759040, by rfl⟩ : syracuseStep 2345387 = 3518081) B3518081
theorem B2345417 : Blo 1563479 2345417 := bstep (se 2 (by rfl) ⟨879531, by rfl⟩ : syracuseStep 2345417 = 1759063) B1759063
theorem B1878535 : Blo 1563479 1878535 := bstep (se 1 (by rfl) ⟨1408901, by rfl⟩ : syracuseStep 1878535 = 2817803) B2817803
theorem B2345531 : Blo 1563479 2345531 := bstep (se 1 (by rfl) ⟨1759148, by rfl⟩ : syracuseStep 2345531 = 3518297) B3518297
theorem B2345591 : Blo 1563479 2345591 := bstep (se 1 (by rfl) ⟨1759193, by rfl⟩ : syracuseStep 2345591 = 3518387) B3518387
theorem B2345615 : Blo 1563479 2345615 := bstep (se 1 (by rfl) ⟨1759211, by rfl⟩ : syracuseStep 2345615 = 3518423) B3518423
theorem B2345657 : Blo 1563479 2345657 := bstep (se 2 (by rfl) ⟨879621, by rfl⟩ : syracuseStep 2345657 = 1759243) B1759243
theorem B2345735 : Blo 1563479 2345735 := bstep (se 1 (by rfl) ⟨1759301, by rfl⟩ : syracuseStep 2345735 = 3518603) B3518603
theorem B3959563 : Blo 1563479 3959563 := bstep (se 1 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 3959563 = 5939345) B5939345
theorem B2345771 : Blo 1563479 2345771 := bstep (se 1 (by rfl) ⟨1759328, by rfl⟩ : syracuseStep 2345771 = 3518657) B3518657
theorem B2345801 : Blo 1563479 2345801 := bstep (se 2 (by rfl) ⟨879675, by rfl⟩ : syracuseStep 2345801 = 1759351) B1759351
theorem B2640775 : Blo 1563479 2640775 := bstep (se 1 (by rfl) ⟨1980581, by rfl⟩ : syracuseStep 2640775 = 3961163) B3961163
theorem B4230035 : Blo 1563479 4230035 := bstep (se 1 (by rfl) ⟨3172526, by rfl⟩ : syracuseStep 4230035 = 6345053) B6345053
theorem B3959705 : Blo 1563479 3959705 := bstep (se 2 (by rfl) ⟨1484889, by rfl⟩ : syracuseStep 3959705 = 2969779) B2969779
theorem B2345915 : Blo 1563479 2345915 := bstep (se 1 (by rfl) ⟨1759436, by rfl⟩ : syracuseStep 2345915 = 3518873) B3518873
theorem B2378683 : Blo 1563479 2378683 := bstep (se 1 (by rfl) ⟨1784012, by rfl⟩ : syracuseStep 2378683 = 3568025) B3568025
theorem B12684235 : Blo 1563479 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B2345975 : Blo 1563479 2345975 := bstep (se 1 (by rfl) ⟨1759481, by rfl⟩ : syracuseStep 2345975 = 3518963) B3518963
theorem B2345999 : Blo 1563479 2345999 := bstep (se 1 (by rfl) ⟨1759499, by rfl⟩ : syracuseStep 2345999 = 3518999) B3518999
theorem B2540842019 : Blo 1563479 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B2346041 : Blo 1563479 2346041 := bstep (se 2 (by rfl) ⟨879765, by rfl⟩ : syracuseStep 2346041 = 1759531) B1759531
theorem B3959867 : Blo 1563479 3959867 := bstep (se 1 (by rfl) ⟨2969900, by rfl⟩ : syracuseStep 3959867 = 5939801) B5939801
theorem B2346119 : Blo 1563479 2346119 := bstep (se 1 (by rfl) ⟨1759589, by rfl⟩ : syracuseStep 2346119 = 3519179) B3519179
theorem B2346155 : Blo 1563479 2346155 := bstep (se 1 (by rfl) ⟨1759616, by rfl⟩ : syracuseStep 2346155 = 3519233) B3519233
theorem B2346185 : Blo 1563479 2346185 := bstep (se 2 (by rfl) ⟨879819, by rfl⟩ : syracuseStep 2346185 = 1759639) B1759639
theorem B2346299 : Blo 1563479 2346299 := bstep (se 1 (by rfl) ⟨1759724, by rfl⟩ : syracuseStep 2346299 = 3519449) B3519449
theorem B2346359 : Blo 1563479 2346359 := bstep (se 1 (by rfl) ⟨1759769, by rfl⟩ : syracuseStep 2346359 = 3519539) B3519539
theorem B15232387 : Blo 1563479 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B2968967 : Blo 1563479 2968967 := bstep (se 1 (by rfl) ⟨2226725, by rfl⟩ : syracuseStep 2968967 = 4453451) B4453451
theorem B2346383 : Blo 1563479 2346383 := bstep (se 1 (by rfl) ⟨1759787, by rfl⟩ : syracuseStep 2346383 = 3519575) B3519575
theorem B3960211 : Blo 1563479 3960211 := bstep (se 1 (by rfl) ⟨2970158, by rfl⟩ : syracuseStep 3960211 = 5940317) B5940317
theorem B2346425 : Blo 1563479 2346425 := bstep (se 2 (by rfl) ⟨879909, by rfl⟩ : syracuseStep 2346425 = 1759819) B1759819
theorem B17821133 : Blo 1563479 17821133 := bstep (se 3 (by rfl) ⟨3341462, by rfl⟩ : syracuseStep 17821133 = 6682925) B6682925
theorem B2346503 : Blo 1563479 2346503 := bstep (se 1 (by rfl) ⟨1759877, by rfl⟩ : syracuseStep 2346503 = 3519755) B3519755
theorem B3960353 : Blo 1563479 3960353 := bstep (se 2 (by rfl) ⟨1485132, by rfl⟩ : syracuseStep 3960353 = 2970265) B2970265
theorem B2346539 : Blo 1563479 2346539 := bstep (se 1 (by rfl) ⟨1759904, by rfl⟩ : syracuseStep 2346539 = 3519809) B3519809
theorem B2346569 : Blo 1563479 2346569 := bstep (se 2 (by rfl) ⟨879963, by rfl⟩ : syracuseStep 2346569 = 1759927) B1759927
theorem B3518099 : Blo 1563479 3518099 := bstep (se 1 (by rfl) ⟨2638574, by rfl⟩ : syracuseStep 3518099 = 5277149) B5277149
theorem B1879723 : Blo 1563479 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B2346683 : Blo 1563479 2346683 := bstep (se 1 (by rfl) ⟨1760012, by rfl⟩ : syracuseStep 2346683 = 3520025) B3520025
theorem B3518153 : Blo 1563479 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B11882213 : Blo 1563479 11882213 := bstep (se 4 (by rfl) ⟨1113957, by rfl⟩ : syracuseStep 11882213 = 2227915) B2227915
theorem B2346743 : Blo 1563479 2346743 := bstep (se 1 (by rfl) ⟨1760057, by rfl⟩ : syracuseStep 2346743 = 3520115) B3520115
theorem B2346767 : Blo 1563479 2346767 := bstep (se 1 (by rfl) ⟨1760075, by rfl⟩ : syracuseStep 2346767 = 3520151) B3520151
theorem B2346809 : Blo 1563479 2346809 := bstep (se 2 (by rfl) ⟨880053, by rfl⟩ : syracuseStep 2346809 = 1760107) B1760107
theorem B4755287 : Blo 1563479 4755287 := bstep (se 1 (by rfl) ⟨3566465, by rfl⟩ : syracuseStep 4755287 = 7132931) B7132931
theorem B2346887 : Blo 1563479 2346887 := bstep (se 1 (by rfl) ⟨1760165, by rfl⟩ : syracuseStep 2346887 = 3520331) B3520331
theorem B2346923 : Blo 1563479 2346923 := bstep (se 1 (by rfl) ⟨1760192, by rfl⟩ : syracuseStep 2346923 = 3520385) B3520385
theorem B2346953 : Blo 1563479 2346953 := bstep (se 2 (by rfl) ⟨880107, by rfl⟩ : syracuseStep 2346953 = 1760215) B1760215
theorem B4755457 : Blo 1563479 4755457 := bstep (se 2 (by rfl) ⟨1783296, by rfl⟩ : syracuseStep 4755457 = 3566593) B3566593
theorem B30060557 : Blo 1563479 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B3051535 : Blo 1563479 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B2347067 : Blo 1563479 2347067 := bstep (se 1 (by rfl) ⟨1760300, by rfl⟩ : syracuseStep 2347067 = 3520601) B3520601
theorem B25710709 : Blo 1563479 25710709 := bstep (se 5 (by rfl) ⟨1205189, by rfl⟩ : syracuseStep 25710709 = 2410379) B2410379
theorem B2347127 : Blo 1563479 2347127 := bstep (se 1 (by rfl) ⟨1760345, by rfl⟩ : syracuseStep 2347127 = 3520691) B3520691
theorem B11874437 : Blo 1563479 11874437 := bstep (se 4 (by rfl) ⟨1113228, by rfl⟩ : syracuseStep 11874437 = 2226457) B2226457
theorem B2347151 : Blo 1563479 2347151 := bstep (se 1 (by rfl) ⟨1760363, by rfl⟩ : syracuseStep 2347151 = 3520727) B3520727
theorem B8908973 : Blo 1563479 8908973 := bstep (se 3 (by rfl) ⟨1670432, by rfl⟩ : syracuseStep 8908973 = 3340865) B3340865
theorem B2347193 : Blo 1563479 2347193 := bstep (se 2 (by rfl) ⟨880197, by rfl⟩ : syracuseStep 2347193 = 1760395) B1760395
theorem B2347271 : Blo 1563479 2347271 := bstep (se 1 (by rfl) ⟨1760453, by rfl⟩ : syracuseStep 2347271 = 3520907) B3520907
theorem B4452641 : Blo 1563479 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B2650411 : Blo 1563479 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B2347307 : Blo 1563479 2347307 := bstep (se 1 (by rfl) ⟨1760480, by rfl⟩ : syracuseStep 2347307 = 3520961) B3520961
theorem B2347337 : Blo 1563479 2347337 := bstep (se 2 (by rfl) ⟨880251, by rfl⟩ : syracuseStep 2347337 = 1760503) B1760503
theorem B3518855 : Blo 1563479 3518855 := bstep (se 1 (by rfl) ⟨2639141, by rfl⟩ : syracuseStep 3518855 = 5278283) B5278283
theorem B7516601 : Blo 1563479 7516601 := bstep (se 2 (by rfl) ⟨2818725, by rfl⟩ : syracuseStep 7516601 = 5637451) B5637451
theorem B2347451 : Blo 1563479 2347451 := bstep (se 1 (by rfl) ⟨1760588, by rfl⟩ : syracuseStep 2347451 = 3521177) B3521177
theorem B3961345 : Blo 1563479 3961345 := bstep (se 2 (by rfl) ⟨1485504, by rfl⟩ : syracuseStep 3961345 = 2971009) B2971009
theorem B3519035 : Blo 1563479 3519035 := bstep (se 1 (by rfl) ⟨2639276, by rfl⟩ : syracuseStep 3519035 = 5278553) B5278553
theorem B6681149 : Blo 1563479 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B3519161 : Blo 1563479 3519161 := bstep (se 2 (by rfl) ⟨1319685, by rfl⟩ : syracuseStep 3519161 = 2639371) B2639371
theorem B8024777 : Blo 1563479 8024777 := bstep (se 2 (by rfl) ⟨3009291, by rfl⟩ : syracuseStep 8024777 = 6018583) B6018583
theorem B22549337 : Blo 1563479 22549337 := bstep (se 2 (by rfl) ⟨8456001, by rfl⟩ : syracuseStep 22549337 = 16912003) B16912003
theorem B1979255 : Blo 1563479 1979255 := bstep (se 1 (by rfl) ⟨1484441, by rfl⟩ : syracuseStep 1979255 = 2968883) B2968883
theorem B6681491 : Blo 1563479 6681491 := bstep (se 1 (by rfl) ⟨5011118, by rfl⟩ : syracuseStep 6681491 = 10022237) B10022237
theorem B5280659 : Blo 1563479 5280659 := bstep (se 1 (by rfl) ⟨3960494, by rfl⟩ : syracuseStep 5280659 = 7920989) B7920989
theorem B3257273 : Blo 1563479 3257273 := bstep (se 2 (by rfl) ⟨1221477, by rfl⟩ : syracuseStep 3257273 = 2442955) B2442955
theorem B2970569 : Blo 1563479 2970569 := bstep (se 2 (by rfl) ⟨1113963, by rfl⟩ : syracuseStep 2970569 = 2227927) B2227927
theorem B1979407 : Blo 1563479 1979407 := bstep (se 1 (by rfl) ⟨1484555, by rfl⟩ : syracuseStep 1979407 = 2969111) B2969111
theorem B3519503 : Blo 1563479 3519503 := bstep (se 1 (by rfl) ⟨2639627, by rfl⟩ : syracuseStep 3519503 = 5279255) B5279255
theorem B3519521 : Blo 1563479 3519521 := bstep (se 2 (by rfl) ⟨1319820, by rfl⟩ : syracuseStep 3519521 = 2639641) B2639641
theorem B5715011 : Blo 1563479 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B4576375 : Blo 1563479 4576375 := bstep (se 1 (by rfl) ⟨3432281, by rfl⟩ : syracuseStep 4576375 = 6864563) B6864563
theorem B1979579 : Blo 1563479 1979579 := bstep (se 1 (by rfl) ⟨1484684, by rfl⟩ : syracuseStep 1979579 = 2969369) B2969369
theorem B4453643 : Blo 1563479 4453643 := bstep (se 1 (by rfl) ⟨3340232, by rfl⟩ : syracuseStep 4453643 = 6680465) B6680465
theorem B5936399 : Blo 1563479 5936399 := bstep (se 1 (by rfl) ⟨4452299, by rfl⟩ : syracuseStep 5936399 = 8904599) B8904599
theorem B8459635 : Blo 1563479 8459635 := bstep (se 1 (by rfl) ⟨6344726, by rfl⟩ : syracuseStep 8459635 = 12689453) B12689453
theorem B3519863 : Blo 1563479 3519863 := bstep (se 1 (by rfl) ⟨2639897, by rfl⟩ : syracuseStep 3519863 = 5279795) B5279795
theorem B3520043 : Blo 1563479 3520043 := bstep (se 1 (by rfl) ⟨2640032, by rfl⟩ : syracuseStep 3520043 = 5280065) B5280065
theorem B1693319 : Blo 1563479 1693319 := bstep (se 1 (by rfl) ⟨1269989, by rfl⟩ : syracuseStep 1693319 = 2539979) B2539979
theorem B1758991 : Blo 1563479 1758991 := bstep (se 1 (by rfl) ⟨1319243, by rfl⟩ : syracuseStep 1758991 = 2638487) B2638487
theorem B3520403 : Blo 1563479 3520403 := bstep (se 1 (by rfl) ⟨2640302, by rfl⟩ : syracuseStep 3520403 = 5280605) B5280605
theorem B3520457 : Blo 1563479 3520457 := bstep (se 2 (by rfl) ⟨1320171, by rfl⟩ : syracuseStep 3520457 = 2640343) B2640343
theorem B1783867 : Blo 1563479 1783867 := bstep (se 1 (by rfl) ⟨1337900, by rfl⟩ : syracuseStep 1783867 = 2675801) B2675801
theorem B1980551 : Blo 1563479 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B2226361 : Blo 1563479 2226361 := bstep (se 2 (by rfl) ⟨834885, by rfl⟩ : syracuseStep 2226361 = 1669771) B1669771
theorem B4888777 : Blo 1563479 4888777 := bstep (se 2 (by rfl) ⟨1833291, by rfl⟩ : syracuseStep 4888777 = 3666583) B3666583
theorem B1759495 : Blo 1563479 1759495 := bstep (se 1 (by rfl) ⟨1319621, by rfl⟩ : syracuseStep 1759495 = 2639243) B2639243
theorem B7518599 : Blo 1563479 7518599 := bstep (se 1 (by rfl) ⟨5638949, by rfl⟩ : syracuseStep 7518599 = 11277899) B11277899
theorem B7920017 : Blo 1563479 7920017 := bstep (se 2 (by rfl) ⟨2970006, by rfl⟩ : syracuseStep 7920017 = 5940013) B5940013
theorem B1759675 : Blo 1563479 1759675 := bstep (se 1 (by rfl) ⟨1319756, by rfl⟩ : syracuseStep 1759675 = 2639513) B2639513
theorem B11876867 : Blo 1563479 11876867 := bstep (se 1 (by rfl) ⟨8907650, by rfl⟩ : syracuseStep 11876867 = 17815301) B17815301
theorem B3521159 : Blo 1563479 3521159 := bstep (se 1 (by rfl) ⟨2640869, by rfl⟩ : syracuseStep 3521159 = 5281739) B5281739
theorem B13368037 : Blo 1563479 13368037 := bstep (se 4 (by rfl) ⟨1253253, by rfl⟩ : syracuseStep 13368037 = 2506507) B2506507
theorem B1563527 : Blo 1563479 1563527 := bstep (se 1 (by rfl) ⟨1172645, by rfl⟩ : syracuseStep 1563527 = 2345291) B2345291
theorem B5938055 : Blo 1563479 5938055 := bstep (se 1 (by rfl) ⟨4453541, by rfl⟩ : syracuseStep 5938055 = 8907083) B8907083
theorem B1563535 : Blo 1563479 1563535 := bstep (se 1 (by rfl) ⟨1172651, by rfl⟩ : syracuseStep 1563535 = 2345303) B2345303
theorem B1760143 : Blo 1563479 1760143 := bstep (se 1 (by rfl) ⟨1320107, by rfl⟩ : syracuseStep 1760143 = 2640215) B2640215
theorem B1563579 : Blo 1563479 1563579 := bstep (se 1 (by rfl) ⟨1172684, by rfl⟩ : syracuseStep 1563579 = 2345369) B2345369
theorem B1563655 : Blo 1563479 1563655 := bstep (se 1 (by rfl) ⟨1172741, by rfl⟩ : syracuseStep 1563655 = 2345483) B2345483
theorem B1563663 : Blo 1563479 1563663 := bstep (se 1 (by rfl) ⟨1172747, by rfl⟩ : syracuseStep 1563663 = 2345495) B2345495
theorem B1563707 : Blo 1563479 1563707 := bstep (se 1 (by rfl) ⟨1172780, by rfl⟩ : syracuseStep 1563707 = 2345561) B2345561
theorem B3759223 : Blo 1563479 3759223 := bstep (se 1 (by rfl) ⟨2819417, by rfl⟩ : syracuseStep 3759223 = 5638835) B5638835
theorem B7519351 : Blo 1563479 7519351 := bstep (se 1 (by rfl) ⟨5639513, by rfl⟩ : syracuseStep 7519351 = 11279027) B11279027
theorem B1563783 : Blo 1563479 1563783 := bstep (se 1 (by rfl) ⟨1172837, by rfl⟩ : syracuseStep 1563783 = 2345675) B2345675
theorem B1563791 : Blo 1563479 1563791 := bstep (se 1 (by rfl) ⟨1172843, by rfl⟩ : syracuseStep 1563791 = 2345687) B2345687
theorem B1563835 : Blo 1563479 1563835 := bstep (se 1 (by rfl) ⟨1172876, by rfl⟩ : syracuseStep 1563835 = 2345753) B2345753
theorem B1563911 : Blo 1563479 1563911 := bstep (se 1 (by rfl) ⟨1172933, by rfl⟩ : syracuseStep 1563911 = 2345867) B2345867
theorem B1563919 : Blo 1563479 1563919 := bstep (se 1 (by rfl) ⟨1172939, by rfl⟩ : syracuseStep 1563919 = 2345879) B2345879
theorem B1563963 : Blo 1563479 1563963 := bstep (se 1 (by rfl) ⟨1172972, by rfl⟩ : syracuseStep 1563963 = 2345945) B2345945
theorem B4455739 : Blo 1563479 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B1564039 : Blo 1563479 1564039 := bstep (se 1 (by rfl) ⟨1173029, by rfl⟩ : syracuseStep 1564039 = 2346059) B2346059
theorem B2227591 : Blo 1563479 2227591 := bstep (se 1 (by rfl) ⟨1670693, by rfl⟩ : syracuseStep 2227591 = 3341387) B3341387
theorem B1564047 : Blo 1563479 1564047 := bstep (se 1 (by rfl) ⟨1173035, by rfl⟩ : syracuseStep 1564047 = 2346071) B2346071
theorem B1564091 : Blo 1563479 1564091 := bstep (se 1 (by rfl) ⟨1173068, by rfl⟩ : syracuseStep 1564091 = 2346137) B2346137
theorem B18062797 : Blo 1563479 18062797 := bstep (se 3 (by rfl) ⟨3386774, by rfl⟩ : syracuseStep 18062797 = 6773549) B6773549
theorem B1564167 : Blo 1563479 1564167 := bstep (se 1 (by rfl) ⟨1173125, by rfl⟩ : syracuseStep 1564167 = 2346251) B2346251
theorem B1670663 : Blo 1563479 1670663 := bstep (se 1 (by rfl) ⟨1252997, by rfl⟩ : syracuseStep 1670663 = 2505995) B2505995
theorem B4226575 : Blo 1563479 4226575 := bstep (se 1 (by rfl) ⟨3169931, by rfl⟩ : syracuseStep 4226575 = 6339863) B6339863
theorem B1564175 : Blo 1563479 1564175 := bstep (se 1 (by rfl) ⟨1173131, by rfl⟩ : syracuseStep 1564175 = 2346263) B2346263
theorem B3341839 : Blo 1563479 3341839 := bstep (se 1 (by rfl) ⟨2506379, by rfl⟩ : syracuseStep 3341839 = 5012759) B5012759
theorem B1564219 : Blo 1563479 1564219 := bstep (se 1 (by rfl) ⟨1173164, by rfl⟩ : syracuseStep 1564219 = 2346329) B2346329
theorem B1564295 : Blo 1563479 1564295 := bstep (se 1 (by rfl) ⟨1173221, by rfl⟩ : syracuseStep 1564295 = 2346443) B2346443
theorem B1564303 : Blo 1563479 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B1564347 : Blo 1563479 1564347 := bstep (se 1 (by rfl) ⟨1173260, by rfl⟩ : syracuseStep 1564347 = 2346521) B2346521
theorem B1564423 : Blo 1563479 1564423 := bstep (se 1 (by rfl) ⟨1173317, by rfl⟩ : syracuseStep 1564423 = 2346635) B2346635
theorem B1564431 : Blo 1563479 1564431 := bstep (se 1 (by rfl) ⟨1173323, by rfl⟩ : syracuseStep 1564431 = 2346647) B2346647
theorem B1564475 : Blo 1563479 1564475 := bstep (se 1 (by rfl) ⟨1173356, by rfl⟩ : syracuseStep 1564475 = 2346713) B2346713
theorem B1564551 : Blo 1563479 1564551 := bstep (se 1 (by rfl) ⟨1173413, by rfl⟩ : syracuseStep 1564551 = 2346827) B2346827
theorem B3342215 : Blo 1563479 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B6684551 : Blo 1563479 6684551 := bstep (se 1 (by rfl) ⟨5013413, by rfl⟩ : syracuseStep 6684551 = 10026827) B10026827
theorem B1564559 : Blo 1563479 1564559 := bstep (se 1 (by rfl) ⟨1173419, by rfl⟩ : syracuseStep 1564559 = 2346839) B2346839
theorem B4226963 : Blo 1563479 4226963 := bstep (se 1 (by rfl) ⟨3170222, by rfl⟩ : syracuseStep 4226963 = 6340445) B6340445
theorem B1564603 : Blo 1563479 1564603 := bstep (se 1 (by rfl) ⟨1173452, by rfl⟩ : syracuseStep 1564603 = 2346905) B2346905
theorem B3915721 : Blo 1563479 3915721 := bstep (se 2 (by rfl) ⟨1468395, by rfl⟩ : syracuseStep 3915721 = 2936791) B2936791
theorem B6340609 : Blo 1563479 6340609 := bstep (se 2 (by rfl) ⟨2377728, by rfl⟩ : syracuseStep 6340609 = 4755457) B4755457
theorem B13369373 : Blo 1563479 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B107135011 : Blo 1563479 107135011 := bstep (se 1 (by rfl) ⟨80351258, by rfl⟩ : syracuseStep 107135011 = 160702517) B160702517
theorem B10018853 : Blo 1563479 10018853 := bstep (se 4 (by rfl) ⟨939267, by rfl⟩ : syracuseStep 10018853 = 1878535) B1878535
theorem B1564711 : Blo 1563479 1564711 := bstep (se 1 (by rfl) ⟨1173533, by rfl⟩ : syracuseStep 1564711 = 2347067) B2347067
theorem B1564751 : Blo 1563479 1564751 := bstep (se 1 (by rfl) ⟨1173563, by rfl⟩ : syracuseStep 1564751 = 2347127) B2347127
theorem B1564767 : Blo 1563479 1564767 := bstep (se 1 (by rfl) ⟨1173575, by rfl⟩ : syracuseStep 1564767 = 2347151) B2347151
theorem B5939315 : Blo 1563479 5939315 := bstep (se 1 (by rfl) ⟨4454486, by rfl⟩ : syracuseStep 5939315 = 8908973) B8908973
theorem B1564795 : Blo 1563479 1564795 := bstep (se 1 (by rfl) ⟨1173596, by rfl⟩ : syracuseStep 1564795 = 2347193) B2347193
theorem B1564847 : Blo 1563479 1564847 := bstep (se 1 (by rfl) ⟨1173635, by rfl⟩ : syracuseStep 1564847 = 2347271) B2347271
theorem B1564871 : Blo 1563479 1564871 := bstep (se 1 (by rfl) ⟨1173653, by rfl⟩ : syracuseStep 1564871 = 2347307) B2347307
theorem B1564891 : Blo 1563479 1564891 := bstep (se 1 (by rfl) ⟨1173668, by rfl⟩ : syracuseStep 1564891 = 2347337) B2347337
theorem B1564967 : Blo 1563479 1564967 := bstep (se 1 (by rfl) ⟨1173725, by rfl⟩ : syracuseStep 1564967 = 2347451) B2347451
theorem B5349851 : Blo 1563479 5349851 := bstep (se 1 (by rfl) ⟨4012388, by rfl⟩ : syracuseStep 5349851 = 8024777) B8024777
theorem B15032891 : Blo 1563479 15032891 := bstep (se 1 (by rfl) ⟨11274668, by rfl⟩ : syracuseStep 15032891 = 22549337) B22549337
theorem B2818639 : Blo 1563479 2818639 := bstep (se 1 (by rfl) ⟨2113979, by rfl⟩ : syracuseStep 2818639 = 4227959) B4227959
theorem B2171515 : Blo 1563479 2171515 := bstep (se 1 (by rfl) ⟨1628636, by rfl⟩ : syracuseStep 2171515 = 3257273) B3257273
theorem B2638507 : Blo 1563479 2638507 := bstep (se 1 (by rfl) ⟨1978880, by rfl⟩ : syracuseStep 2638507 = 3957761) B3957761
theorem B3810007 : Blo 1563479 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B3957599 : Blo 1563479 3957599 := bstep (se 1 (by rfl) ⟨2968199, by rfl⟩ : syracuseStep 3957599 = 5936399) B5936399
theorem B2638811 : Blo 1563479 2638811 := bstep (se 1 (by rfl) ⟨1979108, by rfl⟩ : syracuseStep 2638811 = 3958217) B3958217
theorem B5276825 : Blo 1563479 5276825 := bstep (se 2 (by rfl) ⟨1978809, by rfl⟩ : syracuseStep 5276825 = 3957619) B3957619
theorem B2639047 : Blo 1563479 2639047 := bstep (se 1 (by rfl) ⟨1979285, by rfl⟩ : syracuseStep 2639047 = 3958571) B3958571
theorem B2639209 : Blo 1563479 2639209 := bstep (se 2 (by rfl) ⟨989703, by rfl⟩ : syracuseStep 2639209 = 1979407) B1979407
theorem B4515517 : Blo 1563479 4515517 := bstep (se 3 (by rfl) ⟨846659, by rfl⟩ : syracuseStep 4515517 = 1693319) B1693319
theorem B5940985 : Blo 1563479 5940985 := bstep (se 2 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 5940985 = 4455739) B4455739
theorem B20309849 : Blo 1563479 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B3958703 : Blo 1563479 3958703 := bstep (se 1 (by rfl) ⟨2969027, by rfl⟩ : syracuseStep 3958703 = 5938055) B5938055
theorem B2820023 : Blo 1563479 2820023 := bstep (se 1 (by rfl) ⟨2115017, by rfl⟩ : syracuseStep 2820023 = 4230035) B4230035
theorem B2639803 : Blo 1563479 2639803 := bstep (se 1 (by rfl) ⟨1979852, by rfl⟩ : syracuseStep 2639803 = 3959705) B3959705
theorem B1693894679 : Blo 1563479 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B2639911 : Blo 1563479 2639911 := bstep (se 1 (by rfl) ⟨1979933, by rfl⟩ : syracuseStep 2639911 = 3959867) B3959867
theorem B11880755 : Blo 1563479 11880755 := bstep (se 1 (by rfl) ⟨8910566, by rfl⟩ : syracuseStep 11880755 = 17821133) B17821133
theorem B5278013 : Blo 1563479 5278013 := bstep (se 3 (by rfl) ⟨989627, by rfl⟩ : syracuseStep 5278013 = 1979255) B1979255
theorem B2345321 : Blo 1563479 2345321 := bstep (se 2 (by rfl) ⟨879495, by rfl⟩ : syracuseStep 2345321 = 1758991) B1758991
theorem B2640235 : Blo 1563479 2640235 := bstep (se 1 (by rfl) ⟨1980176, by rfl⟩ : syracuseStep 2640235 = 3960353) B3960353
theorem B20883845 : Blo 1563479 20883845 := bstep (se 4 (by rfl) ⟨1957860, by rfl⟩ : syracuseStep 20883845 = 3915721) B3915721
theorem B2345399 : Blo 1563479 2345399 := bstep (se 1 (by rfl) ⟨1759049, by rfl⟩ : syracuseStep 2345399 = 3518099) B3518099
theorem B2345435 : Blo 1563479 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B20040371 : Blo 1563479 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B11872979 : Blo 1563479 11872979 := bstep (se 1 (by rfl) ⟨8904734, by rfl⟩ : syracuseStep 11872979 = 17809469) B17809469
theorem B2378489 : Blo 1563479 2378489 := bstep (se 2 (by rfl) ⟨891933, by rfl⟩ : syracuseStep 2378489 = 1783867) B1783867
theorem B7916291 : Blo 1563479 7916291 := bstep (se 1 (by rfl) ⟨5937218, by rfl⟩ : syracuseStep 7916291 = 11874437) B11874437
theorem B7514909 : Blo 1563479 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B2968427 : Blo 1563479 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B2968481 : Blo 1563479 2968481 := bstep (se 2 (by rfl) ⟨1113180, by rfl⟩ : syracuseStep 2968481 = 2226361) B2226361
theorem B2345903 : Blo 1563479 2345903 := bstep (se 1 (by rfl) ⟨1759427, by rfl⟩ : syracuseStep 2345903 = 3518855) B3518855
theorem B2345993 : Blo 1563479 2345993 := bstep (se 2 (by rfl) ⟨879747, by rfl⟩ : syracuseStep 2345993 = 1759495) B1759495
theorem B2346023 : Blo 1563479 2346023 := bstep (se 1 (by rfl) ⟨1759517, by rfl⟩ : syracuseStep 2346023 = 3519035) B3519035
theorem B3533881 : Blo 1563479 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B3959887 : Blo 1563479 3959887 := bstep (se 1 (by rfl) ⟨2969915, by rfl⟩ : syracuseStep 3959887 = 5939831) B5939831
theorem B2346107 : Blo 1563479 2346107 := bstep (se 1 (by rfl) ⟨1759580, by rfl⟩ : syracuseStep 2346107 = 3519161) B3519161
theorem B5278877 : Blo 1563479 5278877 := bstep (se 3 (by rfl) ⟨989789, by rfl⟩ : syracuseStep 5278877 = 1979579) B1979579
theorem B2346233 : Blo 1563479 2346233 := bstep (se 2 (by rfl) ⟨879837, by rfl⟩ : syracuseStep 2346233 = 1759675) B1759675
theorem B2346335 : Blo 1563479 2346335 := bstep (se 1 (by rfl) ⟨1759751, by rfl⟩ : syracuseStep 2346335 = 3519503) B3519503
theorem B2346347 : Blo 1563479 2346347 := bstep (se 1 (by rfl) ⟨1759760, by rfl⟩ : syracuseStep 2346347 = 3519521) B3519521
theorem B3517991 : Blo 1563479 3517991 := bstep (se 1 (by rfl) ⟨2638493, by rfl⟩ : syracuseStep 3517991 = 5276987) B5276987
theorem B2346575 : Blo 1563479 2346575 := bstep (se 1 (by rfl) ⟨1759931, by rfl⟩ : syracuseStep 2346575 = 3519863) B3519863
theorem B5279417 : Blo 1563479 5279417 := bstep (se 2 (by rfl) ⟨1979781, by rfl⟩ : syracuseStep 5279417 = 3959563) B3959563
theorem B2346695 : Blo 1563479 2346695 := bstep (se 1 (by rfl) ⟨1760021, by rfl⟩ : syracuseStep 2346695 = 3520043) B3520043
theorem B3960535 : Blo 1563479 3960535 := bstep (se 1 (by rfl) ⟨2970401, by rfl⟩ : syracuseStep 3960535 = 5940803) B5940803
theorem B8457949 : Blo 1563479 8457949 := bstep (se 3 (by rfl) ⟨1585865, by rfl⟩ : syracuseStep 8457949 = 3171731) B3171731
theorem B2346857 : Blo 1563479 2346857 := bstep (se 2 (by rfl) ⟨880071, by rfl⟩ : syracuseStep 2346857 = 1760143) B1760143
theorem B3518315 : Blo 1563479 3518315 := bstep (se 1 (by rfl) ⟨2638736, by rfl⟩ : syracuseStep 3518315 = 5277473) B5277473
theorem B1879915 : Blo 1563479 1879915 := bstep (se 1 (by rfl) ⟨1409936, by rfl⟩ : syracuseStep 1879915 = 2819873) B2819873
theorem B3518369 : Blo 1563479 3518369 := bstep (se 2 (by rfl) ⟨1319388, by rfl⟩ : syracuseStep 3518369 = 2638777) B2638777
theorem B2346935 : Blo 1563479 2346935 := bstep (se 1 (by rfl) ⟨1760201, by rfl⟩ : syracuseStep 2346935 = 3520403) B3520403
theorem B16912313 : Blo 1563479 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B2346971 : Blo 1563479 2346971 := bstep (se 1 (by rfl) ⟨1760228, by rfl⟩ : syracuseStep 2346971 = 3520457) B3520457
theorem B3960839 : Blo 1563479 3960839 := bstep (se 1 (by rfl) ⟨2970629, by rfl⟩ : syracuseStep 3960839 = 5941259) B5941259
theorem B3518711 : Blo 1563479 3518711 := bstep (se 1 (by rfl) ⟨2639033, by rfl⟩ : syracuseStep 3518711 = 5278067) B5278067
theorem B5280011 : Blo 1563479 5280011 := bstep (se 1 (by rfl) ⟨3960008, by rfl⟩ : syracuseStep 5280011 = 7920017) B7920017
theorem B7917911 : Blo 1563479 7917911 := bstep (se 1 (by rfl) ⟨5938433, by rfl⟩ : syracuseStep 7917911 = 11876867) B11876867
theorem B83538305 : Blo 1563479 83538305 := bstep (se 2 (by rfl) ⟨31326864, by rfl⟩ : syracuseStep 83538305 = 62653729) B62653729
theorem B2347439 : Blo 1563479 2347439 := bstep (se 1 (by rfl) ⟨1760579, by rfl⟩ : syracuseStep 2347439 = 3521159) B3521159
theorem B2970121 : Blo 1563479 2970121 := bstep (se 2 (by rfl) ⟨1113795, by rfl⟩ : syracuseStep 2970121 = 2227591) B2227591
theorem B5280281 : Blo 1563479 5280281 := bstep (se 2 (by rfl) ⟨1980105, by rfl⟩ : syracuseStep 5280281 = 3960211) B3960211
theorem B3519305 : Blo 1563479 3519305 := bstep (se 2 (by rfl) ⟨1319739, by rfl⟩ : syracuseStep 3519305 = 2639479) B2639479
theorem B1979311 : Blo 1563479 1979311 := bstep (se 1 (by rfl) ⟨1484483, by rfl⟩ : syracuseStep 1979311 = 2968967) B2968967
theorem B12686309 : Blo 1563479 12686309 := bstep (se 4 (by rfl) ⟨1189341, by rfl⟩ : syracuseStep 12686309 = 2378683) B2378683
theorem B4068713 : Blo 1563479 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B34280945 : Blo 1563479 34280945 := bstep (se 2 (by rfl) ⟨12855354, by rfl⟩ : syracuseStep 34280945 = 25710709) B25710709
theorem B3520097 : Blo 1563479 3520097 := bstep (se 2 (by rfl) ⟨1320036, by rfl⟩ : syracuseStep 3520097 = 2640073) B2640073
theorem B6518369 : Blo 1563479 6518369 := bstep (se 2 (by rfl) ⟨2444388, by rfl⟩ : syracuseStep 6518369 = 4888777) B4888777
theorem B5011067 : Blo 1563479 5011067 := bstep (se 1 (by rfl) ⟨3758300, by rfl⟩ : syracuseStep 5011067 = 7516601) B7516601
theorem B5281415 : Blo 1563479 5281415 := bstep (se 1 (by rfl) ⟨3961061, by rfl⟩ : syracuseStep 5281415 = 7922123) B7922123
theorem B5281469 : Blo 1563479 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B1758919 : Blo 1563479 1758919 := bstep (se 1 (by rfl) ⟨1319189, by rfl⟩ : syracuseStep 1758919 = 2638379) B2638379
theorem B4454099 : Blo 1563479 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B5281631 : Blo 1563479 5281631 := bstep (se 1 (by rfl) ⟨3961223, by rfl⟩ : syracuseStep 5281631 = 7922447) B7922447
theorem B7231393 : Blo 1563479 7231393 := bstep (se 2 (by rfl) ⟨2711772, by rfl⟩ : syracuseStep 7231393 = 5423545) B5423545
theorem B3757985 : Blo 1563479 3757985 := bstep (se 2 (by rfl) ⟨1409244, by rfl⟩ : syracuseStep 3757985 = 2818489) B2818489
theorem B4454327 : Blo 1563479 4454327 := bstep (se 1 (by rfl) ⟨3340745, by rfl⟩ : syracuseStep 4454327 = 6681491) B6681491
theorem B3520439 : Blo 1563479 3520439 := bstep (se 1 (by rfl) ⟨2640329, by rfl⟩ : syracuseStep 3520439 = 5280659) B5280659
theorem B5937083 : Blo 1563479 5937083 := bstep (se 1 (by rfl) ⟨4452812, by rfl⟩ : syracuseStep 5937083 = 8905625) B8905625
theorem B1980379 : Blo 1563479 1980379 := bstep (se 1 (by rfl) ⟨1485284, by rfl⟩ : syracuseStep 1980379 = 2970569) B2970569
theorem B5281793 : Blo 1563479 5281793 := bstep (se 2 (by rfl) ⟨1980672, by rfl⟩ : syracuseStep 5281793 = 3961345) B3961345
theorem B18061319 : Blo 1563479 18061319 := bstep (se 1 (by rfl) ⟨13545989, by rfl⟩ : syracuseStep 18061319 = 27091979) B27091979
theorem B11876381 : Blo 1563479 11876381 := bstep (se 3 (by rfl) ⟨2226821, by rfl⟩ : syracuseStep 11876381 = 4453643) B4453643
theorem B11278565 : Blo 1563479 11278565 := bstep (se 4 (by rfl) ⟨1057365, by rfl⟩ : syracuseStep 11278565 = 2114731) B2114731
theorem B17824049 : Blo 1563479 17824049 := bstep (se 2 (by rfl) ⟨6684018, by rfl⟩ : syracuseStep 17824049 = 13368037) B13368037
theorem B22288691 : Blo 1563479 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B13359563 : Blo 1563479 13359563 := bstep (se 1 (by rfl) ⟨10019672, by rfl⟩ : syracuseStep 13359563 = 20039345) B20039345
theorem B3521033 : Blo 1563479 3521033 := bstep (se 2 (by rfl) ⟨1320387, by rfl⟩ : syracuseStep 3521033 = 2640775) B2640775
theorem B1759783 : Blo 1563479 1759783 := bstep (se 1 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 1759783 = 2639675) B2639675
theorem B4455101 : Blo 1563479 4455101 := bstep (se 3 (by rfl) ⟨835331, by rfl⟩ : syracuseStep 4455101 = 1670663) B1670663
theorem B6101833 : Blo 1563479 6101833 := bstep (se 2 (by rfl) ⟨2288187, by rfl⟩ : syracuseStep 6101833 = 4576375) B4576375
theorem B5012297 : Blo 1563479 5012297 := bstep (se 2 (by rfl) ⟨1879611, by rfl⟩ : syracuseStep 5012297 = 3759223) B3759223
theorem B10025801 : Blo 1563479 10025801 := bstep (se 2 (by rfl) ⟨3759675, by rfl⟩ : syracuseStep 10025801 = 7519351) B7519351
theorem B1563487 : Blo 1563479 1563487 := bstep (se 1 (by rfl) ⟨1172615, by rfl⟩ : syracuseStep 1563487 = 2345231) B2345231
theorem B1563515 : Blo 1563479 1563515 := bstep (se 1 (by rfl) ⟨1172636, by rfl⟩ : syracuseStep 1563515 = 2345273) B2345273
theorem B1563567 : Blo 1563479 1563567 := bstep (se 1 (by rfl) ⟨1172675, by rfl⟩ : syracuseStep 1563567 = 2345351) B2345351
theorem B5012399 : Blo 1563479 5012399 := bstep (se 1 (by rfl) ⟨3759299, by rfl⟩ : syracuseStep 5012399 = 7518599) B7518599
theorem B1563591 : Blo 1563479 1563591 := bstep (se 1 (by rfl) ⟨1172693, by rfl⟩ : syracuseStep 1563591 = 2345387) B2345387
theorem B1563611 : Blo 1563479 1563611 := bstep (se 1 (by rfl) ⟨1172708, by rfl⟩ : syracuseStep 1563611 = 2345417) B2345417
theorem B1563687 : Blo 1563479 1563687 := bstep (se 1 (by rfl) ⟨1172765, by rfl⟩ : syracuseStep 1563687 = 2345531) B2345531
theorem B1563727 : Blo 1563479 1563727 := bstep (se 1 (by rfl) ⟨1172795, by rfl⟩ : syracuseStep 1563727 = 2345591) B2345591
theorem B1563743 : Blo 1563479 1563743 := bstep (se 1 (by rfl) ⟨1172807, by rfl⟩ : syracuseStep 1563743 = 2345615) B2345615
theorem B1563771 : Blo 1563479 1563771 := bstep (se 1 (by rfl) ⟨1172828, by rfl⟩ : syracuseStep 1563771 = 2345657) B2345657
theorem B11279513 : Blo 1563479 11279513 := bstep (se 2 (by rfl) ⟨4229817, by rfl⟩ : syracuseStep 11279513 = 8459635) B8459635
theorem B1563823 : Blo 1563479 1563823 := bstep (se 1 (by rfl) ⟨1172867, by rfl⟩ : syracuseStep 1563823 = 2345735) B2345735
theorem B1563847 : Blo 1563479 1563847 := bstep (se 1 (by rfl) ⟨1172885, by rfl⟩ : syracuseStep 1563847 = 2345771) B2345771
theorem B1563867 : Blo 1563479 1563867 := bstep (se 1 (by rfl) ⟨1172900, by rfl⟩ : syracuseStep 1563867 = 2345801) B2345801
theorem B24083729 : Blo 1563479 24083729 := bstep (se 2 (by rfl) ⟨9031398, by rfl⟩ : syracuseStep 24083729 = 18062797) B18062797
theorem B1563943 : Blo 1563479 1563943 := bstep (se 1 (by rfl) ⟨1172957, by rfl⟩ : syracuseStep 1563943 = 2345915) B2345915
theorem B1563983 : Blo 1563479 1563983 := bstep (se 1 (by rfl) ⟨1172987, by rfl⟩ : syracuseStep 1563983 = 2345975) B2345975
theorem B1563999 : Blo 1563479 1563999 := bstep (se 1 (by rfl) ⟨1172999, by rfl⟩ : syracuseStep 1563999 = 2345999) B2345999
theorem B5635433 : Blo 1563479 5635433 := bstep (se 2 (by rfl) ⟨2113287, by rfl⟩ : syracuseStep 5635433 = 4226575) B4226575
theorem B4455785 : Blo 1563479 4455785 := bstep (se 2 (by rfl) ⟨1670919, by rfl⟩ : syracuseStep 4455785 = 3341839) B3341839
theorem B1564027 : Blo 1563479 1564027 := bstep (se 1 (by rfl) ⟨1173020, by rfl⟩ : syracuseStep 1564027 = 2346041) B2346041
theorem B1564079 : Blo 1563479 1564079 := bstep (se 1 (by rfl) ⟨1173059, by rfl⟩ : syracuseStep 1564079 = 2346119) B2346119
theorem B1564103 : Blo 1563479 1564103 := bstep (se 1 (by rfl) ⟨1173077, by rfl⟩ : syracuseStep 1564103 = 2346155) B2346155
theorem B1564123 : Blo 1563479 1564123 := bstep (se 1 (by rfl) ⟨1173092, by rfl⟩ : syracuseStep 1564123 = 2346185) B2346185
theorem B1564199 : Blo 1563479 1564199 := bstep (se 1 (by rfl) ⟨1173149, by rfl⟩ : syracuseStep 1564199 = 2346299) B2346299
theorem B2506297 : Blo 1563479 2506297 := bstep (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) B1879723
theorem B1564239 : Blo 1563479 1564239 := bstep (se 1 (by rfl) ⟨1173179, by rfl⟩ : syracuseStep 1564239 = 2346359) B2346359
theorem B1564255 : Blo 1563479 1564255 := bstep (se 1 (by rfl) ⟨1173191, by rfl⟩ : syracuseStep 1564255 = 2346383) B2346383
theorem B1564283 : Blo 1563479 1564283 := bstep (se 1 (by rfl) ⟨1173212, by rfl⟩ : syracuseStep 1564283 = 2346425) B2346425
theorem B1564335 : Blo 1563479 1564335 := bstep (se 1 (by rfl) ⟨1173251, by rfl⟩ : syracuseStep 1564335 = 2346503) B2346503
theorem B1564359 : Blo 1563479 1564359 := bstep (se 1 (by rfl) ⟨1173269, by rfl⟩ : syracuseStep 1564359 = 2346539) B2346539
theorem B1564379 : Blo 1563479 1564379 := bstep (se 1 (by rfl) ⟨1173284, by rfl⟩ : syracuseStep 1564379 = 2346569) B2346569
theorem B11271901 : Blo 1563479 11271901 := bstep (se 3 (by rfl) ⟨2113481, by rfl⟩ : syracuseStep 11271901 = 4226963) B4226963
theorem B1564455 : Blo 1563479 1564455 := bstep (se 1 (by rfl) ⟨1173341, by rfl⟩ : syracuseStep 1564455 = 2346683) B2346683
theorem B7921475 : Blo 1563479 7921475 := bstep (se 1 (by rfl) ⟨5941106, by rfl⟩ : syracuseStep 7921475 = 11882213) B11882213
theorem B1564495 : Blo 1563479 1564495 := bstep (se 1 (by rfl) ⟨1173371, by rfl⟩ : syracuseStep 1564495 = 2346743) B2346743
theorem B1564511 : Blo 1563479 1564511 := bstep (se 1 (by rfl) ⟨1173383, by rfl⟩ : syracuseStep 1564511 = 2346767) B2346767
theorem B1564539 : Blo 1563479 1564539 := bstep (se 1 (by rfl) ⟨1173404, by rfl⟩ : syracuseStep 1564539 = 2346809) B2346809
theorem B3170191 : Blo 1563479 3170191 := bstep (se 1 (by rfl) ⟨2377643, by rfl⟩ : syracuseStep 3170191 = 4755287) B4755287
theorem B1564591 : Blo 1563479 1564591 := bstep (se 1 (by rfl) ⟨1173443, by rfl⟩ : syracuseStep 1564591 = 2346887) B2346887
theorem B2228143 : Blo 1563479 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B4456367 : Blo 1563479 4456367 := bstep (se 1 (by rfl) ⟨3342275, by rfl⟩ : syracuseStep 4456367 = 6684551) B6684551
theorem B1564615 : Blo 1563479 1564615 := bstep (se 1 (by rfl) ⟨1173461, by rfl⟩ : syracuseStep 1564615 = 2346923) B2346923
theorem B1564635 : Blo 1563479 1564635 := bstep (se 1 (by rfl) ⟨1173476, by rfl⟩ : syracuseStep 1564635 = 2346953) B2346953
theorem B8454145 : Blo 1563479 8454145 := bstep (se 2 (by rfl) ⟨3170304, by rfl⟩ : syracuseStep 8454145 = 6340609) B6340609
theorem B8912915 : Blo 1563479 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B1564959 : Blo 1563479 1564959 := bstep (se 1 (by rfl) ⟨1173719, by rfl⟩ : syracuseStep 1564959 = 2347439) B2347439
theorem B2638399 : Blo 1563479 2638399 := bstep (se 1 (by rfl) ⟨1978799, by rfl⟩ : syracuseStep 2638399 = 3957599) B3957599
theorem B2712475 : Blo 1563479 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B5080009 : Blo 1563479 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B8135777 : Blo 1563479 8135777 := bstep (se 2 (by rfl) ⟨3050916, by rfl⟩ : syracuseStep 8135777 = 6101833) B6101833
theorem B2639081 : Blo 1563479 2639081 := bstep (se 2 (by rfl) ⟨989655, by rfl⟩ : syracuseStep 2639081 = 1979311) B1979311
theorem B2639135 : Blo 1563479 2639135 := bstep (se 1 (by rfl) ⟨1979351, by rfl⟩ : syracuseStep 2639135 = 3958703) B3958703
theorem B3958055 : Blo 1563479 3958055 := bstep (se 1 (by rfl) ⟨2968541, by rfl⟩ : syracuseStep 3958055 = 5937083) B5937083
theorem B4711841 : Blo 1563479 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B8906375 : Blo 1563479 8906375 := bstep (se 1 (by rfl) ⟨6679781, by rfl⟩ : syracuseStep 8906375 = 13359563) B13359563
theorem B7915319 : Blo 1563479 7915319 := bstep (se 1 (by rfl) ⟨5936489, by rfl⟩ : syracuseStep 7915319 = 11872979) B11872979
theorem B11880269 : Blo 1563479 11880269 := bstep (se 3 (by rfl) ⟨2227550, by rfl⟩ : syracuseStep 11880269 = 4455101) B4455101
theorem B5277527 : Blo 1563479 5277527 := bstep (se 1 (by rfl) ⟨3958145, by rfl⟩ : syracuseStep 5277527 = 7916291) B7916291
theorem B6342637 : Blo 1563479 6342637 := bstep (se 3 (by rfl) ⟨1189244, by rfl⟩ : syracuseStep 6342637 = 2378489) B2378489
theorem B2345225 : Blo 1563479 2345225 := bstep (se 2 (by rfl) ⟨879459, by rfl⟩ : syracuseStep 2345225 = 1758919) B1758919
theorem B7915805 : Blo 1563479 7915805 := bstep (se 3 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 7915805 = 2968427) B2968427
theorem B2345327 : Blo 1563479 2345327 := bstep (se 1 (by rfl) ⟨1758995, by rfl⟩ : syracuseStep 2345327 = 3517991) B3517991
theorem B2345543 : Blo 1563479 2345543 := bstep (se 1 (by rfl) ⟨1759157, by rfl⟩ : syracuseStep 2345543 = 3518315) B3518315
theorem B2345579 : Blo 1563479 2345579 := bstep (se 1 (by rfl) ⟨1759184, by rfl⟩ : syracuseStep 2345579 = 3518369) B3518369
theorem B2640505 : Blo 1563479 2640505 := bstep (se 2 (by rfl) ⟨990189, by rfl⟩ : syracuseStep 2640505 = 1980379) B1980379
theorem B11274875 : Blo 1563479 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B2640559 : Blo 1563479 2640559 := bstep (se 1 (by rfl) ⟨1980419, by rfl⟩ : syracuseStep 2640559 = 3960839) B3960839
theorem B48163517 : Blo 1563479 48163517 := bstep (se 3 (by rfl) ⟨9030659, by rfl⟩ : syracuseStep 48163517 = 18061319) B18061319
theorem B6679235 : Blo 1563479 6679235 := bstep (se 1 (by rfl) ⟨5009426, by rfl⟩ : syracuseStep 6679235 = 10018853) B10018853
theorem B142846681 : Blo 1563479 142846681 := bstep (se 2 (by rfl) ⟨53567505, by rfl⟩ : syracuseStep 142846681 = 107135011) B107135011
theorem B3959543 : Blo 1563479 3959543 := bstep (se 1 (by rfl) ⟨2969657, by rfl⟩ : syracuseStep 3959543 = 5939315) B5939315
theorem B2345807 : Blo 1563479 2345807 := bstep (se 1 (by rfl) ⟨1759355, by rfl⟩ : syracuseStep 2345807 = 3518711) B3518711
theorem B5278607 : Blo 1563479 5278607 := bstep (se 1 (by rfl) ⟨3958955, by rfl⟩ : syracuseStep 5278607 = 7917911) B7917911
theorem B55692203 : Blo 1563479 55692203 := bstep (se 1 (by rfl) ⟨41769152, by rfl⟩ : syracuseStep 55692203 = 83538305) B83538305
theorem B3566567 : Blo 1563479 3566567 := bstep (se 1 (by rfl) ⟨2674925, by rfl⟩ : syracuseStep 3566567 = 5349851) B5349851
theorem B2346203 : Blo 1563479 2346203 := bstep (se 1 (by rfl) ⟨1759652, by rfl⟩ : syracuseStep 2346203 = 3519305) B3519305
theorem B8457539 : Blo 1563479 8457539 := bstep (se 1 (by rfl) ⟨6343154, by rfl⟩ : syracuseStep 8457539 = 12686309) B12686309
theorem B3960161 : Blo 1563479 3960161 := bstep (se 2 (by rfl) ⟨1485060, by rfl⟩ : syracuseStep 3960161 = 2970121) B2970121
theorem B2346377 : Blo 1563479 2346377 := bstep (se 2 (by rfl) ⟨879891, by rfl⟩ : syracuseStep 2346377 = 1759783) B1759783
theorem B3517883 : Blo 1563479 3517883 := bstep (se 1 (by rfl) ⟨2638412, by rfl⟩ : syracuseStep 3517883 = 5276825) B5276825
theorem B59436509 : Blo 1563479 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B2895353 : Blo 1563479 2895353 := bstep (se 2 (by rfl) ⟨1085757, by rfl⟩ : syracuseStep 2895353 = 2171515) B2171515
theorem B3518009 : Blo 1563479 3518009 := bstep (se 2 (by rfl) ⟨1319253, by rfl⟩ : syracuseStep 3518009 = 2638507) B2638507
theorem B2346731 : Blo 1563479 2346731 := bstep (se 1 (by rfl) ⟨1760048, by rfl⟩ : syracuseStep 2346731 = 3520097) B3520097
theorem B4345579 : Blo 1563479 4345579 := bstep (se 1 (by rfl) ⟨3259184, by rfl⟩ : syracuseStep 4345579 = 6518369) B6518369
theorem B2969399 : Blo 1563479 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B45109061 : Blo 1563479 45109061 := bstep (se 4 (by rfl) ⟨4228974, by rfl⟩ : syracuseStep 45109061 = 8457949) B8457949
theorem B2969551 : Blo 1563479 2969551 := bstep (se 1 (by rfl) ⟨2227163, by rfl⟩ : syracuseStep 2969551 = 4454327) B4454327
theorem B2346959 : Blo 1563479 2346959 := bstep (se 1 (by rfl) ⟨1760219, by rfl⟩ : syracuseStep 2346959 = 3520439) B3520439
theorem B1880015 : Blo 1563479 1880015 := bstep (se 1 (by rfl) ⟨1410011, by rfl⟩ : syracuseStep 1880015 = 2820023) B2820023
theorem B1129263119 : Blo 1563479 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B7917587 : Blo 1563479 7917587 := bstep (se 1 (by rfl) ⟨5938190, by rfl⟩ : syracuseStep 7917587 = 11876381) B11876381
theorem B5279849 : Blo 1563479 5279849 := bstep (se 2 (by rfl) ⟨1979943, by rfl⟩ : syracuseStep 5279849 = 3959887) B3959887
theorem B40087709 : Blo 1563479 40087709 := bstep (se 3 (by rfl) ⟨7516445, by rfl⟩ : syracuseStep 40087709 = 15032891) B15032891
theorem B11882699 : Blo 1563479 11882699 := bstep (se 1 (by rfl) ⟨8912024, by rfl⟩ : syracuseStep 11882699 = 17824049) B17824049
theorem B3518675 : Blo 1563479 3518675 := bstep (se 1 (by rfl) ⟨2639006, by rfl⟩ : syracuseStep 3518675 = 5278013) B5278013
theorem B13922563 : Blo 1563479 13922563 := bstep (se 1 (by rfl) ⟨10441922, by rfl⟩ : syracuseStep 13922563 = 20883845) B20883845
theorem B3518729 : Blo 1563479 3518729 := bstep (se 2 (by rfl) ⟨1319523, by rfl⟩ : syracuseStep 3518729 = 2639047) B2639047
theorem B2347355 : Blo 1563479 2347355 := bstep (se 1 (by rfl) ⟨1760516, by rfl⟩ : syracuseStep 2347355 = 3521033) B3521033
theorem B3518945 : Blo 1563479 3518945 := bstep (se 2 (by rfl) ⟨1319604, by rfl⟩ : syracuseStep 3518945 = 2639209) B2639209
theorem B5009939 : Blo 1563479 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B1978987 : Blo 1563479 1978987 := bstep (se 1 (by rfl) ⟨1484240, by rfl⟩ : syracuseStep 1978987 = 2968481) B2968481
theorem B3519251 : Blo 1563479 3519251 := bstep (se 1 (by rfl) ⟨2639438, by rfl⟩ : syracuseStep 3519251 = 5278877) B5278877
theorem B3756955 : Blo 1563479 3756955 := bstep (se 1 (by rfl) ⟨2817716, by rfl⟩ : syracuseStep 3756955 = 5635433) B5635433
theorem B2970523 : Blo 1563479 2970523 := bstep (se 1 (by rfl) ⟨2227892, by rfl⟩ : syracuseStep 2970523 = 4455785) B4455785
theorem B5280713 : Blo 1563479 5280713 := bstep (se 2 (by rfl) ⟨1980267, by rfl⟩ : syracuseStep 5280713 = 3960535) B3960535
theorem B15029201 : Blo 1563479 15029201 := bstep (se 2 (by rfl) ⟨5635950, by rfl⟩ : syracuseStep 15029201 = 11271901) B11271901
theorem B3519611 : Blo 1563479 3519611 := bstep (se 1 (by rfl) ⟨2639708, by rfl⟩ : syracuseStep 3519611 = 5279417) B5279417
theorem B13366397 : Blo 1563479 13366397 := bstep (se 3 (by rfl) ⟨2506199, by rfl⟩ : syracuseStep 13366397 = 5012399) B5012399
theorem B5280983 : Blo 1563479 5280983 := bstep (se 1 (by rfl) ⟨3960737, by rfl⟩ : syracuseStep 5280983 = 7921475) B7921475
theorem B2970857 : Blo 1563479 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B3519737 : Blo 1563479 3519737 := bstep (se 2 (by rfl) ⟨1319901, by rfl⟩ : syracuseStep 3519737 = 2639803) B2639803
theorem B2970911 : Blo 1563479 2970911 := bstep (se 1 (by rfl) ⟨2228183, by rfl⟩ : syracuseStep 2970911 = 4456367) B4456367
theorem B3519881 : Blo 1563479 3519881 := bstep (se 2 (by rfl) ⟨1319955, by rfl⟩ : syracuseStep 3519881 = 2639911) B2639911
theorem B3520007 : Blo 1563479 3520007 := bstep (se 1 (by rfl) ⟨2640005, by rfl⟩ : syracuseStep 3520007 = 5280011) B5280011
theorem B3520187 : Blo 1563479 3520187 := bstep (se 1 (by rfl) ⟨2640140, by rfl⟩ : syracuseStep 3520187 = 5280281) B5280281
theorem B30078701 : Blo 1563479 30078701 := bstep (se 3 (by rfl) ⟨5639756, by rfl⟩ : syracuseStep 30078701 = 11279513) B11279513
theorem B3520313 : Blo 1563479 3520313 := bstep (se 2 (by rfl) ⟨1320117, by rfl⟩ : syracuseStep 3520313 = 2640235) B2640235
theorem B1759207 : Blo 1563479 1759207 := bstep (se 1 (by rfl) ⟨1319405, by rfl⟩ : syracuseStep 1759207 = 2638811) B2638811
theorem B3758185 : Blo 1563479 3758185 := bstep (se 2 (by rfl) ⟨1409319, by rfl⟩ : syracuseStep 3758185 = 2818639) B2818639
theorem B22853963 : Blo 1563479 22853963 := bstep (se 1 (by rfl) ⟨17140472, by rfl⟩ : syracuseStep 22853963 = 34280945) B34280945
theorem B3340711 : Blo 1563479 3340711 := bstep (se 1 (by rfl) ⟨2505533, by rfl⟩ : syracuseStep 3340711 = 5011067) B5011067
theorem B3520943 : Blo 1563479 3520943 := bstep (se 1 (by rfl) ⟨2640707, by rfl⟩ : syracuseStep 3520943 = 5281415) B5281415
theorem B3520979 : Blo 1563479 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B13539899 : Blo 1563479 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B3521087 : Blo 1563479 3521087 := bstep (se 1 (by rfl) ⟨2640815, by rfl⟩ : syracuseStep 3521087 = 5281631) B5281631
theorem B2505323 : Blo 1563479 2505323 := bstep (se 1 (by rfl) ⟨1878992, by rfl⟩ : syracuseStep 2505323 = 3757985) B3757985
theorem B3521195 : Blo 1563479 3521195 := bstep (se 1 (by rfl) ⟨2640896, by rfl⟩ : syracuseStep 3521195 = 5281793) B5281793
theorem B7519043 : Blo 1563479 7519043 := bstep (se 1 (by rfl) ⟨5639282, by rfl⟩ : syracuseStep 7519043 = 11278565) B11278565
theorem B7920503 : Blo 1563479 7920503 := bstep (se 1 (by rfl) ⟨5940377, by rfl⟩ : syracuseStep 7920503 = 11880755) B11880755
theorem B1563547 : Blo 1563479 1563547 := bstep (se 1 (by rfl) ⟨1172660, by rfl⟩ : syracuseStep 1563547 = 2345321) B2345321
theorem B1563599 : Blo 1563479 1563599 := bstep (se 1 (by rfl) ⟨1172699, by rfl⟩ : syracuseStep 1563599 = 2345399) B2345399
theorem B1563623 : Blo 1563479 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B13360247 : Blo 1563479 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B3341531 : Blo 1563479 3341531 := bstep (se 1 (by rfl) ⟨2506148, by rfl⟩ : syracuseStep 3341531 = 5012297) B5012297
theorem B6683867 : Blo 1563479 6683867 := bstep (se 1 (by rfl) ⟨5012900, by rfl⟩ : syracuseStep 6683867 = 10025801) B10025801
theorem B1563935 : Blo 1563479 1563935 := bstep (se 1 (by rfl) ⟨1172951, by rfl⟩ : syracuseStep 1563935 = 2345903) B2345903
theorem B1563995 : Blo 1563479 1563995 := bstep (se 1 (by rfl) ⟨1172996, by rfl⟩ : syracuseStep 1563995 = 2345993) B2345993
theorem B1564015 : Blo 1563479 1564015 := bstep (se 1 (by rfl) ⟨1173011, by rfl⟩ : syracuseStep 1564015 = 2346023) B2346023
theorem B3341729 : Blo 1563479 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B1564071 : Blo 1563479 1564071 := bstep (se 1 (by rfl) ⟨1173053, by rfl⟩ : syracuseStep 1564071 = 2346107) B2346107
theorem B1564155 : Blo 1563479 1564155 := bstep (se 1 (by rfl) ⟨1173116, by rfl⟩ : syracuseStep 1564155 = 2346233) B2346233
theorem B16055819 : Blo 1563479 16055819 := bstep (se 1 (by rfl) ⟨12041864, by rfl⟩ : syracuseStep 16055819 = 24083729) B24083729
theorem B1564223 : Blo 1563479 1564223 := bstep (se 1 (by rfl) ⟨1173167, by rfl⟩ : syracuseStep 1564223 = 2346335) B2346335
theorem B1564231 : Blo 1563479 1564231 := bstep (se 1 (by rfl) ⟨1173173, by rfl⟩ : syracuseStep 1564231 = 2346347) B2346347
theorem B6020689 : Blo 1563479 6020689 := bstep (se 2 (by rfl) ⟨2257758, by rfl⟩ : syracuseStep 6020689 = 4515517) B4515517
theorem B7921313 : Blo 1563479 7921313 := bstep (se 2 (by rfl) ⟨2970492, by rfl⟩ : syracuseStep 7921313 = 5940985) B5940985
theorem B1564383 : Blo 1563479 1564383 := bstep (se 1 (by rfl) ⟨1173287, by rfl⟩ : syracuseStep 1564383 = 2346575) B2346575
theorem B1564463 : Blo 1563479 1564463 := bstep (se 1 (by rfl) ⟨1173347, by rfl⟩ : syracuseStep 1564463 = 2346695) B2346695
theorem B2506553 : Blo 1563479 2506553 := bstep (se 2 (by rfl) ⟨939957, by rfl⟩ : syracuseStep 2506553 = 1879915) B1879915
theorem B4226921 : Blo 1563479 4226921 := bstep (se 2 (by rfl) ⟨1585095, by rfl⟩ : syracuseStep 4226921 = 3170191) B3170191
theorem B9641857 : Blo 1563479 9641857 := bstep (se 2 (by rfl) ⟨3615696, by rfl⟩ : syracuseStep 9641857 = 7231393) B7231393
theorem B1564571 : Blo 1563479 1564571 := bstep (se 1 (by rfl) ⟨1173428, by rfl⟩ : syracuseStep 1564571 = 2346857) B2346857
theorem B1564623 : Blo 1563479 1564623 := bstep (se 1 (by rfl) ⟨1173467, by rfl⟩ : syracuseStep 1564623 = 2346935) B2346935
theorem B1564647 : Blo 1563479 1564647 := bstep (se 1 (by rfl) ⟨1173485, by rfl⟩ : syracuseStep 1564647 = 2346971) B2346971
theorem B11272193 : Blo 1563479 11272193 := bstep (se 2 (by rfl) ⟨4227072, by rfl⟩ : syracuseStep 11272193 = 8454145) B8454145
theorem B7921799 : Blo 1563479 7921799 := bstep (se 1 (by rfl) ⟨5941349, by rfl⟩ : syracuseStep 7921799 = 11882699) B11882699
theorem B1564903 : Blo 1563479 1564903 := bstep (se 1 (by rfl) ⟨1173677, by rfl⟩ : syracuseStep 1564903 = 2347355) B2347355
theorem B18563417 : Blo 1563479 18563417 := bstep (se 2 (by rfl) ⟨6961281, by rfl⟩ : syracuseStep 18563417 = 13922563) B13922563
theorem B7922285 : Blo 1563479 7922285 := bstep (se 3 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 7922285 = 2970857) B2970857
theorem B10019467 : Blo 1563479 10019467 := bstep (se 1 (by rfl) ⟨7514600, by rfl⟩ : syracuseStep 10019467 = 15029201) B15029201
theorem B5423851 : Blo 1563479 5423851 := bstep (se 1 (by rfl) ⟨4067888, by rfl⟩ : syracuseStep 5423851 = 8135777) B8135777
theorem B2638649 : Blo 1563479 2638649 := bstep (se 2 (by rfl) ⟨989493, by rfl⟩ : syracuseStep 2638649 = 1978987) B1978987
theorem B22553437 : Blo 1563479 22553437 := bstep (se 3 (by rfl) ⟨4228769, by rfl⟩ : syracuseStep 22553437 = 8457539) B8457539
theorem B2638703 : Blo 1563479 2638703 := bstep (se 1 (by rfl) ⟨1979027, by rfl⟩ : syracuseStep 2638703 = 3958055) B3958055
theorem B5276879 : Blo 1563479 5276879 := bstep (se 1 (by rfl) ⟨3957659, by rfl⟩ : syracuseStep 5276879 = 7915319) B7915319
theorem B5277203 : Blo 1563479 5277203 := bstep (se 1 (by rfl) ⟨3957902, by rfl⟩ : syracuseStep 5277203 = 7915805) B7915805
theorem B2639695 : Blo 1563479 2639695 := bstep (se 1 (by rfl) ⟨1979771, by rfl⟩ : syracuseStep 2639695 = 3959543) B3959543
theorem B2377711 : Blo 1563479 2377711 := bstep (se 1 (by rfl) ⟨1783283, by rfl⟩ : syracuseStep 2377711 = 3566567) B3566567
theorem B8906831 : Blo 1563479 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B2640107 : Blo 1563479 2640107 := bstep (se 1 (by rfl) ⟨1980080, by rfl⟩ : syracuseStep 2640107 = 3960161) B3960161
theorem B2345255 : Blo 1563479 2345255 := bstep (se 1 (by rfl) ⟨1758941, by rfl⟩ : syracuseStep 2345255 = 3517883) B3517883
theorem B5794105 : Blo 1563479 5794105 := bstep (se 2 (by rfl) ⟨2172789, by rfl⟩ : syracuseStep 5794105 = 4345579) B4345579
theorem B2345339 : Blo 1563479 2345339 := bstep (se 1 (by rfl) ⟨1759004, by rfl⟩ : syracuseStep 2345339 = 3518009) B3518009
theorem B12855809 : Blo 1563479 12855809 := bstep (se 2 (by rfl) ⟨4820928, by rfl⟩ : syracuseStep 12855809 = 9641857) B9641857
theorem B3959401 : Blo 1563479 3959401 := bstep (se 2 (by rfl) ⟨1484775, by rfl⟩ : syracuseStep 3959401 = 2969551) B2969551
theorem B2345609 : Blo 1563479 2345609 := bstep (se 2 (by rfl) ⟨879603, by rfl⟩ : syracuseStep 2345609 = 1759207) B1759207
theorem B8456849 : Blo 1563479 8456849 := bstep (se 2 (by rfl) ⟨3171318, by rfl⟩ : syracuseStep 8456849 = 6342637) B6342637
theorem B5278391 : Blo 1563479 5278391 := bstep (se 1 (by rfl) ⟨3958793, by rfl⟩ : syracuseStep 5278391 = 7917587) B7917587
theorem B5941943 : Blo 1563479 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B26725139 : Blo 1563479 26725139 := bstep (se 1 (by rfl) ⟨20043854, by rfl⟩ : syracuseStep 26725139 = 40087709) B40087709
theorem B2345783 : Blo 1563479 2345783 := bstep (se 1 (by rfl) ⟨1759337, by rfl⟩ : syracuseStep 2345783 = 3518675) B3518675
theorem B2345819 : Blo 1563479 2345819 := bstep (se 1 (by rfl) ⟨1759364, by rfl⟩ : syracuseStep 2345819 = 3518729) B3518729
theorem B2345963 : Blo 1563479 2345963 := bstep (se 1 (by rfl) ⟨1759472, by rfl⟩ : syracuseStep 2345963 = 3518945) B3518945
theorem B2346167 : Blo 1563479 2346167 := bstep (se 1 (by rfl) ⟨1759625, by rfl⟩ : syracuseStep 2346167 = 3519251) B3519251
theorem B2346407 : Blo 1563479 2346407 := bstep (se 1 (by rfl) ⟨1759805, by rfl⟩ : syracuseStep 2346407 = 3519611) B3519611
theorem B3517865 : Blo 1563479 3517865 := bstep (se 2 (by rfl) ⟨1319199, by rfl⟩ : syracuseStep 3517865 = 2638399) B2638399
theorem B2346491 : Blo 1563479 2346491 := bstep (se 1 (by rfl) ⟨1759868, by rfl⟩ : syracuseStep 2346491 = 3519737) B3519737
theorem B2346587 : Blo 1563479 2346587 := bstep (se 1 (by rfl) ⟨1759940, by rfl⟩ : syracuseStep 2346587 = 3519881) B3519881
theorem B3141227 : Blo 1563479 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B2346671 : Blo 1563479 2346671 := bstep (se 1 (by rfl) ⟨1760003, by rfl⟩ : syracuseStep 2346671 = 3520007) B3520007
theorem B2346791 : Blo 1563479 2346791 := bstep (se 1 (by rfl) ⟨1760093, by rfl⟩ : syracuseStep 2346791 = 3520187) B3520187
theorem B5009273 : Blo 1563479 5009273 := bstep (se 2 (by rfl) ⟨1878477, by rfl⟩ : syracuseStep 5009273 = 3756955) B3756955
theorem B3616633 : Blo 1563479 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B2346875 : Blo 1563479 2346875 := bstep (se 1 (by rfl) ⟨1760156, by rfl⟩ : syracuseStep 2346875 = 3520313) B3520313
theorem B3960697 : Blo 1563479 3960697 := bstep (se 2 (by rfl) ⟨1485261, by rfl⟩ : syracuseStep 3960697 = 2970523) B2970523
theorem B3518351 : Blo 1563479 3518351 := bstep (se 1 (by rfl) ⟨2638763, by rfl⟩ : syracuseStep 3518351 = 5277527) B5277527
theorem B2347295 : Blo 1563479 2347295 := bstep (se 1 (by rfl) ⟨1760471, by rfl⟩ : syracuseStep 2347295 = 3520943) B3520943
theorem B2347319 : Blo 1563479 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B2347391 : Blo 1563479 2347391 := bstep (se 1 (by rfl) ⟨1760543, by rfl⟩ : syracuseStep 2347391 = 3521087) B3521087
theorem B7516583 : Blo 1563479 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B2347463 : Blo 1563479 2347463 := bstep (se 1 (by rfl) ⟨1760597, by rfl⟩ : syracuseStep 2347463 = 3521195) B3521195
theorem B32109011 : Blo 1563479 32109011 := bstep (se 1 (by rfl) ⟨24081758, by rfl⟩ : syracuseStep 32109011 = 48163517) B48163517
theorem B4452823 : Blo 1563479 4452823 := bstep (se 1 (by rfl) ⟨3339617, by rfl⟩ : syracuseStep 4452823 = 6679235) B6679235
theorem B5280335 : Blo 1563479 5280335 := bstep (se 1 (by rfl) ⟨3960251, by rfl⟩ : syracuseStep 5280335 = 7920503) B7920503
theorem B3519071 : Blo 1563479 3519071 := bstep (se 1 (by rfl) ⟨2639303, by rfl⟩ : syracuseStep 3519071 = 5278607) B5278607
theorem B7918397 : Blo 1563479 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B1930235 : Blo 1563479 1930235 := bstep (se 1 (by rfl) ⟨1447676, by rfl⟩ : syracuseStep 1930235 = 2895353) B2895353
theorem B10703879 : Blo 1563479 10703879 := bstep (se 1 (by rfl) ⟨8027909, by rfl⟩ : syracuseStep 10703879 = 16055819) B16055819
theorem B5280875 : Blo 1563479 5280875 := bstep (se 1 (by rfl) ⟨3960656, by rfl⟩ : syracuseStep 5280875 = 7921313) B7921313
theorem B752842079 : Blo 1563479 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B3519899 : Blo 1563479 3519899 := bstep (se 1 (by rfl) ⟨2639924, by rfl⟩ : syracuseStep 3519899 = 5279849) B5279849
theorem B5010913 : Blo 1563479 5010913 := bstep (se 2 (by rfl) ⟨1879092, by rfl⟩ : syracuseStep 5010913 = 3758185) B3758185
theorem B3339959 : Blo 1563479 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B4454281 : Blo 1563479 4454281 := bstep (se 2 (by rfl) ⟨1670355, by rfl⟩ : syracuseStep 4454281 = 3340711) B3340711
theorem B8910749 : Blo 1563479 8910749 := bstep (se 3 (by rfl) ⟨1670765, by rfl⟩ : syracuseStep 8910749 = 3341531) B3341531
theorem B3520475 : Blo 1563479 3520475 := bstep (se 1 (by rfl) ⟨2640356, by rfl⟩ : syracuseStep 3520475 = 5280713) B5280713
theorem B8910931 : Blo 1563479 8910931 := bstep (se 1 (by rfl) ⟨6683198, by rfl⟩ : syracuseStep 8910931 = 13366397) B13366397
theorem B3520655 : Blo 1563479 3520655 := bstep (se 1 (by rfl) ⟨2640491, by rfl⟩ : syracuseStep 3520655 = 5280983) B5280983
theorem B1759387 : Blo 1563479 1759387 := bstep (se 1 (by rfl) ⟨1319540, by rfl⟩ : syracuseStep 1759387 = 2639081) B2639081
theorem B3520673 : Blo 1563479 3520673 := bstep (se 2 (by rfl) ⟨1320252, by rfl⟩ : syracuseStep 3520673 = 2640505) B2640505
theorem B1759423 : Blo 1563479 1759423 := bstep (se 1 (by rfl) ⟨1319567, by rfl⟩ : syracuseStep 1759423 = 2639135) B2639135
theorem B1980607 : Blo 1563479 1980607 := bstep (se 1 (by rfl) ⟨1485455, by rfl⟩ : syracuseStep 1980607 = 2970911) B2970911
theorem B3520745 : Blo 1563479 3520745 := bstep (se 2 (by rfl) ⟨1320279, by rfl⟩ : syracuseStep 3520745 = 2640559) B2640559
theorem B190462241 : Blo 1563479 190462241 := bstep (se 2 (by rfl) ⟨71423340, by rfl⟩ : syracuseStep 190462241 = 142846681) B142846681
theorem B5937583 : Blo 1563479 5937583 := bstep (se 1 (by rfl) ⟨4453187, by rfl⟩ : syracuseStep 5937583 = 8906375) B8906375
theorem B20052467 : Blo 1563479 20052467 := bstep (se 1 (by rfl) ⟨15039350, by rfl⟩ : syracuseStep 20052467 = 30078701) B30078701
theorem B7920179 : Blo 1563479 7920179 := bstep (se 1 (by rfl) ⟨5940134, by rfl⟩ : syracuseStep 7920179 = 11880269) B11880269
theorem B158497357 : Blo 1563479 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B6773345 : Blo 1563479 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B1563483 : Blo 1563479 1563483 := bstep (se 1 (by rfl) ⟨1172612, by rfl⟩ : syracuseStep 1563483 = 2345225) B2345225
theorem B15235975 : Blo 1563479 15235975 := bstep (se 1 (by rfl) ⟨11426981, by rfl⟩ : syracuseStep 15235975 = 22853963) B22853963
theorem B1563551 : Blo 1563479 1563551 := bstep (se 1 (by rfl) ⟨1172663, by rfl⟩ : syracuseStep 1563551 = 2345327) B2345327
theorem B9026599 : Blo 1563479 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B1563695 : Blo 1563479 1563695 := bstep (se 1 (by rfl) ⟨1172771, by rfl⟩ : syracuseStep 1563695 = 2345543) B2345543
theorem B1563719 : Blo 1563479 1563719 := bstep (se 1 (by rfl) ⟨1172789, by rfl⟩ : syracuseStep 1563719 = 2345579) B2345579
theorem B1670215 : Blo 1563479 1670215 := bstep (se 1 (by rfl) ⟨1252661, by rfl⟩ : syracuseStep 1670215 = 2505323) B2505323
theorem B5012695 : Blo 1563479 5012695 := bstep (se 1 (by rfl) ⟨3759521, by rfl⟩ : syracuseStep 5012695 = 7519043) B7519043
theorem B1563871 : Blo 1563479 1563871 := bstep (se 1 (by rfl) ⟨1172903, by rfl⟩ : syracuseStep 1563871 = 2345807) B2345807
theorem B8027585 : Blo 1563479 8027585 := bstep (se 2 (by rfl) ⟨3010344, by rfl⟩ : syracuseStep 8027585 = 6020689) B6020689
theorem B1564135 : Blo 1563479 1564135 := bstep (se 1 (by rfl) ⟨1173101, by rfl⟩ : syracuseStep 1564135 = 2346203) B2346203
theorem B4455911 : Blo 1563479 4455911 := bstep (se 1 (by rfl) ⟨3341933, by rfl⟩ : syracuseStep 4455911 = 6683867) B6683867
theorem B20053493 : Blo 1563479 20053493 := bstep (se 5 (by rfl) ⟨940007, by rfl⟩ : syracuseStep 20053493 = 1880015) B1880015
theorem B1564251 : Blo 1563479 1564251 := bstep (se 1 (by rfl) ⟨1173188, by rfl⟩ : syracuseStep 1564251 = 2346377) B2346377
theorem B2227819 : Blo 1563479 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B148512541 : Blo 1563479 148512541 := bstep (se 3 (by rfl) ⟨27846101, by rfl⟩ : syracuseStep 148512541 = 55692203) B55692203
theorem B1564487 : Blo 1563479 1564487 := bstep (se 1 (by rfl) ⟨1173365, by rfl⟩ : syracuseStep 1564487 = 2346731) B2346731
theorem B1671035 : Blo 1563479 1671035 := bstep (se 1 (by rfl) ⟨1253276, by rfl⟩ : syracuseStep 1671035 = 2506553) B2506553
theorem B30072707 : Blo 1563479 30072707 := bstep (se 1 (by rfl) ⟨22554530, by rfl⟩ : syracuseStep 30072707 = 45109061) B45109061
theorem B2817947 : Blo 1563479 2817947 := bstep (se 1 (by rfl) ⟨2113460, by rfl⟩ : syracuseStep 2817947 = 4226921) B4226921
theorem B1564639 : Blo 1563479 1564639 := bstep (se 1 (by rfl) ⟨1173479, by rfl⟩ : syracuseStep 1564639 = 2346959) B2346959
theorem B1564863 : Blo 1563479 1564863 := bstep (se 1 (by rfl) ⟨1173647, by rfl⟩ : syracuseStep 1564863 = 2347295) B2347295
theorem B1564879 : Blo 1563479 1564879 := bstep (se 1 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 1564879 = 2347319) B2347319
theorem B1564927 : Blo 1563479 1564927 := bstep (se 1 (by rfl) ⟨1173695, by rfl⟩ : syracuseStep 1564927 = 2347391) B2347391
theorem B1564975 : Blo 1563479 1564975 := bstep (se 1 (by rfl) ⟨1173731, by rfl⟩ : syracuseStep 1564975 = 2347463) B2347463
theorem B21406007 : Blo 1563479 21406007 := bstep (se 1 (by rfl) ⟨16054505, by rfl⟩ : syracuseStep 21406007 = 32109011) B32109011
theorem B7725473 : Blo 1563479 7725473 := bstep (se 2 (by rfl) ⟨2897052, by rfl⟩ : syracuseStep 7725473 = 5794105) B5794105
theorem B7135919 : Blo 1563479 7135919 := bstep (se 1 (by rfl) ⟨5351939, by rfl⟩ : syracuseStep 7135919 = 10703879) B10703879
theorem B211329809 : Blo 1563479 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B5940499 : Blo 1563479 5940499 := bstep (se 1 (by rfl) ⟨4455374, by rfl⟩ : syracuseStep 5940499 = 8910749) B8910749
theorem B12035465 : Blo 1563479 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B8570539 : Blo 1563479 8570539 := bstep (se 1 (by rfl) ⟨6427904, by rfl⟩ : syracuseStep 8570539 = 12855809) B12855809
theorem B4515563 : Blo 1563479 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B5637899 : Blo 1563479 5637899 := bstep (se 1 (by rfl) ⟨4228424, by rfl⟩ : syracuseStep 5637899 = 8456849) B8456849
theorem B8906557 : Blo 1563479 8906557 := bstep (se 3 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 8906557 = 3339959) B3339959
theorem B2345243 : Blo 1563479 2345243 := bstep (se 1 (by rfl) ⟨1758932, by rfl⟩ : syracuseStep 2345243 = 3517865) B3517865
theorem B5351723 : Blo 1563479 5351723 := bstep (se 1 (by rfl) ⟨4013792, by rfl⟩ : syracuseStep 5351723 = 8027585) B8027585
theorem B7514525 : Blo 1563479 7514525 := bstep (se 3 (by rfl) ⟨1408973, by rfl⟩ : syracuseStep 7514525 = 2817947) B2817947
theorem B20048471 : Blo 1563479 20048471 := bstep (se 1 (by rfl) ⟨15036353, by rfl⟩ : syracuseStep 20048471 = 30072707) B30072707
theorem B2345567 : Blo 1563479 2345567 := bstep (se 1 (by rfl) ⟨1759175, by rfl⟩ : syracuseStep 2345567 = 3518351) B3518351
theorem B5147293 : Blo 1563479 5147293 := bstep (se 3 (by rfl) ⟨965117, by rfl⟩ : syracuseStep 5147293 = 1930235) B1930235
theorem B7514795 : Blo 1563479 7514795 := bstep (se 1 (by rfl) ⟨5636096, by rfl⟩ : syracuseStep 7514795 = 11272193) B11272193
theorem B11881241 : Blo 1563479 11881241 := bstep (se 2 (by rfl) ⟨4455465, by rfl⟩ : syracuseStep 11881241 = 8910931) B8910931
theorem B2345849 : Blo 1563479 2345849 := bstep (se 2 (by rfl) ⟨879693, by rfl⟩ : syracuseStep 2345849 = 1759387) B1759387
theorem B2345897 : Blo 1563479 2345897 := bstep (se 2 (by rfl) ⟨879711, by rfl⟩ : syracuseStep 2345897 = 1759423) B1759423
theorem B2640809 : Blo 1563479 2640809 := bstep (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) B1980607
theorem B2346047 : Blo 1563479 2346047 := bstep (se 1 (by rfl) ⟨1759535, by rfl⟩ : syracuseStep 2346047 = 3519071) B3519071
theorem B5278931 : Blo 1563479 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B7916777 : Blo 1563479 7916777 := bstep (se 2 (by rfl) ⟨2968791, by rfl⟩ : syracuseStep 7916777 = 5937583) B5937583
theorem B3517919 : Blo 1563479 3517919 := bstep (se 1 (by rfl) ⟨2638439, by rfl⟩ : syracuseStep 3517919 = 5276879) B5276879
theorem B5279201 : Blo 1563479 5279201 := bstep (se 2 (by rfl) ⟨1979700, by rfl⟩ : syracuseStep 5279201 = 3959401) B3959401
theorem B501894719 : Blo 1563479 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B2346599 : Blo 1563479 2346599 := bstep (se 1 (by rfl) ⟨1759949, by rfl⟩ : syracuseStep 2346599 = 3519899) B3519899
theorem B3518135 : Blo 1563479 3518135 := bstep (se 1 (by rfl) ⟨2638601, by rfl⟩ : syracuseStep 3518135 = 5277203) B5277203
theorem B2346983 : Blo 1563479 2346983 := bstep (se 1 (by rfl) ⟨1760237, by rfl⟩ : syracuseStep 2346983 = 3520475) B3520475
theorem B2347103 : Blo 1563479 2347103 := bstep (se 1 (by rfl) ⟨1760327, by rfl⟩ : syracuseStep 2347103 = 3520655) B3520655
theorem B2347115 : Blo 1563479 2347115 := bstep (se 1 (by rfl) ⟨1760336, by rfl⟩ : syracuseStep 2347115 = 3520673) B3520673
theorem B2347163 : Blo 1563479 2347163 := bstep (se 1 (by rfl) ⟨1760372, by rfl⟩ : syracuseStep 2347163 = 3520745) B3520745
theorem B8376605 : Blo 1563479 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B5280119 : Blo 1563479 5280119 := bstep (se 1 (by rfl) ⟨3960089, by rfl⟩ : syracuseStep 5280119 = 7920179) B7920179
theorem B3518927 : Blo 1563479 3518927 := bstep (se 1 (by rfl) ⟨2639195, by rfl⟩ : syracuseStep 3518927 = 5278391) B5278391
theorem B3961295 : Blo 1563479 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B6681217 : Blo 1563479 6681217 := bstep (se 2 (by rfl) ⟨2505456, by rfl⟩ : syracuseStep 6681217 = 5010913) B5010913
theorem B19288709 : Blo 1563479 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B2970425 : Blo 1563479 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B2970607 : Blo 1563479 2970607 := bstep (se 1 (by rfl) ⟨2227955, by rfl⟩ : syracuseStep 2970607 = 4455911) B4455911
theorem B3519593 : Blo 1563479 3519593 := bstep (se 2 (by rfl) ⟨1319847, by rfl⟩ : syracuseStep 3519593 = 2639695) B2639695
theorem B5280929 : Blo 1563479 5280929 := bstep (se 2 (by rfl) ⟨1980348, by rfl⟩ : syracuseStep 5280929 = 3960697) B3960697
theorem B3339515 : Blo 1563479 3339515 := bstep (se 1 (by rfl) ⟨2504636, by rfl⟩ : syracuseStep 3339515 = 5009273) B5009273
theorem B5281199 : Blo 1563479 5281199 := bstep (se 1 (by rfl) ⟨3960899, by rfl⟩ : syracuseStep 5281199 = 7921799) B7921799
theorem B12375611 : Blo 1563479 12375611 := bstep (se 1 (by rfl) ⟨9281708, by rfl⟩ : syracuseStep 12375611 = 18563417) B18563417
theorem B5011055 : Blo 1563479 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B3520223 : Blo 1563479 3520223 := bstep (se 1 (by rfl) ⟨2640167, by rfl⟩ : syracuseStep 3520223 = 5280335) B5280335
theorem B5281523 : Blo 1563479 5281523 := bstep (se 1 (by rfl) ⟨3961142, by rfl⟩ : syracuseStep 5281523 = 7922285) B7922285
theorem B1759099 : Blo 1563479 1759099 := bstep (se 1 (by rfl) ⟨1319324, by rfl⟩ : syracuseStep 1759099 = 2638649) B2638649
theorem B1759135 : Blo 1563479 1759135 := bstep (se 1 (by rfl) ⟨1319351, by rfl⟩ : syracuseStep 1759135 = 2638703) B2638703
theorem B5937097 : Blo 1563479 5937097 := bstep (se 2 (by rfl) ⟨2226411, by rfl⟩ : syracuseStep 5937097 = 4452823) B4452823
theorem B3520583 : Blo 1563479 3520583 := bstep (se 1 (by rfl) ⟨2640437, by rfl⟩ : syracuseStep 3520583 = 5280875) B5280875
theorem B13359289 : Blo 1563479 13359289 := bstep (se 2 (by rfl) ⟨5009733, by rfl⟩ : syracuseStep 13359289 = 10019467) B10019467
theorem B7231801 : Blo 1563479 7231801 := bstep (se 2 (by rfl) ⟨2711925, by rfl⟩ : syracuseStep 7231801 = 5423851) B5423851
theorem B30071249 : Blo 1563479 30071249 := bstep (se 2 (by rfl) ⟨11276718, by rfl⟩ : syracuseStep 30071249 = 22553437) B22553437
theorem B20314633 : Blo 1563479 20314633 := bstep (se 2 (by rfl) ⟨7617987, by rfl⟩ : syracuseStep 20314633 = 15235975) B15235975
theorem B5937887 : Blo 1563479 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B2226953 : Blo 1563479 2226953 := bstep (se 2 (by rfl) ⟨835107, by rfl⟩ : syracuseStep 2226953 = 1670215) B1670215
theorem B1760071 : Blo 1563479 1760071 := bstep (se 1 (by rfl) ⟨1320053, by rfl⟩ : syracuseStep 1760071 = 2640107) B2640107
theorem B126974827 : Blo 1563479 126974827 := bstep (se 1 (by rfl) ⟨95231120, by rfl⟩ : syracuseStep 126974827 = 190462241) B190462241
theorem B1563503 : Blo 1563479 1563503 := bstep (se 1 (by rfl) ⟨1172627, by rfl⟩ : syracuseStep 1563503 = 2345255) B2345255
theorem B1563559 : Blo 1563479 1563559 := bstep (se 1 (by rfl) ⟨1172669, by rfl⟩ : syracuseStep 1563559 = 2345339) B2345339
theorem B6683593 : Blo 1563479 6683593 := bstep (se 2 (by rfl) ⟨2506347, by rfl⟩ : syracuseStep 6683593 = 5012695) B5012695
theorem B13368311 : Blo 1563479 13368311 := bstep (se 1 (by rfl) ⟨10026233, by rfl⟩ : syracuseStep 13368311 = 20052467) B20052467
theorem B1563739 : Blo 1563479 1563739 := bstep (se 1 (by rfl) ⟨1172804, by rfl⟩ : syracuseStep 1563739 = 2345609) B2345609
theorem B17816759 : Blo 1563479 17816759 := bstep (se 1 (by rfl) ⟨13362569, by rfl⟩ : syracuseStep 17816759 = 26725139) B26725139
theorem B1563855 : Blo 1563479 1563855 := bstep (se 1 (by rfl) ⟨1172891, by rfl⟩ : syracuseStep 1563855 = 2345783) B2345783
theorem B1563879 : Blo 1563479 1563879 := bstep (se 1 (by rfl) ⟨1172909, by rfl⟩ : syracuseStep 1563879 = 2345819) B2345819
theorem B1563975 : Blo 1563479 1563975 := bstep (se 1 (by rfl) ⟨1172981, by rfl⟩ : syracuseStep 1563975 = 2345963) B2345963
theorem B1564111 : Blo 1563479 1564111 := bstep (se 1 (by rfl) ⟨1173083, by rfl⟩ : syracuseStep 1564111 = 2346167) B2346167
theorem B1564271 : Blo 1563479 1564271 := bstep (se 1 (by rfl) ⟨1173203, by rfl⟩ : syracuseStep 1564271 = 2346407) B2346407
theorem B4456093 : Blo 1563479 4456093 := bstep (se 3 (by rfl) ⟨835517, by rfl⟩ : syracuseStep 4456093 = 1671035) B1671035
theorem B13368995 : Blo 1563479 13368995 := bstep (se 1 (by rfl) ⟨10026746, by rfl⟩ : syracuseStep 13368995 = 20053493) B20053493
theorem B1564327 : Blo 1563479 1564327 := bstep (se 1 (by rfl) ⟨1173245, by rfl⟩ : syracuseStep 1564327 = 2346491) B2346491
theorem B198016721 : Blo 1563479 198016721 := bstep (se 2 (by rfl) ⟨74256270, by rfl⟩ : syracuseStep 198016721 = 148512541) B148512541
theorem B1564391 : Blo 1563479 1564391 := bstep (se 1 (by rfl) ⟨1173293, by rfl⟩ : syracuseStep 1564391 = 2346587) B2346587
theorem B1564447 : Blo 1563479 1564447 := bstep (se 1 (by rfl) ⟨1173335, by rfl⟩ : syracuseStep 1564447 = 2346671) B2346671
theorem B5939041 : Blo 1563479 5939041 := bstep (se 2 (by rfl) ⟨2227140, by rfl⟩ : syracuseStep 5939041 = 4454281) B4454281
theorem B1564527 : Blo 1563479 1564527 := bstep (se 1 (by rfl) ⟨1173395, by rfl⟩ : syracuseStep 1564527 = 2346791) B2346791
theorem B1564583 : Blo 1563479 1564583 := bstep (se 1 (by rfl) ⟨1173437, by rfl⟩ : syracuseStep 1564583 = 2346875) B2346875
theorem B3170281 : Blo 1563479 3170281 := bstep (se 2 (by rfl) ⟨1188855, by rfl⟩ : syracuseStep 3170281 = 2377711) B2377711
theorem B1564735 : Blo 1563479 1564735 := bstep (se 1 (by rfl) ⟨1173551, by rfl⟩ : syracuseStep 1564735 = 2347103) B2347103
theorem B1564743 : Blo 1563479 1564743 := bstep (se 1 (by rfl) ⟨1173557, by rfl⟩ : syracuseStep 1564743 = 2347115) B2347115
theorem B1564775 : Blo 1563479 1564775 := bstep (se 1 (by rfl) ⟨1173581, by rfl⟩ : syracuseStep 1564775 = 2347163) B2347163
theorem B14270671 : Blo 1563479 14270671 := bstep (se 1 (by rfl) ⟨10703003, by rfl⟩ : syracuseStep 14270671 = 21406007) B21406007
theorem B9642401 : Blo 1563479 9642401 := bstep (se 2 (by rfl) ⟨3615900, by rfl⟩ : syracuseStep 9642401 = 7231801) B7231801
theorem B140886539 : Blo 1563479 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B8905373 : Blo 1563479 8905373 := bstep (se 3 (by rfl) ⟨1669757, by rfl⟩ : syracuseStep 8905373 = 3339515) B3339515
theorem B8250407 : Blo 1563479 8250407 := bstep (se 1 (by rfl) ⟨6187805, by rfl⟩ : syracuseStep 8250407 = 12375611) B12375611
theorem B20047499 : Blo 1563479 20047499 := bstep (se 1 (by rfl) ⟨15035624, by rfl⟩ : syracuseStep 20047499 = 30071249) B30071249
theorem B3958591 : Blo 1563479 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B5277851 : Blo 1563479 5277851 := bstep (se 1 (by rfl) ⟨3958388, by rfl⟩ : syracuseStep 5277851 = 7916777) B7916777
theorem B5941457 : Blo 1563479 5941457 := bstep (se 2 (by rfl) ⟨2228046, by rfl⟩ : syracuseStep 5941457 = 4456093) B4456093
theorem B2345279 : Blo 1563479 2345279 := bstep (se 1 (by rfl) ⟨1758959, by rfl⟩ : syracuseStep 2345279 = 3517919) B3517919
theorem B334596479 : Blo 1563479 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B2345423 : Blo 1563479 2345423 := bstep (se 1 (by rfl) ⟨1759067, by rfl⟩ : syracuseStep 2345423 = 3518135) B3518135
theorem B2345465 : Blo 1563479 2345465 := bstep (se 2 (by rfl) ⟨879549, by rfl⟩ : syracuseStep 2345465 = 1759099) B1759099
theorem B2345513 : Blo 1563479 2345513 := bstep (se 2 (by rfl) ⟨879567, by rfl⟩ : syracuseStep 2345513 = 1759135) B1759135
theorem B7916129 : Blo 1563479 7916129 := bstep (se 2 (by rfl) ⟨2968548, by rfl⟩ : syracuseStep 7916129 = 5937097) B5937097
theorem B17812385 : Blo 1563479 17812385 := bstep (se 2 (by rfl) ⟨6679644, by rfl⟩ : syracuseStep 17812385 = 13359289) B13359289
theorem B2345951 : Blo 1563479 2345951 := bstep (se 1 (by rfl) ⟨1759463, by rfl⟩ : syracuseStep 2345951 = 3518927) B3518927
theorem B2640863 : Blo 1563479 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B27086177 : Blo 1563479 27086177 := bstep (se 2 (by rfl) ⟨10157316, by rfl⟩ : syracuseStep 27086177 = 20314633) B20314633
theorem B2346395 : Blo 1563479 2346395 := bstep (se 1 (by rfl) ⟨1759796, by rfl⟩ : syracuseStep 2346395 = 3519593) B3519593
theorem B8908289 : Blo 1563479 8908289 := bstep (se 2 (by rfl) ⟨3340608, by rfl⟩ : syracuseStep 8908289 = 6681217) B6681217
theorem B8023643 : Blo 1563479 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B2346761 : Blo 1563479 2346761 := bstep (se 2 (by rfl) ⟨880035, by rfl⟩ : syracuseStep 2346761 = 1760071) B1760071
theorem B169299769 : Blo 1563479 169299769 := bstep (se 2 (by rfl) ⟨63487413, by rfl⟩ : syracuseStep 169299769 = 126974827) B126974827
theorem B2346815 : Blo 1563479 2346815 := bstep (se 1 (by rfl) ⟨1760111, by rfl⟩ : syracuseStep 2346815 = 3520223) B3520223
theorem B3010375 : Blo 1563479 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B3960809 : Blo 1563479 3960809 := bstep (se 2 (by rfl) ⟨1485303, by rfl⟩ : syracuseStep 3960809 = 2970607) B2970607
theorem B2347055 : Blo 1563479 2347055 := bstep (se 1 (by rfl) ⟨1760291, by rfl⟩ : syracuseStep 2347055 = 3520583) B3520583
theorem B3567815 : Blo 1563479 3567815 := bstep (se 1 (by rfl) ⟨2675861, by rfl⟩ : syracuseStep 3567815 = 5351723) B5351723
theorem B5009683 : Blo 1563479 5009683 := bstep (se 1 (by rfl) ⟨3757262, by rfl⟩ : syracuseStep 5009683 = 7514525) B7514525
theorem B13365647 : Blo 1563479 13365647 := bstep (se 1 (by rfl) ⟨10024235, by rfl⟩ : syracuseStep 13365647 = 20048471) B20048471
theorem B5009863 : Blo 1563479 5009863 := bstep (se 1 (by rfl) ⟨3757397, by rfl⟩ : syracuseStep 5009863 = 7514795) B7514795
theorem B76116469 : Blo 1563479 76116469 := bstep (se 5 (by rfl) ⟨3567959, by rfl⟩ : syracuseStep 76116469 = 7135919) B7135919
theorem B3519287 : Blo 1563479 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B3519467 : Blo 1563479 3519467 := bstep (se 1 (by rfl) ⟨2639600, by rfl⟩ : syracuseStep 3519467 = 5279201) B5279201
theorem B11875409 : Blo 1563479 11875409 := bstep (se 2 (by rfl) ⟨4453278, by rfl⟩ : syracuseStep 11875409 = 8906557) B8906557
theorem B7918721 : Blo 1563479 7918721 := bstep (se 2 (by rfl) ⟨2969520, by rfl⟩ : syracuseStep 7918721 = 5939041) B5939041
theorem B132011147 : Blo 1563479 132011147 := bstep (se 1 (by rfl) ⟨99008360, by rfl⟩ : syracuseStep 132011147 = 198016721) B198016721
theorem B5584403 : Blo 1563479 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B3520079 : Blo 1563479 3520079 := bstep (se 1 (by rfl) ⟨2640059, by rfl⟩ : syracuseStep 3520079 = 5280119) B5280119
theorem B5150315 : Blo 1563479 5150315 := bstep (se 1 (by rfl) ⟨3862736, by rfl⟩ : syracuseStep 5150315 = 7725473) B7725473
theorem B12859139 : Blo 1563479 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B1980283 : Blo 1563479 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B3520619 : Blo 1563479 3520619 := bstep (se 1 (by rfl) ⟨2640464, by rfl⟩ : syracuseStep 3520619 = 5280929) B5280929
theorem B6863057 : Blo 1563479 6863057 := bstep (se 2 (by rfl) ⟨2573646, by rfl⟩ : syracuseStep 6863057 = 5147293) B5147293
theorem B45709541 : Blo 1563479 45709541 := bstep (se 4 (by rfl) ⟨4285269, by rfl⟩ : syracuseStep 45709541 = 8570539) B8570539
theorem B3520799 : Blo 1563479 3520799 := bstep (se 1 (by rfl) ⟨2640599, by rfl⟩ : syracuseStep 3520799 = 5281199) B5281199
theorem B3340703 : Blo 1563479 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B3521015 : Blo 1563479 3521015 := bstep (se 1 (by rfl) ⟨2640761, by rfl⟩ : syracuseStep 3521015 = 5281523) B5281523
theorem B3758599 : Blo 1563479 3758599 := bstep (se 1 (by rfl) ⟨2818949, by rfl⟩ : syracuseStep 3758599 = 5637899) B5637899
theorem B8911457 : Blo 1563479 8911457 := bstep (se 2 (by rfl) ⟨3341796, by rfl⟩ : syracuseStep 8911457 = 6683593) B6683593
theorem B1563495 : Blo 1563479 1563495 := bstep (se 1 (by rfl) ⟨1172621, by rfl⟩ : syracuseStep 1563495 = 2345243) B2345243
theorem B7920665 : Blo 1563479 7920665 := bstep (se 2 (by rfl) ⟨2970249, by rfl⟩ : syracuseStep 7920665 = 5940499) B5940499
theorem B1563711 : Blo 1563479 1563711 := bstep (se 1 (by rfl) ⟨1172783, by rfl⟩ : syracuseStep 1563711 = 2345567) B2345567
theorem B7920827 : Blo 1563479 7920827 := bstep (se 1 (by rfl) ⟨5940620, by rfl⟩ : syracuseStep 7920827 = 11881241) B11881241
theorem B1563899 : Blo 1563479 1563899 := bstep (se 1 (by rfl) ⟨1172924, by rfl⟩ : syracuseStep 1563899 = 2345849) B2345849
theorem B1563931 : Blo 1563479 1563931 := bstep (se 1 (by rfl) ⟨1172948, by rfl⟩ : syracuseStep 1563931 = 2345897) B2345897
theorem B1760539 : Blo 1563479 1760539 := bstep (se 1 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 1760539 = 2640809) B2640809
theorem B8912207 : Blo 1563479 8912207 := bstep (se 1 (by rfl) ⟨6684155, by rfl⟩ : syracuseStep 8912207 = 13368311) B13368311
theorem B5938541 : Blo 1563479 5938541 := bstep (se 3 (by rfl) ⟨1113476, by rfl⟩ : syracuseStep 5938541 = 2226953) B2226953
theorem B1564031 : Blo 1563479 1564031 := bstep (se 1 (by rfl) ⟨1173023, by rfl⟩ : syracuseStep 1564031 = 2346047) B2346047
theorem B11877839 : Blo 1563479 11877839 := bstep (se 1 (by rfl) ⟨8908379, by rfl⟩ : syracuseStep 11877839 = 17816759) B17816759
theorem B1564399 : Blo 1563479 1564399 := bstep (se 1 (by rfl) ⟨1173299, by rfl⟩ : syracuseStep 1564399 = 2346599) B2346599
theorem B8912663 : Blo 1563479 8912663 := bstep (se 1 (by rfl) ⟨6684497, by rfl⟩ : syracuseStep 8912663 = 13368995) B13368995
theorem B4227041 : Blo 1563479 4227041 := bstep (se 2 (by rfl) ⟨1585140, by rfl⟩ : syracuseStep 4227041 = 3170281) B3170281
theorem B1564655 : Blo 1563479 1564655 := bstep (se 1 (by rfl) ⟨1173491, by rfl⟩ : syracuseStep 1564655 = 2346983) B2346983
theorem B1564703 : Blo 1563479 1564703 := bstep (se 1 (by rfl) ⟨1173527, by rfl⟩ : syracuseStep 1564703 = 2347055) B2347055
theorem B88007431 : Blo 1563479 88007431 := bstep (se 1 (by rfl) ⟨66005573, by rfl⟩ : syracuseStep 88007431 = 132011147) B132011147
theorem B892257277 : Blo 1563479 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B5277419 : Blo 1563479 5277419 := bstep (se 1 (by rfl) ⟨3958064, by rfl⟩ : syracuseStep 5277419 = 7916129) B7916129
theorem B5940971 : Blo 1563479 5940971 := bstep (se 1 (by rfl) ⟨4455728, by rfl⟩ : syracuseStep 5940971 = 8911457) B8911457
theorem B5941471 : Blo 1563479 5941471 := bstep (se 1 (by rfl) ⟨4456103, by rfl⟩ : syracuseStep 5941471 = 8912207) B8912207
theorem B18057451 : Blo 1563479 18057451 := bstep (se 1 (by rfl) ⟨13543088, by rfl⟩ : syracuseStep 18057451 = 27086177) B27086177
theorem B3959027 : Blo 1563479 3959027 := bstep (se 1 (by rfl) ⟨2969270, by rfl⟩ : syracuseStep 3959027 = 5938541) B5938541
theorem B225733025 : Blo 1563479 225733025 := bstep (se 2 (by rfl) ⟨84649884, by rfl⟩ : syracuseStep 225733025 = 169299769) B169299769
theorem B5278121 : Blo 1563479 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B2640377 : Blo 1563479 2640377 := bstep (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) B1980283
theorem B5941775 : Blo 1563479 5941775 := bstep (se 1 (by rfl) ⟨4456331, by rfl⟩ : syracuseStep 5941775 = 8912663) B8912663
theorem B2640539 : Blo 1563479 2640539 := bstep (se 1 (by rfl) ⟨1980404, by rfl⟩ : syracuseStep 2640539 = 3960809) B3960809
theorem B2378543 : Blo 1563479 2378543 := bstep (se 1 (by rfl) ⟨1783907, by rfl⟩ : syracuseStep 2378543 = 3567815) B3567815
theorem B93924359 : Blo 1563479 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B6679577 : Blo 1563479 6679577 := bstep (se 2 (by rfl) ⟨2504841, by rfl⟩ : syracuseStep 6679577 = 5009683) B5009683
theorem B2346191 : Blo 1563479 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B6679817 : Blo 1563479 6679817 := bstep (se 2 (by rfl) ⟨2504931, by rfl⟩ : syracuseStep 6679817 = 5009863) B5009863
theorem B2346311 : Blo 1563479 2346311 := bstep (se 1 (by rfl) ⟨1759733, by rfl⟩ : syracuseStep 2346311 = 3519467) B3519467
theorem B5500271 : Blo 1563479 5500271 := bstep (se 1 (by rfl) ⟨4125203, by rfl⟩ : syracuseStep 5500271 = 8250407) B8250407
theorem B7916939 : Blo 1563479 7916939 := bstep (se 1 (by rfl) ⟨5937704, by rfl⟩ : syracuseStep 7916939 = 11875409) B11875409
theorem B5279147 : Blo 1563479 5279147 := bstep (se 1 (by rfl) ⟨3959360, by rfl⟩ : syracuseStep 5279147 = 7918721) B7918721
theorem B3722935 : Blo 1563479 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B2346719 : Blo 1563479 2346719 := bstep (se 1 (by rfl) ⟨1760039, by rfl⟩ : syracuseStep 2346719 = 3520079) B3520079
theorem B8908541 : Blo 1563479 8908541 := bstep (se 3 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 8908541 = 3340703) B3340703
theorem B13364999 : Blo 1563479 13364999 := bstep (se 1 (by rfl) ⟨10023749, by rfl⟩ : syracuseStep 13364999 = 20047499) B20047499
theorem B8572759 : Blo 1563479 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B2347079 : Blo 1563479 2347079 := bstep (se 1 (by rfl) ⟨1760309, by rfl⟩ : syracuseStep 2347079 = 3520619) B3520619
theorem B3518567 : Blo 1563479 3518567 := bstep (se 1 (by rfl) ⟨2638925, by rfl⟩ : syracuseStep 3518567 = 5277851) B5277851
theorem B4575371 : Blo 1563479 4575371 := bstep (se 1 (by rfl) ⟨3431528, by rfl⟩ : syracuseStep 4575371 = 6863057) B6863057
theorem B3960971 : Blo 1563479 3960971 := bstep (se 1 (by rfl) ⟨2970728, by rfl⟩ : syracuseStep 3960971 = 5941457) B5941457
theorem B2347199 : Blo 1563479 2347199 := bstep (se 1 (by rfl) ⟨1760399, by rfl⟩ : syracuseStep 2347199 = 3520799) B3520799
theorem B13734173 : Blo 1563479 13734173 := bstep (se 3 (by rfl) ⟨2575157, by rfl⟩ : syracuseStep 13734173 = 5150315) B5150315
theorem B2347343 : Blo 1563479 2347343 := bstep (se 1 (by rfl) ⟨1760507, by rfl⟩ : syracuseStep 2347343 = 3521015) B3521015
theorem B2347385 : Blo 1563479 2347385 := bstep (se 2 (by rfl) ⟨880269, by rfl⟩ : syracuseStep 2347385 = 1760539) B1760539
theorem B11874923 : Blo 1563479 11874923 := bstep (se 1 (by rfl) ⟨8906192, by rfl⟩ : syracuseStep 11874923 = 17812385) B17812385
theorem B5280443 : Blo 1563479 5280443 := bstep (se 1 (by rfl) ⟨3960332, by rfl⟩ : syracuseStep 5280443 = 7920665) B7920665
theorem B5280551 : Blo 1563479 5280551 := bstep (se 1 (by rfl) ⟨3960413, by rfl⟩ : syracuseStep 5280551 = 7920827) B7920827
theorem B7918559 : Blo 1563479 7918559 := bstep (se 1 (by rfl) ⟨5938919, by rfl⟩ : syracuseStep 7918559 = 11877839) B11877839
theorem B8910431 : Blo 1563479 8910431 := bstep (se 1 (by rfl) ⟨6682823, by rfl⟩ : syracuseStep 8910431 = 13365647) B13365647
theorem B19027561 : Blo 1563479 19027561 := bstep (se 2 (by rfl) ⟨7135335, by rfl⟩ : syracuseStep 19027561 = 14270671) B14270671
theorem B6428267 : Blo 1563479 6428267 := bstep (se 1 (by rfl) ⟨4821200, by rfl⟩ : syracuseStep 6428267 = 9642401) B9642401
theorem B5936915 : Blo 1563479 5936915 := bstep (se 1 (by rfl) ⟨4452686, by rfl⟩ : syracuseStep 5936915 = 8905373) B8905373
theorem B101488625 : Blo 1563479 101488625 := bstep (se 2 (by rfl) ⟨38058234, by rfl⟩ : syracuseStep 101488625 = 76116469) B76116469
theorem B5011465 : Blo 1563479 5011465 := bstep (se 2 (by rfl) ⟨1879299, by rfl⟩ : syracuseStep 5011465 = 3758599) B3758599
theorem B30473027 : Blo 1563479 30473027 := bstep (se 1 (by rfl) ⟨22854770, by rfl⟩ : syracuseStep 30473027 = 45709541) B45709541
theorem B1563519 : Blo 1563479 1563519 := bstep (se 1 (by rfl) ⟨1172639, by rfl⟩ : syracuseStep 1563519 = 2345279) B2345279
theorem B1563615 : Blo 1563479 1563615 := bstep (se 1 (by rfl) ⟨1172711, by rfl⟩ : syracuseStep 1563615 = 2345423) B2345423
theorem B1563643 : Blo 1563479 1563643 := bstep (se 1 (by rfl) ⟨1172732, by rfl⟩ : syracuseStep 1563643 = 2345465) B2345465
theorem B1563675 : Blo 1563479 1563675 := bstep (se 1 (by rfl) ⟨1172756, by rfl⟩ : syracuseStep 1563675 = 2345513) B2345513
theorem B16055333 : Blo 1563479 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B1563967 : Blo 1563479 1563967 := bstep (se 1 (by rfl) ⟨1172975, by rfl⟩ : syracuseStep 1563967 = 2345951) B2345951
theorem B1760575 : Blo 1563479 1760575 := bstep (se 1 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 1760575 = 2640863) B2640863
theorem B1564263 : Blo 1563479 1564263 := bstep (se 1 (by rfl) ⟨1173197, by rfl⟩ : syracuseStep 1564263 = 2346395) B2346395
theorem B5938859 : Blo 1563479 5938859 := bstep (se 1 (by rfl) ⟨4454144, by rfl⟩ : syracuseStep 5938859 = 8908289) B8908289
theorem B5349095 : Blo 1563479 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B1564507 : Blo 1563479 1564507 := bstep (se 1 (by rfl) ⟨1173380, by rfl⟩ : syracuseStep 1564507 = 2346761) B2346761
theorem B1564543 : Blo 1563479 1564543 := bstep (se 1 (by rfl) ⟨1173407, by rfl⟩ : syracuseStep 1564543 = 2346815) B2346815
theorem B2818027 : Blo 1563479 2818027 := bstep (se 1 (by rfl) ⟨2113520, by rfl⟩ : syracuseStep 2818027 = 4227041) B4227041
theorem B1564719 : Blo 1563479 1564719 := bstep (se 1 (by rfl) ⟨1173539, by rfl⟩ : syracuseStep 1564719 = 2347079) B2347079
theorem B1564799 : Blo 1563479 1564799 := bstep (se 1 (by rfl) ⟨1173599, by rfl⟩ : syracuseStep 1564799 = 2347199) B2347199
theorem B1564895 : Blo 1563479 1564895 := bstep (se 1 (by rfl) ⟨1173671, by rfl⟩ : syracuseStep 1564895 = 2347343) B2347343
theorem B1564923 : Blo 1563479 1564923 := bstep (se 1 (by rfl) ⟨1173692, by rfl⟩ : syracuseStep 1564923 = 2347385) B2347385
theorem B7921961 : Blo 1563479 7921961 := bstep (se 2 (by rfl) ⟨2970735, by rfl⟩ : syracuseStep 7921961 = 5941471) B5941471
theorem B24076601 : Blo 1563479 24076601 := bstep (se 2 (by rfl) ⟨9028725, by rfl⟩ : syracuseStep 24076601 = 18057451) B18057451
theorem B117343241 : Blo 1563479 117343241 := bstep (se 2 (by rfl) ⟨44003715, by rfl⟩ : syracuseStep 117343241 = 88007431) B88007431
theorem B5940287 : Blo 1563479 5940287 := bstep (se 1 (by rfl) ⟨4455215, by rfl⟩ : syracuseStep 5940287 = 8910431) B8910431
theorem B4285511 : Blo 1563479 4285511 := bstep (se 1 (by rfl) ⟨3214133, by rfl⟩ : syracuseStep 4285511 = 6428267) B6428267
theorem B3957943 : Blo 1563479 3957943 := bstep (se 1 (by rfl) ⟨2968457, by rfl⟩ : syracuseStep 3957943 = 5936915) B5936915
theorem B67659083 : Blo 1563479 67659083 := bstep (se 1 (by rfl) ⟨50744312, by rfl⟩ : syracuseStep 67659083 = 101488625) B101488625
theorem B1189676369 : Blo 1563479 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B2639351 : Blo 1563479 2639351 := bstep (se 1 (by rfl) ⟨1979513, by rfl⟩ : syracuseStep 2639351 = 3959027) B3959027
theorem B45721381 : Blo 1563479 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B6342781 : Blo 1563479 6342781 := bstep (se 3 (by rfl) ⟨1189271, by rfl⟩ : syracuseStep 6342781 = 2378543) B2378543
theorem B5277959 : Blo 1563479 5277959 := bstep (se 1 (by rfl) ⟨3958469, by rfl⟩ : syracuseStep 5277959 = 7916939) B7916939
theorem B3959239 : Blo 1563479 3959239 := bstep (se 1 (by rfl) ⟨2969429, by rfl⟩ : syracuseStep 3959239 = 5938859) B5938859
theorem B3566063 : Blo 1563479 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B2345711 : Blo 1563479 2345711 := bstep (se 1 (by rfl) ⟨1759283, by rfl⟩ : syracuseStep 2345711 = 3518567) B3518567
theorem B2640647 : Blo 1563479 2640647 := bstep (se 1 (by rfl) ⟨1980485, by rfl⟩ : syracuseStep 2640647 = 3960971) B3960971
theorem B12200989 : Blo 1563479 12200989 := bstep (se 3 (by rfl) ⟨2287685, by rfl⟩ : syracuseStep 12200989 = 4575371) B4575371
theorem B7916615 : Blo 1563479 7916615 := bstep (se 1 (by rfl) ⟨5937461, by rfl⟩ : syracuseStep 7916615 = 11874923) B11874923
theorem B5279039 : Blo 1563479 5279039 := bstep (se 1 (by rfl) ⟨3959279, by rfl⟩ : syracuseStep 5279039 = 7918559) B7918559
theorem B14667389 : Blo 1563479 14667389 := bstep (se 3 (by rfl) ⟨2750135, by rfl⟩ : syracuseStep 14667389 = 5500271) B5500271
theorem B3518279 : Blo 1563479 3518279 := bstep (se 1 (by rfl) ⟨2638709, by rfl⟩ : syracuseStep 3518279 = 5277419) B5277419
theorem B3960647 : Blo 1563479 3960647 := bstep (se 1 (by rfl) ⟨2970485, by rfl⟩ : syracuseStep 3960647 = 5940971) B5940971
theorem B3518747 : Blo 1563479 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B3961183 : Blo 1563479 3961183 := bstep (se 1 (by rfl) ⟨2970887, by rfl⟩ : syracuseStep 3961183 = 5941775) B5941775
theorem B2347433 : Blo 1563479 2347433 := bstep (se 2 (by rfl) ⟨880287, by rfl⟩ : syracuseStep 2347433 = 1760575) B1760575
theorem B62616239 : Blo 1563479 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B4453051 : Blo 1563479 4453051 := bstep (se 1 (by rfl) ⟨3339788, by rfl⟩ : syracuseStep 4453051 = 6679577) B6679577
theorem B10703555 : Blo 1563479 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B4453211 : Blo 1563479 4453211 := bstep (se 1 (by rfl) ⟨3339908, by rfl⟩ : syracuseStep 4453211 = 6679817) B6679817
theorem B3519431 : Blo 1563479 3519431 := bstep (se 1 (by rfl) ⟨2639573, by rfl⟩ : syracuseStep 3519431 = 5279147) B5279147
theorem B8909999 : Blo 1563479 8909999 := bstep (se 1 (by rfl) ⟨6682499, by rfl⟩ : syracuseStep 8909999 = 13364999) B13364999
theorem B3757369 : Blo 1563479 3757369 := bstep (se 2 (by rfl) ⟨1409013, by rfl⟩ : syracuseStep 3757369 = 2818027) B2818027
theorem B6681953 : Blo 1563479 6681953 := bstep (se 2 (by rfl) ⟨2505732, by rfl⟩ : syracuseStep 6681953 = 5011465) B5011465
theorem B9156115 : Blo 1563479 9156115 := bstep (se 1 (by rfl) ⟨6867086, by rfl⟩ : syracuseStep 9156115 = 13734173) B13734173
theorem B3520295 : Blo 1563479 3520295 := bstep (se 1 (by rfl) ⟨2640221, by rfl⟩ : syracuseStep 3520295 = 5280443) B5280443
theorem B3520367 : Blo 1563479 3520367 := bstep (se 1 (by rfl) ⟨2640275, by rfl⟩ : syracuseStep 3520367 = 5280551) B5280551
theorem B601954733 : Blo 1563479 601954733 := bstep (se 3 (by rfl) ⟨112866512, by rfl⟩ : syracuseStep 601954733 = 225733025) B225733025
theorem B1760251 : Blo 1563479 1760251 := bstep (se 1 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 1760251 = 2640377) B2640377
theorem B1760359 : Blo 1563479 1760359 := bstep (se 1 (by rfl) ⟨1320269, by rfl⟩ : syracuseStep 1760359 = 2640539) B2640539
theorem B20315351 : Blo 1563479 20315351 := bstep (se 1 (by rfl) ⟨15236513, by rfl⟩ : syracuseStep 20315351 = 30473027) B30473027
theorem B1564127 : Blo 1563479 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B25370081 : Blo 1563479 25370081 := bstep (se 2 (by rfl) ⟨9513780, by rfl⟩ : syracuseStep 25370081 = 19027561) B19027561
theorem B1564207 : Blo 1563479 1564207 := bstep (se 1 (by rfl) ⟨1173155, by rfl⟩ : syracuseStep 1564207 = 2346311) B2346311
theorem B4963913 : Blo 1563479 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B1564479 : Blo 1563479 1564479 := bstep (se 1 (by rfl) ⟨1173359, by rfl⟩ : syracuseStep 1564479 = 2346719) B2346719
theorem B5939027 : Blo 1563479 5939027 := bstep (se 1 (by rfl) ⟨4454270, by rfl⟩ : syracuseStep 5939027 = 8908541) B8908541
theorem B1564955 : Blo 1563479 1564955 := bstep (se 1 (by rfl) ⟨1173716, by rfl⟩ : syracuseStep 1564955 = 2347433) B2347433
theorem B7135703 : Blo 1563479 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B5939999 : Blo 1563479 5939999 := bstep (se 1 (by rfl) ⟨4454999, by rfl⟩ : syracuseStep 5939999 = 8909999) B8909999
theorem B45106055 : Blo 1563479 45106055 := bstep (se 1 (by rfl) ⟨33829541, by rfl⟩ : syracuseStep 45106055 = 67659083) B67659083
theorem B5277257 : Blo 1563479 5277257 := bstep (se 2 (by rfl) ⟨1978971, by rfl⟩ : syracuseStep 5277257 = 3957943) B3957943
theorem B401303155 : Blo 1563479 401303155 := bstep (se 1 (by rfl) ⟨300977366, by rfl⟩ : syracuseStep 401303155 = 601954733) B601954733
theorem B12208153 : Blo 1563479 12208153 := bstep (se 2 (by rfl) ⟨4578057, by rfl⟩ : syracuseStep 12208153 = 9156115) B9156115
theorem B5277743 : Blo 1563479 5277743 := bstep (se 1 (by rfl) ⟨3958307, by rfl⟩ : syracuseStep 5277743 = 7916615) B7916615
theorem B13543567 : Blo 1563479 13543567 := bstep (se 1 (by rfl) ⟨10157675, by rfl⟩ : syracuseStep 13543567 = 20315351) B20315351
theorem B2345519 : Blo 1563479 2345519 := bstep (se 1 (by rfl) ⟨1759139, by rfl⟩ : syracuseStep 2345519 = 3518279) B3518279
theorem B2640431 : Blo 1563479 2640431 := bstep (se 1 (by rfl) ⟨1980323, by rfl⟩ : syracuseStep 2640431 = 3960647) B3960647
theorem B3959351 : Blo 1563479 3959351 := bstep (se 1 (by rfl) ⟨2969513, by rfl⟩ : syracuseStep 3959351 = 5939027) B5939027
theorem B8457041 : Blo 1563479 8457041 := bstep (se 2 (by rfl) ⟨3171390, by rfl⟩ : syracuseStep 8457041 = 6342781) B6342781
theorem B2345831 : Blo 1563479 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B16051067 : Blo 1563479 16051067 := bstep (se 1 (by rfl) ⟨12038300, by rfl⟩ : syracuseStep 16051067 = 24076601) B24076601
theorem B2968807 : Blo 1563479 2968807 := bstep (se 1 (by rfl) ⟨2226605, by rfl⟩ : syracuseStep 2968807 = 4453211) B4453211
theorem B5278985 : Blo 1563479 5278985 := bstep (se 2 (by rfl) ⟨1979619, by rfl⟩ : syracuseStep 5278985 = 3959239) B3959239
theorem B2346287 : Blo 1563479 2346287 := bstep (se 1 (by rfl) ⟨1759715, by rfl⟩ : syracuseStep 2346287 = 3519431) B3519431
theorem B78228827 : Blo 1563479 78228827 := bstep (se 1 (by rfl) ⟨58671620, by rfl⟩ : syracuseStep 78228827 = 117343241) B117343241
theorem B3960191 : Blo 1563479 3960191 := bstep (se 1 (by rfl) ⟨2970143, by rfl⟩ : syracuseStep 3960191 = 5940287) B5940287
theorem B3172470317 : Blo 1563479 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B2346863 : Blo 1563479 2346863 := bstep (se 1 (by rfl) ⟨1760147, by rfl⟩ : syracuseStep 2346863 = 3520295) B3520295
theorem B2346911 : Blo 1563479 2346911 := bstep (se 1 (by rfl) ⟨1760183, by rfl⟩ : syracuseStep 2346911 = 3520367) B3520367
theorem B2347001 : Blo 1563479 2347001 := bstep (se 2 (by rfl) ⟨880125, by rfl⟩ : syracuseStep 2347001 = 1760251) B1760251
theorem B2347145 : Blo 1563479 2347145 := bstep (se 2 (by rfl) ⟨880179, by rfl⟩ : syracuseStep 2347145 = 1760359) B1760359
theorem B3518639 : Blo 1563479 3518639 := bstep (se 1 (by rfl) ⟨2638979, by rfl⟩ : syracuseStep 3518639 = 5277959) B5277959
theorem B5009825 : Blo 1563479 5009825 := bstep (se 2 (by rfl) ⟨1878684, by rfl⟩ : syracuseStep 5009825 = 3757369) B3757369
theorem B3519359 : Blo 1563479 3519359 := bstep (se 1 (by rfl) ⟨2639519, by rfl⟩ : syracuseStep 3519359 = 5279039) B5279039
theorem B16913387 : Blo 1563479 16913387 := bstep (se 1 (by rfl) ⟨12685040, by rfl⟩ : syracuseStep 16913387 = 25370081) B25370081
theorem B60961841 : Blo 1563479 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B9778259 : Blo 1563479 9778259 := bstep (se 1 (by rfl) ⟨7333694, by rfl⟩ : syracuseStep 9778259 = 14667389) B14667389
theorem B5281307 : Blo 1563479 5281307 := bstep (se 1 (by rfl) ⟨3960980, by rfl⟩ : syracuseStep 5281307 = 7921961) B7921961
theorem B41744159 : Blo 1563479 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B5281577 : Blo 1563479 5281577 := bstep (se 2 (by rfl) ⟨1980591, by rfl⟩ : syracuseStep 5281577 = 3961183) B3961183
theorem B2857007 : Blo 1563479 2857007 := bstep (se 1 (by rfl) ⟨2142755, by rfl⟩ : syracuseStep 2857007 = 4285511) B4285511
theorem B4454635 : Blo 1563479 4454635 := bstep (se 1 (by rfl) ⟨3340976, by rfl⟩ : syracuseStep 4454635 = 6681953) B6681953
theorem B5937401 : Blo 1563479 5937401 := bstep (se 2 (by rfl) ⟨2226525, by rfl⟩ : syracuseStep 5937401 = 4453051) B4453051
theorem B1759567 : Blo 1563479 1759567 := bstep (se 1 (by rfl) ⟨1319675, by rfl⟩ : syracuseStep 1759567 = 2639351) B2639351
theorem B9509501 : Blo 1563479 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B16267985 : Blo 1563479 16267985 := bstep (se 2 (by rfl) ⟨6100494, by rfl⟩ : syracuseStep 16267985 = 12200989) B12200989
theorem B1563807 : Blo 1563479 1563807 := bstep (se 1 (by rfl) ⟨1172855, by rfl⟩ : syracuseStep 1563807 = 2345711) B2345711
theorem B1760431 : Blo 1563479 1760431 := bstep (se 1 (by rfl) ⟨1320323, by rfl⟩ : syracuseStep 1760431 = 2640647) B2640647
theorem B3309275 : Blo 1563479 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B16277537 : Blo 1563479 16277537 := bstep (se 2 (by rfl) ⟨6104076, by rfl⟩ : syracuseStep 16277537 = 12208153) B12208153
theorem B1564763 : Blo 1563479 1564763 := bstep (se 1 (by rfl) ⟨1173572, by rfl⟩ : syracuseStep 1564763 = 2347145) B2347145
theorem B5939513 : Blo 1563479 5939513 := bstep (se 2 (by rfl) ⟨2227317, by rfl⟩ : syracuseStep 5939513 = 4454635) B4454635
theorem B40641227 : Blo 1563479 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B27829439 : Blo 1563479 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B3958267 : Blo 1563479 3958267 := bstep (se 1 (by rfl) ⟨2968700, by rfl⟩ : syracuseStep 3958267 = 5937401) B5937401
theorem B3958409 : Blo 1563479 3958409 := bstep (se 2 (by rfl) ⟨1484403, by rfl⟩ : syracuseStep 3958409 = 2968807) B2968807
theorem B2639567 : Blo 1563479 2639567 := bstep (se 1 (by rfl) ⟨1979675, by rfl⟩ : syracuseStep 2639567 = 3959351) B3959351
theorem B5638027 : Blo 1563479 5638027 := bstep (se 1 (by rfl) ⟨4228520, by rfl⟩ : syracuseStep 5638027 = 8457041) B8457041
theorem B8824733 : Blo 1563479 8824733 := bstep (se 3 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 8824733 = 3309275) B3309275
theorem B10700711 : Blo 1563479 10700711 := bstep (se 1 (by rfl) ⟨8025533, by rfl⟩ : syracuseStep 10700711 = 16051067) B16051067
theorem B535070873 : Blo 1563479 535070873 := bstep (se 2 (by rfl) ⟨200651577, by rfl⟩ : syracuseStep 535070873 = 401303155) B401303155
theorem B52152551 : Blo 1563479 52152551 := bstep (se 1 (by rfl) ⟨39114413, by rfl⟩ : syracuseStep 52152551 = 78228827) B78228827
theorem B2640127 : Blo 1563479 2640127 := bstep (se 1 (by rfl) ⟨1980095, by rfl⟩ : syracuseStep 2640127 = 3960191) B3960191
theorem B2114980211 : Blo 1563479 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B2345759 : Blo 1563479 2345759 := bstep (se 1 (by rfl) ⟨1759319, by rfl⟩ : syracuseStep 2345759 = 3518639) B3518639
theorem B2346089 : Blo 1563479 2346089 := bstep (se 2 (by rfl) ⟨879783, by rfl⟩ : syracuseStep 2346089 = 1759567) B1759567
theorem B3959999 : Blo 1563479 3959999 := bstep (se 1 (by rfl) ⟨2969999, by rfl⟩ : syracuseStep 3959999 = 5939999) B5939999
theorem B2346239 : Blo 1563479 2346239 := bstep (se 1 (by rfl) ⟨1759679, by rfl⟩ : syracuseStep 2346239 = 3519359) B3519359
theorem B72232357 : Blo 1563479 72232357 := bstep (se 4 (by rfl) ⟨6771783, by rfl⟩ : syracuseStep 72232357 = 13543567) B13543567
theorem B3518171 : Blo 1563479 3518171 := bstep (se 1 (by rfl) ⟨2638628, by rfl⟩ : syracuseStep 3518171 = 5277257) B5277257
theorem B3518495 : Blo 1563479 3518495 := bstep (se 1 (by rfl) ⟨2638871, by rfl⟩ : syracuseStep 3518495 = 5277743) B5277743
theorem B1904671 : Blo 1563479 1904671 := bstep (se 1 (by rfl) ⟨1428503, by rfl⟩ : syracuseStep 1904671 = 2857007) B2857007
theorem B2347241 : Blo 1563479 2347241 := bstep (se 2 (by rfl) ⟨880215, by rfl⟩ : syracuseStep 2347241 = 1760431) B1760431
theorem B3519323 : Blo 1563479 3519323 := bstep (se 1 (by rfl) ⟨2639492, by rfl⟩ : syracuseStep 3519323 = 5278985) B5278985
theorem B45102365 : Blo 1563479 45102365 := bstep (se 3 (by rfl) ⟨8456693, by rfl⟩ : syracuseStep 45102365 = 16913387) B16913387
theorem B3339883 : Blo 1563479 3339883 := bstep (se 1 (by rfl) ⟨2504912, by rfl⟩ : syracuseStep 3339883 = 5009825) B5009825
theorem B4757135 : Blo 1563479 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B30070703 : Blo 1563479 30070703 := bstep (se 1 (by rfl) ⟨22553027, by rfl⟩ : syracuseStep 30070703 = 45106055) B45106055
theorem B6518839 : Blo 1563479 6518839 := bstep (se 1 (by rfl) ⟨4889129, by rfl⟩ : syracuseStep 6518839 = 9778259) B9778259
theorem B3520871 : Blo 1563479 3520871 := bstep (se 1 (by rfl) ⟨2640653, by rfl⟩ : syracuseStep 3520871 = 5281307) B5281307
theorem B3521051 : Blo 1563479 3521051 := bstep (se 1 (by rfl) ⟨2640788, by rfl⟩ : syracuseStep 3521051 = 5281577) B5281577
theorem B1563679 : Blo 1563479 1563679 := bstep (se 1 (by rfl) ⟨1172759, by rfl⟩ : syracuseStep 1563679 = 2345519) B2345519
theorem B1760287 : Blo 1563479 1760287 := bstep (se 1 (by rfl) ⟨1320215, by rfl⟩ : syracuseStep 1760287 = 2640431) B2640431
theorem B6339667 : Blo 1563479 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B10845323 : Blo 1563479 10845323 := bstep (se 1 (by rfl) ⟨8133992, by rfl⟩ : syracuseStep 10845323 = 16267985) B16267985
theorem B1563887 : Blo 1563479 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B1564191 : Blo 1563479 1564191 := bstep (se 1 (by rfl) ⟨1173143, by rfl⟩ : syracuseStep 1564191 = 2346287) B2346287
theorem B1564575 : Blo 1563479 1564575 := bstep (se 1 (by rfl) ⟨1173431, by rfl⟩ : syracuseStep 1564575 = 2346863) B2346863
theorem B1564607 : Blo 1563479 1564607 := bstep (se 1 (by rfl) ⟨1173455, by rfl⟩ : syracuseStep 1564607 = 2346911) B2346911
theorem B1564667 : Blo 1563479 1564667 := bstep (se 1 (by rfl) ⟨1173500, by rfl⟩ : syracuseStep 1564667 = 2347001) B2347001
theorem B8691785 : Blo 1563479 8691785 := bstep (se 2 (by rfl) ⟨3259419, by rfl⟩ : syracuseStep 8691785 = 6518839) B6518839
theorem B1564827 : Blo 1563479 1564827 := bstep (se 1 (by rfl) ⟨1173620, by rfl⟩ : syracuseStep 1564827 = 2347241) B2347241
theorem B10158245 : Blo 1563479 10158245 := bstep (se 4 (by rfl) ⟨952335, by rfl⟩ : syracuseStep 10158245 = 1904671) B1904671
theorem B2638939 : Blo 1563479 2638939 := bstep (se 1 (by rfl) ⟨1979204, by rfl⟩ : syracuseStep 2638939 = 3958409) B3958409
theorem B5883155 : Blo 1563479 5883155 := bstep (se 1 (by rfl) ⟨4412366, by rfl⟩ : syracuseStep 5883155 = 8824733) B8824733
theorem B20047135 : Blo 1563479 20047135 := bstep (se 1 (by rfl) ⟨15035351, by rfl⟩ : syracuseStep 20047135 = 30070703) B30070703
theorem B34768367 : Blo 1563479 34768367 := bstep (se 1 (by rfl) ⟨26076275, by rfl⟩ : syracuseStep 34768367 = 52152551) B52152551
theorem B50742773 : Blo 1563479 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B5277689 : Blo 1563479 5277689 := bstep (se 2 (by rfl) ⟨1979133, by rfl⟩ : syracuseStep 5277689 = 3958267) B3958267
theorem B2639999 : Blo 1563479 2639999 := bstep (se 1 (by rfl) ⟨1979999, by rfl⟩ : syracuseStep 2639999 = 3959999) B3959999
theorem B2345447 : Blo 1563479 2345447 := bstep (se 1 (by rfl) ⟨1759085, by rfl⟩ : syracuseStep 2345447 = 3518171) B3518171
theorem B2345663 : Blo 1563479 2345663 := bstep (se 1 (by rfl) ⟨1759247, by rfl⟩ : syracuseStep 2345663 = 3518495) B3518495
theorem B3959675 : Blo 1563479 3959675 := bstep (se 1 (by rfl) ⟨2969756, by rfl⟩ : syracuseStep 3959675 = 5939513) B5939513
theorem B27094151 : Blo 1563479 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B2346215 : Blo 1563479 2346215 := bstep (se 1 (by rfl) ⟨1759661, by rfl⟩ : syracuseStep 2346215 = 3519323) B3519323
theorem B30068243 : Blo 1563479 30068243 := bstep (se 1 (by rfl) ⟨22551182, by rfl⟩ : syracuseStep 30068243 = 45102365) B45102365
theorem B2347049 : Blo 1563479 2347049 := bstep (se 2 (by rfl) ⟨880143, by rfl⟩ : syracuseStep 2347049 = 1760287) B1760287
theorem B2347247 : Blo 1563479 2347247 := bstep (se 1 (by rfl) ⟨1760435, by rfl⟩ : syracuseStep 2347247 = 3520871) B3520871
theorem B1409986807 : Blo 1563479 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B2347367 : Blo 1563479 2347367 := bstep (se 1 (by rfl) ⟨1760525, by rfl⟩ : syracuseStep 2347367 = 3521051) B3521051
theorem B96309809 : Blo 1563479 96309809 := bstep (se 2 (by rfl) ⟨36116178, by rfl⟩ : syracuseStep 96309809 = 72232357) B72232357
theorem B7230215 : Blo 1563479 7230215 := bstep (se 1 (by rfl) ⟨5422661, by rfl⟩ : syracuseStep 7230215 = 10845323) B10845323
theorem B4453177 : Blo 1563479 4453177 := bstep (se 2 (by rfl) ⟨1669941, by rfl⟩ : syracuseStep 4453177 = 3339883) B3339883
theorem B7517369 : Blo 1563479 7517369 := bstep (se 2 (by rfl) ⟨2819013, by rfl⟩ : syracuseStep 7517369 = 5638027) B5638027
theorem B10851691 : Blo 1563479 10851691 := bstep (se 1 (by rfl) ⟨8138768, by rfl⟩ : syracuseStep 10851691 = 16277537) B16277537
theorem B3520169 : Blo 1563479 3520169 := bstep (se 2 (by rfl) ⟨1320063, by rfl⟩ : syracuseStep 3520169 = 2640127) B2640127
theorem B1426855661 : Blo 1563479 1426855661 := bstep (se 3 (by rfl) ⟨267535436, by rfl⟩ : syracuseStep 1426855661 = 535070873) B535070873
theorem B18552959 : Blo 1563479 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B1759711 : Blo 1563479 1759711 := bstep (se 1 (by rfl) ⟨1319783, by rfl⟩ : syracuseStep 1759711 = 2639567) B2639567
theorem B7133807 : Blo 1563479 7133807 := bstep (se 1 (by rfl) ⟨5350355, by rfl⟩ : syracuseStep 7133807 = 10700711) B10700711
theorem B8452889 : Blo 1563479 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B1563839 : Blo 1563479 1563839 := bstep (se 1 (by rfl) ⟨1172879, by rfl⟩ : syracuseStep 1563839 = 2345759) B2345759
theorem B1564059 : Blo 1563479 1564059 := bstep (se 1 (by rfl) ⟨1173044, by rfl⟩ : syracuseStep 1564059 = 2346089) B2346089
theorem B1564159 : Blo 1563479 1564159 := bstep (se 1 (by rfl) ⟨1173119, by rfl⟩ : syracuseStep 1564159 = 2346239) B2346239
theorem B1564699 : Blo 1563479 1564699 := bstep (se 1 (by rfl) ⟨1173524, by rfl⟩ : syracuseStep 1564699 = 2347049) B2347049
theorem B1564831 : Blo 1563479 1564831 := bstep (se 1 (by rfl) ⟨1173623, by rfl⟩ : syracuseStep 1564831 = 2347247) B2347247
theorem B1564911 : Blo 1563479 1564911 := bstep (se 1 (by rfl) ⟨1173683, by rfl⟩ : syracuseStep 1564911 = 2347367) B2347367
theorem B14468921 : Blo 1563479 14468921 := bstep (se 2 (by rfl) ⟨5425845, by rfl⟩ : syracuseStep 14468921 = 10851691) B10851691
theorem B2639783 : Blo 1563479 2639783 := bstep (se 1 (by rfl) ⟨1979837, by rfl⟩ : syracuseStep 2639783 = 3959675) B3959675
theorem B5794523 : Blo 1563479 5794523 := bstep (se 1 (by rfl) ⟨4345892, by rfl⟩ : syracuseStep 5794523 = 8691785) B8691785
theorem B4820143 : Blo 1563479 4820143 := bstep (se 1 (by rfl) ⟨3615107, by rfl⟩ : syracuseStep 4820143 = 7230215) B7230215
theorem B2346281 : Blo 1563479 2346281 := bstep (se 2 (by rfl) ⟨879855, by rfl⟩ : syracuseStep 2346281 = 1759711) B1759711
theorem B23178911 : Blo 1563479 23178911 := bstep (se 1 (by rfl) ⟨17384183, by rfl⟩ : syracuseStep 23178911 = 34768367) B34768367
theorem B33828515 : Blo 1563479 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B2346779 : Blo 1563479 2346779 := bstep (se 1 (by rfl) ⟨1760084, by rfl⟩ : syracuseStep 2346779 = 3520169) B3520169
theorem B3518459 : Blo 1563479 3518459 := bstep (se 1 (by rfl) ⟨2638844, by rfl⟩ : syracuseStep 3518459 = 5277689) B5277689
theorem B3518585 : Blo 1563479 3518585 := bstep (se 2 (by rfl) ⟨1319469, by rfl⟩ : syracuseStep 3518585 = 2638939) B2638939
theorem B4755871 : Blo 1563479 4755871 := bstep (se 1 (by rfl) ⟨3566903, by rfl⟩ : syracuseStep 4755871 = 7133807) B7133807
theorem B30079718549 : Blo 1563479 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B6772163 : Blo 1563479 6772163 := bstep (se 1 (by rfl) ⟨5079122, by rfl⟩ : syracuseStep 6772163 = 10158245) B10158245
theorem B64206539 : Blo 1563479 64206539 := bstep (se 1 (by rfl) ⟨48154904, by rfl⟩ : syracuseStep 64206539 = 96309809) B96309809
theorem B5011579 : Blo 1563479 5011579 := bstep (se 1 (by rfl) ⟨3758684, by rfl⟩ : syracuseStep 5011579 = 7517369) B7517369
theorem B3922103 : Blo 1563479 3922103 := bstep (se 1 (by rfl) ⟨2941577, by rfl⟩ : syracuseStep 3922103 = 5883155) B5883155
theorem B5937569 : Blo 1563479 5937569 := bstep (se 2 (by rfl) ⟨2226588, by rfl⟩ : syracuseStep 5937569 = 4453177) B4453177
theorem B951237107 : Blo 1563479 951237107 := bstep (se 1 (by rfl) ⟨713427830, by rfl⟩ : syracuseStep 951237107 = 1426855661) B1426855661
theorem B12368639 : Blo 1563479 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B1759999 : Blo 1563479 1759999 := bstep (se 1 (by rfl) ⟨1319999, by rfl⟩ : syracuseStep 1759999 = 2639999) B2639999
theorem B1563631 : Blo 1563479 1563631 := bstep (se 1 (by rfl) ⟨1172723, by rfl⟩ : syracuseStep 1563631 = 2345447) B2345447
theorem B26729513 : Blo 1563479 26729513 := bstep (se 2 (by rfl) ⟨10023567, by rfl⟩ : syracuseStep 26729513 = 20047135) B20047135
theorem B1563775 : Blo 1563479 1563775 := bstep (se 1 (by rfl) ⟨1172831, by rfl⟩ : syracuseStep 1563775 = 2345663) B2345663
theorem B5635259 : Blo 1563479 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B18062767 : Blo 1563479 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B1564143 : Blo 1563479 1564143 := bstep (se 1 (by rfl) ⟨1173107, by rfl⟩ : syracuseStep 1564143 = 2346215) B2346215
theorem B20045495 : Blo 1563479 20045495 := bstep (se 1 (by rfl) ⟨15034121, by rfl⟩ : syracuseStep 20045495 = 30068243) B30068243
theorem B6341161 : Blo 1563479 6341161 := bstep (se 2 (by rfl) ⟨2377935, by rfl⟩ : syracuseStep 6341161 = 4755871) B4755871
theorem B42804359 : Blo 1563479 42804359 := bstep (se 1 (by rfl) ⟨32103269, by rfl⟩ : syracuseStep 42804359 = 64206539) B64206539
theorem B2614735 : Blo 1563479 2614735 := bstep (se 1 (by rfl) ⟨1961051, by rfl⟩ : syracuseStep 2614735 = 3922103) B3922103
theorem B3958379 : Blo 1563479 3958379 := bstep (se 1 (by rfl) ⟨2968784, by rfl⟩ : syracuseStep 3958379 = 5937569) B5937569
theorem B32983037 : Blo 1563479 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B17819675 : Blo 1563479 17819675 := bstep (se 1 (by rfl) ⟨13364756, by rfl⟩ : syracuseStep 17819675 = 26729513) B26729513
theorem B13363663 : Blo 1563479 13363663 := bstep (se 1 (by rfl) ⟨10022747, by rfl⟩ : syracuseStep 13363663 = 20045495) B20045495
theorem B2345639 : Blo 1563479 2345639 := bstep (se 1 (by rfl) ⟨1759229, by rfl⟩ : syracuseStep 2345639 = 3518459) B3518459
theorem B2345723 : Blo 1563479 2345723 := bstep (se 1 (by rfl) ⟨1759292, by rfl⟩ : syracuseStep 2345723 = 3518585) B3518585
theorem B2346665 : Blo 1563479 2346665 := bstep (se 2 (by rfl) ⟨879999, by rfl⟩ : syracuseStep 2346665 = 1759999) B1759999
theorem B9645947 : Blo 1563479 9645947 := bstep (se 1 (by rfl) ⟨7234460, by rfl⟩ : syracuseStep 9645947 = 14468921) B14468921
theorem B6426857 : Blo 1563479 6426857 := bstep (se 2 (by rfl) ⟨2410071, by rfl⟩ : syracuseStep 6426857 = 4820143) B4820143
theorem B3863015 : Blo 1563479 3863015 := bstep (se 1 (by rfl) ⟨2897261, by rfl⟩ : syracuseStep 3863015 = 5794523) B5794523
theorem B3756839 : Blo 1563479 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B6682105 : Blo 1563479 6682105 := bstep (se 2 (by rfl) ⟨2505789, by rfl⟩ : syracuseStep 6682105 = 5011579) B5011579
theorem B20053145699 : Blo 1563479 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B1759855 : Blo 1563479 1759855 := bstep (se 1 (by rfl) ⟨1319891, by rfl⟩ : syracuseStep 1759855 = 2639783) B2639783
theorem B247241717 : Blo 1563479 247241717 := bstep (se 5 (by rfl) ⟨11589455, by rfl⟩ : syracuseStep 247241717 = 23178911) B23178911
theorem B634158071 : Blo 1563479 634158071 := bstep (se 1 (by rfl) ⟨475618553, by rfl⟩ : syracuseStep 634158071 = 951237107) B951237107
theorem B24083689 : Blo 1563479 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B72236405 : Blo 1563479 72236405 := bstep (se 5 (by rfl) ⟨3386081, by rfl⟩ : syracuseStep 72236405 = 6772163) B6772163
theorem B1564187 : Blo 1563479 1564187 := bstep (se 1 (by rfl) ⟨1173140, by rfl⟩ : syracuseStep 1564187 = 2346281) B2346281
theorem B22552343 : Blo 1563479 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B1564519 : Blo 1563479 1564519 := bstep (se 1 (by rfl) ⟨1173389, by rfl⟩ : syracuseStep 1564519 = 2346779) B2346779
theorem B4284571 : Blo 1563479 4284571 := bstep (se 1 (by rfl) ⟨3213428, by rfl⟩ : syracuseStep 4284571 = 6426857) B6426857
theorem B17818217 : Blo 1563479 17818217 := bstep (se 2 (by rfl) ⟨6681831, by rfl⟩ : syracuseStep 17818217 = 13363663) B13363663
theorem B8454881 : Blo 1563479 8454881 := bstep (se 2 (by rfl) ⟨3170580, by rfl⟩ : syracuseStep 8454881 = 6341161) B6341161
theorem B2638919 : Blo 1563479 2638919 := bstep (se 1 (by rfl) ⟨1979189, by rfl⟩ : syracuseStep 2638919 = 3958379) B3958379
theorem B21988691 : Blo 1563479 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B11879783 : Blo 1563479 11879783 := bstep (se 1 (by rfl) ⟨8909837, by rfl⟩ : syracuseStep 11879783 = 17819675) B17819675
theorem B13368763799 : Blo 1563479 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B15034895 : Blo 1563479 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B2575343 : Blo 1563479 2575343 := bstep (se 1 (by rfl) ⟨1931507, by rfl⟩ : syracuseStep 2575343 = 3863015) B3863015
theorem B28536239 : Blo 1563479 28536239 := bstep (se 1 (by rfl) ⟨21402179, by rfl⟩ : syracuseStep 28536239 = 42804359) B42804359
theorem B2346473 : Blo 1563479 2346473 := bstep (se 2 (by rfl) ⟨879927, by rfl⟩ : syracuseStep 2346473 = 1759855) B1759855
theorem B192630413 : Blo 1563479 192630413 := bstep (se 3 (by rfl) ⟨36118202, by rfl⟩ : syracuseStep 192630413 = 72236405) B72236405
theorem B3486313 : Blo 1563479 3486313 := bstep (se 2 (by rfl) ⟨1307367, by rfl⟩ : syracuseStep 3486313 = 2614735) B2614735
theorem B8909473 : Blo 1563479 8909473 := bstep (se 2 (by rfl) ⟨3341052, by rfl⟩ : syracuseStep 8909473 = 6682105) B6682105
theorem B164827811 : Blo 1563479 164827811 := bstep (se 1 (by rfl) ⟨123620858, by rfl⟩ : syracuseStep 164827811 = 247241717) B247241717
theorem B32111585 : Blo 1563479 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B1563759 : Blo 1563479 1563759 := bstep (se 1 (by rfl) ⟨1172819, by rfl⟩ : syracuseStep 1563759 = 2345639) B2345639
theorem B1563815 : Blo 1563479 1563815 := bstep (se 1 (by rfl) ⟨1172861, by rfl⟩ : syracuseStep 1563815 = 2345723) B2345723
theorem B422772047 : Blo 1563479 422772047 := bstep (se 1 (by rfl) ⟨317079035, by rfl⟩ : syracuseStep 422772047 = 634158071) B634158071
theorem B10018237 : Blo 1563479 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B1564443 : Blo 1563479 1564443 := bstep (se 1 (by rfl) ⟨1173332, by rfl⟩ : syracuseStep 1564443 = 2346665) B2346665
theorem B6430631 : Blo 1563479 6430631 := bstep (se 1 (by rfl) ⟨4822973, by rfl⟩ : syracuseStep 6430631 = 9645947) B9645947
theorem B11878811 : Blo 1563479 11878811 := bstep (se 1 (by rfl) ⟨8909108, by rfl⟩ : syracuseStep 11878811 = 17818217) B17818217
theorem B5636587 : Blo 1563479 5636587 := bstep (se 1 (by rfl) ⟨4227440, by rfl⟩ : syracuseStep 5636587 = 8454881) B8454881
theorem B11879297 : Blo 1563479 11879297 := bstep (se 2 (by rfl) ⟨4454736, by rfl⟩ : syracuseStep 11879297 = 8909473) B8909473
theorem B68593397 : Blo 1563479 68593397 := bstep (se 5 (by rfl) ⟨3215315, by rfl⟩ : syracuseStep 68593397 = 6430631) B6430631
theorem B21407723 : Blo 1563479 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B281848031 : Blo 1563479 281848031 := bstep (se 1 (by rfl) ⟨211386023, by rfl⟩ : syracuseStep 281848031 = 422772047) B422772047
theorem B19024159 : Blo 1563479 19024159 := bstep (se 1 (by rfl) ⟨14268119, by rfl⟩ : syracuseStep 19024159 = 28536239) B28536239
theorem B128420275 : Blo 1563479 128420275 := bstep (se 1 (by rfl) ⟨96315206, by rfl⟩ : syracuseStep 128420275 = 192630413) B192630413
theorem B5712761 : Blo 1563479 5712761 := bstep (se 2 (by rfl) ⟨2142285, by rfl⟩ : syracuseStep 5712761 = 4284571) B4284571
theorem B4648417 : Blo 1563479 4648417 := bstep (se 2 (by rfl) ⟨1743156, by rfl⟩ : syracuseStep 4648417 = 3486313) B3486313
theorem B14659127 : Blo 1563479 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B10023263 : Blo 1563479 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B13357649 : Blo 1563479 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B1716895 : Blo 1563479 1716895 := bstep (se 1 (by rfl) ⟨1287671, by rfl⟩ : syracuseStep 1716895 = 2575343) B2575343
theorem B109885207 : Blo 1563479 109885207 := bstep (se 1 (by rfl) ⟨82413905, by rfl⟩ : syracuseStep 109885207 = 164827811) B164827811
theorem B1759279 : Blo 1563479 1759279 := bstep (se 1 (by rfl) ⟨1319459, by rfl⟩ : syracuseStep 1759279 = 2638919) B2638919
theorem B7919855 : Blo 1563479 7919855 := bstep (se 1 (by rfl) ⟨5939891, by rfl⟩ : syracuseStep 7919855 = 11879783) B11879783
theorem B8912509199 : Blo 1563479 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B1564315 : Blo 1563479 1564315 := bstep (se 1 (by rfl) ⟨1173236, by rfl⟩ : syracuseStep 1564315 = 2346473) B2346473
theorem B8905099 : Blo 1563479 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B14271815 : Blo 1563479 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B24791557 : Blo 1563479 24791557 := bstep (se 4 (by rfl) ⟨2324208, by rfl⟩ : syracuseStep 24791557 = 4648417) B4648417
theorem B731662901 : Blo 1563479 731662901 := bstep (se 5 (by rfl) ⟨34296698, by rfl⟩ : syracuseStep 731662901 = 68593397) B68593397
theorem B2345705 : Blo 1563479 2345705 := bstep (se 2 (by rfl) ⟨879639, by rfl⟩ : syracuseStep 2345705 = 1759279) B1759279
theorem B25365545 : Blo 1563479 25365545 := bstep (se 2 (by rfl) ⟨9512079, by rfl⟩ : syracuseStep 25365545 = 19024159) B19024159
theorem B7515449 : Blo 1563479 7515449 := bstep (se 2 (by rfl) ⟨2818293, by rfl⟩ : syracuseStep 7515449 = 5636587) B5636587
theorem B5279903 : Blo 1563479 5279903 := bstep (se 1 (by rfl) ⟨3959927, by rfl⟩ : syracuseStep 5279903 = 7919855) B7919855
theorem B6682175 : Blo 1563479 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B7919207 : Blo 1563479 7919207 := bstep (se 1 (by rfl) ⟨5939405, by rfl⟩ : syracuseStep 7919207 = 11878811) B11878811
theorem B171227033 : Blo 1563479 171227033 := bstep (se 2 (by rfl) ⟨64210137, by rfl⟩ : syracuseStep 171227033 = 128420275) B128420275
theorem B7919531 : Blo 1563479 7919531 := bstep (se 1 (by rfl) ⟨5939648, by rfl⟩ : syracuseStep 7919531 = 11879297) B11879297
theorem B9156773 : Blo 1563479 9156773 := bstep (se 4 (by rfl) ⟨858447, by rfl⟩ : syracuseStep 9156773 = 1716895) B1716895
theorem B187898687 : Blo 1563479 187898687 := bstep (se 1 (by rfl) ⟨140924015, by rfl⟩ : syracuseStep 187898687 = 281848031) B281848031
theorem B5941672799 : Blo 1563479 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B3808507 : Blo 1563479 3808507 := bstep (se 1 (by rfl) ⟨2856380, by rfl⟩ : syracuseStep 3808507 = 5712761) B5712761
theorem B146513609 : Blo 1563479 146513609 := bstep (se 2 (by rfl) ⟨54942603, by rfl⟩ : syracuseStep 146513609 = 109885207) B109885207
theorem B9772751 : Blo 1563479 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B33055409 : Blo 1563479 33055409 := bstep (se 2 (by rfl) ⟨12395778, by rfl⟩ : syracuseStep 33055409 = 24791557) B24791557
theorem B26060669 : Blo 1563479 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B125265791 : Blo 1563479 125265791 := bstep (se 1 (by rfl) ⟨93949343, by rfl⟩ : syracuseStep 125265791 = 187898687) B187898687
theorem B16910363 : Blo 1563479 16910363 := bstep (se 1 (by rfl) ⟨12682772, by rfl⟩ : syracuseStep 16910363 = 25365545) B25365545
theorem B15844460797 : Blo 1563479 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B97675739 : Blo 1563479 97675739 := bstep (se 1 (by rfl) ⟨73256804, by rfl⟩ : syracuseStep 97675739 = 146513609) B146513609
theorem B11873465 : Blo 1563479 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B9514543 : Blo 1563479 9514543 := bstep (se 1 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 9514543 = 14271815) B14271815
theorem B5279471 : Blo 1563479 5279471 := bstep (se 1 (by rfl) ⟨3959603, by rfl⟩ : syracuseStep 5279471 = 7919207) B7919207
theorem B114151355 : Blo 1563479 114151355 := bstep (se 1 (by rfl) ⟨85613516, by rfl⟩ : syracuseStep 114151355 = 171227033) B171227033
theorem B5279687 : Blo 1563479 5279687 := bstep (se 1 (by rfl) ⟨3959765, by rfl⟩ : syracuseStep 5279687 = 7919531) B7919531
theorem B5010299 : Blo 1563479 5010299 := bstep (se 1 (by rfl) ⟨3757724, by rfl⟩ : syracuseStep 5010299 = 7515449) B7515449
theorem B3519935 : Blo 1563479 3519935 := bstep (se 1 (by rfl) ⟨2639951, by rfl⟩ : syracuseStep 3519935 = 5279903) B5279903
theorem B24418061 : Blo 1563479 24418061 := bstep (se 3 (by rfl) ⟨4578386, by rfl⟩ : syracuseStep 24418061 = 9156773) B9156773
theorem B4454783 : Blo 1563479 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B5078009 : Blo 1563479 5078009 := bstep (se 2 (by rfl) ⟨1904253, by rfl⟩ : syracuseStep 5078009 = 3808507) B3808507
theorem B487775267 : Blo 1563479 487775267 := bstep (se 1 (by rfl) ⟨365831450, by rfl⟩ : syracuseStep 487775267 = 731662901) B731662901
theorem B1563803 : Blo 1563479 1563803 := bstep (se 1 (by rfl) ⟨1172852, by rfl⟩ : syracuseStep 1563803 = 2345705) B2345705
theorem B21125947729 : Blo 1563479 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B16278707 : Blo 1563479 16278707 := bstep (se 1 (by rfl) ⟨12209030, by rfl⟩ : syracuseStep 16278707 = 24418061) B24418061
theorem B83510527 : Blo 1563479 83510527 := bstep (se 1 (by rfl) ⟨62632895, by rfl⟩ : syracuseStep 83510527 = 125265791) B125265791
theorem B11273575 : Blo 1563479 11273575 := bstep (se 1 (by rfl) ⟨8455181, by rfl⟩ : syracuseStep 11273575 = 16910363) B16910363
theorem B88147757 : Blo 1563479 88147757 := bstep (se 3 (by rfl) ⟨16527704, by rfl⟩ : syracuseStep 88147757 = 33055409) B33055409
theorem B325183511 : Blo 1563479 325183511 := bstep (se 1 (by rfl) ⟨243887633, by rfl⟩ : syracuseStep 325183511 = 487775267) B487775267
theorem B7915643 : Blo 1563479 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B2346623 : Blo 1563479 2346623 := bstep (se 1 (by rfl) ⟨1759967, by rfl⟩ : syracuseStep 2346623 = 3519935) B3519935
theorem B2969855 : Blo 1563479 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B12686057 : Blo 1563479 12686057 := bstep (se 2 (by rfl) ⟨4757271, by rfl⟩ : syracuseStep 12686057 = 9514543) B9514543
theorem B3519647 : Blo 1563479 3519647 := bstep (se 1 (by rfl) ⟨2639735, by rfl⟩ : syracuseStep 3519647 = 5279471) B5279471
theorem B76100903 : Blo 1563479 76100903 := bstep (se 1 (by rfl) ⟨57075677, by rfl⟩ : syracuseStep 76100903 = 114151355) B114151355
theorem B3519791 : Blo 1563479 3519791 := bstep (se 1 (by rfl) ⟨2639843, by rfl⟩ : syracuseStep 3519791 = 5279687) B5279687
theorem B3340199 : Blo 1563479 3340199 := bstep (se 1 (by rfl) ⟨2505149, by rfl⟩ : syracuseStep 3340199 = 5010299) B5010299
theorem B17373779 : Blo 1563479 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B65117159 : Blo 1563479 65117159 := bstep (se 1 (by rfl) ⟨48837869, by rfl⟩ : syracuseStep 65117159 = 97675739) B97675739
theorem B13541357 : Blo 1563479 13541357 := bstep (se 3 (by rfl) ⟨2539004, by rfl⟩ : syracuseStep 13541357 = 5078009) B5078009
theorem B28167930305 : Blo 1563479 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B50733935 : Blo 1563479 50733935 := bstep (se 1 (by rfl) ⟨38050451, by rfl⟩ : syracuseStep 50733935 = 76100903) B76100903
theorem B5277095 : Blo 1563479 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B111347369 : Blo 1563479 111347369 := bstep (se 2 (by rfl) ⟨41755263, by rfl⟩ : syracuseStep 111347369 = 83510527) B83510527
theorem B43411439 : Blo 1563479 43411439 := bstep (se 1 (by rfl) ⟨32558579, by rfl⟩ : syracuseStep 43411439 = 65117159) B65117159
theorem B8457371 : Blo 1563479 8457371 := bstep (se 1 (by rfl) ⟨6343028, by rfl⟩ : syracuseStep 8457371 = 12686057) B12686057
theorem B2346431 : Blo 1563479 2346431 := bstep (se 1 (by rfl) ⟨1759823, by rfl⟩ : syracuseStep 2346431 = 3519647) B3519647
theorem B2346527 : Blo 1563479 2346527 := bstep (se 1 (by rfl) ⟨1759895, by rfl⟩ : syracuseStep 2346527 = 3519791) B3519791
theorem B58765171 : Blo 1563479 58765171 := bstep (se 1 (by rfl) ⟨44073878, by rfl⟩ : syracuseStep 58765171 = 88147757) B88147757
theorem B216789007 : Blo 1563479 216789007 := bstep (se 1 (by rfl) ⟨162591755, by rfl⟩ : syracuseStep 216789007 = 325183511) B325183511
theorem B1979903 : Blo 1563479 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B10852471 : Blo 1563479 10852471 := bstep (se 1 (by rfl) ⟨8139353, by rfl⟩ : syracuseStep 10852471 = 16278707) B16278707
theorem B2226799 : Blo 1563479 2226799 := bstep (se 1 (by rfl) ⟨1670099, by rfl⟩ : syracuseStep 2226799 = 3340199) B3340199
theorem B11582519 : Blo 1563479 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B15031433 : Blo 1563479 15031433 := bstep (se 2 (by rfl) ⟨5636787, by rfl⟩ : syracuseStep 15031433 = 11273575) B11273575
theorem B1564415 : Blo 1563479 1564415 := bstep (se 1 (by rfl) ⟨1173311, by rfl⟩ : syracuseStep 1564415 = 2346623) B2346623
theorem B9027571 : Blo 1563479 9027571 := bstep (se 1 (by rfl) ⟨6770678, by rfl⟩ : syracuseStep 9027571 = 13541357) B13541357
theorem B18778620203 : Blo 1563479 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B10020955 : Blo 1563479 10020955 := bstep (se 1 (by rfl) ⟨7515716, by rfl⟩ : syracuseStep 10020955 = 15031433) B15031433
theorem B5638247 : Blo 1563479 5638247 := bstep (se 1 (by rfl) ⟨4228685, by rfl⟩ : syracuseStep 5638247 = 8457371) B8457371
theorem B12036761 : Blo 1563479 12036761 := bstep (se 2 (by rfl) ⟨4513785, by rfl⟩ : syracuseStep 12036761 = 9027571) B9027571
theorem B14469961 : Blo 1563479 14469961 := bstep (se 2 (by rfl) ⟨5426235, by rfl⟩ : syracuseStep 14469961 = 10852471) B10852471
theorem B123546869 : Blo 1563479 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B2969065 : Blo 1563479 2969065 := bstep (se 2 (by rfl) ⟨1113399, by rfl⟩ : syracuseStep 2969065 = 2226799) B2226799
theorem B3518063 : Blo 1563479 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B74231579 : Blo 1563479 74231579 := bstep (se 1 (by rfl) ⟨55673684, by rfl⟩ : syracuseStep 74231579 = 111347369) B111347369
theorem B5279741 : Blo 1563479 5279741 := bstep (se 3 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 5279741 = 1979903) B1979903
theorem B78353561 : Blo 1563479 78353561 := bstep (se 2 (by rfl) ⟨29382585, by rfl⟩ : syracuseStep 78353561 = 58765171) B58765171
theorem B289052009 : Blo 1563479 289052009 := bstep (se 2 (by rfl) ⟨108394503, by rfl⟩ : syracuseStep 289052009 = 216789007) B216789007
theorem B33822623 : Blo 1563479 33822623 := bstep (se 1 (by rfl) ⟨25366967, by rfl⟩ : syracuseStep 33822623 = 50733935) B50733935
theorem B28940959 : Blo 1563479 28940959 := bstep (se 1 (by rfl) ⟨21705719, by rfl⟩ : syracuseStep 28940959 = 43411439) B43411439
theorem B1564287 : Blo 1563479 1564287 := bstep (se 1 (by rfl) ⟨1173215, by rfl⟩ : syracuseStep 1564287 = 2346431) B2346431
theorem B1564351 : Blo 1563479 1564351 := bstep (se 1 (by rfl) ⟨1173263, by rfl⟩ : syracuseStep 1564351 = 2346527) B2346527
theorem B13361273 : Blo 1563479 13361273 := bstep (se 2 (by rfl) ⟨5010477, by rfl⟩ : syracuseStep 13361273 = 10020955) B10020955
theorem B12519080135 : Blo 1563479 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B192701339 : Blo 1563479 192701339 := bstep (se 1 (by rfl) ⟨144526004, by rfl⟩ : syracuseStep 192701339 = 289052009) B289052009
theorem B19293281 : Blo 1563479 19293281 := bstep (se 2 (by rfl) ⟨7234980, by rfl⟩ : syracuseStep 19293281 = 14469961) B14469961
theorem B3958753 : Blo 1563479 3958753 := bstep (se 2 (by rfl) ⟨1484532, by rfl⟩ : syracuseStep 3958753 = 2969065) B2969065
theorem B82364579 : Blo 1563479 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B2345375 : Blo 1563479 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B52235707 : Blo 1563479 52235707 := bstep (se 1 (by rfl) ⟨39176780, by rfl⟩ : syracuseStep 52235707 = 78353561) B78353561
theorem B22548415 : Blo 1563479 22548415 := bstep (se 1 (by rfl) ⟨16911311, by rfl⟩ : syracuseStep 22548415 = 33822623) B33822623
theorem B8024507 : Blo 1563479 8024507 := bstep (se 1 (by rfl) ⟨6018380, by rfl⟩ : syracuseStep 8024507 = 12036761) B12036761
theorem B3519827 : Blo 1563479 3519827 := bstep (se 1 (by rfl) ⟨2639870, by rfl⟩ : syracuseStep 3519827 = 5279741) B5279741
theorem B154351781 : Blo 1563479 154351781 := bstep (se 4 (by rfl) ⟨14470479, by rfl⟩ : syracuseStep 154351781 = 28940959) B28940959
theorem B3758831 : Blo 1563479 3758831 := bstep (se 1 (by rfl) ⟨2819123, by rfl⟩ : syracuseStep 3758831 = 5638247) B5638247
theorem B197950877 : Blo 1563479 197950877 := bstep (se 3 (by rfl) ⟨37115789, by rfl⟩ : syracuseStep 197950877 = 74231579) B74231579
theorem B5349671 : Blo 1563479 5349671 := bstep (se 1 (by rfl) ⟨4012253, by rfl⟩ : syracuseStep 5349671 = 8024507) B8024507
theorem B128467559 : Blo 1563479 128467559 := bstep (se 1 (by rfl) ⟨96350669, by rfl⟩ : syracuseStep 128467559 = 192701339) B192701339
theorem B12862187 : Blo 1563479 12862187 := bstep (se 1 (by rfl) ⟨9646640, by rfl⟩ : syracuseStep 12862187 = 19293281) B19293281
theorem B102901187 : Blo 1563479 102901187 := bstep (se 1 (by rfl) ⟨77175890, by rfl⟩ : syracuseStep 102901187 = 154351781) B154351781
theorem B131967251 : Blo 1563479 131967251 := bstep (se 1 (by rfl) ⟨98975438, by rfl⟩ : syracuseStep 131967251 = 197950877) B197950877
theorem B5278337 : Blo 1563479 5278337 := bstep (se 2 (by rfl) ⟨1979376, by rfl⟩ : syracuseStep 5278337 = 3958753) B3958753
theorem B8907515 : Blo 1563479 8907515 := bstep (se 1 (by rfl) ⟨6680636, by rfl⟩ : syracuseStep 8907515 = 13361273) B13361273
theorem B8346053423 : Blo 1563479 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B2346551 : Blo 1563479 2346551 := bstep (se 1 (by rfl) ⟨1759913, by rfl⟩ : syracuseStep 2346551 = 3519827) B3519827
theorem B54909719 : Blo 1563479 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B1563583 : Blo 1563479 1563583 := bstep (se 1 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 1563583 = 2345375) B2345375
theorem B2505887 : Blo 1563479 2505887 := bstep (se 1 (by rfl) ⟨1879415, by rfl⟩ : syracuseStep 2505887 = 3758831) B3758831
theorem B69647609 : Blo 1563479 69647609 := bstep (se 2 (by rfl) ⟨26117853, by rfl⟩ : syracuseStep 69647609 = 52235707) B52235707
theorem B30064553 : Blo 1563479 30064553 := bstep (se 2 (by rfl) ⟨11274207, by rfl⟩ : syracuseStep 30064553 = 22548415) B22548415
theorem B68600791 : Blo 1563479 68600791 := bstep (se 1 (by rfl) ⟨51450593, by rfl⟩ : syracuseStep 68600791 = 102901187) B102901187
theorem B22256142461 : Blo 1563479 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B3566447 : Blo 1563479 3566447 := bstep (se 1 (by rfl) ⟨2674835, by rfl⟩ : syracuseStep 3566447 = 5349671) B5349671
theorem B87978167 : Blo 1563479 87978167 := bstep (se 1 (by rfl) ⟨65983625, by rfl⟩ : syracuseStep 87978167 = 131967251) B131967251
theorem B3518891 : Blo 1563479 3518891 := bstep (se 1 (by rfl) ⟨2639168, by rfl⟩ : syracuseStep 3518891 = 5278337) B5278337
theorem B36606479 : Blo 1563479 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B137196661 : Blo 1563479 137196661 := bstep (se 5 (by rfl) ⟨6431093, by rfl⟩ : syracuseStep 137196661 = 12862187) B12862187
theorem B20043035 : Blo 1563479 20043035 := bstep (se 1 (by rfl) ⟨15032276, by rfl⟩ : syracuseStep 20043035 = 30064553) B30064553
theorem B85645039 : Blo 1563479 85645039 := bstep (se 1 (by rfl) ⟨64233779, by rfl⟩ : syracuseStep 85645039 = 128467559) B128467559
theorem B5938343 : Blo 1563479 5938343 := bstep (se 1 (by rfl) ⟨4453757, by rfl⟩ : syracuseStep 5938343 = 8907515) B8907515
theorem B1670591 : Blo 1563479 1670591 := bstep (se 1 (by rfl) ⟨1252943, by rfl⟩ : syracuseStep 1670591 = 2505887) B2505887
theorem B46431739 : Blo 1563479 46431739 := bstep (se 1 (by rfl) ⟨34823804, by rfl⟩ : syracuseStep 46431739 = 69647609) B69647609
theorem B1564367 : Blo 1563479 1564367 := bstep (se 1 (by rfl) ⟨1173275, by rfl⟩ : syracuseStep 1564367 = 2346551) B2346551
theorem B13362023 : Blo 1563479 13362023 := bstep (se 1 (by rfl) ⟨10021517, by rfl⟩ : syracuseStep 13362023 = 20043035) B20043035
theorem B97617277 : Blo 1563479 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B182928881 : Blo 1563479 182928881 := bstep (se 2 (by rfl) ⟨68598330, by rfl⟩ : syracuseStep 182928881 = 137196661) B137196661
theorem B2377631 : Blo 1563479 2377631 := bstep (se 1 (by rfl) ⟨1783223, by rfl⟩ : syracuseStep 2377631 = 3566447) B3566447
theorem B61908985 : Blo 1563479 61908985 := bstep (se 2 (by rfl) ⟨23215869, by rfl⟩ : syracuseStep 61908985 = 46431739) B46431739
theorem B3958895 : Blo 1563479 3958895 := bstep (se 1 (by rfl) ⟨2969171, by rfl⟩ : syracuseStep 3958895 = 5938343) B5938343
theorem B2345927 : Blo 1563479 2345927 := bstep (se 1 (by rfl) ⟨1759445, by rfl⟩ : syracuseStep 2345927 = 3518891) B3518891
theorem B91467721 : Blo 1563479 91467721 := bstep (se 2 (by rfl) ⟨34300395, by rfl⟩ : syracuseStep 91467721 = 68600791) B68600791
theorem B14837428307 : Blo 1563479 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B114193385 : Blo 1563479 114193385 := bstep (se 2 (by rfl) ⟨42822519, by rfl⟩ : syracuseStep 114193385 = 85645039) B85645039
theorem B58652111 : Blo 1563479 58652111 := bstep (se 1 (by rfl) ⟨43989083, by rfl⟩ : syracuseStep 58652111 = 87978167) B87978167
theorem B4454909 : Blo 1563479 4454909 := bstep (se 3 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 4454909 = 1670591) B1670591
theorem B9891618871 : Blo 1563479 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B76128923 : Blo 1563479 76128923 := bstep (se 1 (by rfl) ⟨57096692, by rfl⟩ : syracuseStep 76128923 = 114193385) B114193385
theorem B2639263 : Blo 1563479 2639263 := bstep (se 1 (by rfl) ⟨1979447, by rfl⟩ : syracuseStep 2639263 = 3958895) B3958895
theorem B121956961 : Blo 1563479 121956961 := bstep (se 2 (by rfl) ⟨45733860, by rfl⟩ : syracuseStep 121956961 = 91467721) B91467721
theorem B82545313 : Blo 1563479 82545313 := bstep (se 2 (by rfl) ⟨30954492, by rfl⟩ : syracuseStep 82545313 = 61908985) B61908985
theorem B8908015 : Blo 1563479 8908015 := bstep (se 1 (by rfl) ⟨6681011, by rfl⟩ : syracuseStep 8908015 = 13362023) B13362023
theorem B156405629 : Blo 1563479 156405629 := bstep (se 3 (by rfl) ⟨29326055, by rfl⟩ : syracuseStep 156405629 = 58652111) B58652111
theorem B2969939 : Blo 1563479 2969939 := bstep (se 1 (by rfl) ⟨2227454, by rfl⟩ : syracuseStep 2969939 = 4454909) B4454909
theorem B121952587 : Blo 1563479 121952587 := bstep (se 1 (by rfl) ⟨91464440, by rfl⟩ : syracuseStep 121952587 = 182928881) B182928881
theorem B1563951 : Blo 1563479 1563951 := bstep (se 1 (by rfl) ⟨1172963, by rfl⟩ : syracuseStep 1563951 = 2345927) B2345927
theorem B520625477 : Blo 1563479 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B6340349 : Blo 1563479 6340349 := bstep (se 3 (by rfl) ⟨1188815, by rfl⟩ : syracuseStep 6340349 = 2377631) B2377631
theorem B13188825161 : Blo 1563479 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B162603449 : Blo 1563479 162603449 := bstep (se 2 (by rfl) ⟨60976293, by rfl⟩ : syracuseStep 162603449 = 121952587) B121952587
theorem B110060417 : Blo 1563479 110060417 := bstep (se 2 (by rfl) ⟨41272656, by rfl⟩ : syracuseStep 110060417 = 82545313) B82545313
theorem B104270419 : Blo 1563479 104270419 := bstep (se 1 (by rfl) ⟨78202814, by rfl⟩ : syracuseStep 104270419 = 156405629) B156405629
theorem B203010461 : Blo 1563479 203010461 := bstep (se 3 (by rfl) ⟨38064461, by rfl⟩ : syracuseStep 203010461 = 76128923) B76128923
theorem B3519017 : Blo 1563479 3519017 := bstep (se 2 (by rfl) ⟨1319631, by rfl⟩ : syracuseStep 3519017 = 2639263) B2639263
theorem B347083651 : Blo 1563479 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B1979959 : Blo 1563479 1979959 := bstep (se 1 (by rfl) ⟨1484969, by rfl⟩ : syracuseStep 1979959 = 2969939) B2969939
theorem B162609281 : Blo 1563479 162609281 := bstep (se 2 (by rfl) ⟨60978480, by rfl⟩ : syracuseStep 162609281 = 121956961) B121956961
theorem B11877353 : Blo 1563479 11877353 := bstep (se 2 (by rfl) ⟨4454007, by rfl⟩ : syracuseStep 11877353 = 8908015) B8908015
theorem B4226899 : Blo 1563479 4226899 := bstep (se 1 (by rfl) ⟨3170174, by rfl⟩ : syracuseStep 4226899 = 6340349) B6340349
theorem B135340307 : Blo 1563479 135340307 := bstep (se 1 (by rfl) ⟨101505230, by rfl⟩ : syracuseStep 135340307 = 203010461) B203010461
theorem B139027225 : Blo 1563479 139027225 := bstep (se 2 (by rfl) ⟨52135209, by rfl⟩ : syracuseStep 139027225 = 104270419) B104270419
theorem B108406187 : Blo 1563479 108406187 := bstep (se 1 (by rfl) ⟨81304640, by rfl⟩ : syracuseStep 108406187 = 162609281) B162609281
theorem B2639945 : Blo 1563479 2639945 := bstep (se 2 (by rfl) ⟨989979, by rfl⟩ : syracuseStep 2639945 = 1979959) B1979959
theorem B8792550107 : Blo 1563479 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B2346011 : Blo 1563479 2346011 := bstep (se 1 (by rfl) ⟨1759508, by rfl⟩ : syracuseStep 2346011 = 3519017) B3519017
theorem B462778201 : Blo 1563479 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B7918235 : Blo 1563479 7918235 := bstep (se 1 (by rfl) ⟨5938676, by rfl⟩ : syracuseStep 7918235 = 11877353) B11877353
theorem B108402299 : Blo 1563479 108402299 := bstep (se 1 (by rfl) ⟨81301724, by rfl⟩ : syracuseStep 108402299 = 162603449) B162603449
theorem B73373611 : Blo 1563479 73373611 := bstep (se 1 (by rfl) ⟨55030208, by rfl⟩ : syracuseStep 73373611 = 110060417) B110060417
theorem B5635865 : Blo 1563479 5635865 := bstep (se 2 (by rfl) ⟨2113449, by rfl⟩ : syracuseStep 5635865 = 4226899) B4226899
theorem B90226871 : Blo 1563479 90226871 := bstep (se 1 (by rfl) ⟨67670153, by rfl⟩ : syracuseStep 90226871 = 135340307) B135340307
theorem B72270791 : Blo 1563479 72270791 := bstep (se 1 (by rfl) ⟨54203093, by rfl⟩ : syracuseStep 72270791 = 108406187) B108406187
theorem B185369633 : Blo 1563479 185369633 := bstep (se 2 (by rfl) ⟨69513612, by rfl⟩ : syracuseStep 185369633 = 139027225) B139027225
theorem B97831481 : Blo 1563479 97831481 := bstep (se 2 (by rfl) ⟨36686805, by rfl⟩ : syracuseStep 97831481 = 73373611) B73373611
theorem B5278823 : Blo 1563479 5278823 := bstep (se 1 (by rfl) ⟨3959117, by rfl⟩ : syracuseStep 5278823 = 7918235) B7918235
theorem B5861700071 : Blo 1563479 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B15028973 : Blo 1563479 15028973 := bstep (se 3 (by rfl) ⟨2817932, by rfl⟩ : syracuseStep 15028973 = 5635865) B5635865
theorem B72268199 : Blo 1563479 72268199 := bstep (se 1 (by rfl) ⟨54201149, by rfl⟩ : syracuseStep 72268199 = 108402299) B108402299
theorem B1759963 : Blo 1563479 1759963 := bstep (se 1 (by rfl) ⟨1319972, by rfl⟩ : syracuseStep 1759963 = 2639945) B2639945
theorem B1564007 : Blo 1563479 1564007 := bstep (se 1 (by rfl) ⟨1173005, by rfl⟩ : syracuseStep 1564007 = 2346011) B2346011
theorem B617037601 : Blo 1563479 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B10019315 : Blo 1563479 10019315 := bstep (se 1 (by rfl) ⟨7514486, by rfl⟩ : syracuseStep 10019315 = 15028973) B15028973
theorem B48178799 : Blo 1563479 48178799 := bstep (se 1 (by rfl) ⟨36134099, by rfl⟩ : syracuseStep 48178799 = 72268199) B72268199
theorem B822716801 : Blo 1563479 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B3907800047 : Blo 1563479 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B48180527 : Blo 1563479 48180527 := bstep (se 1 (by rfl) ⟨36135395, by rfl⟩ : syracuseStep 48180527 = 72270791) B72270791
theorem B123579755 : Blo 1563479 123579755 := bstep (se 1 (by rfl) ⟨92684816, by rfl⟩ : syracuseStep 123579755 = 185369633) B185369633
theorem B2346617 : Blo 1563479 2346617 := bstep (se 2 (by rfl) ⟨879981, by rfl⟩ : syracuseStep 2346617 = 1759963) B1759963
theorem B3519215 : Blo 1563479 3519215 := bstep (se 1 (by rfl) ⟨2639411, by rfl⟩ : syracuseStep 3519215 = 5278823) B5278823
theorem B60151247 : Blo 1563479 60151247 := bstep (se 1 (by rfl) ⟨45113435, by rfl⟩ : syracuseStep 60151247 = 90226871) B90226871
theorem B1043535797 : Blo 1563479 1043535797 := bstep (se 5 (by rfl) ⟨48915740, by rfl⟩ : syracuseStep 1043535797 = 97831481) B97831481
theorem B40100831 : Blo 1563479 40100831 := bstep (se 1 (by rfl) ⟨30075623, by rfl⟩ : syracuseStep 40100831 = 60151247) B60151247
theorem B695690531 : Blo 1563479 695690531 := bstep (se 1 (by rfl) ⟨521767898, by rfl⟩ : syracuseStep 695690531 = 1043535797) B1043535797
theorem B6679543 : Blo 1563479 6679543 := bstep (se 1 (by rfl) ⟨5009657, by rfl⟩ : syracuseStep 6679543 = 10019315) B10019315
theorem B2346143 : Blo 1563479 2346143 := bstep (se 1 (by rfl) ⟨1759607, by rfl⟩ : syracuseStep 2346143 = 3519215) B3519215
theorem B2605200031 : Blo 1563479 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B32119199 : Blo 1563479 32119199 := bstep (se 1 (by rfl) ⟨24089399, by rfl⟩ : syracuseStep 32119199 = 48178799) B48178799
theorem B548477867 : Blo 1563479 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B32120351 : Blo 1563479 32120351 := bstep (se 1 (by rfl) ⟨24090263, by rfl⟩ : syracuseStep 32120351 = 48180527) B48180527
theorem B82386503 : Blo 1563479 82386503 := bstep (se 1 (by rfl) ⟨61789877, by rfl⟩ : syracuseStep 82386503 = 123579755) B123579755
theorem B1564411 : Blo 1563479 1564411 := bstep (se 1 (by rfl) ⟨1173308, by rfl⟩ : syracuseStep 1564411 = 2346617) B2346617
theorem B8906057 : Blo 1563479 8906057 := bstep (se 2 (by rfl) ⟨3339771, by rfl⟩ : syracuseStep 8906057 = 6679543) B6679543
theorem B365651911 : Blo 1563479 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B26733887 : Blo 1563479 26733887 := bstep (se 1 (by rfl) ⟨20050415, by rfl⟩ : syracuseStep 26733887 = 40100831) B40100831
theorem B463793687 : Blo 1563479 463793687 := bstep (se 1 (by rfl) ⟨347845265, by rfl⟩ : syracuseStep 463793687 = 695690531) B695690531
theorem B3473600041 : Blo 1563479 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B54924335 : Blo 1563479 54924335 := bstep (se 1 (by rfl) ⟨41193251, by rfl⟩ : syracuseStep 54924335 = 82386503) B82386503
theorem B21412799 : Blo 1563479 21412799 := bstep (se 1 (by rfl) ⟨16059599, by rfl⟩ : syracuseStep 21412799 = 32119199) B32119199
theorem B1564095 : Blo 1563479 1564095 := bstep (se 1 (by rfl) ⟨1173071, by rfl⟩ : syracuseStep 1564095 = 2346143) B2346143
theorem B21413567 : Blo 1563479 21413567 := bstep (se 1 (by rfl) ⟨16060175, by rfl⟩ : syracuseStep 21413567 = 32120351) B32120351
theorem B14275199 : Blo 1563479 14275199 := bstep (se 1 (by rfl) ⟨10706399, by rfl⟩ : syracuseStep 14275199 = 21412799) B21412799
theorem B4631466721 : Blo 1563479 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B17822591 : Blo 1563479 17822591 := bstep (se 1 (by rfl) ⟨13366943, by rfl⟩ : syracuseStep 17822591 = 26733887) B26733887
theorem B309195791 : Blo 1563479 309195791 := bstep (se 1 (by rfl) ⟨231896843, by rfl⟩ : syracuseStep 309195791 = 463793687) B463793687
theorem B14275711 : Blo 1563479 14275711 := bstep (se 1 (by rfl) ⟨10706783, by rfl⟩ : syracuseStep 14275711 = 21413567) B21413567
theorem B487535881 : Blo 1563479 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B36616223 : Blo 1563479 36616223 := bstep (se 1 (by rfl) ⟨27462167, by rfl⟩ : syracuseStep 36616223 = 54924335) B54924335
theorem B5937371 : Blo 1563479 5937371 := bstep (se 1 (by rfl) ⟨4453028, by rfl⟩ : syracuseStep 5937371 = 8906057) B8906057
theorem B3958247 : Blo 1563479 3958247 := bstep (se 1 (by rfl) ⟨2968685, by rfl⟩ : syracuseStep 3958247 = 5937371) B5937371
theorem B11881727 : Blo 1563479 11881727 := bstep (se 1 (by rfl) ⟨8911295, by rfl⟩ : syracuseStep 11881727 = 17822591) B17822591
theorem B206130527 : Blo 1563479 206130527 := bstep (se 1 (by rfl) ⟨154597895, by rfl⟩ : syracuseStep 206130527 = 309195791) B309195791
theorem B6175288961 : Blo 1563479 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B19034281 : Blo 1563479 19034281 := bstep (se 2 (by rfl) ⟨7137855, by rfl⟩ : syracuseStep 19034281 = 14275711) B14275711
theorem B650047841 : Blo 1563479 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B9516799 : Blo 1563479 9516799 := bstep (se 1 (by rfl) ⟨7137599, by rfl⟩ : syracuseStep 9516799 = 14275199) B14275199
theorem B24410815 : Blo 1563479 24410815 := bstep (se 1 (by rfl) ⟨18308111, by rfl⟩ : syracuseStep 24410815 = 36616223) B36616223
theorem B25379041 : Blo 1563479 25379041 := bstep (se 2 (by rfl) ⟨9517140, by rfl⟩ : syracuseStep 25379041 = 19034281) B19034281
theorem B433365227 : Blo 1563479 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B2638831 : Blo 1563479 2638831 := bstep (se 1 (by rfl) ⟨1979123, by rfl⟩ : syracuseStep 2638831 = 3958247) B3958247
theorem B4116859307 : Blo 1563479 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B130191013 : Blo 1563479 130191013 := bstep (se 4 (by rfl) ⟨12205407, by rfl⟩ : syracuseStep 130191013 = 24410815) B24410815
theorem B7921151 : Blo 1563479 7921151 := bstep (se 1 (by rfl) ⟨5940863, by rfl⟩ : syracuseStep 7921151 = 11881727) B11881727
theorem B137420351 : Blo 1563479 137420351 := bstep (se 1 (by rfl) ⟨103065263, by rfl⟩ : syracuseStep 137420351 = 206130527) B206130527
theorem B12689065 : Blo 1563479 12689065 := bstep (se 2 (by rfl) ⟨4758399, by rfl⟩ : syracuseStep 12689065 = 9516799) B9516799
theorem B16918753 : Blo 1563479 16918753 := bstep (se 2 (by rfl) ⟨6344532, by rfl⟩ : syracuseStep 16918753 = 12689065) B12689065
theorem B91613567 : Blo 1563479 91613567 := bstep (se 1 (by rfl) ⟨68710175, by rfl⟩ : syracuseStep 91613567 = 137420351) B137420351
theorem B288910151 : Blo 1563479 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B3518441 : Blo 1563479 3518441 := bstep (se 2 (by rfl) ⟨1319415, by rfl⟩ : syracuseStep 3518441 = 2638831) B2638831
theorem B5280767 : Blo 1563479 5280767 := bstep (se 1 (by rfl) ⟨3960575, by rfl⟩ : syracuseStep 5280767 = 7921151) B7921151
theorem B33838721 : Blo 1563479 33838721 := bstep (se 2 (by rfl) ⟨12689520, by rfl⟩ : syracuseStep 33838721 = 25379041) B25379041
theorem B2744572871 : Blo 1563479 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B173588017 : Blo 1563479 173588017 := bstep (se 2 (by rfl) ⟨65095506, by rfl⟩ : syracuseStep 173588017 = 130191013) B130191013
theorem B231450689 : Blo 1563479 231450689 := bstep (se 2 (by rfl) ⟨86794008, by rfl⟩ : syracuseStep 231450689 = 173588017) B173588017
theorem B2345627 : Blo 1563479 2345627 := bstep (se 1 (by rfl) ⟨1759220, by rfl⟩ : syracuseStep 2345627 = 3518441) B3518441
theorem B61075711 : Blo 1563479 61075711 := bstep (se 1 (by rfl) ⟨45806783, by rfl⟩ : syracuseStep 61075711 = 91613567) B91613567
theorem B192606767 : Blo 1563479 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B22558337 : Blo 1563479 22558337 := bstep (se 2 (by rfl) ⟨8459376, by rfl⟩ : syracuseStep 22558337 = 16918753) B16918753
theorem B3520511 : Blo 1563479 3520511 := bstep (se 1 (by rfl) ⟨2640383, by rfl⟩ : syracuseStep 3520511 = 5280767) B5280767
theorem B22559147 : Blo 1563479 22559147 := bstep (se 1 (by rfl) ⟨16919360, by rfl⟩ : syracuseStep 22559147 = 33838721) B33838721
theorem B1829715247 : Blo 1563479 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B2439620329 : Blo 1563479 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B128404511 : Blo 1563479 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B2347007 : Blo 1563479 2347007 := bstep (se 1 (by rfl) ⟨1760255, by rfl⟩ : syracuseStep 2347007 = 3520511) B3520511
theorem B154300459 : Blo 1563479 154300459 := bstep (se 1 (by rfl) ⟨115725344, by rfl⟩ : syracuseStep 154300459 = 231450689) B231450689
theorem B81434281 : Blo 1563479 81434281 := bstep (se 2 (by rfl) ⟨30537855, by rfl⟩ : syracuseStep 81434281 = 61075711) B61075711
theorem B15038891 : Blo 1563479 15038891 := bstep (se 1 (by rfl) ⟨11279168, by rfl⟩ : syracuseStep 15038891 = 22558337) B22558337
theorem B15039431 : Blo 1563479 15039431 := bstep (se 1 (by rfl) ⟨11279573, by rfl⟩ : syracuseStep 15039431 = 22559147) B22559147
theorem B1563751 : Blo 1563479 1563751 := bstep (se 1 (by rfl) ⟨1172813, by rfl⟩ : syracuseStep 1563751 = 2345627) B2345627
theorem B205733945 : Blo 1563479 205733945 := bstep (se 2 (by rfl) ⟨77150229, by rfl⟩ : syracuseStep 205733945 = 154300459) B154300459
theorem B108579041 : Blo 1563479 108579041 := bstep (se 2 (by rfl) ⟨40717140, by rfl⟩ : syracuseStep 108579041 = 81434281) B81434281
theorem B85603007 : Blo 1563479 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B3252827105 : Blo 1563479 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B10025927 : Blo 1563479 10025927 := bstep (se 1 (by rfl) ⟨7519445, by rfl⟩ : syracuseStep 10025927 = 15038891) B15038891
theorem B10026287 : Blo 1563479 10026287 := bstep (se 1 (by rfl) ⟨7519715, by rfl⟩ : syracuseStep 10026287 = 15039431) B15039431
theorem B1564671 : Blo 1563479 1564671 := bstep (se 1 (by rfl) ⟨1173503, by rfl⟩ : syracuseStep 1564671 = 2347007) B2347007
theorem B72386027 : Blo 1563479 72386027 := bstep (se 1 (by rfl) ⟨54289520, by rfl⟩ : syracuseStep 72386027 = 108579041) B108579041
theorem B57068671 : Blo 1563479 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B137155963 : Blo 1563479 137155963 := bstep (se 1 (by rfl) ⟨102866972, by rfl⟩ : syracuseStep 137155963 = 205733945) B205733945
theorem B2168551403 : Blo 1563479 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B6683951 : Blo 1563479 6683951 := bstep (se 1 (by rfl) ⟨5012963, by rfl⟩ : syracuseStep 6683951 = 10025927) B10025927
theorem B6684191 : Blo 1563479 6684191 := bstep (se 1 (by rfl) ⟨5013143, by rfl⟩ : syracuseStep 6684191 = 10026287) B10026287
theorem B1445700935 : Blo 1563479 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B76091561 : Blo 1563479 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B182874617 : Blo 1563479 182874617 := bstep (se 2 (by rfl) ⟨68577981, by rfl⟩ : syracuseStep 182874617 = 137155963) B137155963
theorem B48257351 : Blo 1563479 48257351 := bstep (se 1 (by rfl) ⟨36193013, by rfl⟩ : syracuseStep 48257351 = 72386027) B72386027
theorem B4455967 : Blo 1563479 4455967 := bstep (se 1 (by rfl) ⟨3341975, by rfl⟩ : syracuseStep 4455967 = 6683951) B6683951
theorem B4456127 : Blo 1563479 4456127 := bstep (se 1 (by rfl) ⟨3342095, by rfl⟩ : syracuseStep 4456127 = 6684191) B6684191
theorem B32171567 : Blo 1563479 32171567 := bstep (se 1 (by rfl) ⟨24128675, by rfl⟩ : syracuseStep 32171567 = 48257351) B48257351
theorem B5941289 : Blo 1563479 5941289 := bstep (se 2 (by rfl) ⟨2227983, by rfl⟩ : syracuseStep 5941289 = 4455967) B4455967
theorem B50727707 : Blo 1563479 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B121916411 : Blo 1563479 121916411 := bstep (se 1 (by rfl) ⟨91437308, by rfl⟩ : syracuseStep 121916411 = 182874617) B182874617
theorem B963800623 : Blo 1563479 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B2970751 : Blo 1563479 2970751 := bstep (se 1 (by rfl) ⟨2228063, by rfl⟩ : syracuseStep 2970751 = 4456127) B4456127
theorem B33818471 : Blo 1563479 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B5140269989 : Blo 1563479 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B3960859 : Blo 1563479 3960859 := bstep (se 1 (by rfl) ⟨2970644, by rfl⟩ : syracuseStep 3960859 = 5941289) B5941289
theorem B85790845 : Blo 1563479 85790845 := bstep (se 3 (by rfl) ⟨16085783, by rfl⟩ : syracuseStep 85790845 = 32171567) B32171567
theorem B3961001 : Blo 1563479 3961001 := bstep (se 2 (by rfl) ⟨1485375, by rfl⟩ : syracuseStep 3961001 = 2970751) B2970751
theorem B81277607 : Blo 1563479 81277607 := bstep (se 1 (by rfl) ⟨60958205, by rfl⟩ : syracuseStep 81277607 = 121916411) B121916411
theorem B22545647 : Blo 1563479 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B3426846659 : Blo 1563479 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B2640667 : Blo 1563479 2640667 := bstep (se 1 (by rfl) ⟨1980500, by rfl⟩ : syracuseStep 2640667 = 3961001) B3961001
theorem B54185071 : Blo 1563479 54185071 := bstep (se 1 (by rfl) ⟨40638803, by rfl⟩ : syracuseStep 54185071 = 81277607) B81277607
theorem B457551173 : Blo 1563479 457551173 := bstep (se 4 (by rfl) ⟨42895422, by rfl⟩ : syracuseStep 457551173 = 85790845) B85790845
theorem B5281145 : Blo 1563479 5281145 := bstep (se 2 (by rfl) ⟨1980429, by rfl⟩ : syracuseStep 5281145 = 3960859) B3960859
theorem B72246761 : Blo 1563479 72246761 := bstep (se 2 (by rfl) ⟨27092535, by rfl⟩ : syracuseStep 72246761 = 54185071) B54185071
theorem B2284564439 : Blo 1563479 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B305034115 : Blo 1563479 305034115 := bstep (se 1 (by rfl) ⟨228775586, by rfl⟩ : syracuseStep 305034115 = 457551173) B457551173
theorem B15030431 : Blo 1563479 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B3520763 : Blo 1563479 3520763 := bstep (se 1 (by rfl) ⟨2640572, by rfl⟩ : syracuseStep 3520763 = 5281145) B5281145
theorem B3520889 : Blo 1563479 3520889 := bstep (se 2 (by rfl) ⟨1320333, by rfl⟩ : syracuseStep 3520889 = 2640667) B2640667
theorem B10020287 : Blo 1563479 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B1523042959 : Blo 1563479 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B48164507 : Blo 1563479 48164507 := bstep (se 1 (by rfl) ⟨36123380, by rfl⟩ : syracuseStep 48164507 = 72246761) B72246761
theorem B406712153 : Blo 1563479 406712153 := bstep (se 2 (by rfl) ⟨152517057, by rfl⟩ : syracuseStep 406712153 = 305034115) B305034115
theorem B2347175 : Blo 1563479 2347175 := bstep (se 1 (by rfl) ⟨1760381, by rfl⟩ : syracuseStep 2347175 = 3520763) B3520763
theorem B2347259 : Blo 1563479 2347259 := bstep (se 1 (by rfl) ⟨1760444, by rfl⟩ : syracuseStep 2347259 = 3520889) B3520889
theorem B1564783 : Blo 1563479 1564783 := bstep (se 1 (by rfl) ⟨1173587, by rfl⟩ : syracuseStep 1564783 = 2347175) B2347175
theorem B1564839 : Blo 1563479 1564839 := bstep (se 1 (by rfl) ⟨1173629, by rfl⟩ : syracuseStep 1564839 = 2347259) B2347259
theorem B2030723945 : Blo 1563479 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B271141435 : Blo 1563479 271141435 := bstep (se 1 (by rfl) ⟨203356076, by rfl⟩ : syracuseStep 271141435 = 406712153) B406712153
theorem B32109671 : Blo 1563479 32109671 := bstep (se 1 (by rfl) ⟨24082253, by rfl⟩ : syracuseStep 32109671 = 48164507) B48164507
theorem B26720765 : Blo 1563479 26720765 := bstep (se 3 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 26720765 = 10020287) B10020287
theorem B21406447 : Blo 1563479 21406447 := bstep (se 1 (by rfl) ⟨16054835, by rfl⟩ : syracuseStep 21406447 = 32109671) B32109671
theorem B1446087653 : Blo 1563479 1446087653 := bstep (se 4 (by rfl) ⟨135570717, by rfl⟩ : syracuseStep 1446087653 = 271141435) B271141435
theorem B17813843 : Blo 1563479 17813843 := bstep (se 1 (by rfl) ⟨13360382, by rfl⟩ : syracuseStep 17813843 = 26720765) B26720765
theorem B1353815963 : Blo 1563479 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B28541929 : Blo 1563479 28541929 := bstep (se 2 (by rfl) ⟨10703223, by rfl⟩ : syracuseStep 28541929 = 21406447) B21406447
theorem B11875895 : Blo 1563479 11875895 := bstep (se 1 (by rfl) ⟨8906921, by rfl⟩ : syracuseStep 11875895 = 17813843) B17813843
theorem B902543975 : Blo 1563479 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B964058435 : Blo 1563479 964058435 := bstep (se 1 (by rfl) ⟨723043826, by rfl⟩ : syracuseStep 964058435 = 1446087653) B1446087653
theorem B601695983 : Blo 1563479 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B642705623 : Blo 1563479 642705623 := bstep (se 1 (by rfl) ⟨482029217, by rfl⟩ : syracuseStep 642705623 = 964058435) B964058435
theorem B7917263 : Blo 1563479 7917263 := bstep (se 1 (by rfl) ⟨5937947, by rfl⟩ : syracuseStep 7917263 = 11875895) B11875895
theorem B38055905 : Blo 1563479 38055905 := bstep (se 2 (by rfl) ⟨14270964, by rfl⟩ : syracuseStep 38055905 = 28541929) B28541929
theorem B5278175 : Blo 1563479 5278175 := bstep (se 1 (by rfl) ⟨3958631, by rfl⟩ : syracuseStep 5278175 = 7917263) B7917263
theorem B428470415 : Blo 1563479 428470415 := bstep (se 1 (by rfl) ⟨321352811, by rfl⟩ : syracuseStep 428470415 = 642705623) B642705623
theorem B1604522621 : Blo 1563479 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B25370603 : Blo 1563479 25370603 := bstep (se 1 (by rfl) ⟨19027952, by rfl⟩ : syracuseStep 25370603 = 38055905) B38055905
theorem B285646943 : Blo 1563479 285646943 := bstep (se 1 (by rfl) ⟨214235207, by rfl⟩ : syracuseStep 285646943 = 428470415) B428470415
theorem B3518783 : Blo 1563479 3518783 := bstep (se 1 (by rfl) ⟨2639087, by rfl⟩ : syracuseStep 3518783 = 5278175) B5278175
theorem B4278726989 : Blo 1563479 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B16913735 : Blo 1563479 16913735 := bstep (se 1 (by rfl) ⟨12685301, by rfl⟩ : syracuseStep 16913735 = 25370603) B25370603
theorem B761725181 : Blo 1563479 761725181 := bstep (se 3 (by rfl) ⟨142823471, by rfl⟩ : syracuseStep 761725181 = 285646943) B285646943
theorem B2345855 : Blo 1563479 2345855 := bstep (se 1 (by rfl) ⟨1759391, by rfl⟩ : syracuseStep 2345855 = 3518783) B3518783
theorem B11275823 : Blo 1563479 11275823 := bstep (se 1 (by rfl) ⟨8456867, by rfl⟩ : syracuseStep 11275823 = 16913735) B16913735
theorem B2852484659 : Blo 1563479 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B507816787 : Blo 1563479 507816787 := bstep (se 1 (by rfl) ⟨380862590, by rfl⟩ : syracuseStep 507816787 = 761725181) B761725181
theorem B7517215 : Blo 1563479 7517215 := bstep (se 1 (by rfl) ⟨5637911, by rfl⟩ : syracuseStep 7517215 = 11275823) B11275823
theorem B1901656439 : Blo 1563479 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B1563903 : Blo 1563479 1563903 := bstep (se 1 (by rfl) ⟨1172927, by rfl⟩ : syracuseStep 1563903 = 2345855) B2345855
theorem B1267770959 : Blo 1563479 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B677089049 : Blo 1563479 677089049 := bstep (se 2 (by rfl) ⟨253908393, by rfl⟩ : syracuseStep 677089049 = 507816787) B507816787
theorem B10022953 : Blo 1563479 10022953 := bstep (se 2 (by rfl) ⟨3758607, by rfl⟩ : syracuseStep 10022953 = 7517215) B7517215
theorem B13363937 : Blo 1563479 13363937 := bstep (se 2 (by rfl) ⟨5011476, by rfl⟩ : syracuseStep 13363937 = 10022953) B10022953
theorem B845180639 : Blo 1563479 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B1805570797 : Blo 1563479 1805570797 := bstep (se 3 (by rfl) ⟨338544524, by rfl⟩ : syracuseStep 1805570797 = 677089049) B677089049
theorem B2407427729 : Blo 1563479 2407427729 := bstep (se 2 (by rfl) ⟨902785398, by rfl⟩ : syracuseStep 2407427729 = 1805570797) B1805570797
theorem B8909291 : Blo 1563479 8909291 := bstep (se 1 (by rfl) ⟨6681968, by rfl⟩ : syracuseStep 8909291 = 13363937) B13363937
theorem B563453759 : Blo 1563479 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B5939527 : Blo 1563479 5939527 := bstep (se 1 (by rfl) ⟨4454645, by rfl⟩ : syracuseStep 5939527 = 8909291) B8909291
theorem B1502543357 : Blo 1563479 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1604951819 : Blo 1563479 1604951819 := bstep (se 1 (by rfl) ⟨1203713864, by rfl⟩ : syracuseStep 1604951819 = 2407427729) B2407427729
theorem B1001695571 : Blo 1563479 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B1069967879 : Blo 1563479 1069967879 := bstep (se 1 (by rfl) ⟨802475909, by rfl⟩ : syracuseStep 1069967879 = 1604951819) B1604951819
theorem B7919369 : Blo 1563479 7919369 := bstep (se 2 (by rfl) ⟨2969763, by rfl⟩ : syracuseStep 7919369 = 5939527) B5939527
theorem B667797047 : Blo 1563479 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B713311919 : Blo 1563479 713311919 := bstep (se 1 (by rfl) ⟨534983939, by rfl⟩ : syracuseStep 713311919 = 1069967879) B1069967879
theorem B5279579 : Blo 1563479 5279579 := bstep (se 1 (by rfl) ⟨3959684, by rfl⟩ : syracuseStep 5279579 = 7919369) B7919369
theorem B445198031 : Blo 1563479 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B475541279 : Blo 1563479 475541279 := bstep (se 1 (by rfl) ⟨356655959, by rfl⟩ : syracuseStep 475541279 = 713311919) B713311919
theorem B3519719 : Blo 1563479 3519719 := bstep (se 1 (by rfl) ⟨2639789, by rfl⟩ : syracuseStep 3519719 = 5279579) B5279579
theorem B296798687 : Blo 1563479 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B2346479 : Blo 1563479 2346479 := bstep (se 1 (by rfl) ⟨1759859, by rfl⟩ : syracuseStep 2346479 = 3519719) B3519719
theorem B317027519 : Blo 1563479 317027519 := bstep (se 1 (by rfl) ⟨237770639, by rfl⟩ : syracuseStep 317027519 = 475541279) B475541279
theorem B197865791 : Blo 1563479 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B211351679 : Blo 1563479 211351679 := bstep (se 1 (by rfl) ⟨158513759, by rfl⟩ : syracuseStep 211351679 = 317027519) B317027519
theorem B1564319 : Blo 1563479 1564319 := bstep (se 1 (by rfl) ⟨1173239, by rfl⟩ : syracuseStep 1564319 = 2346479) B2346479
theorem B131910527 : Blo 1563479 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B140901119 : Blo 1563479 140901119 := bstep (se 1 (by rfl) ⟨105675839, by rfl⟩ : syracuseStep 140901119 = 211351679) B211351679
theorem B93934079 : Blo 1563479 93934079 := bstep (se 1 (by rfl) ⟨70450559, by rfl⟩ : syracuseStep 93934079 = 140901119) B140901119
theorem B87940351 : Blo 1563479 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B117253801 : Blo 1563479 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B62622719 : Blo 1563479 62622719 := bstep (se 1 (by rfl) ⟨46967039, by rfl⟩ : syracuseStep 62622719 = 93934079) B93934079
theorem B625353605 : Blo 1563479 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B41748479 : Blo 1563479 41748479 := bstep (se 1 (by rfl) ⟨31311359, by rfl⟩ : syracuseStep 41748479 = 62622719) B62622719
theorem B416902403 : Blo 1563479 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B27832319 : Blo 1563479 27832319 := bstep (se 1 (by rfl) ⟨20874239, by rfl⟩ : syracuseStep 27832319 = 41748479) B41748479
theorem B1111739741 : Blo 1563479 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B18554879 : Blo 1563479 18554879 := bstep (se 1 (by rfl) ⟨13916159, by rfl⟩ : syracuseStep 18554879 = 27832319) B27832319
theorem B12369919 : Blo 1563479 12369919 := bstep (se 1 (by rfl) ⟨9277439, by rfl⟩ : syracuseStep 12369919 = 18554879) B18554879
theorem B741159827 : Blo 1563479 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B16493225 : Blo 1563479 16493225 := bstep (se 2 (by rfl) ⟨6184959, by rfl⟩ : syracuseStep 16493225 = 12369919) B12369919
theorem B494106551 : Blo 1563479 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B329404367 : Blo 1563479 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B175927733 : Blo 1563479 175927733 := bstep (se 5 (by rfl) ⟨8246612, by rfl⟩ : syracuseStep 175927733 = 16493225) B16493225
theorem B117285155 : Blo 1563479 117285155 := bstep (se 1 (by rfl) ⟨87963866, by rfl⟩ : syracuseStep 117285155 = 175927733) B175927733
theorem B219602911 : Blo 1563479 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B292803881 : Blo 1563479 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B78190103 : Blo 1563479 78190103 := bstep (se 1 (by rfl) ⟨58642577, by rfl⟩ : syracuseStep 78190103 = 117285155) B117285155
theorem B52126735 : Blo 1563479 52126735 := bstep (se 1 (by rfl) ⟨39095051, by rfl⟩ : syracuseStep 52126735 = 78190103) B78190103
theorem B780810349 : Blo 1563479 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B1041080465 : Blo 1563479 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B69502313 : Blo 1563479 69502313 := bstep (se 2 (by rfl) ⟨26063367, by rfl⟩ : syracuseStep 69502313 = 52126735) B52126735
theorem B46334875 : Blo 1563479 46334875 := bstep (se 1 (by rfl) ⟨34751156, by rfl⟩ : syracuseStep 46334875 = 69502313) B69502313
theorem B694053643 : Blo 1563479 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 1563479 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B61779833 : Blo 1563479 61779833 := bstep (se 2 (by rfl) ⟨23167437, by rfl⟩ : syracuseStep 61779833 = 46334875) B46334875
theorem B616936571 : Blo 1563479 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B41186555 : Blo 1563479 41186555 := bstep (se 1 (by rfl) ⟨30889916, by rfl⟩ : syracuseStep 41186555 = 61779833) B61779833
theorem B411291047 : Blo 1563479 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B27457703 : Blo 1563479 27457703 := bstep (se 1 (by rfl) ⟨20593277, by rfl⟩ : syracuseStep 27457703 = 41186555) B41186555
theorem B18305135 : Blo 1563479 18305135 := bstep (se 1 (by rfl) ⟨13728851, by rfl⟩ : syracuseStep 18305135 = 27457703) B27457703
theorem B1096776125 : Blo 1563479 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B12203423 : Blo 1563479 12203423 := bstep (se 1 (by rfl) ⟨9152567, by rfl⟩ : syracuseStep 12203423 = 18305135) B18305135
theorem B731184083 : Blo 1563479 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B8135615 : Blo 1563479 8135615 := bstep (se 1 (by rfl) ⟨6101711, by rfl⟩ : syracuseStep 8135615 = 12203423) B12203423
theorem B487456055 : Blo 1563479 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B5423743 : Blo 1563479 5423743 := bstep (se 1 (by rfl) ⟨4067807, by rfl⟩ : syracuseStep 5423743 = 8135615) B8135615
theorem B324970703 : Blo 1563479 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B28926629 : Blo 1563479 28926629 := bstep (se 4 (by rfl) ⟨2711871, by rfl⟩ : syracuseStep 28926629 = 5423743) B5423743
theorem B216647135 : Blo 1563479 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B19284419 : Blo 1563479 19284419 := bstep (se 1 (by rfl) ⟨14463314, by rfl⟩ : syracuseStep 19284419 = 28926629) B28926629
theorem B144431423 : Blo 1563479 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B51425117 : Blo 1563479 51425117 := bstep (se 3 (by rfl) ⟨9642209, by rfl⟩ : syracuseStep 51425117 = 19284419) B19284419
theorem B96287615 : Blo 1563479 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B64191743 : Blo 1563479 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B34283411 : Blo 1563479 34283411 := bstep (se 1 (by rfl) ⟨25712558, by rfl⟩ : syracuseStep 34283411 = 51425117) B51425117
theorem B42794495 : Blo 1563479 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B22855607 : Blo 1563479 22855607 := bstep (se 1 (by rfl) ⟨17141705, by rfl⟩ : syracuseStep 22855607 = 34283411) B34283411
theorem B28529663 : Blo 1563479 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B15237071 : Blo 1563479 15237071 := bstep (se 1 (by rfl) ⟨11427803, by rfl⟩ : syracuseStep 15237071 = 22855607) B22855607
theorem B10158047 : Blo 1563479 10158047 := bstep (se 1 (by rfl) ⟨7618535, by rfl⟩ : syracuseStep 10158047 = 15237071) B15237071
theorem B76079101 : Blo 1563479 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B6772031 : Blo 1563479 6772031 := bstep (se 1 (by rfl) ⟨5079023, by rfl⟩ : syracuseStep 6772031 = 10158047) B10158047
theorem B101438801 : Blo 1563479 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B4514687 : Blo 1563479 4514687 := bstep (se 1 (by rfl) ⟨3386015, by rfl⟩ : syracuseStep 4514687 = 6772031) B6772031
theorem B67625867 : Blo 1563479 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B3009791 : Blo 1563479 3009791 := bstep (se 1 (by rfl) ⟨2257343, by rfl⟩ : syracuseStep 3009791 = 4514687) B4514687
theorem B45083911 : Blo 1563479 45083911 := bstep (se 1 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 45083911 = 67625867) B67625867
theorem B60111881 : Blo 1563479 60111881 := bstep (se 2 (by rfl) ⟨22541955, by rfl⟩ : syracuseStep 60111881 = 45083911) B45083911
theorem B2006527 : Blo 1563479 2006527 := bstep (se 1 (by rfl) ⟨1504895, by rfl⟩ : syracuseStep 2006527 = 3009791) B3009791
theorem B2675369 : Blo 1563479 2675369 := bstep (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) B2006527
theorem B40074587 : Blo 1563479 40074587 := bstep (se 1 (by rfl) ⟨30055940, by rfl⟩ : syracuseStep 40074587 = 60111881) B60111881
theorem B26716391 : Blo 1563479 26716391 := bstep (se 1 (by rfl) ⟨20037293, by rfl⟩ : syracuseStep 26716391 = 40074587) B40074587
theorem B7134317 : Blo 1563479 7134317 := bstep (se 3 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 7134317 = 2675369) B2675369
theorem B17810927 : Blo 1563479 17810927 := bstep (se 1 (by rfl) ⟨13358195, by rfl⟩ : syracuseStep 17810927 = 26716391) B26716391
theorem B4756211 : Blo 1563479 4756211 := bstep (se 1 (by rfl) ⟨3567158, by rfl⟩ : syracuseStep 4756211 = 7134317) B7134317
theorem B3170807 : Blo 1563479 3170807 := bstep (se 1 (by rfl) ⟨2378105, by rfl⟩ : syracuseStep 3170807 = 4756211) B4756211
theorem B11873951 : Blo 1563479 11873951 := bstep (se 1 (by rfl) ⟨8905463, by rfl⟩ : syracuseStep 11873951 = 17810927) B17810927
theorem B2113871 : Blo 1563479 2113871 := bstep (se 1 (by rfl) ⟨1585403, by rfl⟩ : syracuseStep 2113871 = 3170807) B3170807
theorem B7915967 : Blo 1563479 7915967 := bstep (se 1 (by rfl) ⟨5936975, by rfl⟩ : syracuseStep 7915967 = 11873951) B11873951
theorem B5636989 : Blo 1563479 5636989 := bstep (se 3 (by rfl) ⟨1056935, by rfl⟩ : syracuseStep 5636989 = 2113871) B2113871
theorem B5277311 : Blo 1563479 5277311 := bstep (se 1 (by rfl) ⟨3957983, by rfl⟩ : syracuseStep 5277311 = 7915967) B7915967
theorem B3518207 : Blo 1563479 3518207 := bstep (se 1 (by rfl) ⟨2638655, by rfl⟩ : syracuseStep 3518207 = 5277311) B5277311
theorem B7515985 : Blo 1563479 7515985 := bstep (se 2 (by rfl) ⟨2818494, by rfl⟩ : syracuseStep 7515985 = 5636989) B5636989
theorem B10021313 : Blo 1563479 10021313 := bstep (se 2 (by rfl) ⟨3757992, by rfl⟩ : syracuseStep 10021313 = 7515985) B7515985
theorem B2345471 : Blo 1563479 2345471 := bstep (se 1 (by rfl) ⟨1759103, by rfl⟩ : syracuseStep 2345471 = 3518207) B3518207
theorem B6680875 : Blo 1563479 6680875 := bstep (se 1 (by rfl) ⟨5010656, by rfl⟩ : syracuseStep 6680875 = 10021313) B10021313
theorem B1563647 : Blo 1563479 1563647 := bstep (se 1 (by rfl) ⟨1172735, by rfl⟩ : syracuseStep 1563647 = 2345471) B2345471
theorem B8907833 : Blo 1563479 8907833 := bstep (se 2 (by rfl) ⟨3340437, by rfl⟩ : syracuseStep 8907833 = 6680875) B6680875
theorem B5938555 : Blo 1563479 5938555 := bstep (se 1 (by rfl) ⟨4453916, by rfl⟩ : syracuseStep 5938555 = 8907833) B8907833
theorem B7918073 : Blo 1563479 7918073 := bstep (se 2 (by rfl) ⟨2969277, by rfl⟩ : syracuseStep 7918073 = 5938555) B5938555
theorem B5278715 : Blo 1563479 5278715 := bstep (se 1 (by rfl) ⟨3959036, by rfl⟩ : syracuseStep 5278715 = 7918073) B7918073
theorem B3519143 : Blo 1563479 3519143 := bstep (se 1 (by rfl) ⟨2639357, by rfl⟩ : syracuseStep 3519143 = 5278715) B5278715
theorem B2346095 : Blo 1563479 2346095 := bstep (se 1 (by rfl) ⟨1759571, by rfl⟩ : syracuseStep 2346095 = 3519143) B3519143
theorem B1564063 : Blo 1563479 1564063 := bstep (se 1 (by rfl) ⟨1173047, by rfl⟩ : syracuseStep 1564063 = 2346095) B2346095

theorem C0 (j : ℕ) (h1 : 390869 ≤ j) (h2 : j ≤ 391244) : Blo 1563479 (4 * j + 3) := by
  interval_cases j
  · exact B1563479
  · exact B1563483
  · exact B1563487
  · exact B1563491
  · exact B1563495
  · exact B1563499
  · exact B1563503
  · exact B1563507
  · exact B1563511
  · exact B1563515
  · exact B1563519
  · exact B1563523
  · exact B1563527
  · exact B1563531
  · exact B1563535
  · exact B1563539
  · exact B1563543
  · exact B1563547
  · exact B1563551
  · exact B1563555
  · exact B1563559
  · exact B1563563
  · exact B1563567
  · exact B1563571
  · exact B1563575
  · exact B1563579
  · exact B1563583
  · exact B1563587
  · exact B1563591
  · exact B1563595
  · exact B1563599
  · exact B1563603
  · exact B1563607
  · exact B1563611
  · exact B1563615
  · exact B1563619
  · exact B1563623
  · exact B1563627
  · exact B1563631
  · exact B1563635
  · exact B1563639
  · exact B1563643
  · exact B1563647
  · exact B1563651
  · exact B1563655
  · exact B1563659
  · exact B1563663
  · exact B1563667
  · exact B1563671
  · exact B1563675
  · exact B1563679
  · exact B1563683
  · exact B1563687
  · exact B1563691
  · exact B1563695
  · exact B1563699
  · exact B1563703
  · exact B1563707
  · exact B1563711
  · exact B1563715
  · exact B1563719
  · exact B1563723
  · exact B1563727
  · exact B1563731
  · exact B1563735
  · exact B1563739
  · exact B1563743
  · exact B1563747
  · exact B1563751
  · exact B1563755
  · exact B1563759
  · exact B1563763
  · exact B1563767
  · exact B1563771
  · exact B1563775
  · exact B1563779
  · exact B1563783
  · exact B1563787
  · exact B1563791
  · exact B1563795
  · exact B1563799
  · exact B1563803
  · exact B1563807
  · exact B1563811
  · exact B1563815
  · exact B1563819
  · exact B1563823
  · exact B1563827
  · exact B1563831
  · exact B1563835
  · exact B1563839
  · exact B1563843
  · exact B1563847
  · exact B1563851
  · exact B1563855
  · exact B1563859
  · exact B1563863
  · exact B1563867
  · exact B1563871
  · exact B1563875
  · exact B1563879
  · exact B1563883
  · exact B1563887
  · exact B1563891
  · exact B1563895
  · exact B1563899
  · exact B1563903
  · exact B1563907
  · exact B1563911
  · exact B1563915
  · exact B1563919
  · exact B1563923
  · exact B1563927
  · exact B1563931
  · exact B1563935
  · exact B1563939
  · exact B1563943
  · exact B1563947
  · exact B1563951
  · exact B1563955
  · exact B1563959
  · exact B1563963
  · exact B1563967
  · exact B1563971
  · exact B1563975
  · exact B1563979
  · exact B1563983
  · exact B1563987
  · exact B1563991
  · exact B1563995
  · exact B1563999
  · exact B1564003
  · exact B1564007
  · exact B1564011
  · exact B1564015
  · exact B1564019
  · exact B1564023
  · exact B1564027
  · exact B1564031
  · exact B1564035
  · exact B1564039
  · exact B1564043
  · exact B1564047
  · exact B1564051
  · exact B1564055
  · exact B1564059
  · exact B1564063
  · exact B1564067
  · exact B1564071
  · exact B1564075
  · exact B1564079
  · exact B1564083
  · exact B1564087
  · exact B1564091
  · exact B1564095
  · exact B1564099
  · exact B1564103
  · exact B1564107
  · exact B1564111
  · exact B1564115
  · exact B1564119
  · exact B1564123
  · exact B1564127
  · exact B1564131
  · exact B1564135
  · exact B1564139
  · exact B1564143
  · exact B1564147
  · exact B1564151
  · exact B1564155
  · exact B1564159
  · exact B1564163
  · exact B1564167
  · exact B1564171
  · exact B1564175
  · exact B1564179
  · exact B1564183
  · exact B1564187
  · exact B1564191
  · exact B1564195
  · exact B1564199
  · exact B1564203
  · exact B1564207
  · exact B1564211
  · exact B1564215
  · exact B1564219
  · exact B1564223
  · exact B1564227
  · exact B1564231
  · exact B1564235
  · exact B1564239
  · exact B1564243
  · exact B1564247
  · exact B1564251
  · exact B1564255
  · exact B1564259
  · exact B1564263
  · exact B1564267
  · exact B1564271
  · exact B1564275
  · exact B1564279
  · exact B1564283
  · exact B1564287
  · exact B1564291
  · exact B1564295
  · exact B1564299
  · exact B1564303
  · exact B1564307
  · exact B1564311
  · exact B1564315
  · exact B1564319
  · exact B1564323
  · exact B1564327
  · exact B1564331
  · exact B1564335
  · exact B1564339
  · exact B1564343
  · exact B1564347
  · exact B1564351
  · exact B1564355
  · exact B1564359
  · exact B1564363
  · exact B1564367
  · exact B1564371
  · exact B1564375
  · exact B1564379
  · exact B1564383
  · exact B1564387
  · exact B1564391
  · exact B1564395
  · exact B1564399
  · exact B1564403
  · exact B1564407
  · exact B1564411
  · exact B1564415
  · exact B1564419
  · exact B1564423
  · exact B1564427
  · exact B1564431
  · exact B1564435
  · exact B1564439
  · exact B1564443
  · exact B1564447
  · exact B1564451
  · exact B1564455
  · exact B1564459
  · exact B1564463
  · exact B1564467
  · exact B1564471
  · exact B1564475
  · exact B1564479
  · exact B1564483
  · exact B1564487
  · exact B1564491
  · exact B1564495
  · exact B1564499
  · exact B1564503
  · exact B1564507
  · exact B1564511
  · exact B1564515
  · exact B1564519
  · exact B1564523
  · exact B1564527
  · exact B1564531
  · exact B1564535
  · exact B1564539
  · exact B1564543
  · exact B1564547
  · exact B1564551
  · exact B1564555
  · exact B1564559
  · exact B1564563
  · exact B1564567
  · exact B1564571
  · exact B1564575
  · exact B1564579
  · exact B1564583
  · exact B1564587
  · exact B1564591
  · exact B1564595
  · exact B1564599
  · exact B1564603
  · exact B1564607
  · exact B1564611
  · exact B1564615
  · exact B1564619
  · exact B1564623
  · exact B1564627
  · exact B1564631
  · exact B1564635
  · exact B1564639
  · exact B1564643
  · exact B1564647
  · exact B1564651
  · exact B1564655
  · exact B1564659
  · exact B1564663
  · exact B1564667
  · exact B1564671
  · exact B1564675
  · exact B1564679
  · exact B1564683
  · exact B1564687
  · exact B1564691
  · exact B1564695
  · exact B1564699
  · exact B1564703
  · exact B1564707
  · exact B1564711
  · exact B1564715
  · exact B1564719
  · exact B1564723
  · exact B1564727
  · exact B1564731
  · exact B1564735
  · exact B1564739
  · exact B1564743
  · exact B1564747
  · exact B1564751
  · exact B1564755
  · exact B1564759
  · exact B1564763
  · exact B1564767
  · exact B1564771
  · exact B1564775
  · exact B1564779
  · exact B1564783
  · exact B1564787
  · exact B1564791
  · exact B1564795
  · exact B1564799
  · exact B1564803
  · exact B1564807
  · exact B1564811
  · exact B1564815
  · exact B1564819
  · exact B1564823
  · exact B1564827
  · exact B1564831
  · exact B1564835
  · exact B1564839
  · exact B1564843
  · exact B1564847
  · exact B1564851
  · exact B1564855
  · exact B1564859
  · exact B1564863
  · exact B1564867
  · exact B1564871
  · exact B1564875
  · exact B1564879
  · exact B1564883
  · exact B1564887
  · exact B1564891
  · exact B1564895
  · exact B1564899
  · exact B1564903
  · exact B1564907
  · exact B1564911
  · exact B1564915
  · exact B1564919
  · exact B1564923
  · exact B1564927
  · exact B1564931
  · exact B1564935
  · exact B1564939
  · exact B1564943
  · exact B1564947
  · exact B1564951
  · exact B1564955
  · exact B1564959
  · exact B1564963
  · exact B1564967
  · exact B1564971
  · exact B1564975
  · exact B1564979

theorem solution (m : ℕ) (hlo : 1563479 ≤ m) (hhi : m ≤ 1564979) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 390869 ≤ j := by omega
    have hj2 : j ≤ 391244 := by omega
    have hb : Blo 1563479 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
