-- Prove2me | solution 1 for syracuse_descends_range_1234435_1236435
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:06.264115+00:00
-- url     : https://prove2.me/submissions/3a2795a4-2b5d-4480-8ece-1302096bc644

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


theorem B1564697 : Blo 1234435 1564697 := bbase (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) (by norm_num)
theorem B1564753 : Blo 1234435 1564753 := bbase (se 2 (by rfl) ⟨586782, by rfl⟩ : syracuseStep 1564753 = 1173565) (by norm_num)
theorem B1319009 : Blo 1234435 1319009 := bbase (se 2 (by rfl) ⟨494628, by rfl⟩ : syracuseStep 1319009 = 989257) (by norm_num)
theorem B1409125 : Blo 1234435 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B2031725 : Blo 1234435 2031725 := bbase (se 3 (by rfl) ⟨380948, by rfl⟩ : syracuseStep 2031725 = 761897) (by norm_num)
theorem B1564849 : Blo 1234435 1564849 := bbase (se 2 (by rfl) ⟨586818, by rfl⟩ : syracuseStep 1564849 = 1173637) (by norm_num)
theorem B6258869 : Blo 1234435 6258869 := bbase (se 5 (by rfl) ⟨293384, by rfl⟩ : syracuseStep 6258869 = 586769) (by norm_num)
theorem B4694213 : Blo 1234435 4694213 := bbase (se 4 (by rfl) ⟨440082, by rfl⟩ : syracuseStep 4694213 = 880165) (by norm_num)
theorem B1851653 : Blo 1234435 1851653 := bbase (se 4 (by rfl) ⟨173592, by rfl⟩ : syracuseStep 1851653 = 347185) (by norm_num)
theorem B3170573 : Blo 1234435 3170573 := bbase (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) (by norm_num)
theorem B4227349 : Blo 1234435 4227349 := bbase (se 6 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 4227349 = 198157) (by norm_num)
theorem B1851677 : Blo 1234435 1851677 := bbase (se 3 (by rfl) ⟨347189, by rfl⟩ : syracuseStep 1851677 = 694379) (by norm_num)
theorem B3129637 : Blo 1234435 3129637 := bbase (se 4 (by rfl) ⟨293403, by rfl⟩ : syracuseStep 3129637 = 586807) (by norm_num)
theorem B1851701 : Blo 1234435 1851701 := bbase (se 5 (by rfl) ⟨86798, by rfl⟩ : syracuseStep 1851701 = 173597) (by norm_num)
theorem B1851725 : Blo 1234435 1851725 := bbase (se 3 (by rfl) ⟨347198, by rfl⟩ : syracuseStep 1851725 = 694397) (by norm_num)
theorem B1319257 : Blo 1234435 1319257 := bbase (se 2 (by rfl) ⟨494721, by rfl⟩ : syracuseStep 1319257 = 989443) (by norm_num)
theorem B1851749 : Blo 1234435 1851749 := bbase (se 4 (by rfl) ⟨173601, by rfl⟩ : syracuseStep 1851749 = 347203) (by norm_num)
theorem B1851773 : Blo 1234435 1851773 := bbase (se 3 (by rfl) ⟨347207, by rfl⟩ : syracuseStep 1851773 = 694415) (by norm_num)
theorem B1851797 : Blo 1234435 1851797 := bbase (se 6 (by rfl) ⟨43401, by rfl⟩ : syracuseStep 1851797 = 86803) (by norm_num)
theorem B4170149 : Blo 1234435 4170149 := bbase (se 4 (by rfl) ⟨390951, by rfl⟩ : syracuseStep 4170149 = 781903) (by norm_num)
theorem B1851821 : Blo 1234435 1851821 := bbase (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) (by norm_num)
theorem B2777525 : Blo 1234435 2777525 := bbase (se 5 (by rfl) ⟨130196, by rfl⟩ : syracuseStep 2777525 = 260393) (by norm_num)
theorem B1851845 : Blo 1234435 1851845 := bbase (se 4 (by rfl) ⟨173610, by rfl⟩ : syracuseStep 1851845 = 347221) (by norm_num)
theorem B1851869 : Blo 1234435 1851869 := bbase (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) (by norm_num)
theorem B1851893 : Blo 1234435 1851893 := bbase (se 5 (by rfl) ⟨86807, by rfl⟩ : syracuseStep 1851893 = 173615) (by norm_num)
theorem B2777597 : Blo 1234435 2777597 := bbase (se 3 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 2777597 = 1041599) (by norm_num)
theorem B1851917 : Blo 1234435 1851917 := bbase (se 3 (by rfl) ⟨347234, by rfl⟩ : syracuseStep 1851917 = 694469) (by norm_num)
theorem B7225877 : Blo 1234435 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B1851941 : Blo 1234435 1851941 := bbase (se 4 (by rfl) ⟨173619, by rfl⟩ : syracuseStep 1851941 = 347239) (by norm_num)
theorem B1851965 : Blo 1234435 1851965 := bbase (se 3 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 1851965 = 694487) (by norm_num)
theorem B2777669 : Blo 1234435 2777669 := bbase (se 4 (by rfl) ⟨260406, by rfl⟩ : syracuseStep 2777669 = 520813) (by norm_num)
theorem B1851989 : Blo 1234435 1851989 := bbase (se 8 (by rfl) ⟨10851, by rfl⟩ : syracuseStep 1851989 = 21703) (by norm_num)
theorem B6251093 : Blo 1234435 6251093 := bbase (se 8 (by rfl) ⟨36627, by rfl⟩ : syracuseStep 6251093 = 73255) (by norm_num)
theorem B1852013 : Blo 1234435 1852013 := bbase (se 3 (by rfl) ⟨347252, by rfl⟩ : syracuseStep 1852013 = 694505) (by norm_num)
theorem B1852037 : Blo 1234435 1852037 := bbase (se 4 (by rfl) ⟨173628, by rfl⟩ : syracuseStep 1852037 = 347257) (by norm_num)
theorem B2777741 : Blo 1234435 2777741 := bbase (se 3 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 2777741 = 1041653) (by norm_num)
theorem B1852061 : Blo 1234435 1852061 := bbase (se 3 (by rfl) ⟨347261, by rfl⟩ : syracuseStep 1852061 = 694523) (by norm_num)
theorem B2712229 : Blo 1234435 2712229 := bbase (se 4 (by rfl) ⟨254271, by rfl⟩ : syracuseStep 2712229 = 508543) (by norm_num)
theorem B2540197 : Blo 1234435 2540197 := bbase (se 4 (by rfl) ⟨238143, by rfl⟩ : syracuseStep 2540197 = 476287) (by norm_num)
theorem B1852085 : Blo 1234435 1852085 := bbase (se 5 (by rfl) ⟨86816, by rfl⟩ : syracuseStep 1852085 = 173633) (by norm_num)
theorem B2343629 : Blo 1234435 2343629 := bbase (se 3 (by rfl) ⟨439430, by rfl⟩ : syracuseStep 2343629 = 878861) (by norm_num)
theorem B1852109 : Blo 1234435 1852109 := bbase (se 3 (by rfl) ⟨347270, by rfl⟩ : syracuseStep 1852109 = 694541) (by norm_num)
theorem B2777813 : Blo 1234435 2777813 := bbase (se 7 (by rfl) ⟨32552, by rfl⟩ : syracuseStep 2777813 = 65105) (by norm_num)
theorem B1852133 : Blo 1234435 1852133 := bbase (se 4 (by rfl) ⟨173637, by rfl⟩ : syracuseStep 1852133 = 347275) (by norm_num)
theorem B2638565 : Blo 1234435 2638565 := bbase (se 4 (by rfl) ⟨247365, by rfl⟩ : syracuseStep 2638565 = 494731) (by norm_num)
theorem B1852157 : Blo 1234435 1852157 := bbase (se 3 (by rfl) ⟨347279, by rfl⟩ : syracuseStep 1852157 = 694559) (by norm_num)
theorem B1852181 : Blo 1234435 1852181 := bbase (se 6 (by rfl) ⟨43410, by rfl⟩ : syracuseStep 1852181 = 86821) (by norm_num)
theorem B1319701 : Blo 1234435 1319701 := bbase (se 6 (by rfl) ⟨30930, by rfl⟩ : syracuseStep 1319701 = 61861) (by norm_num)
theorem B2777885 : Blo 1234435 2777885 := bbase (se 3 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 2777885 = 1041707) (by norm_num)
theorem B1852205 : Blo 1234435 1852205 := bbase (se 3 (by rfl) ⟨347288, by rfl⟩ : syracuseStep 1852205 = 694577) (by norm_num)
theorem B4449077 : Blo 1234435 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B1852229 : Blo 1234435 1852229 := bbase (se 4 (by rfl) ⟨173646, by rfl⟩ : syracuseStep 1852229 = 347293) (by norm_num)
theorem B1319761 : Blo 1234435 1319761 := bbase (se 2 (by rfl) ⟨494910, by rfl⟩ : syracuseStep 1319761 = 989821) (by norm_num)
theorem B4170581 : Blo 1234435 4170581 := bbase (se 9 (by rfl) ⟨12218, by rfl⟩ : syracuseStep 4170581 = 24437) (by norm_num)
theorem B1852253 : Blo 1234435 1852253 := bbase (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) (by norm_num)
theorem B2777957 : Blo 1234435 2777957 := bbase (se 4 (by rfl) ⟨260433, by rfl⟩ : syracuseStep 2777957 = 520867) (by norm_num)
theorem B3957605 : Blo 1234435 3957605 := bbase (se 4 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 3957605 = 742051) (by norm_num)
theorem B1852277 : Blo 1234435 1852277 := bbase (se 5 (by rfl) ⟨86825, by rfl⟩ : syracuseStep 1852277 = 173651) (by norm_num)
theorem B1483645 : Blo 1234435 1483645 := bbase (se 3 (by rfl) ⟨278183, by rfl⟩ : syracuseStep 1483645 = 556367) (by norm_num)
theorem B1852301 : Blo 1234435 1852301 := bbase (se 3 (by rfl) ⟨347306, by rfl⟩ : syracuseStep 1852301 = 694613) (by norm_num)
theorem B1606541 : Blo 1234435 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B1852325 : Blo 1234435 1852325 := bbase (se 4 (by rfl) ⟨173655, by rfl⟩ : syracuseStep 1852325 = 347311) (by norm_num)
theorem B2778029 : Blo 1234435 2778029 := bbase (se 3 (by rfl) ⟨520880, by rfl⟩ : syracuseStep 2778029 = 1041761) (by norm_num)
theorem B11871157 : Blo 1234435 11871157 := bbase (se 5 (by rfl) ⟨556460, by rfl⟩ : syracuseStep 11871157 = 1112921) (by norm_num)
theorem B1852349 : Blo 1234435 1852349 := bbase (se 3 (by rfl) ⟨347315, by rfl⟩ : syracuseStep 1852349 = 694631) (by norm_num)
theorem B1852373 : Blo 1234435 1852373 := bbase (se 7 (by rfl) ⟨21707, by rfl⟩ : syracuseStep 1852373 = 43415) (by norm_num)
theorem B1483741 : Blo 1234435 1483741 := bbase (se 3 (by rfl) ⟨278201, by rfl⟩ : syracuseStep 1483741 = 556403) (by norm_num)
theorem B2638813 : Blo 1234435 2638813 := bbase (se 3 (by rfl) ⟨494777, by rfl⟩ : syracuseStep 2638813 = 989555) (by norm_num)
theorem B2343917 : Blo 1234435 2343917 := bbase (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) (by norm_num)
theorem B1852397 : Blo 1234435 1852397 := bbase (se 3 (by rfl) ⟨347324, by rfl⟩ : syracuseStep 1852397 = 694649) (by norm_num)
theorem B2778101 : Blo 1234435 2778101 := bbase (se 5 (by rfl) ⟨130223, by rfl⟩ : syracuseStep 2778101 = 260447) (by norm_num)
theorem B1852421 : Blo 1234435 1852421 := bbase (se 4 (by rfl) ⟨173664, by rfl⟩ : syracuseStep 1852421 = 347329) (by norm_num)
theorem B1852445 : Blo 1234435 1852445 := bbase (se 3 (by rfl) ⟨347333, by rfl⟩ : syracuseStep 1852445 = 694667) (by norm_num)
theorem B1852469 : Blo 1234435 1852469 := bbase (se 5 (by rfl) ⟨86834, by rfl⟩ : syracuseStep 1852469 = 173669) (by norm_num)
theorem B2778173 : Blo 1234435 2778173 := bbase (se 3 (by rfl) ⟨520907, by rfl⟩ : syracuseStep 2778173 = 1041815) (by norm_num)
theorem B1852493 : Blo 1234435 1852493 := bbase (se 3 (by rfl) ⟨347342, by rfl⟩ : syracuseStep 1852493 = 694685) (by norm_num)
theorem B1852517 : Blo 1234435 1852517 := bbase (se 4 (by rfl) ⟨173673, by rfl⟩ : syracuseStep 1852517 = 347347) (by norm_num)
theorem B1852541 : Blo 1234435 1852541 := bbase (se 3 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 1852541 = 694703) (by norm_num)
theorem B2344069 : Blo 1234435 2344069 := bbase (se 4 (by rfl) ⟨219756, by rfl⟩ : syracuseStep 2344069 = 439513) (by norm_num)
theorem B2778245 : Blo 1234435 2778245 := bbase (se 4 (by rfl) ⟨260460, by rfl⟩ : syracuseStep 2778245 = 520921) (by norm_num)
theorem B1320077 : Blo 1234435 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B1852565 : Blo 1234435 1852565 := bbase (se 6 (by rfl) ⟨43419, by rfl⟩ : syracuseStep 1852565 = 86839) (by norm_num)
theorem B5276821 : Blo 1234435 5276821 := bbase (se 6 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 5276821 = 247351) (by norm_num)
theorem B15836309 : Blo 1234435 15836309 := bbase (se 6 (by rfl) ⟨371163, by rfl⟩ : syracuseStep 15836309 = 742327) (by norm_num)
theorem B3515557 : Blo 1234435 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B1852589 : Blo 1234435 1852589 := bbase (se 3 (by rfl) ⟨347360, by rfl⟩ : syracuseStep 1852589 = 694721) (by norm_num)
theorem B1852613 : Blo 1234435 1852613 := bbase (se 4 (by rfl) ⟨173682, by rfl⟩ : syracuseStep 1852613 = 347365) (by norm_num)
theorem B2778317 : Blo 1234435 2778317 := bbase (se 3 (by rfl) ⟨520934, by rfl⟩ : syracuseStep 2778317 = 1041869) (by norm_num)
theorem B1852637 : Blo 1234435 1852637 := bbase (se 3 (by rfl) ⟨347369, by rfl⟩ : syracuseStep 1852637 = 694739) (by norm_num)
theorem B1852661 : Blo 1234435 1852661 := bbase (se 5 (by rfl) ⟨86843, by rfl⟩ : syracuseStep 1852661 = 173687) (by norm_num)
theorem B4171013 : Blo 1234435 4171013 := bbase (se 4 (by rfl) ⟨391032, by rfl⟩ : syracuseStep 4171013 = 782065) (by norm_num)
theorem B1852685 : Blo 1234435 1852685 := bbase (se 3 (by rfl) ⟨347378, by rfl⟩ : syracuseStep 1852685 = 694757) (by norm_num)
theorem B2778389 : Blo 1234435 2778389 := bbase (se 6 (by rfl) ⟨65118, by rfl⟩ : syracuseStep 2778389 = 130237) (by norm_num)
theorem B1852709 : Blo 1234435 1852709 := bbase (se 4 (by rfl) ⟨173691, by rfl⟩ : syracuseStep 1852709 = 347383) (by norm_num)
theorem B1852733 : Blo 1234435 1852733 := bbase (se 3 (by rfl) ⟨347387, by rfl⟩ : syracuseStep 1852733 = 694775) (by norm_num)
theorem B3515717 : Blo 1234435 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B1852757 : Blo 1234435 1852757 := bbase (se 12 (by rfl) ⟨678, by rfl⟩ : syracuseStep 1852757 = 1357) (by norm_num)
theorem B2778461 : Blo 1234435 2778461 := bbase (se 3 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 2778461 = 1041923) (by norm_num)
theorem B1852781 : Blo 1234435 1852781 := bbase (se 3 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 1852781 = 694793) (by norm_num)
theorem B1852805 : Blo 1234435 1852805 := bbase (se 4 (by rfl) ⟨173700, by rfl⟩ : syracuseStep 1852805 = 347401) (by norm_num)
theorem B1852829 : Blo 1234435 1852829 := bbase (se 3 (by rfl) ⟨347405, by rfl⟩ : syracuseStep 1852829 = 694811) (by norm_num)
theorem B2778533 : Blo 1234435 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B2344373 : Blo 1234435 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B1852853 : Blo 1234435 1852853 := bbase (se 5 (by rfl) ⟨86852, by rfl⟩ : syracuseStep 1852853 = 173705) (by norm_num)
theorem B1852877 : Blo 1234435 1852877 := bbase (se 3 (by rfl) ⟨347414, by rfl⟩ : syracuseStep 1852877 = 694829) (by norm_num)
theorem B2639317 : Blo 1234435 2639317 := bbase (se 7 (by rfl) ⟨30929, by rfl⟩ : syracuseStep 2639317 = 61859) (by norm_num)
theorem B1852901 : Blo 1234435 1852901 := bbase (se 4 (by rfl) ⟨173709, by rfl⟩ : syracuseStep 1852901 = 347419) (by norm_num)
theorem B2778605 : Blo 1234435 2778605 := bbase (se 3 (by rfl) ⟨520988, by rfl⟩ : syracuseStep 2778605 = 1041977) (by norm_num)
theorem B1852925 : Blo 1234435 1852925 := bbase (se 3 (by rfl) ⟨347423, by rfl⟩ : syracuseStep 1852925 = 694847) (by norm_num)
theorem B4752901 : Blo 1234435 4752901 := bbase (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) (by norm_num)
theorem B3171845 : Blo 1234435 3171845 := bbase (se 4 (by rfl) ⟨297360, by rfl⟩ : syracuseStep 3171845 = 594721) (by norm_num)
theorem B1852949 : Blo 1234435 1852949 := bbase (se 6 (by rfl) ⟨43428, by rfl⟩ : syracuseStep 1852949 = 86857) (by norm_num)
theorem B1852973 : Blo 1234435 1852973 := bbase (se 3 (by rfl) ⟨347432, by rfl⟩ : syracuseStep 1852973 = 694865) (by norm_num)
theorem B3515957 : Blo 1234435 3515957 := bbase (se 5 (by rfl) ⟨164810, by rfl⟩ : syracuseStep 3515957 = 329621) (by norm_num)
theorem B2778677 : Blo 1234435 2778677 := bbase (se 5 (by rfl) ⟨130250, by rfl⟩ : syracuseStep 2778677 = 260501) (by norm_num)
theorem B1852997 : Blo 1234435 1852997 := bbase (se 4 (by rfl) ⟨173718, by rfl⟩ : syracuseStep 1852997 = 347437) (by norm_num)
theorem B1853021 : Blo 1234435 1853021 := bbase (se 3 (by rfl) ⟨347441, by rfl⟩ : syracuseStep 1853021 = 694883) (by norm_num)
theorem B1853045 : Blo 1234435 1853045 := bbase (se 5 (by rfl) ⟨86861, by rfl⟩ : syracuseStep 1853045 = 173723) (by norm_num)
theorem B2778749 : Blo 1234435 2778749 := bbase (se 3 (by rfl) ⟨521015, by rfl⟩ : syracuseStep 2778749 = 1042031) (by norm_num)
theorem B1853069 : Blo 1234435 1853069 := bbase (se 3 (by rfl) ⟨347450, by rfl⟩ : syracuseStep 1853069 = 694901) (by norm_num)
theorem B2967205 : Blo 1234435 2967205 := bbase (se 4 (by rfl) ⟨278175, by rfl⟩ : syracuseStep 2967205 = 556351) (by norm_num)
theorem B1853093 : Blo 1234435 1853093 := bbase (se 4 (by rfl) ⟨173727, by rfl⟩ : syracuseStep 1853093 = 347455) (by norm_num)
theorem B4171445 : Blo 1234435 4171445 := bbase (se 5 (by rfl) ⟨195536, by rfl⟩ : syracuseStep 4171445 = 391073) (by norm_num)
theorem B1853117 : Blo 1234435 1853117 := bbase (se 3 (by rfl) ⟨347459, by rfl⟩ : syracuseStep 1853117 = 694919) (by norm_num)
theorem B2778821 : Blo 1234435 2778821 := bbase (se 4 (by rfl) ⟨260514, by rfl⟩ : syracuseStep 2778821 = 521029) (by norm_num)
theorem B1853141 : Blo 1234435 1853141 := bbase (se 7 (by rfl) ⟨21716, by rfl⟩ : syracuseStep 1853141 = 43433) (by norm_num)
theorem B7038677 : Blo 1234435 7038677 := bbase (se 7 (by rfl) ⟨82484, by rfl⟩ : syracuseStep 7038677 = 164969) (by norm_num)
theorem B3385061 : Blo 1234435 3385061 := bbase (se 4 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 3385061 = 634699) (by norm_num)
theorem B1853165 : Blo 1234435 1853165 := bbase (se 3 (by rfl) ⟨347468, by rfl⟩ : syracuseStep 1853165 = 694937) (by norm_num)
theorem B1484525 : Blo 1234435 1484525 := bbase (se 3 (by rfl) ⟨278348, by rfl⟩ : syracuseStep 1484525 = 556697) (by norm_num)
theorem B3516149 : Blo 1234435 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B1853189 : Blo 1234435 1853189 := bbase (se 4 (by rfl) ⟨173736, by rfl⟩ : syracuseStep 1853189 = 347473) (by norm_num)
theorem B2778893 : Blo 1234435 2778893 := bbase (se 3 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 2778893 = 1042085) (by norm_num)
theorem B1853213 : Blo 1234435 1853213 := bbase (se 3 (by rfl) ⟨347477, by rfl⟩ : syracuseStep 1853213 = 694955) (by norm_num)
theorem B1853237 : Blo 1234435 1853237 := bbase (se 5 (by rfl) ⟨86870, by rfl⟩ : syracuseStep 1853237 = 173741) (by norm_num)
theorem B1853261 : Blo 1234435 1853261 := bbase (se 3 (by rfl) ⟨347486, by rfl⟩ : syracuseStep 1853261 = 694973) (by norm_num)
theorem B2778965 : Blo 1234435 2778965 := bbase (se 9 (by rfl) ⟨8141, by rfl⟩ : syracuseStep 2778965 = 16283) (by norm_num)
theorem B6252389 : Blo 1234435 6252389 := bbase (se 4 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 6252389 = 1172323) (by norm_num)
theorem B1853285 : Blo 1234435 1853285 := bbase (se 4 (by rfl) ⟨173745, by rfl⟩ : syracuseStep 1853285 = 347491) (by norm_num)
theorem B1853309 : Blo 1234435 1853309 := bbase (se 3 (by rfl) ⟨347495, by rfl⟩ : syracuseStep 1853309 = 694991) (by norm_num)
theorem B1853333 : Blo 1234435 1853333 := bbase (se 6 (by rfl) ⟨43437, by rfl⟩ : syracuseStep 1853333 = 86875) (by norm_num)
theorem B2779037 : Blo 1234435 2779037 := bbase (se 3 (by rfl) ⟨521069, by rfl⟩ : syracuseStep 2779037 = 1042139) (by norm_num)
theorem B1853357 : Blo 1234435 1853357 := bbase (se 3 (by rfl) ⟨347504, by rfl⟩ : syracuseStep 1853357 = 695009) (by norm_num)
theorem B1853381 : Blo 1234435 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B3008477 : Blo 1234435 3008477 := bbase (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) (by norm_num)
theorem B1853405 : Blo 1234435 1853405 := bbase (se 3 (by rfl) ⟨347513, by rfl⟩ : syracuseStep 1853405 = 695027) (by norm_num)
theorem B2779109 : Blo 1234435 2779109 := bbase (se 4 (by rfl) ⟨260541, by rfl⟩ : syracuseStep 2779109 = 521083) (by norm_num)
theorem B1853429 : Blo 1234435 1853429 := bbase (se 5 (by rfl) ⟨86879, by rfl⟩ : syracuseStep 1853429 = 173759) (by norm_num)
theorem B1853453 : Blo 1234435 1853453 := bbase (se 3 (by rfl) ⟨347522, by rfl⟩ : syracuseStep 1853453 = 695045) (by norm_num)
theorem B1484833 : Blo 1234435 1484833 := bbase (se 2 (by rfl) ⟨556812, by rfl⟩ : syracuseStep 1484833 = 1113625) (by norm_num)
theorem B1853477 : Blo 1234435 1853477 := bbase (se 4 (by rfl) ⟨173763, by rfl⟩ : syracuseStep 1853477 = 347527) (by norm_num)
theorem B2779181 : Blo 1234435 2779181 := bbase (se 3 (by rfl) ⟨521096, by rfl⟩ : syracuseStep 2779181 = 1042193) (by norm_num)
theorem B1853501 : Blo 1234435 1853501 := bbase (se 3 (by rfl) ⟨347531, by rfl⟩ : syracuseStep 1853501 = 695063) (by norm_num)
theorem B1853525 : Blo 1234435 1853525 := bbase (se 8 (by rfl) ⟨10860, by rfl⟩ : syracuseStep 1853525 = 21721) (by norm_num)
theorem B4171877 : Blo 1234435 4171877 := bbase (se 4 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 4171877 = 782227) (by norm_num)
theorem B1853549 : Blo 1234435 1853549 := bbase (se 3 (by rfl) ⟨347540, by rfl⟩ : syracuseStep 1853549 = 695081) (by norm_num)
theorem B2779253 : Blo 1234435 2779253 := bbase (se 5 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 2779253 = 260555) (by norm_num)
theorem B1853573 : Blo 1234435 1853573 := bbase (se 4 (by rfl) ⟨173772, by rfl⟩ : syracuseStep 1853573 = 347545) (by norm_num)
theorem B1853597 : Blo 1234435 1853597 := bbase (se 3 (by rfl) ⟨347549, by rfl⟩ : syracuseStep 1853597 = 695099) (by norm_num)
theorem B2345125 : Blo 1234435 2345125 := bbase (se 4 (by rfl) ⟨219855, by rfl⟩ : syracuseStep 2345125 = 439711) (by norm_num)
theorem B3958949 : Blo 1234435 3958949 := bbase (se 4 (by rfl) ⟨371151, by rfl⟩ : syracuseStep 3958949 = 742303) (by norm_num)
theorem B1853621 : Blo 1234435 1853621 := bbase (se 5 (by rfl) ⟨86888, by rfl⟩ : syracuseStep 1853621 = 173777) (by norm_num)
theorem B2779325 : Blo 1234435 2779325 := bbase (se 3 (by rfl) ⟨521123, by rfl⟩ : syracuseStep 2779325 = 1042247) (by norm_num)
theorem B1853645 : Blo 1234435 1853645 := bbase (se 3 (by rfl) ⟨347558, by rfl⟩ : syracuseStep 1853645 = 695117) (by norm_num)
theorem B26699989 : Blo 1234435 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B1853669 : Blo 1234435 1853669 := bbase (se 4 (by rfl) ⟨173781, by rfl⟩ : syracuseStep 1853669 = 347563) (by norm_num)
theorem B1853693 : Blo 1234435 1853693 := bbase (se 3 (by rfl) ⟨347567, by rfl⟩ : syracuseStep 1853693 = 695135) (by norm_num)
theorem B2779397 : Blo 1234435 2779397 := bbase (se 4 (by rfl) ⟨260568, by rfl⟩ : syracuseStep 2779397 = 521137) (by norm_num)
theorem B1853717 : Blo 1234435 1853717 := bbase (se 6 (by rfl) ⟨43446, by rfl⟩ : syracuseStep 1853717 = 86893) (by norm_num)
theorem B2083117 : Blo 1234435 2083117 := bbase (se 3 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 2083117 = 781169) (by norm_num)
theorem B1853741 : Blo 1234435 1853741 := bbase (se 3 (by rfl) ⟨347576, by rfl⟩ : syracuseStep 1853741 = 695153) (by norm_num)
theorem B8898869 : Blo 1234435 8898869 := bbase (se 5 (by rfl) ⟨417134, by rfl⟩ : syracuseStep 8898869 = 834269) (by norm_num)
theorem B2345269 : Blo 1234435 2345269 := bbase (se 5 (by rfl) ⟨109934, by rfl⟩ : syracuseStep 2345269 = 219869) (by norm_num)
theorem B1853765 : Blo 1234435 1853765 := bbase (se 4 (by rfl) ⟨173790, by rfl⟩ : syracuseStep 1853765 = 347581) (by norm_num)
theorem B2779469 : Blo 1234435 2779469 := bbase (se 3 (by rfl) ⟨521150, by rfl⟩ : syracuseStep 2779469 = 1042301) (by norm_num)
theorem B2640205 : Blo 1234435 2640205 := bbase (se 3 (by rfl) ⟨495038, by rfl⟩ : syracuseStep 2640205 = 990077) (by norm_num)
theorem B9382229 : Blo 1234435 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B1853789 : Blo 1234435 1853789 := bbase (se 3 (by rfl) ⟨347585, by rfl⟩ : syracuseStep 1853789 = 695171) (by norm_num)
theorem B1853813 : Blo 1234435 1853813 := bbase (se 5 (by rfl) ⟨86897, by rfl⟩ : syracuseStep 1853813 = 173795) (by norm_num)
theorem B2083205 : Blo 1234435 2083205 := bbase (se 4 (by rfl) ⟨195300, by rfl⟩ : syracuseStep 2083205 = 390601) (by norm_num)
theorem B1853837 : Blo 1234435 1853837 := bbase (se 3 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 1853837 = 695189) (by norm_num)
theorem B2779541 : Blo 1234435 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B1853861 : Blo 1234435 1853861 := bbase (se 4 (by rfl) ⟨173799, by rfl⟩ : syracuseStep 1853861 = 347599) (by norm_num)
theorem B1485221 : Blo 1234435 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B1853885 : Blo 1234435 1853885 := bbase (se 3 (by rfl) ⟨347603, by rfl⟩ : syracuseStep 1853885 = 695207) (by norm_num)
theorem B2345429 : Blo 1234435 2345429 := bbase (se 7 (by rfl) ⟨27485, by rfl⟩ : syracuseStep 2345429 = 54971) (by norm_num)
theorem B1853909 : Blo 1234435 1853909 := bbase (se 7 (by rfl) ⟨21725, by rfl⟩ : syracuseStep 1853909 = 43451) (by norm_num)
theorem B2779613 : Blo 1234435 2779613 := bbase (se 3 (by rfl) ⟨521177, by rfl⟩ : syracuseStep 2779613 = 1042355) (by norm_num)
theorem B1853933 : Blo 1234435 1853933 := bbase (se 3 (by rfl) ⟨347612, by rfl⟩ : syracuseStep 1853933 = 695225) (by norm_num)
theorem B2083333 : Blo 1234435 2083333 := bbase (se 4 (by rfl) ⟨195312, by rfl⟩ : syracuseStep 2083333 = 390625) (by norm_num)
theorem B1853957 : Blo 1234435 1853957 := bbase (se 4 (by rfl) ⟨173808, by rfl⟩ : syracuseStep 1853957 = 347617) (by norm_num)
theorem B4172309 : Blo 1234435 4172309 := bbase (se 6 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 4172309 = 195577) (by norm_num)
theorem B1853981 : Blo 1234435 1853981 := bbase (se 3 (by rfl) ⟨347621, by rfl⟩ : syracuseStep 1853981 = 695243) (by norm_num)
theorem B2779685 : Blo 1234435 2779685 := bbase (se 4 (by rfl) ⟨260595, by rfl⟩ : syracuseStep 2779685 = 521191) (by norm_num)
theorem B2673197 : Blo 1234435 2673197 := bbase (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) (by norm_num)
theorem B1854005 : Blo 1234435 1854005 := bbase (se 5 (by rfl) ⟨86906, by rfl⟩ : syracuseStep 1854005 = 173813) (by norm_num)
theorem B1854029 : Blo 1234435 1854029 := bbase (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) (by norm_num)
theorem B2083421 : Blo 1234435 2083421 := bbase (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) (by norm_num)
theorem B2345573 : Blo 1234435 2345573 := bbase (se 4 (by rfl) ⟨219897, by rfl⟩ : syracuseStep 2345573 = 439795) (by norm_num)
theorem B1854053 : Blo 1234435 1854053 := bbase (se 4 (by rfl) ⟨173817, by rfl⟩ : syracuseStep 1854053 = 347635) (by norm_num)
theorem B2779757 : Blo 1234435 2779757 := bbase (se 3 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 2779757 = 1042409) (by norm_num)
theorem B1854077 : Blo 1234435 1854077 := bbase (se 3 (by rfl) ⟨347639, by rfl⟩ : syracuseStep 1854077 = 695279) (by norm_num)
theorem B1854101 : Blo 1234435 1854101 := bbase (se 6 (by rfl) ⟨43455, by rfl⟩ : syracuseStep 1854101 = 86911) (by norm_num)
theorem B4688549 : Blo 1234435 4688549 := bbase (se 4 (by rfl) ⟨439551, by rfl⟩ : syracuseStep 4688549 = 879103) (by norm_num)
theorem B1854125 : Blo 1234435 1854125 := bbase (se 3 (by rfl) ⟨347648, by rfl⟩ : syracuseStep 1854125 = 695297) (by norm_num)
theorem B2779829 : Blo 1234435 2779829 := bbase (se 5 (by rfl) ⟨130304, by rfl⟩ : syracuseStep 2779829 = 260609) (by norm_num)
theorem B1854149 : Blo 1234435 1854149 := bbase (se 4 (by rfl) ⟨173826, by rfl⟩ : syracuseStep 1854149 = 347653) (by norm_num)
theorem B3517141 : Blo 1234435 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B2083549 : Blo 1234435 2083549 := bbase (se 3 (by rfl) ⟨390665, by rfl⟩ : syracuseStep 2083549 = 781331) (by norm_num)
theorem B1854173 : Blo 1234435 1854173 := bbase (se 3 (by rfl) ⟨347657, by rfl⟩ : syracuseStep 1854173 = 695315) (by norm_num)
theorem B1583849 : Blo 1234435 1583849 := bbase (se 2 (by rfl) ⟨593943, by rfl⟩ : syracuseStep 1583849 = 1187887) (by norm_num)
theorem B9374453 : Blo 1234435 9374453 := bbase (se 5 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 9374453 = 878855) (by norm_num)
theorem B1854197 : Blo 1234435 1854197 := bbase (se 5 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 1854197 = 173831) (by norm_num)
theorem B2779901 : Blo 1234435 2779901 := bbase (se 3 (by rfl) ⟨521231, by rfl⟩ : syracuseStep 2779901 = 1042463) (by norm_num)
theorem B1854221 : Blo 1234435 1854221 := bbase (se 3 (by rfl) ⟨347666, by rfl⟩ : syracuseStep 1854221 = 695333) (by norm_num)
theorem B1854245 : Blo 1234435 1854245 := bbase (se 4 (by rfl) ⟨173835, by rfl⟩ : syracuseStep 1854245 = 347671) (by norm_num)
theorem B3337013 : Blo 1234435 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B2083637 : Blo 1234435 2083637 := bbase (se 5 (by rfl) ⟨97670, by rfl⟩ : syracuseStep 2083637 = 195341) (by norm_num)
theorem B1854269 : Blo 1234435 1854269 := bbase (se 3 (by rfl) ⟨347675, by rfl⟩ : syracuseStep 1854269 = 695351) (by norm_num)
theorem B2640701 : Blo 1234435 2640701 := bbase (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) (by norm_num)
theorem B2779973 : Blo 1234435 2779973 := bbase (se 4 (by rfl) ⟨260622, by rfl⟩ : syracuseStep 2779973 = 521245) (by norm_num)
theorem B1854293 : Blo 1234435 1854293 := bbase (se 9 (by rfl) ⟨5432, by rfl⟩ : syracuseStep 1854293 = 10865) (by norm_num)
theorem B1854317 : Blo 1234435 1854317 := bbase (se 3 (by rfl) ⟨347684, by rfl⟩ : syracuseStep 1854317 = 695369) (by norm_num)
theorem B2345861 : Blo 1234435 2345861 := bbase (se 4 (by rfl) ⟨219924, by rfl⟩ : syracuseStep 2345861 = 439849) (by norm_num)
theorem B1854341 : Blo 1234435 1854341 := bbase (se 4 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 1854341 = 347689) (by norm_num)
theorem B2780045 : Blo 1234435 2780045 := bbase (se 3 (by rfl) ⟨521258, by rfl⟩ : syracuseStep 2780045 = 1042517) (by norm_num)
theorem B1854365 : Blo 1234435 1854365 := bbase (se 3 (by rfl) ⟨347693, by rfl⟩ : syracuseStep 1854365 = 695387) (by norm_num)
theorem B2083765 : Blo 1234435 2083765 := bbase (se 5 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 2083765 = 195353) (by norm_num)
theorem B5934005 : Blo 1234435 5934005 := bbase (se 5 (by rfl) ⟨278156, by rfl⟩ : syracuseStep 5934005 = 556313) (by norm_num)
theorem B1854389 : Blo 1234435 1854389 := bbase (se 5 (by rfl) ⟨86924, by rfl⟩ : syracuseStep 1854389 = 173849) (by norm_num)
theorem B4688837 : Blo 1234435 4688837 := bbase (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) (by norm_num)
theorem B4172741 : Blo 1234435 4172741 := bbase (se 4 (by rfl) ⟨391194, by rfl⟩ : syracuseStep 4172741 = 782389) (by norm_num)
theorem B1854413 : Blo 1234435 1854413 := bbase (se 3 (by rfl) ⟨347702, by rfl⟩ : syracuseStep 1854413 = 695405) (by norm_num)
theorem B2780117 : Blo 1234435 2780117 := bbase (se 7 (by rfl) ⟨32579, by rfl⟩ : syracuseStep 2780117 = 65159) (by norm_num)
theorem B1854437 : Blo 1234435 1854437 := bbase (se 4 (by rfl) ⟨173853, by rfl⟩ : syracuseStep 1854437 = 347707) (by norm_num)
theorem B1854461 : Blo 1234435 1854461 := bbase (se 3 (by rfl) ⟨347711, by rfl⟩ : syracuseStep 1854461 = 695423) (by norm_num)
theorem B2083853 : Blo 1234435 2083853 := bbase (se 3 (by rfl) ⟨390722, by rfl⟩ : syracuseStep 2083853 = 781445) (by norm_num)
theorem B1854485 : Blo 1234435 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B1977373 : Blo 1234435 1977373 := bbase (se 3 (by rfl) ⟨370757, by rfl⟩ : syracuseStep 1977373 = 741515) (by norm_num)
theorem B2780189 : Blo 1234435 2780189 := bbase (se 3 (by rfl) ⟨521285, by rfl⟩ : syracuseStep 2780189 = 1042571) (by norm_num)
theorem B2346013 : Blo 1234435 2346013 := bbase (se 3 (by rfl) ⟨439877, by rfl⟩ : syracuseStep 2346013 = 879755) (by norm_num)
theorem B1854509 : Blo 1234435 1854509 := bbase (se 3 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 1854509 = 695441) (by norm_num)
theorem B1854533 : Blo 1234435 1854533 := bbase (se 4 (by rfl) ⟨173862, by rfl⟩ : syracuseStep 1854533 = 347725) (by norm_num)
theorem B1854557 : Blo 1234435 1854557 := bbase (se 3 (by rfl) ⟨347729, by rfl⟩ : syracuseStep 1854557 = 695459) (by norm_num)
theorem B2780261 : Blo 1234435 2780261 := bbase (se 4 (by rfl) ⟨260649, by rfl⟩ : syracuseStep 2780261 = 521299) (by norm_num)
theorem B6253685 : Blo 1234435 6253685 := bbase (se 5 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 6253685 = 586283) (by norm_num)
theorem B1854581 : Blo 1234435 1854581 := bbase (se 5 (by rfl) ⟨86933, by rfl⟩ : syracuseStep 1854581 = 173867) (by norm_num)
theorem B2083981 : Blo 1234435 2083981 := bbase (se 3 (by rfl) ⟨390746, by rfl⟩ : syracuseStep 2083981 = 781493) (by norm_num)
theorem B1854605 : Blo 1234435 1854605 := bbase (se 3 (by rfl) ⟨347738, by rfl⟩ : syracuseStep 1854605 = 695477) (by norm_num)
theorem B5500069 : Blo 1234435 5500069 := bbase (se 4 (by rfl) ⟨515631, by rfl⟩ : syracuseStep 5500069 = 1031263) (by norm_num)
theorem B1854629 : Blo 1234435 1854629 := bbase (se 4 (by rfl) ⟨173871, by rfl⟩ : syracuseStep 1854629 = 347743) (by norm_num)
theorem B2780333 : Blo 1234435 2780333 := bbase (se 3 (by rfl) ⟨521312, by rfl⟩ : syracuseStep 2780333 = 1042625) (by norm_num)
theorem B1854653 : Blo 1234435 1854653 := bbase (se 3 (by rfl) ⟨347747, by rfl⟩ : syracuseStep 1854653 = 695495) (by norm_num)
theorem B2084069 : Blo 1234435 2084069 := bbase (se 4 (by rfl) ⟨195381, by rfl⟩ : syracuseStep 2084069 = 390763) (by norm_num)
theorem B2780405 : Blo 1234435 2780405 := bbase (se 5 (by rfl) ⟨130331, by rfl⟩ : syracuseStep 2780405 = 260663) (by norm_num)
theorem B3755285 : Blo 1234435 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B1977629 : Blo 1234435 1977629 := bbase (se 3 (by rfl) ⟨370805, by rfl⟩ : syracuseStep 1977629 = 741611) (by norm_num)
theorem B2780477 : Blo 1234435 2780477 := bbase (se 3 (by rfl) ⟨521339, by rfl⟩ : syracuseStep 2780477 = 1042679) (by norm_num)
theorem B2346317 : Blo 1234435 2346317 := bbase (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) (by norm_num)
theorem B6344021 : Blo 1234435 6344021 := bbase (se 11 (by rfl) ⟨4646, by rfl⟩ : syracuseStep 6344021 = 9293) (by norm_num)
theorem B2084197 : Blo 1234435 2084197 := bbase (se 4 (by rfl) ⟨195393, by rfl⟩ : syracuseStep 2084197 = 390787) (by norm_num)
theorem B2780549 : Blo 1234435 2780549 := bbase (se 4 (by rfl) ⟨260676, by rfl⟩ : syracuseStep 2780549 = 521353) (by norm_num)
theorem B1584569 : Blo 1234435 1584569 := bbase (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) (by norm_num)
theorem B2084285 : Blo 1234435 2084285 := bbase (se 3 (by rfl) ⟨390803, by rfl⟩ : syracuseStep 2084285 = 781607) (by norm_num)
theorem B2780621 : Blo 1234435 2780621 := bbase (se 3 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 2780621 = 1042733) (by norm_num)
theorem B4009429 : Blo 1234435 4009429 := bbase (se 7 (by rfl) ⟨46985, by rfl⟩ : syracuseStep 4009429 = 93971) (by norm_num)
theorem B3124757 : Blo 1234435 3124757 := bbase (se 6 (by rfl) ⟨73236, by rfl⟩ : syracuseStep 3124757 = 146473) (by norm_num)
theorem B7917077 : Blo 1234435 7917077 := bbase (se 6 (by rfl) ⟨185556, by rfl⟩ : syracuseStep 7917077 = 371113) (by norm_num)
theorem B2780693 : Blo 1234435 2780693 := bbase (se 6 (by rfl) ⟨65172, by rfl⟩ : syracuseStep 2780693 = 130345) (by norm_num)
theorem B3960373 : Blo 1234435 3960373 := bbase (se 5 (by rfl) ⟨185642, by rfl⟩ : syracuseStep 3960373 = 371285) (by norm_num)
theorem B2084413 : Blo 1234435 2084413 := bbase (se 3 (by rfl) ⟨390827, by rfl⟩ : syracuseStep 2084413 = 781655) (by norm_num)
theorem B2780765 : Blo 1234435 2780765 := bbase (se 3 (by rfl) ⟨521393, by rfl⟩ : syracuseStep 2780765 = 1042787) (by norm_num)
theorem B2084501 : Blo 1234435 2084501 := bbase (se 6 (by rfl) ⟨48855, by rfl⟩ : syracuseStep 2084501 = 97711) (by norm_num)
theorem B2780837 : Blo 1234435 2780837 := bbase (se 4 (by rfl) ⟨260703, by rfl⟩ : syracuseStep 2780837 = 521407) (by norm_num)
theorem B2780909 : Blo 1234435 2780909 := bbase (se 3 (by rfl) ⟨521420, by rfl⟩ : syracuseStep 2780909 = 1042841) (by norm_num)
theorem B2084629 : Blo 1234435 2084629 := bbase (se 6 (by rfl) ⟨48858, by rfl⟩ : syracuseStep 2084629 = 97717) (by norm_num)
theorem B3518245 : Blo 1234435 3518245 := bbase (se 4 (by rfl) ⟨329835, by rfl⟩ : syracuseStep 3518245 = 659671) (by norm_num)
theorem B5353253 : Blo 1234435 5353253 := bbase (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) (by norm_num)
theorem B2748205 : Blo 1234435 2748205 := bbase (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) (by norm_num)
theorem B2780981 : Blo 1234435 2780981 := bbase (se 5 (by rfl) ⟨130358, by rfl⟩ : syracuseStep 2780981 = 260717) (by norm_num)
theorem B3125101 : Blo 1234435 3125101 := bbase (se 3 (by rfl) ⟨585956, by rfl⟩ : syracuseStep 3125101 = 1171913) (by norm_num)
theorem B2084717 : Blo 1234435 2084717 := bbase (se 3 (by rfl) ⟨390884, by rfl⟩ : syracuseStep 2084717 = 781769) (by norm_num)
theorem B2781053 : Blo 1234435 2781053 := bbase (se 3 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 2781053 = 1042895) (by norm_num)
theorem B2781125 : Blo 1234435 2781125 := bbase (se 4 (by rfl) ⟨260730, by rfl⟩ : syracuseStep 2781125 = 521461) (by norm_num)
theorem B3125213 : Blo 1234435 3125213 := bbase (se 3 (by rfl) ⟨585977, by rfl⟩ : syracuseStep 3125213 = 1171955) (by norm_num)
theorem B2084845 : Blo 1234435 2084845 := bbase (se 3 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 2084845 = 781817) (by norm_num)
theorem B2969597 : Blo 1234435 2969597 := bbase (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) (by norm_num)
theorem B2781197 : Blo 1234435 2781197 := bbase (se 3 (by rfl) ⟨521474, by rfl⟩ : syracuseStep 2781197 = 1042949) (by norm_num)
theorem B2347069 : Blo 1234435 2347069 := bbase (se 3 (by rfl) ⟨440075, by rfl⟩ : syracuseStep 2347069 = 880151) (by norm_num)
theorem B2084933 : Blo 1234435 2084933 := bbase (se 4 (by rfl) ⟨195462, by rfl⟩ : syracuseStep 2084933 = 390925) (by norm_num)
theorem B5279813 : Blo 1234435 5279813 := bbase (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) (by norm_num)
theorem B1585225 : Blo 1234435 1585225 := bbase (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) (by norm_num)
theorem B2781269 : Blo 1234435 2781269 := bbase (se 8 (by rfl) ⟨16296, by rfl⟩ : syracuseStep 2781269 = 32593) (by norm_num)
theorem B4690021 : Blo 1234435 4690021 := bbase (se 4 (by rfl) ⟨439689, by rfl⟩ : syracuseStep 4690021 = 879379) (by norm_num)
theorem B1978501 : Blo 1234435 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B2969741 : Blo 1234435 2969741 := bbase (se 3 (by rfl) ⟨556826, by rfl⟩ : syracuseStep 2969741 = 1113653) (by norm_num)
theorem B3125405 : Blo 1234435 3125405 := bbase (se 3 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 3125405 = 1172027) (by norm_num)
theorem B2781341 : Blo 1234435 2781341 := bbase (se 3 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 2781341 = 1043003) (by norm_num)
theorem B2085061 : Blo 1234435 2085061 := bbase (se 4 (by rfl) ⟨195474, by rfl⟩ : syracuseStep 2085061 = 390949) (by norm_num)
theorem B1388749 : Blo 1234435 1388749 := bbase (se 3 (by rfl) ⟨260390, by rfl⟩ : syracuseStep 1388749 = 520781) (by norm_num)
theorem B2347213 : Blo 1234435 2347213 := bbase (se 3 (by rfl) ⟨440102, by rfl⟩ : syracuseStep 2347213 = 880205) (by norm_num)
theorem B1978597 : Blo 1234435 1978597 := bbase (se 4 (by rfl) ⟨185493, by rfl⟩ : syracuseStep 1978597 = 370987) (by norm_num)
theorem B2781413 : Blo 1234435 2781413 := bbase (se 4 (by rfl) ⟨260757, by rfl⟩ : syracuseStep 2781413 = 521515) (by norm_num)
theorem B1388785 : Blo 1234435 1388785 := bbase (se 2 (by rfl) ⟨520794, by rfl⟩ : syracuseStep 1388785 = 1041589) (by norm_num)
theorem B1388821 : Blo 1234435 1388821 := bbase (se 6 (by rfl) ⟨32550, by rfl⟩ : syracuseStep 1388821 = 65101) (by norm_num)
theorem B2085149 : Blo 1234435 2085149 := bbase (se 3 (by rfl) ⟨390965, by rfl⟩ : syracuseStep 2085149 = 781931) (by norm_num)
theorem B2674981 : Blo 1234435 2674981 := bbase (se 4 (by rfl) ⟨250779, by rfl⟩ : syracuseStep 2674981 = 501559) (by norm_num)
theorem B2781485 : Blo 1234435 2781485 := bbase (se 3 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 2781485 = 1043057) (by norm_num)
theorem B1388857 : Blo 1234435 1388857 := bbase (se 2 (by rfl) ⟨520821, by rfl⟩ : syracuseStep 1388857 = 1041643) (by norm_num)
theorem B1388893 : Blo 1234435 1388893 := bbase (se 3 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 1388893 = 520835) (by norm_num)
theorem B10015093 : Blo 1234435 10015093 := bbase (se 5 (by rfl) ⟨469457, by rfl⟩ : syracuseStep 10015093 = 938915) (by norm_num)
theorem B3051893 : Blo 1234435 3051893 := bbase (se 5 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 3051893 = 286115) (by norm_num)
theorem B2781557 : Blo 1234435 2781557 := bbase (se 5 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 2781557 = 260771) (by norm_num)
theorem B1388929 : Blo 1234435 1388929 := bbase (se 2 (by rfl) ⟨520848, by rfl⟩ : syracuseStep 1388929 = 1041697) (by norm_num)
theorem B1978757 : Blo 1234435 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B6254981 : Blo 1234435 6254981 := bbase (se 4 (by rfl) ⟨586404, by rfl⟩ : syracuseStep 6254981 = 1172809) (by norm_num)
theorem B4690325 : Blo 1234435 4690325 := bbase (se 6 (by rfl) ⟨109929, by rfl⟩ : syracuseStep 4690325 = 219859) (by norm_num)
theorem B2085277 : Blo 1234435 2085277 := bbase (se 3 (by rfl) ⟨390989, by rfl⟩ : syracuseStep 2085277 = 781979) (by norm_num)
theorem B1388965 : Blo 1234435 1388965 := bbase (se 4 (by rfl) ⟨130215, by rfl⟩ : syracuseStep 1388965 = 260431) (by norm_num)
theorem B10555829 : Blo 1234435 10555829 := bbase (se 5 (by rfl) ⟨494804, by rfl⟩ : syracuseStep 10555829 = 989609) (by norm_num)
theorem B12038581 : Blo 1234435 12038581 := bbase (se 5 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 12038581 = 1128617) (by norm_num)
theorem B7516597 : Blo 1234435 7516597 := bbase (se 5 (by rfl) ⟨352340, by rfl⟩ : syracuseStep 7516597 = 704681) (by norm_num)
theorem B2781629 : Blo 1234435 2781629 := bbase (se 3 (by rfl) ⟨521555, by rfl⟩ : syracuseStep 2781629 = 1043111) (by norm_num)
theorem B1389001 : Blo 1234435 1389001 := bbase (se 2 (by rfl) ⟨520875, by rfl⟩ : syracuseStep 1389001 = 1041751) (by norm_num)
theorem B7033301 : Blo 1234435 7033301 := bbase (se 7 (by rfl) ⟨82421, by rfl⟩ : syracuseStep 7033301 = 164843) (by norm_num)
theorem B1389037 : Blo 1234435 1389037 := bbase (se 3 (by rfl) ⟨260444, by rfl⟩ : syracuseStep 1389037 = 520889) (by norm_num)
theorem B3125749 : Blo 1234435 3125749 := bbase (se 5 (by rfl) ⟨146519, by rfl⟩ : syracuseStep 3125749 = 293039) (by norm_num)
theorem B2085365 : Blo 1234435 2085365 := bbase (se 5 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 2085365 = 195503) (by norm_num)
theorem B2781701 : Blo 1234435 2781701 := bbase (se 4 (by rfl) ⟨260784, by rfl⟩ : syracuseStep 2781701 = 521569) (by norm_num)
theorem B1389073 : Blo 1234435 1389073 := bbase (se 2 (by rfl) ⟨520902, by rfl⟩ : syracuseStep 1389073 = 1041805) (by norm_num)
theorem B1692181 : Blo 1234435 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B10547765 : Blo 1234435 10547765 := bbase (se 5 (by rfl) ⟨494426, by rfl⟩ : syracuseStep 10547765 = 988853) (by norm_num)
theorem B1389109 : Blo 1234435 1389109 := bbase (se 5 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 1389109 = 130229) (by norm_num)
theorem B2781773 : Blo 1234435 2781773 := bbase (se 3 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 2781773 = 1043165) (by norm_num)
theorem B1389145 : Blo 1234435 1389145 := bbase (se 2 (by rfl) ⟨520929, by rfl⟩ : syracuseStep 1389145 = 1041859) (by norm_num)
theorem B3125861 : Blo 1234435 3125861 := bbase (se 4 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 3125861 = 586099) (by norm_num)
theorem B4166261 : Blo 1234435 4166261 := bbase (se 5 (by rfl) ⟨195293, by rfl⟩ : syracuseStep 4166261 = 390587) (by norm_num)
theorem B2085493 : Blo 1234435 2085493 := bbase (se 5 (by rfl) ⟨97757, by rfl⟩ : syracuseStep 2085493 = 195515) (by norm_num)
theorem B1389181 : Blo 1234435 1389181 := bbase (se 3 (by rfl) ⟨260471, by rfl⟩ : syracuseStep 1389181 = 520943) (by norm_num)
theorem B2781845 : Blo 1234435 2781845 := bbase (se 6 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 2781845 = 130399) (by norm_num)
theorem B1389217 : Blo 1234435 1389217 := bbase (se 2 (by rfl) ⟨520956, by rfl⟩ : syracuseStep 1389217 = 1041913) (by norm_num)
theorem B1389253 : Blo 1234435 1389253 := bbase (se 4 (by rfl) ⟨130242, by rfl⟩ : syracuseStep 1389253 = 260485) (by norm_num)
theorem B2085581 : Blo 1234435 2085581 := bbase (se 3 (by rfl) ⟨391046, by rfl⟩ : syracuseStep 2085581 = 782093) (by norm_num)
theorem B2781917 : Blo 1234435 2781917 := bbase (se 3 (by rfl) ⟨521609, by rfl⟩ : syracuseStep 2781917 = 1043219) (by norm_num)
theorem B1389289 : Blo 1234435 1389289 := bbase (se 2 (by rfl) ⟨520983, by rfl⟩ : syracuseStep 1389289 = 1041967) (by norm_num)
theorem B10695413 : Blo 1234435 10695413 := bbase (se 5 (by rfl) ⟨501347, by rfl⟩ : syracuseStep 10695413 = 1002695) (by norm_num)
theorem B1389325 : Blo 1234435 1389325 := bbase (se 3 (by rfl) ⟨260498, by rfl⟩ : syracuseStep 1389325 = 520997) (by norm_num)
theorem B4223765 : Blo 1234435 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B3126053 : Blo 1234435 3126053 := bbase (se 4 (by rfl) ⟨293067, by rfl⟩ : syracuseStep 3126053 = 586135) (by norm_num)
theorem B1389361 : Blo 1234435 1389361 := bbase (se 2 (by rfl) ⟨521010, by rfl⟩ : syracuseStep 1389361 = 1042021) (by norm_num)
theorem B1758029 : Blo 1234435 1758029 := bbase (se 3 (by rfl) ⟨329630, by rfl⟩ : syracuseStep 1758029 = 659261) (by norm_num)
theorem B2085709 : Blo 1234435 2085709 := bbase (se 3 (by rfl) ⟨391070, by rfl⟩ : syracuseStep 2085709 = 782141) (by norm_num)
theorem B1389397 : Blo 1234435 1389397 := bbase (se 9 (by rfl) ⟨4070, by rfl⟩ : syracuseStep 1389397 = 8141) (by norm_num)
theorem B1692509 : Blo 1234435 1692509 := bbase (se 3 (by rfl) ⟨317345, by rfl⟩ : syracuseStep 1692509 = 634691) (by norm_num)
theorem B1389433 : Blo 1234435 1389433 := bbase (se 2 (by rfl) ⟨521037, by rfl⟩ : syracuseStep 1389433 = 1042075) (by norm_num)
theorem B1389469 : Blo 1234435 1389469 := bbase (se 3 (by rfl) ⟨260525, by rfl⟩ : syracuseStep 1389469 = 521051) (by norm_num)
theorem B2085797 : Blo 1234435 2085797 := bbase (se 4 (by rfl) ⟨195543, by rfl⟩ : syracuseStep 2085797 = 391087) (by norm_num)
theorem B1389505 : Blo 1234435 1389505 := bbase (se 2 (by rfl) ⟨521064, by rfl⟩ : syracuseStep 1389505 = 1042129) (by norm_num)
theorem B1389541 : Blo 1234435 1389541 := bbase (se 4 (by rfl) ⟨130269, by rfl⟩ : syracuseStep 1389541 = 260539) (by norm_num)
theorem B2503685 : Blo 1234435 2503685 := bbase (se 4 (by rfl) ⟨234720, by rfl⟩ : syracuseStep 2503685 = 469441) (by norm_num)
theorem B1389577 : Blo 1234435 1389577 := bbase (se 2 (by rfl) ⟨521091, by rfl⟩ : syracuseStep 1389577 = 1042183) (by norm_num)
theorem B4166693 : Blo 1234435 4166693 := bbase (se 4 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 4166693 = 781255) (by norm_num)
theorem B2085925 : Blo 1234435 2085925 := bbase (se 4 (by rfl) ⟨195555, by rfl⟩ : syracuseStep 2085925 = 391111) (by norm_num)
theorem B1389613 : Blo 1234435 1389613 := bbase (se 3 (by rfl) ⟨260552, by rfl⟩ : syracuseStep 1389613 = 521105) (by norm_num)
theorem B5280821 : Blo 1234435 5280821 := bbase (se 5 (by rfl) ⟨247538, by rfl⟩ : syracuseStep 5280821 = 495077) (by norm_num)
theorem B1389649 : Blo 1234435 1389649 := bbase (se 2 (by rfl) ⟨521118, by rfl⟩ : syracuseStep 1389649 = 1042237) (by norm_num)
theorem B1389685 : Blo 1234435 1389685 := bbase (se 5 (by rfl) ⟨65141, by rfl⟩ : syracuseStep 1389685 = 130283) (by norm_num)
theorem B8909941 : Blo 1234435 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B1447033 : Blo 1234435 1447033 := bbase (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) (by norm_num)
theorem B3126397 : Blo 1234435 3126397 := bbase (se 3 (by rfl) ⟨586199, by rfl⟩ : syracuseStep 3126397 = 1172399) (by norm_num)
theorem B2086013 : Blo 1234435 2086013 := bbase (se 3 (by rfl) ⟨391127, by rfl⟩ : syracuseStep 2086013 = 782255) (by norm_num)
theorem B1389721 : Blo 1234435 1389721 := bbase (se 2 (by rfl) ⟨521145, by rfl⟩ : syracuseStep 1389721 = 1042291) (by norm_num)
theorem B1389757 : Blo 1234435 1389757 := bbase (se 3 (by rfl) ⟨260579, by rfl⟩ : syracuseStep 1389757 = 521159) (by norm_num)
theorem B1389793 : Blo 1234435 1389793 := bbase (se 2 (by rfl) ⟨521172, by rfl⟩ : syracuseStep 1389793 = 1042345) (by norm_num)
theorem B3126509 : Blo 1234435 3126509 := bbase (se 3 (by rfl) ⟨586220, by rfl⟩ : syracuseStep 3126509 = 1172441) (by norm_num)
theorem B2086141 : Blo 1234435 2086141 := bbase (se 3 (by rfl) ⟨391151, by rfl⟩ : syracuseStep 2086141 = 782303) (by norm_num)
theorem B1389829 : Blo 1234435 1389829 := bbase (se 4 (by rfl) ⟨130296, by rfl⟩ : syracuseStep 1389829 = 260593) (by norm_num)
theorem B3519749 : Blo 1234435 3519749 := bbase (se 4 (by rfl) ⟨329976, by rfl⟩ : syracuseStep 3519749 = 659953) (by norm_num)
theorem B1389865 : Blo 1234435 1389865 := bbase (se 2 (by rfl) ⟨521199, by rfl⟩ : syracuseStep 1389865 = 1042399) (by norm_num)
theorem B2225461 : Blo 1234435 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B1389901 : Blo 1234435 1389901 := bbase (se 3 (by rfl) ⟨260606, by rfl⟩ : syracuseStep 1389901 = 521213) (by norm_num)
theorem B2086229 : Blo 1234435 2086229 := bbase (se 15 (by rfl) ⟨95, by rfl⟩ : syracuseStep 2086229 = 191) (by norm_num)
theorem B1389937 : Blo 1234435 1389937 := bbase (se 2 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 1389937 = 1042453) (by norm_num)
theorem B1389973 : Blo 1234435 1389973 := bbase (se 6 (by rfl) ⟨32577, by rfl⟩ : syracuseStep 1389973 = 65155) (by norm_num)
theorem B3126701 : Blo 1234435 3126701 := bbase (se 3 (by rfl) ⟨586256, by rfl⟩ : syracuseStep 3126701 = 1172513) (by norm_num)
theorem B1390009 : Blo 1234435 1390009 := bbase (se 2 (by rfl) ⟨521253, by rfl⟩ : syracuseStep 1390009 = 1042507) (by norm_num)
theorem B4167125 : Blo 1234435 4167125 := bbase (se 7 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 4167125 = 97667) (by norm_num)
theorem B2086357 : Blo 1234435 2086357 := bbase (se 7 (by rfl) ⟨24449, by rfl⟩ : syracuseStep 2086357 = 48899) (by norm_num)
theorem B1390045 : Blo 1234435 1390045 := bbase (se 3 (by rfl) ⟨260633, by rfl⟩ : syracuseStep 1390045 = 521267) (by norm_num)
theorem B1979885 : Blo 1234435 1979885 := bbase (se 3 (by rfl) ⟨371228, by rfl⟩ : syracuseStep 1979885 = 742457) (by norm_num)
theorem B3094013 : Blo 1234435 3094013 := bbase (se 3 (by rfl) ⟨580127, by rfl⟩ : syracuseStep 3094013 = 1160255) (by norm_num)
theorem B1390081 : Blo 1234435 1390081 := bbase (se 2 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 1390081 = 1042561) (by norm_num)
theorem B1390117 : Blo 1234435 1390117 := bbase (se 4 (by rfl) ⟨130323, by rfl⟩ : syracuseStep 1390117 = 260647) (by norm_num)
theorem B2086445 : Blo 1234435 2086445 := bbase (se 3 (by rfl) ⟨391208, by rfl⟩ : syracuseStep 2086445 = 782417) (by norm_num)
theorem B1758781 : Blo 1234435 1758781 := bbase (se 3 (by rfl) ⟨329771, by rfl⟩ : syracuseStep 1758781 = 659543) (by norm_num)
theorem B3339845 : Blo 1234435 3339845 := bbase (se 4 (by rfl) ⟨313110, by rfl⟩ : syracuseStep 3339845 = 626221) (by norm_num)
theorem B1390153 : Blo 1234435 1390153 := bbase (se 2 (by rfl) ⟨521307, by rfl⟩ : syracuseStep 1390153 = 1042615) (by norm_num)
theorem B1390189 : Blo 1234435 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B7034485 : Blo 1234435 7034485 := bbase (se 5 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 7034485 = 659483) (by norm_num)
theorem B2504317 : Blo 1234435 2504317 := bbase (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) (by norm_num)
theorem B3167885 : Blo 1234435 3167885 := bbase (se 3 (by rfl) ⟨593978, by rfl⟩ : syracuseStep 3167885 = 1187957) (by norm_num)
theorem B1390225 : Blo 1234435 1390225 := bbase (se 2 (by rfl) ⟨521334, by rfl⟩ : syracuseStep 1390225 = 1042669) (by norm_num)
theorem B6256277 : Blo 1234435 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B1390261 : Blo 1234435 1390261 := bbase (se 5 (by rfl) ⟨65168, by rfl⟩ : syracuseStep 1390261 = 130337) (by norm_num)
theorem B1390297 : Blo 1234435 1390297 := bbase (se 2 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 1390297 = 1042723) (by norm_num)
theorem B1390333 : Blo 1234435 1390333 := bbase (se 3 (by rfl) ⟨260687, by rfl⟩ : syracuseStep 1390333 = 521375) (by norm_num)
theorem B3127045 : Blo 1234435 3127045 := bbase (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) (by norm_num)
theorem B1390369 : Blo 1234435 1390369 := bbase (se 2 (by rfl) ⟨521388, by rfl⟩ : syracuseStep 1390369 = 1042777) (by norm_num)
theorem B1562429 : Blo 1234435 1562429 := bbase (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) (by norm_num)
theorem B1390405 : Blo 1234435 1390405 := bbase (se 4 (by rfl) ⟨130350, by rfl⟩ : syracuseStep 1390405 = 260701) (by norm_num)
theorem B1390441 : Blo 1234435 1390441 := bbase (se 2 (by rfl) ⟨521415, by rfl⟩ : syracuseStep 1390441 = 1042831) (by norm_num)
theorem B1562485 : Blo 1234435 1562485 := bbase (se 5 (by rfl) ⟨73241, by rfl⟩ : syracuseStep 1562485 = 146483) (by norm_num)
theorem B3127157 : Blo 1234435 3127157 := bbase (se 5 (by rfl) ⟨146585, by rfl⟩ : syracuseStep 3127157 = 293171) (by norm_num)
theorem B4167557 : Blo 1234435 4167557 := bbase (se 4 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 4167557 = 781417) (by norm_num)
theorem B1390477 : Blo 1234435 1390477 := bbase (se 3 (by rfl) ⟨260714, by rfl⟩ : syracuseStep 1390477 = 521429) (by norm_num)
theorem B1390513 : Blo 1234435 1390513 := bbase (se 2 (by rfl) ⟨521442, by rfl⟩ : syracuseStep 1390513 = 1042885) (by norm_num)
theorem B5273525 : Blo 1234435 5273525 := bbase (se 5 (by rfl) ⟨247196, by rfl⟩ : syracuseStep 5273525 = 494393) (by norm_num)
theorem B1562581 : Blo 1234435 1562581 := bbase (se 7 (by rfl) ⟨18311, by rfl⟩ : syracuseStep 1562581 = 36623) (by norm_num)
theorem B1390549 : Blo 1234435 1390549 := bbase (se 7 (by rfl) ⟨16295, by rfl⟩ : syracuseStep 1390549 = 32591) (by norm_num)
theorem B1980397 : Blo 1234435 1980397 := bbase (se 3 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 1980397 = 742649) (by norm_num)
theorem B1390585 : Blo 1234435 1390585 := bbase (se 2 (by rfl) ⟨521469, by rfl⟩ : syracuseStep 1390585 = 1042939) (by norm_num)
theorem B1390621 : Blo 1234435 1390621 := bbase (se 3 (by rfl) ⟨260741, by rfl⟩ : syracuseStep 1390621 = 521483) (by norm_num)
theorem B3127349 : Blo 1234435 3127349 := bbase (se 5 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 3127349 = 293189) (by norm_num)
theorem B4454453 : Blo 1234435 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B1390657 : Blo 1234435 1390657 := bbase (se 2 (by rfl) ⟨521496, by rfl⟩ : syracuseStep 1390657 = 1042993) (by norm_num)
theorem B1390693 : Blo 1234435 1390693 := bbase (se 4 (by rfl) ⟨130377, by rfl⟩ : syracuseStep 1390693 = 260755) (by norm_num)
theorem B1562753 : Blo 1234435 1562753 := bbase (se 2 (by rfl) ⟨586032, by rfl⟩ : syracuseStep 1562753 = 1172065) (by norm_num)
theorem B2504837 : Blo 1234435 2504837 := bbase (se 4 (by rfl) ⟨234828, by rfl⟩ : syracuseStep 2504837 = 469657) (by norm_num)
theorem B1390729 : Blo 1234435 1390729 := bbase (se 2 (by rfl) ⟨521523, by rfl⟩ : syracuseStep 1390729 = 1043047) (by norm_num)
theorem B1669285 : Blo 1234435 1669285 := bbase (se 4 (by rfl) ⟨156495, by rfl⟩ : syracuseStep 1669285 = 312991) (by norm_num)
theorem B1390765 : Blo 1234435 1390765 := bbase (se 3 (by rfl) ⟨260768, by rfl⟩ : syracuseStep 1390765 = 521537) (by norm_num)
theorem B1562809 : Blo 1234435 1562809 := bbase (se 2 (by rfl) ⟨586053, by rfl⟩ : syracuseStep 1562809 = 1172107) (by norm_num)
theorem B1390801 : Blo 1234435 1390801 := bbase (se 2 (by rfl) ⟨521550, by rfl⟩ : syracuseStep 1390801 = 1043101) (by norm_num)
theorem B1390837 : Blo 1234435 1390837 := bbase (se 5 (by rfl) ⟨65195, by rfl⟩ : syracuseStep 1390837 = 130391) (by norm_num)
theorem B1562905 : Blo 1234435 1562905 := bbase (se 2 (by rfl) ⟨586089, by rfl⟩ : syracuseStep 1562905 = 1172179) (by norm_num)
theorem B1390873 : Blo 1234435 1390873 := bbase (se 2 (by rfl) ⟨521577, by rfl⟩ : syracuseStep 1390873 = 1043155) (by norm_num)
theorem B4167989 : Blo 1234435 4167989 := bbase (se 5 (by rfl) ⟨195374, by rfl⟩ : syracuseStep 4167989 = 390749) (by norm_num)
theorem B2005301 : Blo 1234435 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B1390909 : Blo 1234435 1390909 := bbase (se 3 (by rfl) ⟨260795, by rfl⟩ : syracuseStep 1390909 = 521591) (by norm_num)
theorem B1759573 : Blo 1234435 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B1390945 : Blo 1234435 1390945 := bbase (se 2 (by rfl) ⟨521604, by rfl⟩ : syracuseStep 1390945 = 1043209) (by norm_num)
theorem B1390981 : Blo 1234435 1390981 := bbase (se 4 (by rfl) ⟨130404, by rfl⟩ : syracuseStep 1390981 = 260809) (by norm_num)
theorem B3127693 : Blo 1234435 3127693 := bbase (se 3 (by rfl) ⟨586442, by rfl⟩ : syracuseStep 3127693 = 1172885) (by norm_num)
theorem B1563077 : Blo 1234435 1563077 := bbase (se 4 (by rfl) ⟨146538, by rfl⟩ : syracuseStep 1563077 = 293077) (by norm_num)
theorem B4692437 : Blo 1234435 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B5937637 : Blo 1234435 5937637 := bbase (se 4 (by rfl) ⟨556653, by rfl⟩ : syracuseStep 5937637 = 1113307) (by norm_num)
theorem B4454885 : Blo 1234435 4454885 := bbase (se 4 (by rfl) ⟨417645, by rfl⟩ : syracuseStep 4454885 = 835291) (by norm_num)
theorem B1563133 : Blo 1234435 1563133 := bbase (se 3 (by rfl) ⟨293087, by rfl⟩ : syracuseStep 1563133 = 586175) (by norm_num)
theorem B3127805 : Blo 1234435 3127805 := bbase (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) (by norm_num)
theorem B5011973 : Blo 1234435 5011973 := bbase (se 4 (by rfl) ⟨469872, by rfl⟩ : syracuseStep 5011973 = 939745) (by norm_num)
theorem B1563229 : Blo 1234435 1563229 := bbase (se 3 (by rfl) ⟨293105, by rfl⟩ : syracuseStep 1563229 = 586211) (by norm_num)
theorem B1784413 : Blo 1234435 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B1759909 : Blo 1234435 1759909 := bbase (se 4 (by rfl) ⟨164991, by rfl⟩ : syracuseStep 1759909 = 329983) (by norm_num)
theorem B3127997 : Blo 1234435 3127997 := bbase (se 3 (by rfl) ⟨586499, by rfl⟩ : syracuseStep 3127997 = 1172999) (by norm_num)
theorem B1252049 : Blo 1234435 1252049 := bbase (se 2 (by rfl) ⟨469518, by rfl⟩ : syracuseStep 1252049 = 939037) (by norm_num)
theorem B4168421 : Blo 1234435 4168421 := bbase (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) (by norm_num)
theorem B4692725 : Blo 1234435 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B1563401 : Blo 1234435 1563401 := bbase (se 2 (by rfl) ⟨586275, by rfl⟩ : syracuseStep 1563401 = 1172551) (by norm_num)
theorem B1669901 : Blo 1234435 1669901 := bbase (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) (by norm_num)
theorem B2112293 : Blo 1234435 2112293 := bbase (se 4 (by rfl) ⟨198027, by rfl⟩ : syracuseStep 2112293 = 396055) (by norm_num)
theorem B1563457 : Blo 1234435 1563457 := bbase (se 2 (by rfl) ⟨586296, by rfl⟩ : syracuseStep 1563457 = 1172593) (by norm_num)
theorem B1760125 : Blo 1234435 1760125 := bbase (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) (by norm_num)
theorem B4225925 : Blo 1234435 4225925 := bbase (se 4 (by rfl) ⟨396180, by rfl⟩ : syracuseStep 4225925 = 792361) (by norm_num)
theorem B1563553 : Blo 1234435 1563553 := bbase (se 2 (by rfl) ⟨586332, by rfl⟩ : syracuseStep 1563553 = 1172665) (by norm_num)
theorem B6257573 : Blo 1234435 6257573 := bbase (se 4 (by rfl) ⟨586647, by rfl⟩ : syracuseStep 6257573 = 1173295) (by norm_num)
theorem B3128341 : Blo 1234435 3128341 := bbase (se 6 (by rfl) ⟨73320, by rfl⟩ : syracuseStep 3128341 = 146641) (by norm_num)
theorem B1563725 : Blo 1234435 1563725 := bbase (se 3 (by rfl) ⟨293198, by rfl⟩ : syracuseStep 1563725 = 586397) (by norm_num)
theorem B11877461 : Blo 1234435 11877461 := bbase (se 8 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 11877461 = 139189) (by norm_num)
theorem B1563781 : Blo 1234435 1563781 := bbase (se 4 (by rfl) ⟨146604, by rfl⟩ : syracuseStep 1563781 = 293209) (by norm_num)
theorem B3128453 : Blo 1234435 3128453 := bbase (se 4 (by rfl) ⟨293292, by rfl⟩ : syracuseStep 3128453 = 586585) (by norm_num)
theorem B4168853 : Blo 1234435 4168853 := bbase (se 6 (by rfl) ⟨97707, by rfl⟩ : syracuseStep 4168853 = 195415) (by norm_num)
theorem B1563877 : Blo 1234435 1563877 := bbase (se 4 (by rfl) ⟨146613, by rfl⟩ : syracuseStep 1563877 = 293227) (by norm_num)
theorem B7920949 : Blo 1234435 7920949 := bbase (se 5 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 7920949 = 742589) (by norm_num)
theorem B6249797 : Blo 1234435 6249797 := bbase (se 4 (by rfl) ⟨585918, by rfl⟩ : syracuseStep 6249797 = 1171837) (by norm_num)
theorem B3128645 : Blo 1234435 3128645 := bbase (se 4 (by rfl) ⟨293310, by rfl⟩ : syracuseStep 3128645 = 586621) (by norm_num)
theorem B1670485 : Blo 1234435 1670485 := bbase (se 11 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1670485 = 2447) (by norm_num)
theorem B2637173 : Blo 1234435 2637173 := bbase (se 5 (by rfl) ⟨123617, by rfl⟩ : syracuseStep 2637173 = 247235) (by norm_num)
theorem B1564049 : Blo 1234435 1564049 := bbase (se 2 (by rfl) ⟨586518, by rfl⟩ : syracuseStep 1564049 = 1173037) (by norm_num)
theorem B5709221 : Blo 1234435 5709221 := bbase (se 4 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 5709221 = 1070479) (by norm_num)
theorem B1318313 : Blo 1234435 1318313 := bbase (se 2 (by rfl) ⟨494367, by rfl⟩ : syracuseStep 1318313 = 988735) (by norm_num)
theorem B1564105 : Blo 1234435 1564105 := bbase (se 2 (by rfl) ⟨586539, by rfl⟩ : syracuseStep 1564105 = 1173079) (by norm_num)
theorem B1670653 : Blo 1234435 1670653 := bbase (se 3 (by rfl) ⟨313247, by rfl⟩ : syracuseStep 1670653 = 626495) (by norm_num)
theorem B2637317 : Blo 1234435 2637317 := bbase (se 4 (by rfl) ⟨247248, by rfl⟩ : syracuseStep 2637317 = 494497) (by norm_num)
theorem B2817557 : Blo 1234435 2817557 := bbase (se 6 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 2817557 = 132073) (by norm_num)
theorem B1564201 : Blo 1234435 1564201 := bbase (se 2 (by rfl) ⟨586575, by rfl⟩ : syracuseStep 1564201 = 1173151) (by norm_num)
theorem B1670701 : Blo 1234435 1670701 := bbase (se 3 (by rfl) ⟨313256, by rfl⟩ : syracuseStep 1670701 = 626513) (by norm_num)
theorem B7036469 : Blo 1234435 7036469 := bbase (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) (by norm_num)
theorem B4169285 : Blo 1234435 4169285 := bbase (se 4 (by rfl) ⟨390870, by rfl⟩ : syracuseStep 4169285 = 781741) (by norm_num)
theorem B1252945 : Blo 1234435 1252945 := bbase (se 2 (by rfl) ⟨469854, by rfl⟩ : syracuseStep 1252945 = 939709) (by norm_num)
theorem B3128989 : Blo 1234435 3128989 := bbase (se 3 (by rfl) ⟨586685, by rfl⟩ : syracuseStep 3128989 = 1173371) (by norm_num)
theorem B1318565 : Blo 1234435 1318565 := bbase (se 4 (by rfl) ⟨123615, by rfl⟩ : syracuseStep 1318565 = 247231) (by norm_num)
theorem B1564373 : Blo 1234435 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B1564429 : Blo 1234435 1564429 := bbase (se 3 (by rfl) ⟨293330, by rfl⟩ : syracuseStep 1564429 = 586661) (by norm_num)
theorem B3129101 : Blo 1234435 3129101 := bbase (se 3 (by rfl) ⟨586706, by rfl⟩ : syracuseStep 3129101 = 1173413) (by norm_num)
theorem B26722133 : Blo 1234435 26722133 := bbase (se 9 (by rfl) ⟨78287, by rfl⟩ : syracuseStep 26722133 = 156575) (by norm_num)
theorem B2637677 : Blo 1234435 2637677 := bbase (se 3 (by rfl) ⟨494564, by rfl⟩ : syracuseStep 2637677 = 989129) (by norm_num)
theorem B1564525 : Blo 1234435 1564525 := bbase (se 3 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 1564525 = 586697) (by norm_num)
theorem B4693909 : Blo 1234435 4693909 := bbase (se 6 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 4693909 = 220027) (by norm_num)
theorem B3129293 : Blo 1234435 3129293 := bbase (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) (by norm_num)
theorem B3956693 : Blo 1234435 3956693 := bbase (se 7 (by rfl) ⟨46367, by rfl⟩ : syracuseStep 3956693 = 92735) (by norm_num)
theorem B4169717 : Blo 1234435 4169717 := bbase (se 5 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 4169717 = 390911) (by norm_num)
theorem B3129425 : Blo 1234435 3129425 := bstep (se 2 (by rfl) ⟨1173534, by rfl⟩ : syracuseStep 3129425 = 2347069) B2347069
theorem B2113633 : Blo 1234435 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B3129475 : Blo 1234435 3129475 := bstep (se 1 (by rfl) ⟨2347106, by rfl⟩ : syracuseStep 3129475 = 4694213) B4694213
theorem B2638001 : Blo 1234435 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B2113715 : Blo 1234435 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B4169933 : Blo 1234435 4169933 := bstep (se 3 (by rfl) ⟨781862, by rfl⟩ : syracuseStep 4169933 = 1563725) B1563725
theorem B1319171 : Blo 1234435 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B4169987 : Blo 1234435 4169987 := bstep (se 1 (by rfl) ⟨3127490, by rfl⟩ : syracuseStep 4169987 = 6254981) B6254981
theorem B1851665 : Blo 1234435 1851665 := bstep (se 2 (by rfl) ⟨694374, by rfl⟩ : syracuseStep 1851665 = 1388749) B1388749
theorem B3129617 : Blo 1234435 3129617 := bstep (se 2 (by rfl) ⟨1173606, by rfl⟩ : syracuseStep 3129617 = 2347213) B2347213
theorem B1851683 : Blo 1234435 1851683 := bstep (se 1 (by rfl) ⟨1388762, by rfl⟩ : syracuseStep 1851683 = 2777525) B2777525
theorem B7037219 : Blo 1234435 7037219 := bstep (se 1 (by rfl) ⟨5277914, by rfl⟩ : syracuseStep 7037219 = 10555829) B10555829
theorem B1851713 : Blo 1234435 1851713 := bstep (se 2 (by rfl) ⟨694392, by rfl⟩ : syracuseStep 1851713 = 1388785) B1388785
theorem B1851731 : Blo 1234435 1851731 := bstep (se 1 (by rfl) ⟨1388798, by rfl⟩ : syracuseStep 1851731 = 2777597) B2777597
theorem B4817251 : Blo 1234435 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B1851761 : Blo 1234435 1851761 := bstep (se 2 (by rfl) ⟨694410, by rfl⟩ : syracuseStep 1851761 = 1388821) B1388821
theorem B5636465 : Blo 1234435 5636465 := bstep (se 2 (by rfl) ⟨2113674, by rfl⟩ : syracuseStep 5636465 = 4227349) B4227349
theorem B1851779 : Blo 1234435 1851779 := bstep (se 1 (by rfl) ⟨1388834, by rfl⟩ : syracuseStep 1851779 = 2777669) B2777669
theorem B2777489 : Blo 1234435 2777489 := bstep (se 2 (by rfl) ⟨1041558, by rfl⟩ : syracuseStep 2777489 = 2083117) B2083117
theorem B1851809 : Blo 1234435 1851809 := bstep (se 2 (by rfl) ⟨694428, by rfl⟩ : syracuseStep 1851809 = 1388857) B1388857
theorem B2777507 : Blo 1234435 2777507 := bstep (se 1 (by rfl) ⟨2083130, by rfl⟩ : syracuseStep 2777507 = 4166261) B4166261
theorem B1851827 : Blo 1234435 1851827 := bstep (se 1 (by rfl) ⟨1388870, by rfl⟩ : syracuseStep 1851827 = 2777741) B2777741
theorem B1851857 : Blo 1234435 1851857 := bstep (se 2 (by rfl) ⟨694446, by rfl⟩ : syracuseStep 1851857 = 1388893) B1388893
theorem B1851875 : Blo 1234435 1851875 := bstep (se 1 (by rfl) ⟨1388906, by rfl⟩ : syracuseStep 1851875 = 2777813) B2777813
theorem B13353457 : Blo 1234435 13353457 := bstep (se 2 (by rfl) ⟨5007546, by rfl⟩ : syracuseStep 13353457 = 10015093) B10015093
theorem B1851905 : Blo 1234435 1851905 := bstep (se 2 (by rfl) ⟨694464, by rfl⟩ : syracuseStep 1851905 = 1388929) B1388929
theorem B4170257 : Blo 1234435 4170257 := bstep (se 2 (by rfl) ⟨1563846, by rfl⟩ : syracuseStep 4170257 = 3127693) B3127693
theorem B1851923 : Blo 1234435 1851923 := bstep (se 1 (by rfl) ⟨1388942, by rfl⟩ : syracuseStep 1851923 = 2777885) B2777885
theorem B2966051 : Blo 1234435 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B1851953 : Blo 1234435 1851953 := bstep (se 2 (by rfl) ⟨694482, by rfl⟩ : syracuseStep 1851953 = 1388965) B1388965
theorem B1851971 : Blo 1234435 1851971 := bstep (se 1 (by rfl) ⟨1388978, by rfl⟩ : syracuseStep 1851971 = 2777957) B2777957
theorem B2638403 : Blo 1234435 2638403 := bstep (se 1 (by rfl) ⟨1978802, by rfl⟩ : syracuseStep 2638403 = 3957605) B3957605
theorem B1852001 : Blo 1234435 1852001 := bstep (se 2 (by rfl) ⟨694500, by rfl⟩ : syracuseStep 1852001 = 1389001) B1389001
theorem B1852019 : Blo 1234435 1852019 := bstep (se 1 (by rfl) ⟨1389014, by rfl⟩ : syracuseStep 1852019 = 2778029) B2778029
theorem B1852049 : Blo 1234435 1852049 := bstep (se 2 (by rfl) ⟨694518, by rfl⟩ : syracuseStep 1852049 = 1389037) B1389037
theorem B1852067 : Blo 1234435 1852067 := bstep (se 1 (by rfl) ⟨1389050, by rfl⟩ : syracuseStep 1852067 = 2778101) B2778101
theorem B2777777 : Blo 1234435 2777777 := bstep (se 2 (by rfl) ⟨1041666, by rfl⟩ : syracuseStep 2777777 = 2083333) B2083333
theorem B1852097 : Blo 1234435 1852097 := bstep (se 2 (by rfl) ⟨694536, by rfl⟩ : syracuseStep 1852097 = 1389073) B1389073
theorem B2777795 : Blo 1234435 2777795 := bstep (se 1 (by rfl) ⟨2083346, by rfl⟩ : syracuseStep 2777795 = 4166693) B4166693
theorem B1852115 : Blo 1234435 1852115 := bstep (se 1 (by rfl) ⟨1389086, by rfl⟩ : syracuseStep 1852115 = 2778173) B2778173
theorem B1852145 : Blo 1234435 1852145 := bstep (se 2 (by rfl) ⟨694554, by rfl⟩ : syracuseStep 1852145 = 1389109) B1389109
theorem B1852163 : Blo 1234435 1852163 := bstep (se 1 (by rfl) ⟨1389122, by rfl⟩ : syracuseStep 1852163 = 2778245) B2778245
theorem B1852193 : Blo 1234435 1852193 := bstep (se 2 (by rfl) ⟨694572, by rfl⟩ : syracuseStep 1852193 = 1389145) B1389145
theorem B1852211 : Blo 1234435 1852211 := bstep (se 1 (by rfl) ⟨1389158, by rfl⟩ : syracuseStep 1852211 = 2778317) B2778317
theorem B1852241 : Blo 1234435 1852241 := bstep (se 2 (by rfl) ⟨694590, by rfl⟩ : syracuseStep 1852241 = 1389181) B1389181
theorem B1852259 : Blo 1234435 1852259 := bstep (se 1 (by rfl) ⟨1389194, by rfl⟩ : syracuseStep 1852259 = 2778389) B2778389
theorem B1852289 : Blo 1234435 1852289 := bstep (se 2 (by rfl) ⟨694608, by rfl⟩ : syracuseStep 1852289 = 1389217) B1389217
theorem B2343811 : Blo 1234435 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B1852307 : Blo 1234435 1852307 := bstep (se 1 (by rfl) ⟨1389230, by rfl⟩ : syracuseStep 1852307 = 2778461) B2778461
theorem B1852337 : Blo 1234435 1852337 := bstep (se 2 (by rfl) ⟨694626, by rfl⟩ : syracuseStep 1852337 = 1389253) B1389253
theorem B1852355 : Blo 1234435 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B2778065 : Blo 1234435 2778065 := bstep (se 2 (by rfl) ⟨1041774, by rfl⟩ : syracuseStep 2778065 = 2083549) B2083549
theorem B1852385 : Blo 1234435 1852385 := bstep (se 2 (by rfl) ⟨694644, by rfl⟩ : syracuseStep 1852385 = 1389289) B1389289
theorem B2778083 : Blo 1234435 2778083 := bstep (se 1 (by rfl) ⟨2083562, by rfl⟩ : syracuseStep 2778083 = 4167125) B4167125
theorem B1852403 : Blo 1234435 1852403 := bstep (se 1 (by rfl) ⟨1389302, by rfl⟩ : syracuseStep 1852403 = 2778605) B2778605
theorem B1319923 : Blo 1234435 1319923 := bstep (se 1 (by rfl) ⟨989942, by rfl⟩ : syracuseStep 1319923 = 1979885) B1979885
theorem B1852433 : Blo 1234435 1852433 := bstep (se 2 (by rfl) ⟨694662, by rfl⟩ : syracuseStep 1852433 = 1389325) B1389325
theorem B2343971 : Blo 1234435 2343971 := bstep (se 1 (by rfl) ⟨1757978, by rfl⟩ : syracuseStep 2343971 = 3515957) B3515957
theorem B1852451 : Blo 1234435 1852451 := bstep (se 1 (by rfl) ⟨1389338, by rfl⟩ : syracuseStep 1852451 = 2778677) B2778677
theorem B4170797 : Blo 1234435 4170797 := bstep (se 3 (by rfl) ⟨782024, by rfl⟩ : syracuseStep 4170797 = 1564049) B1564049
theorem B1852481 : Blo 1234435 1852481 := bstep (se 2 (by rfl) ⟨694680, by rfl⟩ : syracuseStep 1852481 = 1389361) B1389361
theorem B1852499 : Blo 1234435 1852499 := bstep (se 1 (by rfl) ⟨1389374, by rfl⟩ : syracuseStep 1852499 = 2778749) B2778749
theorem B4170851 : Blo 1234435 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B3515501 : Blo 1234435 3515501 := bstep (se 3 (by rfl) ⟨659156, by rfl⟩ : syracuseStep 3515501 = 1318313) B1318313
theorem B1852529 : Blo 1234435 1852529 := bstep (se 2 (by rfl) ⟨694698, by rfl⟩ : syracuseStep 1852529 = 1389397) B1389397
theorem B1852547 : Blo 1234435 1852547 := bstep (se 1 (by rfl) ⟨1389410, by rfl⟩ : syracuseStep 1852547 = 2778821) B2778821
theorem B1852577 : Blo 1234435 1852577 := bstep (se 2 (by rfl) ⟨694716, by rfl⟩ : syracuseStep 1852577 = 1389433) B1389433
theorem B1852595 : Blo 1234435 1852595 := bstep (se 1 (by rfl) ⟨1389446, by rfl⟩ : syracuseStep 1852595 = 2778893) B2778893
theorem B10552517 : Blo 1234435 10552517 := bstep (se 4 (by rfl) ⟨989298, by rfl⟩ : syracuseStep 10552517 = 1978597) B1978597
theorem B1852625 : Blo 1234435 1852625 := bstep (se 2 (by rfl) ⟨694734, by rfl⟩ : syracuseStep 1852625 = 1389469) B1389469
theorem B1852643 : Blo 1234435 1852643 := bstep (se 1 (by rfl) ⟨1389482, by rfl⟩ : syracuseStep 1852643 = 2778965) B2778965
theorem B2778353 : Blo 1234435 2778353 := bstep (se 2 (by rfl) ⟨1041882, by rfl⟩ : syracuseStep 2778353 = 2083765) B2083765
theorem B15828209 : Blo 1234435 15828209 := bstep (se 2 (by rfl) ⟨5935578, by rfl⟩ : syracuseStep 15828209 = 11871157) B11871157
theorem B1852673 : Blo 1234435 1852673 := bstep (se 2 (by rfl) ⟨694752, by rfl⟩ : syracuseStep 1852673 = 1389505) B1389505
theorem B2778371 : Blo 1234435 2778371 := bstep (se 1 (by rfl) ⟨2083778, by rfl⟩ : syracuseStep 2778371 = 4167557) B4167557
theorem B11879693 : Blo 1234435 11879693 := bstep (se 3 (by rfl) ⟨2227442, by rfl⟩ : syracuseStep 11879693 = 4454885) B4454885
theorem B1852691 : Blo 1234435 1852691 := bstep (se 1 (by rfl) ⟨1389518, by rfl⟩ : syracuseStep 1852691 = 2779037) B2779037
theorem B3515683 : Blo 1234435 3515683 := bstep (se 1 (by rfl) ⟨2636762, by rfl⟩ : syracuseStep 3515683 = 5273525) B5273525
theorem B1852721 : Blo 1234435 1852721 := bstep (se 2 (by rfl) ⟨694770, by rfl⟩ : syracuseStep 1852721 = 1389541) B1389541
theorem B1852739 : Blo 1234435 1852739 := bstep (se 1 (by rfl) ⟨1389554, by rfl⟩ : syracuseStep 1852739 = 2779109) B2779109
theorem B1852769 : Blo 1234435 1852769 := bstep (se 2 (by rfl) ⟨694788, by rfl⟩ : syracuseStep 1852769 = 1389577) B1389577
theorem B4171121 : Blo 1234435 4171121 := bstep (se 2 (by rfl) ⟨1564170, by rfl⟩ : syracuseStep 4171121 = 3128341) B3128341
theorem B1852787 : Blo 1234435 1852787 := bstep (se 1 (by rfl) ⟨1389590, by rfl⟩ : syracuseStep 1852787 = 2779181) B2779181
theorem B1852817 : Blo 1234435 1852817 := bstep (se 2 (by rfl) ⟨694806, by rfl⟩ : syracuseStep 1852817 = 1389613) B1389613
theorem B1852835 : Blo 1234435 1852835 := bstep (se 1 (by rfl) ⟨1389626, by rfl⟩ : syracuseStep 1852835 = 2779253) B2779253
theorem B1852865 : Blo 1234435 1852865 := bstep (se 2 (by rfl) ⟨694824, by rfl⟩ : syracuseStep 1852865 = 1389649) B1389649
theorem B2639299 : Blo 1234435 2639299 := bstep (se 1 (by rfl) ⟨1979474, by rfl⟩ : syracuseStep 2639299 = 3958949) B3958949
theorem B1852883 : Blo 1234435 1852883 := bstep (se 1 (by rfl) ⟨1389662, by rfl⟩ : syracuseStep 1852883 = 2779325) B2779325
theorem B1852913 : Blo 1234435 1852913 := bstep (se 2 (by rfl) ⟨694842, by rfl⟩ : syracuseStep 1852913 = 1389685) B1389685
theorem B11879921 : Blo 1234435 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B1852931 : Blo 1234435 1852931 := bstep (se 1 (by rfl) ⟨1389698, by rfl⟩ : syracuseStep 1852931 = 2779397) B2779397
theorem B2778641 : Blo 1234435 2778641 := bstep (se 2 (by rfl) ⟨1041990, by rfl⟩ : syracuseStep 2778641 = 2083981) B2083981
theorem B1852961 : Blo 1234435 1852961 := bstep (se 2 (by rfl) ⟨694860, by rfl⟩ : syracuseStep 1852961 = 1389721) B1389721
theorem B2778659 : Blo 1234435 2778659 := bstep (se 1 (by rfl) ⟨2083994, by rfl⟩ : syracuseStep 2778659 = 4167989) B4167989
theorem B1336867 : Blo 1234435 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B4687409 : Blo 1234435 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B1852979 : Blo 1234435 1852979 := bstep (se 1 (by rfl) ⟨1389734, by rfl⟩ : syracuseStep 1852979 = 2779469) B2779469
theorem B1853009 : Blo 1234435 1853009 := bstep (se 2 (by rfl) ⟨694878, by rfl⟩ : syracuseStep 1853009 = 1389757) B1389757
theorem B1853027 : Blo 1234435 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B1853057 : Blo 1234435 1853057 := bstep (se 2 (by rfl) ⟨694896, by rfl⟩ : syracuseStep 1853057 = 1389793) B1389793
theorem B1853075 : Blo 1234435 1853075 := bstep (se 1 (by rfl) ⟨1389806, by rfl⟩ : syracuseStep 1853075 = 2779613) B2779613
theorem B1853105 : Blo 1234435 1853105 := bstep (se 2 (by rfl) ⟨694914, by rfl⟩ : syracuseStep 1853105 = 1389829) B1389829
theorem B1853123 : Blo 1234435 1853123 := bstep (se 1 (by rfl) ⟨1389842, by rfl⟩ : syracuseStep 1853123 = 2779685) B2779685
theorem B1853153 : Blo 1234435 1853153 := bstep (se 2 (by rfl) ⟨694932, by rfl⟩ : syracuseStep 1853153 = 1389865) B1389865
theorem B2967281 : Blo 1234435 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B10561265 : Blo 1234435 10561265 := bstep (se 2 (by rfl) ⟨3960474, by rfl⟩ : syracuseStep 10561265 = 7920949) B7920949
theorem B1853171 : Blo 1234435 1853171 := bstep (se 1 (by rfl) ⟨1389878, by rfl⟩ : syracuseStep 1853171 = 2779757) B2779757
theorem B3516173 : Blo 1234435 3516173 := bstep (se 3 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 3516173 = 1318565) B1318565
theorem B1853201 : Blo 1234435 1853201 := bstep (se 2 (by rfl) ⟨694950, by rfl⟩ : syracuseStep 1853201 = 1389901) B1389901
theorem B1853219 : Blo 1234435 1853219 := bstep (se 1 (by rfl) ⟨1389914, by rfl⟩ : syracuseStep 1853219 = 2779829) B2779829
theorem B2778929 : Blo 1234435 2778929 := bstep (se 2 (by rfl) ⟨1042098, by rfl⟩ : syracuseStep 2778929 = 2084197) B2084197
theorem B1853249 : Blo 1234435 1853249 := bstep (se 2 (by rfl) ⟨694968, by rfl⟩ : syracuseStep 1853249 = 1389937) B1389937
theorem B2778947 : Blo 1234435 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B1853267 : Blo 1234435 1853267 := bstep (se 1 (by rfl) ⟨1389950, by rfl⟩ : syracuseStep 1853267 = 2779901) B2779901
theorem B1853297 : Blo 1234435 1853297 := bstep (se 2 (by rfl) ⟨694986, by rfl⟩ : syracuseStep 1853297 = 1389973) B1389973
theorem B1853315 : Blo 1234435 1853315 := bstep (se 1 (by rfl) ⟨1389986, by rfl⟩ : syracuseStep 1853315 = 2779973) B2779973
theorem B4171661 : Blo 1234435 4171661 := bstep (se 3 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 4171661 = 1564373) B1564373
theorem B1853345 : Blo 1234435 1853345 := bstep (se 2 (by rfl) ⟨695004, by rfl⟩ : syracuseStep 1853345 = 1390009) B1390009
theorem B1853363 : Blo 1234435 1853363 := bstep (se 1 (by rfl) ⟨1390022, by rfl⟩ : syracuseStep 1853363 = 2780045) B2780045
theorem B4171715 : Blo 1234435 4171715 := bstep (se 1 (by rfl) ⟨3128786, by rfl⟩ : syracuseStep 4171715 = 6257573) B6257573
theorem B3958733 : Blo 1234435 3958733 := bstep (se 3 (by rfl) ⟨742262, by rfl⟩ : syracuseStep 3958733 = 1484525) B1484525
theorem B1853393 : Blo 1234435 1853393 := bstep (se 2 (by rfl) ⟨695022, by rfl⟩ : syracuseStep 1853393 = 1390045) B1390045
theorem B1853411 : Blo 1234435 1853411 := bstep (se 1 (by rfl) ⟨1390058, by rfl⟩ : syracuseStep 1853411 = 2780117) B2780117
theorem B1853441 : Blo 1234435 1853441 := bstep (se 2 (by rfl) ⟨695040, by rfl⟩ : syracuseStep 1853441 = 1390081) B1390081
theorem B1853459 : Blo 1234435 1853459 := bstep (se 1 (by rfl) ⟨1390094, by rfl⟩ : syracuseStep 1853459 = 2780189) B2780189
theorem B1853489 : Blo 1234435 1853489 := bstep (se 2 (by rfl) ⟨695058, by rfl⟩ : syracuseStep 1853489 = 1390117) B1390117
theorem B1853507 : Blo 1234435 1853507 := bstep (se 1 (by rfl) ⟨1390130, by rfl⟩ : syracuseStep 1853507 = 2780261) B2780261
theorem B2779217 : Blo 1234435 2779217 := bstep (se 2 (by rfl) ⟨1042206, by rfl⟩ : syracuseStep 2779217 = 2084413) B2084413
theorem B2345041 : Blo 1234435 2345041 := bstep (se 2 (by rfl) ⟨879390, by rfl⟩ : syracuseStep 2345041 = 1758781) B1758781
theorem B1853537 : Blo 1234435 1853537 := bstep (se 2 (by rfl) ⟨695076, by rfl⟩ : syracuseStep 1853537 = 1390153) B1390153
theorem B2779235 : Blo 1234435 2779235 := bstep (se 1 (by rfl) ⟨2084426, by rfl⟩ : syracuseStep 2779235 = 4168853) B4168853
theorem B1853555 : Blo 1234435 1853555 := bstep (se 1 (by rfl) ⟨1390166, by rfl⟩ : syracuseStep 1853555 = 2780333) B2780333
theorem B1853585 : Blo 1234435 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B1853603 : Blo 1234435 1853603 := bstep (se 1 (by rfl) ⟨1390202, by rfl⟩ : syracuseStep 1853603 = 2780405) B2780405
theorem B13355189 : Blo 1234435 13355189 := bstep (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) B1252049
theorem B1853633 : Blo 1234435 1853633 := bstep (se 2 (by rfl) ⟨695112, by rfl⟩ : syracuseStep 1853633 = 1390225) B1390225
theorem B4688077 : Blo 1234435 4688077 := bstep (se 3 (by rfl) ⟨879014, by rfl⟩ : syracuseStep 4688077 = 1758029) B1758029
theorem B4171985 : Blo 1234435 4171985 := bstep (se 2 (by rfl) ⟨1564494, by rfl⟩ : syracuseStep 4171985 = 3128989) B3128989
theorem B1853651 : Blo 1234435 1853651 := bstep (se 1 (by rfl) ⟨1390238, by rfl⟩ : syracuseStep 1853651 = 2780477) B2780477
theorem B4229347 : Blo 1234435 4229347 := bstep (se 1 (by rfl) ⟨3172010, by rfl⟩ : syracuseStep 4229347 = 6344021) B6344021
theorem B1853681 : Blo 1234435 1853681 := bstep (se 2 (by rfl) ⟨695130, by rfl⟩ : syracuseStep 1853681 = 1390261) B1390261
theorem B1853699 : Blo 1234435 1853699 := bstep (se 1 (by rfl) ⟨1390274, by rfl⟩ : syracuseStep 1853699 = 2780549) B2780549
theorem B1853729 : Blo 1234435 1853729 := bstep (se 2 (by rfl) ⟨695148, by rfl⟩ : syracuseStep 1853729 = 1390297) B1390297
theorem B1853747 : Blo 1234435 1853747 := bstep (se 1 (by rfl) ⟨1390310, by rfl⟩ : syracuseStep 1853747 = 2780621) B2780621
theorem B1853777 : Blo 1234435 1853777 := bstep (se 2 (by rfl) ⟨695166, by rfl⟩ : syracuseStep 1853777 = 1390333) B1390333
theorem B2083171 : Blo 1234435 2083171 := bstep (se 1 (by rfl) ⟨1562378, by rfl⟩ : syracuseStep 2083171 = 3124757) B3124757
theorem B1878371 : Blo 1234435 1878371 := bstep (se 1 (by rfl) ⟨1408778, by rfl⟩ : syracuseStep 1878371 = 2817557) B2817557
theorem B5278051 : Blo 1234435 5278051 := bstep (se 1 (by rfl) ⟨3958538, by rfl⟩ : syracuseStep 5278051 = 7917077) B7917077
theorem B1853795 : Blo 1234435 1853795 := bstep (se 1 (by rfl) ⟨1390346, by rfl⟩ : syracuseStep 1853795 = 2780693) B2780693
theorem B2779505 : Blo 1234435 2779505 := bstep (se 2 (by rfl) ⟨1042314, by rfl⟩ : syracuseStep 2779505 = 2084629) B2084629
theorem B1853825 : Blo 1234435 1853825 := bstep (se 2 (by rfl) ⟨695184, by rfl⟩ : syracuseStep 1853825 = 1390369) B1390369
theorem B2779523 : Blo 1234435 2779523 := bstep (se 1 (by rfl) ⟨2084642, by rfl⟩ : syracuseStep 2779523 = 4169285) B4169285
theorem B3664273 : Blo 1234435 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B1853843 : Blo 1234435 1853843 := bstep (se 1 (by rfl) ⟨1390382, by rfl⟩ : syracuseStep 1853843 = 2780765) B2780765
theorem B1853873 : Blo 1234435 1853873 := bstep (se 2 (by rfl) ⟨695202, by rfl⟩ : syracuseStep 1853873 = 1390405) B1390405
theorem B1853891 : Blo 1234435 1853891 := bstep (se 1 (by rfl) ⟨1390418, by rfl⟩ : syracuseStep 1853891 = 2780837) B2780837
theorem B1853921 : Blo 1234435 1853921 := bstep (se 2 (by rfl) ⟨695220, by rfl⟩ : syracuseStep 1853921 = 1390441) B1390441
theorem B2083313 : Blo 1234435 2083313 := bstep (se 2 (by rfl) ⟨781242, by rfl⟩ : syracuseStep 2083313 = 1562485) B1562485
theorem B1853939 : Blo 1234435 1853939 := bstep (se 1 (by rfl) ⟨1390454, by rfl⟩ : syracuseStep 1853939 = 2780909) B2780909
theorem B1853969 : Blo 1234435 1853969 := bstep (se 2 (by rfl) ⟨695238, by rfl⟩ : syracuseStep 1853969 = 1390477) B1390477
theorem B1853987 : Blo 1234435 1853987 := bstep (se 1 (by rfl) ⟨1390490, by rfl⟩ : syracuseStep 1853987 = 2780981) B2780981
theorem B1854017 : Blo 1234435 1854017 := bstep (se 2 (by rfl) ⟨695256, by rfl⟩ : syracuseStep 1854017 = 1390513) B1390513
theorem B1854035 : Blo 1234435 1854035 := bstep (se 1 (by rfl) ⟨1390526, by rfl⟩ : syracuseStep 1854035 = 2781053) B2781053
theorem B2083441 : Blo 1234435 2083441 := bstep (se 2 (by rfl) ⟨781290, by rfl⟩ : syracuseStep 2083441 = 1562581) B1562581
theorem B1854065 : Blo 1234435 1854065 := bstep (se 2 (by rfl) ⟨695274, by rfl⟩ : syracuseStep 1854065 = 1390549) B1390549
theorem B1854083 : Blo 1234435 1854083 := bstep (se 1 (by rfl) ⟨1390562, by rfl⟩ : syracuseStep 1854083 = 2781125) B2781125
theorem B2779793 : Blo 1234435 2779793 := bstep (se 2 (by rfl) ⟨1042422, by rfl⟩ : syracuseStep 2779793 = 2084845) B2084845
theorem B2083475 : Blo 1234435 2083475 := bstep (se 1 (by rfl) ⟨1562606, by rfl⟩ : syracuseStep 2083475 = 3125213) B3125213
theorem B2640529 : Blo 1234435 2640529 := bstep (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) B1980397
theorem B1854113 : Blo 1234435 1854113 := bstep (se 2 (by rfl) ⟨695292, by rfl⟩ : syracuseStep 1854113 = 1390585) B1390585
theorem B2779811 : Blo 1234435 2779811 := bstep (se 1 (by rfl) ⟨2084858, by rfl⟩ : syracuseStep 2779811 = 4169717) B4169717
theorem B1854131 : Blo 1234435 1854131 := bstep (se 1 (by rfl) ⟨1390598, by rfl⟩ : syracuseStep 1854131 = 2781197) B2781197
theorem B1854161 : Blo 1234435 1854161 := bstep (se 2 (by rfl) ⟨695310, by rfl⟩ : syracuseStep 1854161 = 1390621) B1390621
theorem B1854179 : Blo 1234435 1854179 := bstep (se 1 (by rfl) ⟨1390634, by rfl⟩ : syracuseStep 1854179 = 2781269) B2781269
theorem B4172525 : Blo 1234435 4172525 := bstep (se 3 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 4172525 = 1564697) B1564697
theorem B1354483 : Blo 1234435 1354483 := bstep (se 1 (by rfl) ⟨1015862, by rfl⟩ : syracuseStep 1354483 = 2031725) B2031725
theorem B1854209 : Blo 1234435 1854209 := bstep (se 2 (by rfl) ⟨695328, by rfl⟩ : syracuseStep 1854209 = 1390657) B1390657
theorem B2083603 : Blo 1234435 2083603 := bstep (se 1 (by rfl) ⟨1562702, by rfl⟩ : syracuseStep 2083603 = 3125405) B3125405
theorem B1854227 : Blo 1234435 1854227 := bstep (se 1 (by rfl) ⟨1390670, by rfl⟩ : syracuseStep 1854227 = 2781341) B2781341
theorem B4172579 : Blo 1234435 4172579 := bstep (se 1 (by rfl) ⟨3129434, by rfl⟩ : syracuseStep 4172579 = 6258869) B6258869
theorem B6253361 : Blo 1234435 6253361 := bstep (se 2 (by rfl) ⟨2345010, by rfl⟩ : syracuseStep 6253361 = 4690021) B4690021
theorem B1878833 : Blo 1234435 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B1854257 : Blo 1234435 1854257 := bstep (se 2 (by rfl) ⟨695346, by rfl⟩ : syracuseStep 1854257 = 1390693) B1390693
theorem B1854275 : Blo 1234435 1854275 := bstep (se 1 (by rfl) ⟨1390706, by rfl⟩ : syracuseStep 1854275 = 2781413) B2781413
theorem B1854305 : Blo 1234435 1854305 := bstep (se 2 (by rfl) ⟨695364, by rfl⟩ : syracuseStep 1854305 = 1390729) B1390729
theorem B1854323 : Blo 1234435 1854323 := bstep (se 1 (by rfl) ⟨1390742, by rfl⟩ : syracuseStep 1854323 = 2781485) B2781485
theorem B1854353 : Blo 1234435 1854353 := bstep (se 2 (by rfl) ⟨695382, by rfl⟩ : syracuseStep 1854353 = 1390765) B1390765
theorem B2083745 : Blo 1234435 2083745 := bstep (se 2 (by rfl) ⟨781404, by rfl⟩ : syracuseStep 2083745 = 1562809) B1562809
theorem B2034595 : Blo 1234435 2034595 := bstep (se 1 (by rfl) ⟨1525946, by rfl⟩ : syracuseStep 2034595 = 3051893) B3051893
theorem B1854371 : Blo 1234435 1854371 := bstep (se 1 (by rfl) ⟨1390778, by rfl⟩ : syracuseStep 1854371 = 2781557) B2781557
theorem B3517357 : Blo 1234435 3517357 := bstep (se 3 (by rfl) ⟨659504, by rfl⟩ : syracuseStep 3517357 = 1319009) B1319009
theorem B2780081 : Blo 1234435 2780081 := bstep (se 2 (by rfl) ⟨1042530, by rfl⟩ : syracuseStep 2780081 = 2085061) B2085061
theorem B1854401 : Blo 1234435 1854401 := bstep (se 2 (by rfl) ⟨695400, by rfl⟩ : syracuseStep 1854401 = 1390801) B1390801
theorem B2780099 : Blo 1234435 2780099 := bstep (se 1 (by rfl) ⟨2085074, by rfl⟩ : syracuseStep 2780099 = 4170149) B4170149
theorem B1854419 : Blo 1234435 1854419 := bstep (se 1 (by rfl) ⟨1390814, by rfl⟩ : syracuseStep 1854419 = 2781629) B2781629
theorem B4688867 : Blo 1234435 4688867 := bstep (se 1 (by rfl) ⟨3516650, by rfl⟩ : syracuseStep 4688867 = 7033301) B7033301
theorem B1854449 : Blo 1234435 1854449 := bstep (se 2 (by rfl) ⟨695418, by rfl⟩ : syracuseStep 1854449 = 1390837) B1390837
theorem B1854467 : Blo 1234435 1854467 := bstep (se 1 (by rfl) ⟨1390850, by rfl⟩ : syracuseStep 1854467 = 2781701) B2781701
theorem B2083873 : Blo 1234435 2083873 := bstep (se 2 (by rfl) ⟨781452, by rfl⟩ : syracuseStep 2083873 = 1562905) B1562905
theorem B1854497 : Blo 1234435 1854497 := bstep (se 2 (by rfl) ⟨695436, by rfl⟩ : syracuseStep 1854497 = 1390873) B1390873
theorem B7031843 : Blo 1234435 7031843 := bstep (se 1 (by rfl) ⟨5273882, by rfl⟩ : syracuseStep 7031843 = 10547765) B10547765
theorem B3566641 : Blo 1234435 3566641 := bstep (se 2 (by rfl) ⟨1337490, by rfl⟩ : syracuseStep 3566641 = 2674981) B2674981
theorem B4172849 : Blo 1234435 4172849 := bstep (se 2 (by rfl) ⟨1564818, by rfl⟩ : syracuseStep 4172849 = 3129637) B3129637
theorem B1854515 : Blo 1234435 1854515 := bstep (se 1 (by rfl) ⟨1390886, by rfl⟩ : syracuseStep 1854515 = 2781773) B2781773
theorem B2083907 : Blo 1234435 2083907 := bstep (se 1 (by rfl) ⟨1562930, by rfl⟩ : syracuseStep 2083907 = 3125861) B3125861
theorem B1854545 : Blo 1234435 1854545 := bstep (se 2 (by rfl) ⟨695454, by rfl⟩ : syracuseStep 1854545 = 1390909) B1390909
theorem B1854563 : Blo 1234435 1854563 := bstep (se 1 (by rfl) ⟨1390922, by rfl⟩ : syracuseStep 1854563 = 2781845) B2781845
theorem B2346097 : Blo 1234435 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B1854593 : Blo 1234435 1854593 := bstep (se 2 (by rfl) ⟨695472, by rfl⟩ : syracuseStep 1854593 = 1390945) B1390945
theorem B1854611 : Blo 1234435 1854611 := bstep (se 1 (by rfl) ⟨1390958, by rfl⟩ : syracuseStep 1854611 = 2781917) B2781917
theorem B7130275 : Blo 1234435 7130275 := bstep (se 1 (by rfl) ⟨5347706, by rfl⟩ : syracuseStep 7130275 = 10695413) B10695413
theorem B1854641 : Blo 1234435 1854641 := bstep (se 2 (by rfl) ⟨695490, by rfl⟩ : syracuseStep 1854641 = 1390981) B1390981
theorem B2084035 : Blo 1234435 2084035 := bstep (se 1 (by rfl) ⟨1563026, by rfl⟩ : syracuseStep 2084035 = 3126053) B3126053
theorem B2780369 : Blo 1234435 2780369 := bstep (se 2 (by rfl) ⟨1042638, by rfl⟩ : syracuseStep 2780369 = 2085277) B2085277
theorem B2780387 : Blo 1234435 2780387 := bstep (se 1 (by rfl) ⟨2085290, by rfl⟩ : syracuseStep 2780387 = 4170581) B4170581
theorem B16051441 : Blo 1234435 16051441 := bstep (se 2 (by rfl) ⟨6019290, by rfl⟩ : syracuseStep 16051441 = 12038581) B12038581
theorem B10022129 : Blo 1234435 10022129 := bstep (se 2 (by rfl) ⟨3758298, by rfl⟩ : syracuseStep 10022129 = 7516597) B7516597
theorem B7916849 : Blo 1234435 7916849 := bstep (se 2 (by rfl) ⟨2968818, by rfl⟩ : syracuseStep 7916849 = 5937637) B5937637
theorem B2084177 : Blo 1234435 2084177 := bstep (se 2 (by rfl) ⟨781566, by rfl⟩ : syracuseStep 2084177 = 1563133) B1563133
theorem B2084305 : Blo 1234435 2084305 := bstep (se 2 (by rfl) ⟨781614, by rfl⟩ : syracuseStep 2084305 = 1563229) B1563229
theorem B2379217 : Blo 1234435 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B2780657 : Blo 1234435 2780657 := bstep (se 2 (by rfl) ⟨1042746, by rfl⟩ : syracuseStep 2780657 = 2085493) B2085493
theorem B2084339 : Blo 1234435 2084339 := bstep (se 1 (by rfl) ⟨1563254, by rfl⟩ : syracuseStep 2084339 = 3126509) B3126509
theorem B2780675 : Blo 1234435 2780675 := bstep (se 1 (by rfl) ⟨2085506, by rfl⟩ : syracuseStep 2780675 = 4171013) B4171013
theorem B2346499 : Blo 1234435 2346499 := bstep (se 1 (by rfl) ⟨1759874, by rfl⟩ : syracuseStep 2346499 = 3519749) B3519749
theorem B2346545 : Blo 1234435 2346545 := bstep (se 2 (by rfl) ⟨879954, by rfl⟩ : syracuseStep 2346545 = 1759909) B1759909
theorem B3386929 : Blo 1234435 3386929 := bstep (se 2 (by rfl) ⟨1270098, by rfl⟩ : syracuseStep 3386929 = 2540197) B2540197
theorem B4689521 : Blo 1234435 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B2084467 : Blo 1234435 2084467 := bstep (se 1 (by rfl) ⟨1563350, by rfl⟩ : syracuseStep 2084467 = 3126701) B3126701
theorem B2084609 : Blo 1234435 2084609 := bstep (se 2 (by rfl) ⟨781728, by rfl⟩ : syracuseStep 2084609 = 1563457) B1563457
theorem B3960589 : Blo 1234435 3960589 := bstep (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) B1485221
theorem B2780945 : Blo 1234435 2780945 := bstep (se 2 (by rfl) ⟨1042854, by rfl⟩ : syracuseStep 2780945 = 2085709) B2085709
theorem B2780963 : Blo 1234435 2780963 := bstep (se 1 (by rfl) ⟨2085722, by rfl⟩ : syracuseStep 2780963 = 4171445) B4171445
theorem B2256707 : Blo 1234435 2256707 := bstep (se 1 (by rfl) ⟨1692530, by rfl⟩ : syracuseStep 2256707 = 3385061) B3385061
theorem B1978193 : Blo 1234435 1978193 := bstep (se 2 (by rfl) ⟨741822, by rfl⟩ : syracuseStep 1978193 = 1483645) B1483645
theorem B2346833 : Blo 1234435 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B2084737 : Blo 1234435 2084737 := bstep (se 2 (by rfl) ⟨781776, by rfl⟩ : syracuseStep 2084737 = 1563553) B1563553
theorem B2084771 : Blo 1234435 2084771 := bstep (se 1 (by rfl) ⟨1563578, by rfl⟩ : syracuseStep 2084771 = 3127157) B3127157
theorem B3518417 : Blo 1234435 3518417 := bstep (se 2 (by rfl) ⟨1319406, by rfl⟩ : syracuseStep 3518417 = 2638813) B2638813
theorem B7032845 : Blo 1234435 7032845 := bstep (se 3 (by rfl) ⟨1318658, by rfl⟩ : syracuseStep 7032845 = 2637317) B2637317
theorem B8458253 : Blo 1234435 8458253 := bstep (se 3 (by rfl) ⟨1585922, by rfl⟩ : syracuseStep 8458253 = 3171845) B3171845
theorem B2084899 : Blo 1234435 2084899 := bstep (se 1 (by rfl) ⟨1563674, by rfl⟩ : syracuseStep 2084899 = 3127349) B3127349
theorem B2969635 : Blo 1234435 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B2781233 : Blo 1234435 2781233 := bstep (se 2 (by rfl) ⟨1042962, by rfl⟩ : syracuseStep 2781233 = 2085925) B2085925
theorem B2781251 : Blo 1234435 2781251 := bstep (se 1 (by rfl) ⟨2085938, by rfl⟩ : syracuseStep 2781251 = 4171877) B4171877
theorem B1929377 : Blo 1234435 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B3125425 : Blo 1234435 3125425 := bstep (se 2 (by rfl) ⟨1172034, by rfl⟩ : syracuseStep 3125425 = 2344069) B2344069
theorem B2085041 : Blo 1234435 2085041 := bstep (se 2 (by rfl) ⟨781890, by rfl⟩ : syracuseStep 2085041 = 1563781) B1563781
theorem B6254819 : Blo 1234435 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B1388803 : Blo 1234435 1388803 := bstep (se 1 (by rfl) ⟨1041602, by rfl⟩ : syracuseStep 1388803 = 2083205) B2083205
theorem B2085169 : Blo 1234435 2085169 := bstep (se 2 (by rfl) ⟨781938, by rfl⟩ : syracuseStep 2085169 = 1563877) B1563877
theorem B2781521 : Blo 1234435 2781521 := bstep (se 2 (by rfl) ⟨1043070, by rfl⟩ : syracuseStep 2781521 = 2086141) B2086141
theorem B2085203 : Blo 1234435 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B2781539 : Blo 1234435 2781539 := bstep (se 1 (by rfl) ⟨2086154, by rfl⟩ : syracuseStep 2781539 = 4172309) B4172309
theorem B1782131 : Blo 1234435 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1388947 : Blo 1234435 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B3125699 : Blo 1234435 3125699 := bstep (se 1 (by rfl) ⟨2344274, by rfl⟩ : syracuseStep 3125699 = 4688549) B4688549
theorem B2085331 : Blo 1234435 2085331 := bstep (se 1 (by rfl) ⟨1563998, by rfl⟩ : syracuseStep 2085331 = 3127997) B3127997
theorem B2224675 : Blo 1234435 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B1389091 : Blo 1234435 1389091 := bstep (se 1 (by rfl) ⟨1041818, by rfl⟩ : syracuseStep 1389091 = 2083637) B2083637
theorem B2085473 : Blo 1234435 2085473 := bstep (se 2 (by rfl) ⟨782052, by rfl⟩ : syracuseStep 2085473 = 1564105) B1564105
theorem B4223597 : Blo 1234435 4223597 := bstep (se 3 (by rfl) ⟨791924, by rfl⟩ : syracuseStep 4223597 = 1583849) B1583849
theorem B5345905 : Blo 1234435 5345905 := bstep (se 2 (by rfl) ⟨2004714, by rfl⟩ : syracuseStep 5345905 = 4009429) B4009429
theorem B3519089 : Blo 1234435 3519089 := bstep (se 2 (by rfl) ⟨1319658, by rfl⟩ : syracuseStep 3519089 = 2639317) B2639317
theorem B2781809 : Blo 1234435 2781809 := bstep (se 2 (by rfl) ⟨1043178, by rfl⟩ : syracuseStep 2781809 = 2086357) B2086357
theorem B3125891 : Blo 1234435 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B2781827 : Blo 1234435 2781827 := bstep (se 1 (by rfl) ⟨2086370, by rfl⟩ : syracuseStep 2781827 = 4172741) B4172741
theorem B9376397 : Blo 1234435 9376397 := bstep (se 3 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 9376397 = 3516149) B3516149
theorem B6337201 : Blo 1234435 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B1389235 : Blo 1234435 1389235 := bstep (se 1 (by rfl) ⟨1041926, by rfl⟩ : syracuseStep 1389235 = 2083853) B2083853
theorem B4453069 : Blo 1234435 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B2085601 : Blo 1234435 2085601 := bstep (se 2 (by rfl) ⟨782100, by rfl⟩ : syracuseStep 2085601 = 1564201) B1564201
theorem B7918307 : Blo 1234435 7918307 := bstep (se 1 (by rfl) ⟨5938730, by rfl⟩ : syracuseStep 7918307 = 11877461) B11877461
theorem B5280497 : Blo 1234435 5280497 := bstep (se 2 (by rfl) ⟨1980186, by rfl⟩ : syracuseStep 5280497 = 3960373) B3960373
theorem B2085635 : Blo 1234435 2085635 := bstep (se 1 (by rfl) ⟨1564226, by rfl⟩ : syracuseStep 2085635 = 3128453) B3128453
theorem B1389379 : Blo 1234435 1389379 := bstep (se 1 (by rfl) ⟨1042034, by rfl⟩ : syracuseStep 1389379 = 2084069) B2084069
theorem B4166477 : Blo 1234435 4166477 := bstep (se 3 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 4166477 = 1562429) B1562429
theorem B3339089 : Blo 1234435 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B2503523 : Blo 1234435 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B4166531 : Blo 1234435 4166531 := bstep (se 1 (by rfl) ⟨3124898, by rfl⟩ : syracuseStep 4166531 = 6249797) B6249797
theorem B2085763 : Blo 1234435 2085763 := bstep (se 1 (by rfl) ⟨1564322, by rfl⟩ : syracuseStep 2085763 = 3128645) B3128645
theorem B1758115 : Blo 1234435 1758115 := bstep (se 1 (by rfl) ⟨1318586, by rfl⟩ : syracuseStep 1758115 = 2637173) B2637173
theorem B3806147 : Blo 1234435 3806147 := bstep (se 1 (by rfl) ⟨2854610, by rfl⟩ : syracuseStep 3806147 = 5709221) B5709221
theorem B1389523 : Blo 1234435 1389523 := bstep (se 1 (by rfl) ⟨1042142, by rfl⟩ : syracuseStep 1389523 = 2084285) B2084285
theorem B11269133 : Blo 1234435 11269133 := bstep (se 3 (by rfl) ⟨2112962, by rfl⟩ : syracuseStep 11269133 = 4225925) B4225925
theorem B6255629 : Blo 1234435 6255629 := bstep (se 3 (by rfl) ⟨1172930, by rfl⟩ : syracuseStep 6255629 = 2345861) B2345861
theorem B2085905 : Blo 1234435 2085905 := bstep (se 2 (by rfl) ⟨782214, by rfl⟩ : syracuseStep 2085905 = 1564429) B1564429
theorem B4690979 : Blo 1234435 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B4690993 : Blo 1234435 4690993 := bstep (se 2 (by rfl) ⟨1759122, by rfl⟩ : syracuseStep 4690993 = 3518245) B3518245
theorem B1389667 : Blo 1234435 1389667 := bstep (se 1 (by rfl) ⟨1042250, by rfl⟩ : syracuseStep 1389667 = 2084501) B2084501
theorem B4166801 : Blo 1234435 4166801 := bstep (se 2 (by rfl) ⟨1562550, by rfl⟩ : syracuseStep 4166801 = 3125101) B3125101
theorem B2086033 : Blo 1234435 2086033 := bstep (se 2 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 2086033 = 1564525) B1564525
theorem B2086067 : Blo 1234435 2086067 := bstep (se 1 (by rfl) ⟨1564550, by rfl⟩ : syracuseStep 2086067 = 3129101) B3129101
theorem B3568835 : Blo 1234435 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B17814755 : Blo 1234435 17814755 := bstep (se 1 (by rfl) ⟨13361066, by rfl⟩ : syracuseStep 17814755 = 26722133) B26722133
theorem B1758451 : Blo 1234435 1758451 := bstep (se 1 (by rfl) ⟨1318838, by rfl⟩ : syracuseStep 1758451 = 2637677) B2637677
theorem B1389811 : Blo 1234435 1389811 := bstep (se 1 (by rfl) ⟨1042358, by rfl⟩ : syracuseStep 1389811 = 2084717) B2084717
theorem B2086195 : Blo 1234435 2086195 := bstep (se 1 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 2086195 = 3129293) B3129293
theorem B1979731 : Blo 1234435 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B1979777 : Blo 1234435 1979777 := bstep (se 2 (by rfl) ⟨742416, by rfl⟩ : syracuseStep 1979777 = 1484833) B1484833
theorem B1389955 : Blo 1234435 1389955 := bstep (se 1 (by rfl) ⟨1042466, by rfl⟩ : syracuseStep 1389955 = 2084933) B2084933
theorem B3519875 : Blo 1234435 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B2086337 : Blo 1234435 2086337 := bstep (se 2 (by rfl) ⟨782376, by rfl⟩ : syracuseStep 2086337 = 1564753) B1564753
theorem B9024965 : Blo 1234435 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B1234435 : Blo 1234435 1234435 := bstep (se 1 (by rfl) ⟨925826, by rfl⟩ : syracuseStep 1234435 = 1851653) B1851653
theorem B1234451 : Blo 1234435 1234451 := bstep (se 1 (by rfl) ⟨925838, by rfl⟩ : syracuseStep 1234451 = 1851677) B1851677
theorem B1390099 : Blo 1234435 1390099 := bstep (se 1 (by rfl) ⟨1042574, by rfl⟩ : syracuseStep 1390099 = 2085149) B2085149
theorem B1234467 : Blo 1234435 1234467 := bstep (se 1 (by rfl) ⟨925850, by rfl⟩ : syracuseStep 1234467 = 1851701) B1851701
theorem B2225713 : Blo 1234435 2225713 := bstep (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) B1669285
theorem B3126833 : Blo 1234435 3126833 := bstep (se 2 (by rfl) ⟨1172562, by rfl⟩ : syracuseStep 3126833 = 2345125) B2345125
theorem B1234483 : Blo 1234435 1234483 := bstep (se 1 (by rfl) ⟨925862, by rfl⟩ : syracuseStep 1234483 = 1851725) B1851725
theorem B2086465 : Blo 1234435 2086465 := bstep (se 2 (by rfl) ⟨782424, by rfl⟩ : syracuseStep 2086465 = 1564849) B1564849
theorem B1234499 : Blo 1234435 1234499 := bstep (se 1 (by rfl) ⟨925874, by rfl⟩ : syracuseStep 1234499 = 1851749) B1851749
theorem B1234515 : Blo 1234435 1234515 := bstep (se 1 (by rfl) ⟨925886, by rfl⟩ : syracuseStep 1234515 = 1851773) B1851773
theorem B1234531 : Blo 1234435 1234531 := bstep (se 1 (by rfl) ⟨925898, by rfl⟩ : syracuseStep 1234531 = 1851797) B1851797
theorem B3126883 : Blo 1234435 3126883 := bstep (se 1 (by rfl) ⟨2345162, by rfl⟩ : syracuseStep 3126883 = 4690325) B4690325
theorem B35599985 : Blo 1234435 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B1234547 : Blo 1234435 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B1234563 : Blo 1234435 1234563 := bstep (se 1 (by rfl) ⟨925922, by rfl⟩ : syracuseStep 1234563 = 1851845) B1851845
theorem B1234579 : Blo 1234435 1234579 := bstep (se 1 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 1234579 = 1851869) B1851869
theorem B1234595 : Blo 1234435 1234595 := bstep (se 1 (by rfl) ⟨925946, by rfl⟩ : syracuseStep 1234595 = 1851893) B1851893
theorem B1390243 : Blo 1234435 1390243 := bstep (se 1 (by rfl) ⟨1042682, by rfl⟩ : syracuseStep 1390243 = 2085365) B2085365
theorem B4167341 : Blo 1234435 4167341 := bstep (se 3 (by rfl) ⟨781376, by rfl⟩ : syracuseStep 4167341 = 1562753) B1562753
theorem B1234611 : Blo 1234435 1234611 := bstep (se 1 (by rfl) ⟨925958, by rfl⟩ : syracuseStep 1234611 = 1851917) B1851917
theorem B1234627 : Blo 1234435 1234627 := bstep (se 1 (by rfl) ⟨925970, by rfl⟩ : syracuseStep 1234627 = 1851941) B1851941
theorem B7919309 : Blo 1234435 7919309 := bstep (se 3 (by rfl) ⟨1484870, by rfl⟩ : syracuseStep 7919309 = 2969741) B2969741
theorem B3520205 : Blo 1234435 3520205 := bstep (se 3 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 3520205 = 1320077) B1320077
theorem B1234643 : Blo 1234435 1234643 := bstep (se 1 (by rfl) ⟨925982, by rfl⟩ : syracuseStep 1234643 = 1851965) B1851965
theorem B1234659 : Blo 1234435 1234659 := bstep (se 1 (by rfl) ⟨925994, by rfl⟩ : syracuseStep 1234659 = 1851989) B1851989
theorem B4167395 : Blo 1234435 4167395 := bstep (se 1 (by rfl) ⟨3125546, by rfl⟩ : syracuseStep 4167395 = 6251093) B6251093
theorem B3127025 : Blo 1234435 3127025 := bstep (se 2 (by rfl) ⟨1172634, by rfl⟩ : syracuseStep 3127025 = 2345269) B2345269
theorem B1234675 : Blo 1234435 1234675 := bstep (se 1 (by rfl) ⟨926006, by rfl⟩ : syracuseStep 1234675 = 1852013) B1852013
theorem B1234691 : Blo 1234435 1234691 := bstep (se 1 (by rfl) ⟨926018, by rfl⟩ : syracuseStep 1234691 = 1852037) B1852037
theorem B3520273 : Blo 1234435 3520273 := bstep (se 2 (by rfl) ⟨1320102, by rfl⟩ : syracuseStep 3520273 = 2640205) B2640205
theorem B1234707 : Blo 1234435 1234707 := bstep (se 1 (by rfl) ⟨926030, by rfl⟩ : syracuseStep 1234707 = 1852061) B1852061
theorem B1759009 : Blo 1234435 1759009 := bstep (se 2 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 1759009 = 1319257) B1319257
theorem B1234723 : Blo 1234435 1234723 := bstep (se 1 (by rfl) ⟨926042, by rfl⟩ : syracuseStep 1234723 = 1852085) B1852085
theorem B1562419 : Blo 1234435 1562419 := bstep (se 1 (by rfl) ⟨1171814, by rfl⟩ : syracuseStep 1562419 = 2343629) B2343629
theorem B1234739 : Blo 1234435 1234739 := bstep (se 1 (by rfl) ⟨926054, by rfl⟩ : syracuseStep 1234739 = 1852109) B1852109
theorem B1390387 : Blo 1234435 1390387 := bstep (se 1 (by rfl) ⟨1042790, by rfl⟩ : syracuseStep 1390387 = 2085581) B2085581
theorem B1234755 : Blo 1234435 1234755 := bstep (se 1 (by rfl) ⟨926066, by rfl⟩ : syracuseStep 1234755 = 1852133) B1852133
theorem B1759043 : Blo 1234435 1759043 := bstep (se 1 (by rfl) ⟨1319282, by rfl⟩ : syracuseStep 1759043 = 2638565) B2638565
theorem B1234771 : Blo 1234435 1234771 := bstep (se 1 (by rfl) ⟨926078, by rfl⟩ : syracuseStep 1234771 = 1852157) B1852157
theorem B2815843 : Blo 1234435 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1234787 : Blo 1234435 1234787 := bstep (se 1 (by rfl) ⟨926090, by rfl⟩ : syracuseStep 1234787 = 1852181) B1852181
theorem B1234803 : Blo 1234435 1234803 := bstep (se 1 (by rfl) ⟨926102, by rfl⟩ : syracuseStep 1234803 = 1852205) B1852205
theorem B1234819 : Blo 1234435 1234819 := bstep (se 1 (by rfl) ⟨926114, by rfl⟩ : syracuseStep 1234819 = 1852229) B1852229
theorem B1234835 : Blo 1234435 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B1234851 : Blo 1234435 1234851 := bstep (se 1 (by rfl) ⟨926138, by rfl⟩ : syracuseStep 1234851 = 1852277) B1852277
theorem B1234867 : Blo 1234435 1234867 := bstep (se 1 (by rfl) ⟨926150, by rfl⟩ : syracuseStep 1234867 = 1852301) B1852301
theorem B1234883 : Blo 1234435 1234883 := bstep (se 1 (by rfl) ⟨926162, by rfl⟩ : syracuseStep 1234883 = 1852325) B1852325
theorem B1390531 : Blo 1234435 1390531 := bstep (se 1 (by rfl) ⟨1042898, by rfl⟩ : syracuseStep 1390531 = 2085797) B2085797
theorem B1234899 : Blo 1234435 1234899 := bstep (se 1 (by rfl) ⟨926174, by rfl⟩ : syracuseStep 1234899 = 1852349) B1852349
theorem B1234915 : Blo 1234435 1234915 := bstep (se 1 (by rfl) ⟨926186, by rfl⟩ : syracuseStep 1234915 = 1852373) B1852373
theorem B4167665 : Blo 1234435 4167665 := bstep (se 2 (by rfl) ⟨1562874, by rfl⟩ : syracuseStep 4167665 = 3125749) B3125749
theorem B1234931 : Blo 1234435 1234931 := bstep (se 1 (by rfl) ⟨926198, by rfl⟩ : syracuseStep 1234931 = 1852397) B1852397
theorem B1234947 : Blo 1234435 1234947 := bstep (se 1 (by rfl) ⟨926210, by rfl⟩ : syracuseStep 1234947 = 1852421) B1852421
theorem B1669123 : Blo 1234435 1669123 := bstep (se 1 (by rfl) ⟨1251842, by rfl⟩ : syracuseStep 1669123 = 2503685) B2503685
theorem B1234963 : Blo 1234435 1234963 := bstep (se 1 (by rfl) ⟨926222, by rfl⟩ : syracuseStep 1234963 = 1852445) B1852445
theorem B1234979 : Blo 1234435 1234979 := bstep (se 1 (by rfl) ⟨926234, by rfl⟩ : syracuseStep 1234979 = 1852469) B1852469
theorem B3520547 : Blo 1234435 3520547 := bstep (se 1 (by rfl) ⟨2640410, by rfl⟩ : syracuseStep 3520547 = 5280821) B5280821
theorem B1234995 : Blo 1234435 1234995 := bstep (se 1 (by rfl) ⟨926246, by rfl⟩ : syracuseStep 1234995 = 1852493) B1852493
theorem B1235011 : Blo 1234435 1235011 := bstep (se 1 (by rfl) ⟨926258, by rfl⟩ : syracuseStep 1235011 = 1852517) B1852517
theorem B5273677 : Blo 1234435 5273677 := bstep (se 3 (by rfl) ⟨988814, by rfl⟩ : syracuseStep 5273677 = 1977629) B1977629
theorem B1235027 : Blo 1234435 1235027 := bstep (se 1 (by rfl) ⟨926270, by rfl⟩ : syracuseStep 1235027 = 1852541) B1852541
theorem B1390675 : Blo 1234435 1390675 := bstep (se 1 (by rfl) ⟨1043006, by rfl⟩ : syracuseStep 1390675 = 2086013) B2086013
theorem B1235043 : Blo 1234435 1235043 := bstep (se 1 (by rfl) ⟨926282, by rfl⟩ : syracuseStep 1235043 = 1852565) B1852565
theorem B10557539 : Blo 1234435 10557539 := bstep (se 1 (by rfl) ⟨7918154, by rfl⟩ : syracuseStep 10557539 = 15836309) B15836309
theorem B1235059 : Blo 1234435 1235059 := bstep (se 1 (by rfl) ⟨926294, by rfl⟩ : syracuseStep 1235059 = 1852589) B1852589
theorem B1235075 : Blo 1234435 1235075 := bstep (se 1 (by rfl) ⟨926306, by rfl⟩ : syracuseStep 1235075 = 1852613) B1852613
theorem B23730317 : Blo 1234435 23730317 := bstep (se 3 (by rfl) ⟨4449434, by rfl⟩ : syracuseStep 23730317 = 8898869) B8898869
theorem B1235091 : Blo 1234435 1235091 := bstep (se 1 (by rfl) ⟨926318, by rfl⟩ : syracuseStep 1235091 = 1852637) B1852637
theorem B1235107 : Blo 1234435 1235107 := bstep (se 1 (by rfl) ⟨926330, by rfl⟩ : syracuseStep 1235107 = 1852661) B1852661
theorem B1235123 : Blo 1234435 1235123 := bstep (se 1 (by rfl) ⟨926342, by rfl⟩ : syracuseStep 1235123 = 1852685) B1852685
theorem B1235139 : Blo 1234435 1235139 := bstep (se 1 (by rfl) ⟨926354, by rfl⟩ : syracuseStep 1235139 = 1852709) B1852709
theorem B14465221 : Blo 1234435 14465221 := bstep (se 4 (by rfl) ⟨1356114, by rfl⟩ : syracuseStep 14465221 = 2712229) B2712229
theorem B29333701 : Blo 1234435 29333701 := bstep (se 4 (by rfl) ⟨2750034, by rfl⟩ : syracuseStep 29333701 = 5500069) B5500069
theorem B1235155 : Blo 1234435 1235155 := bstep (se 1 (by rfl) ⟨926366, by rfl⟩ : syracuseStep 1235155 = 1852733) B1852733
theorem B1235171 : Blo 1234435 1235171 := bstep (se 1 (by rfl) ⟨926378, by rfl⟩ : syracuseStep 1235171 = 1852757) B1852757
theorem B1390819 : Blo 1234435 1390819 := bstep (se 1 (by rfl) ⟨1043114, by rfl⟩ : syracuseStep 1390819 = 2086229) B2086229
theorem B1235187 : Blo 1234435 1235187 := bstep (se 1 (by rfl) ⟨926390, by rfl⟩ : syracuseStep 1235187 = 1852781) B1852781
theorem B1235203 : Blo 1234435 1235203 := bstep (se 1 (by rfl) ⟨926402, by rfl⟩ : syracuseStep 1235203 = 1852805) B1852805
theorem B1235219 : Blo 1234435 1235219 := bstep (se 1 (by rfl) ⟨926414, by rfl⟩ : syracuseStep 1235219 = 1852829) B1852829
theorem B1562915 : Blo 1234435 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B1235235 : Blo 1234435 1235235 := bstep (se 1 (by rfl) ⟨926426, by rfl⟩ : syracuseStep 1235235 = 1852853) B1852853
theorem B1235251 : Blo 1234435 1235251 := bstep (se 1 (by rfl) ⟨926438, by rfl⟩ : syracuseStep 1235251 = 1852877) B1852877
theorem B1235267 : Blo 1234435 1235267 := bstep (se 1 (by rfl) ⟨926450, by rfl⟩ : syracuseStep 1235267 = 1852901) B1852901
theorem B1235283 : Blo 1234435 1235283 := bstep (se 1 (by rfl) ⟨926462, by rfl⟩ : syracuseStep 1235283 = 1852925) B1852925
theorem B2062675 : Blo 1234435 2062675 := bstep (se 1 (by rfl) ⟨1547006, by rfl⟩ : syracuseStep 2062675 = 3094013) B3094013
theorem B1235299 : Blo 1234435 1235299 := bstep (se 1 (by rfl) ⟨926474, by rfl⟩ : syracuseStep 1235299 = 1852949) B1852949
theorem B1759601 : Blo 1234435 1759601 := bstep (se 2 (by rfl) ⟨659850, by rfl⟩ : syracuseStep 1759601 = 1319701) B1319701
theorem B1235315 : Blo 1234435 1235315 := bstep (se 1 (by rfl) ⟨926486, by rfl⟩ : syracuseStep 1235315 = 1852973) B1852973
theorem B1390963 : Blo 1234435 1390963 := bstep (se 1 (by rfl) ⟨1043222, by rfl⟩ : syracuseStep 1390963 = 2086445) B2086445
theorem B1235331 : Blo 1234435 1235331 := bstep (se 1 (by rfl) ⟨926498, by rfl⟩ : syracuseStep 1235331 = 1852997) B1852997
theorem B2226563 : Blo 1234435 2226563 := bstep (se 1 (by rfl) ⟨1669922, by rfl⟩ : syracuseStep 2226563 = 3339845) B3339845
theorem B1235347 : Blo 1234435 1235347 := bstep (se 1 (by rfl) ⟨926510, by rfl⟩ : syracuseStep 1235347 = 1853021) B1853021
theorem B1235363 : Blo 1234435 1235363 := bstep (se 1 (by rfl) ⟨926522, by rfl⟩ : syracuseStep 1235363 = 1853045) B1853045
theorem B2111923 : Blo 1234435 2111923 := bstep (se 1 (by rfl) ⟨1583942, by rfl⟩ : syracuseStep 2111923 = 3167885) B3167885
theorem B1235379 : Blo 1234435 1235379 := bstep (se 1 (by rfl) ⟨926534, by rfl⟩ : syracuseStep 1235379 = 1853069) B1853069
theorem B1759681 : Blo 1234435 1759681 := bstep (se 2 (by rfl) ⟨659880, by rfl⟩ : syracuseStep 1759681 = 1319761) B1319761
theorem B1235395 : Blo 1234435 1235395 := bstep (se 1 (by rfl) ⟨926546, by rfl⟩ : syracuseStep 1235395 = 1853093) B1853093
theorem B1235411 : Blo 1234435 1235411 := bstep (se 1 (by rfl) ⟨926558, by rfl⟩ : syracuseStep 1235411 = 1853117) B1853117
theorem B1235427 : Blo 1234435 1235427 := bstep (se 1 (by rfl) ⟨926570, by rfl⟩ : syracuseStep 1235427 = 1853141) B1853141
theorem B4692451 : Blo 1234435 4692451 := bstep (se 1 (by rfl) ⟨3519338, by rfl⟩ : syracuseStep 4692451 = 7038677) B7038677
theorem B4225517 : Blo 1234435 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B1235443 : Blo 1234435 1235443 := bstep (se 1 (by rfl) ⟨926582, by rfl⟩ : syracuseStep 1235443 = 1853165) B1853165
theorem B1235459 : Blo 1234435 1235459 := bstep (se 1 (by rfl) ⟨926594, by rfl⟩ : syracuseStep 1235459 = 1853189) B1853189
theorem B4168205 : Blo 1234435 4168205 := bstep (se 3 (by rfl) ⟨781538, by rfl⟩ : syracuseStep 4168205 = 1563077) B1563077
theorem B1235475 : Blo 1234435 1235475 := bstep (se 1 (by rfl) ⟨926606, by rfl⟩ : syracuseStep 1235475 = 1853213) B1853213
theorem B1235491 : Blo 1234435 1235491 := bstep (se 1 (by rfl) ⟨926618, by rfl⟩ : syracuseStep 1235491 = 1853237) B1853237
theorem B1235507 : Blo 1234435 1235507 := bstep (se 1 (by rfl) ⟨926630, by rfl⟩ : syracuseStep 1235507 = 1853261) B1853261
theorem B4168259 : Blo 1234435 4168259 := bstep (se 1 (by rfl) ⟨3126194, by rfl⟩ : syracuseStep 4168259 = 6252389) B6252389
theorem B1235523 : Blo 1234435 1235523 := bstep (se 1 (by rfl) ⟨926642, by rfl⟩ : syracuseStep 1235523 = 1853285) B1853285
theorem B1235539 : Blo 1234435 1235539 := bstep (se 1 (by rfl) ⟨926654, by rfl⟩ : syracuseStep 1235539 = 1853309) B1853309
theorem B1235555 : Blo 1234435 1235555 := bstep (se 1 (by rfl) ⟨926666, by rfl⟩ : syracuseStep 1235555 = 1853333) B1853333
theorem B1235571 : Blo 1234435 1235571 := bstep (se 1 (by rfl) ⟨926678, by rfl⟩ : syracuseStep 1235571 = 1853357) B1853357
theorem B1235587 : Blo 1234435 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B2005651 : Blo 1234435 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1235603 : Blo 1234435 1235603 := bstep (se 1 (by rfl) ⟨926702, by rfl⟩ : syracuseStep 1235603 = 1853405) B1853405
theorem B1235619 : Blo 1234435 1235619 := bstep (se 1 (by rfl) ⟨926714, by rfl⟩ : syracuseStep 1235619 = 1853429) B1853429
theorem B1235635 : Blo 1234435 1235635 := bstep (se 1 (by rfl) ⟨926726, by rfl⟩ : syracuseStep 1235635 = 1853453) B1853453
theorem B1235651 : Blo 1234435 1235651 := bstep (se 1 (by rfl) ⟨926738, by rfl⟩ : syracuseStep 1235651 = 1853477) B1853477
theorem B2636497 : Blo 1234435 2636497 := bstep (se 2 (by rfl) ⟨988686, by rfl⟩ : syracuseStep 2636497 = 1977373) B1977373
theorem B1235667 : Blo 1234435 1235667 := bstep (se 1 (by rfl) ⟨926750, by rfl⟩ : syracuseStep 1235667 = 1853501) B1853501
theorem B3128017 : Blo 1234435 3128017 := bstep (se 2 (by rfl) ⟨1173006, by rfl⟩ : syracuseStep 3128017 = 2346013) B2346013
theorem B1235683 : Blo 1234435 1235683 := bstep (se 1 (by rfl) ⟨926762, by rfl⟩ : syracuseStep 1235683 = 1853525) B1853525
theorem B1235699 : Blo 1234435 1235699 := bstep (se 1 (by rfl) ⟨926774, by rfl⟩ : syracuseStep 1235699 = 1853549) B1853549
theorem B1669891 : Blo 1234435 1669891 := bstep (se 1 (by rfl) ⟨1252418, by rfl⟩ : syracuseStep 1669891 = 2504837) B2504837
theorem B1235715 : Blo 1234435 1235715 := bstep (se 1 (by rfl) ⟨926786, by rfl⟩ : syracuseStep 1235715 = 1853573) B1853573
theorem B1235731 : Blo 1234435 1235731 := bstep (se 1 (by rfl) ⟨926798, by rfl⟩ : syracuseStep 1235731 = 1853597) B1853597
theorem B1235747 : Blo 1234435 1235747 := bstep (se 1 (by rfl) ⟨926810, by rfl⟩ : syracuseStep 1235747 = 1853621) B1853621
theorem B1235763 : Blo 1234435 1235763 := bstep (se 1 (by rfl) ⟨926822, by rfl⟩ : syracuseStep 1235763 = 1853645) B1853645
theorem B1235779 : Blo 1234435 1235779 := bstep (se 1 (by rfl) ⟨926834, by rfl⟩ : syracuseStep 1235779 = 1853669) B1853669
theorem B4168529 : Blo 1234435 4168529 := bstep (se 2 (by rfl) ⟨1563198, by rfl⟩ : syracuseStep 4168529 = 3126397) B3126397
theorem B1235795 : Blo 1234435 1235795 := bstep (se 1 (by rfl) ⟨926846, by rfl⟩ : syracuseStep 1235795 = 1853693) B1853693
theorem B1235811 : Blo 1234435 1235811 := bstep (se 1 (by rfl) ⟨926858, by rfl⟩ : syracuseStep 1235811 = 1853717) B1853717
theorem B7035761 : Blo 1234435 7035761 := bstep (se 2 (by rfl) ⟨2638410, by rfl⟩ : syracuseStep 7035761 = 5276821) B5276821
theorem B1235827 : Blo 1234435 1235827 := bstep (se 1 (by rfl) ⟨926870, by rfl⟩ : syracuseStep 1235827 = 1853741) B1853741
theorem B1235843 : Blo 1234435 1235843 := bstep (se 1 (by rfl) ⟨926882, by rfl⟩ : syracuseStep 1235843 = 1853765) B1853765
theorem B1235859 : Blo 1234435 1235859 := bstep (se 1 (by rfl) ⟨926894, by rfl⟩ : syracuseStep 1235859 = 1853789) B1853789
theorem B1235875 : Blo 1234435 1235875 := bstep (se 1 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 1235875 = 1853813) B1853813
theorem B1235891 : Blo 1234435 1235891 := bstep (se 1 (by rfl) ⟨926918, by rfl⟩ : syracuseStep 1235891 = 1853837) B1853837
theorem B1235907 : Blo 1234435 1235907 := bstep (se 1 (by rfl) ⟨926930, by rfl⟩ : syracuseStep 1235907 = 1853861) B1853861
theorem B1235923 : Blo 1234435 1235923 := bstep (se 1 (by rfl) ⟨926942, by rfl⟩ : syracuseStep 1235923 = 1853885) B1853885
theorem B1563619 : Blo 1234435 1563619 := bstep (se 1 (by rfl) ⟨1172714, by rfl⟩ : syracuseStep 1563619 = 2345429) B2345429
theorem B3128291 : Blo 1234435 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B1235939 : Blo 1234435 1235939 := bstep (se 1 (by rfl) ⟨926954, by rfl⟩ : syracuseStep 1235939 = 1853909) B1853909
theorem B1235955 : Blo 1234435 1235955 := bstep (se 1 (by rfl) ⟨926966, by rfl⟩ : syracuseStep 1235955 = 1853933) B1853933
theorem B1235971 : Blo 1234435 1235971 := bstep (se 1 (by rfl) ⟨926978, by rfl⟩ : syracuseStep 1235971 = 1853957) B1853957
theorem B3341315 : Blo 1234435 3341315 := bstep (se 1 (by rfl) ⟨2505986, by rfl⟩ : syracuseStep 3341315 = 5011973) B5011973
theorem B1235987 : Blo 1234435 1235987 := bstep (se 1 (by rfl) ⟨926990, by rfl⟩ : syracuseStep 1235987 = 1853981) B1853981
theorem B1236003 : Blo 1234435 1236003 := bstep (se 1 (by rfl) ⟨927002, by rfl⟩ : syracuseStep 1236003 = 1854005) B1854005
theorem B1236019 : Blo 1234435 1236019 := bstep (se 1 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 1236019 = 1854029) B1854029
theorem B1563715 : Blo 1234435 1563715 := bstep (se 1 (by rfl) ⟨1172786, by rfl⟩ : syracuseStep 1563715 = 2345573) B2345573
theorem B1236035 : Blo 1234435 1236035 := bstep (se 1 (by rfl) ⟨927026, by rfl⟩ : syracuseStep 1236035 = 1854053) B1854053
theorem B1236051 : Blo 1234435 1236051 := bstep (se 1 (by rfl) ⟨927038, by rfl⟩ : syracuseStep 1236051 = 1854077) B1854077
theorem B1236067 : Blo 1234435 1236067 := bstep (se 1 (by rfl) ⟨927050, by rfl⟩ : syracuseStep 1236067 = 1854101) B1854101
theorem B2227313 : Blo 1234435 2227313 := bstep (se 2 (by rfl) ⟨835242, by rfl⟩ : syracuseStep 2227313 = 1670485) B1670485
theorem B1236083 : Blo 1234435 1236083 := bstep (se 1 (by rfl) ⟨927062, by rfl⟩ : syracuseStep 1236083 = 1854125) B1854125
theorem B1236099 : Blo 1234435 1236099 := bstep (se 1 (by rfl) ⟨927074, by rfl⟩ : syracuseStep 1236099 = 1854149) B1854149
theorem B1236115 : Blo 1234435 1236115 := bstep (se 1 (by rfl) ⟨927086, by rfl⟩ : syracuseStep 1236115 = 1854173) B1854173
theorem B6249635 : Blo 1234435 6249635 := bstep (se 1 (by rfl) ⟨4687226, by rfl⟩ : syracuseStep 6249635 = 9374453) B9374453
theorem B3128483 : Blo 1234435 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B1236131 : Blo 1234435 1236131 := bstep (se 1 (by rfl) ⟨927098, by rfl⟩ : syracuseStep 1236131 = 1854197) B1854197
theorem B1236147 : Blo 1234435 1236147 := bstep (se 1 (by rfl) ⟨927110, by rfl⟩ : syracuseStep 1236147 = 1854221) B1854221
theorem B1408195 : Blo 1234435 1408195 := bstep (se 1 (by rfl) ⟨1056146, by rfl⟩ : syracuseStep 1408195 = 2112293) B2112293
theorem B1236163 : Blo 1234435 1236163 := bstep (se 1 (by rfl) ⟨927122, by rfl⟩ : syracuseStep 1236163 = 1854245) B1854245
theorem B1236179 : Blo 1234435 1236179 := bstep (se 1 (by rfl) ⟨927134, by rfl⟩ : syracuseStep 1236179 = 1854269) B1854269
theorem B1760467 : Blo 1234435 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B1236195 : Blo 1234435 1236195 := bstep (se 1 (by rfl) ⟨927146, by rfl⟩ : syracuseStep 1236195 = 1854293) B1854293
theorem B1236211 : Blo 1234435 1236211 := bstep (se 1 (by rfl) ⟨927158, by rfl⟩ : syracuseStep 1236211 = 1854317) B1854317
theorem B1236227 : Blo 1234435 1236227 := bstep (se 1 (by rfl) ⟨927170, by rfl⟩ : syracuseStep 1236227 = 1854341) B1854341
theorem B1236243 : Blo 1234435 1236243 := bstep (se 1 (by rfl) ⟨927182, by rfl⟩ : syracuseStep 1236243 = 1854365) B1854365
theorem B3956003 : Blo 1234435 3956003 := bstep (se 1 (by rfl) ⟨2967002, by rfl⟩ : syracuseStep 3956003 = 5934005) B5934005
theorem B1236259 : Blo 1234435 1236259 := bstep (se 1 (by rfl) ⟨927194, by rfl⟩ : syracuseStep 1236259 = 1854389) B1854389
theorem B1236275 : Blo 1234435 1236275 := bstep (se 1 (by rfl) ⟨927206, by rfl⟩ : syracuseStep 1236275 = 1854413) B1854413
theorem B1236291 : Blo 1234435 1236291 := bstep (se 1 (by rfl) ⟨927218, by rfl⟩ : syracuseStep 1236291 = 1854437) B1854437
theorem B2227537 : Blo 1234435 2227537 := bstep (se 2 (by rfl) ⟨835326, by rfl⟩ : syracuseStep 2227537 = 1670653) B1670653
theorem B1236307 : Blo 1234435 1236307 := bstep (se 1 (by rfl) ⟨927230, by rfl⟩ : syracuseStep 1236307 = 1854461) B1854461
theorem B1236323 : Blo 1234435 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B4169069 : Blo 1234435 4169069 := bstep (se 3 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 4169069 = 1563401) B1563401
theorem B1236339 : Blo 1234435 1236339 := bstep (se 1 (by rfl) ⟨927254, by rfl⟩ : syracuseStep 1236339 = 1854509) B1854509
theorem B1236355 : Blo 1234435 1236355 := bstep (se 1 (by rfl) ⟨927266, by rfl⟩ : syracuseStep 1236355 = 1854533) B1854533
theorem B2227601 : Blo 1234435 2227601 := bstep (se 2 (by rfl) ⟨835350, by rfl⟩ : syracuseStep 2227601 = 1670701) B1670701
theorem B1236371 : Blo 1234435 1236371 := bstep (se 1 (by rfl) ⟨927278, by rfl⟩ : syracuseStep 1236371 = 1854557) B1854557
theorem B4169123 : Blo 1234435 4169123 := bstep (se 1 (by rfl) ⟨3126842, by rfl⟩ : syracuseStep 4169123 = 6253685) B6253685
theorem B1236387 : Blo 1234435 1236387 := bstep (se 1 (by rfl) ⟨927290, by rfl⟩ : syracuseStep 1236387 = 1854581) B1854581
theorem B1236403 : Blo 1234435 1236403 := bstep (se 1 (by rfl) ⟨927302, by rfl⟩ : syracuseStep 1236403 = 1854605) B1854605
theorem B1670593 : Blo 1234435 1670593 := bstep (se 2 (by rfl) ⟨626472, by rfl⟩ : syracuseStep 1670593 = 1252945) B1252945
theorem B1236419 : Blo 1234435 1236419 := bstep (se 1 (by rfl) ⟨927314, by rfl⟩ : syracuseStep 1236419 = 1854629) B1854629
theorem B1236435 : Blo 1234435 1236435 := bstep (se 1 (by rfl) ⟨927326, by rfl⟩ : syracuseStep 1236435 = 1854653) B1854653
theorem B9379313 : Blo 1234435 9379313 := bstep (se 2 (by rfl) ⟨3517242, by rfl⟩ : syracuseStep 9379313 = 7034485) B7034485
theorem B3956273 : Blo 1234435 3956273 := bstep (se 2 (by rfl) ⟨1483602, by rfl⟩ : syracuseStep 3956273 = 2967205) B2967205
theorem B1564211 : Blo 1234435 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B4513357 : Blo 1234435 4513357 := bstep (se 3 (by rfl) ⟨846254, by rfl⟩ : syracuseStep 4513357 = 1692509) B1692509
theorem B4169393 : Blo 1234435 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B4284109 : Blo 1234435 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B7913285 : Blo 1234435 7913285 := bstep (se 4 (by rfl) ⟨741870, by rfl⟩ : syracuseStep 7913285 = 1483741) B1483741
theorem B6258545 : Blo 1234435 6258545 := bstep (se 2 (by rfl) ⟨2346954, by rfl⟩ : syracuseStep 6258545 = 4693909) B4693909
theorem B10551181 : Blo 1234435 10551181 := bstep (se 3 (by rfl) ⟨1978346, by rfl⟩ : syracuseStep 10551181 = 3956693) B3956693
theorem B6250445 : Blo 1234435 6250445 := bstep (se 3 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 6250445 = 2343917) B2343917
theorem B4169879 : Blo 1234435 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B1851659 : Blo 1234435 1851659 := bstep (se 1 (by rfl) ⟨1388744, by rfl⟩ : syracuseStep 1851659 = 2777489) B2777489
theorem B6250769 : Blo 1234435 6250769 := bstep (se 2 (by rfl) ⟨2344038, by rfl⟩ : syracuseStep 6250769 = 4688077) B4688077
theorem B1851671 : Blo 1234435 1851671 := bstep (se 1 (by rfl) ⟨1388753, by rfl⟩ : syracuseStep 1851671 = 2777507) B2777507
theorem B1851737 : Blo 1234435 1851737 := bstep (se 2 (by rfl) ⟨694401, by rfl⟩ : syracuseStep 1851737 = 1388803) B1388803
theorem B5145005 : Blo 1234435 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B6250931 : Blo 1234435 6250931 := bstep (se 1 (by rfl) ⟨4688198, by rfl⟩ : syracuseStep 6250931 = 9376397) B9376397
theorem B1851851 : Blo 1234435 1851851 := bstep (se 1 (by rfl) ⟨1388888, by rfl⟩ : syracuseStep 1851851 = 2777777) B2777777
theorem B1851863 : Blo 1234435 1851863 := bstep (se 1 (by rfl) ⟨1388897, by rfl⟩ : syracuseStep 1851863 = 2777795) B2777795
theorem B2777561 : Blo 1234435 2777561 := bstep (se 2 (by rfl) ⟨1041585, by rfl⟩ : syracuseStep 2777561 = 2083171) B2083171
theorem B7037401 : Blo 1234435 7037401 := bstep (se 2 (by rfl) ⟨2639025, by rfl⟩ : syracuseStep 7037401 = 5278051) B5278051
theorem B5636573 : Blo 1234435 5636573 := bstep (se 3 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 5636573 = 2113715) B2113715
theorem B11272709 : Blo 1234435 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B1851929 : Blo 1234435 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B2777651 : Blo 1234435 2777651 := bstep (se 1 (by rfl) ⟨2083238, by rfl⟩ : syracuseStep 2777651 = 4166477) B4166477
theorem B2777687 : Blo 1234435 2777687 := bstep (se 1 (by rfl) ⟨2083265, by rfl⟩ : syracuseStep 2777687 = 4166531) B4166531
theorem B1852043 : Blo 1234435 1852043 := bstep (se 1 (by rfl) ⟨1389032, by rfl⟩ : syracuseStep 1852043 = 2778065) B2778065
theorem B1852055 : Blo 1234435 1852055 := bstep (se 1 (by rfl) ⟨1389041, by rfl⟩ : syracuseStep 1852055 = 2778083) B2778083
theorem B7512755 : Blo 1234435 7512755 := bstep (se 1 (by rfl) ⟨5634566, by rfl⟩ : syracuseStep 7512755 = 11269133) B11269133
theorem B4170419 : Blo 1234435 4170419 := bstep (se 1 (by rfl) ⟨3127814, by rfl⟩ : syracuseStep 4170419 = 6255629) B6255629
theorem B2966233 : Blo 1234435 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B1852121 : Blo 1234435 1852121 := bstep (se 2 (by rfl) ⟨694545, by rfl⟩ : syracuseStep 1852121 = 1389091) B1389091
theorem B2343667 : Blo 1234435 2343667 := bstep (se 1 (by rfl) ⟨1757750, by rfl⟩ : syracuseStep 2343667 = 3515501) B3515501
theorem B14082821 : Blo 1234435 14082821 := bstep (se 4 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 14082821 = 2640529) B2640529
theorem B2777867 : Blo 1234435 2777867 := bstep (se 1 (by rfl) ⟨2083400, by rfl⟩ : syracuseStep 2777867 = 4166801) B4166801
theorem B2777921 : Blo 1234435 2777921 := bstep (se 2 (by rfl) ⟨1041720, by rfl⟩ : syracuseStep 2777921 = 2083441) B2083441
theorem B7127873 : Blo 1234435 7127873 := bstep (se 2 (by rfl) ⟨2672952, by rfl⟩ : syracuseStep 7127873 = 5345905) B5345905
theorem B1852235 : Blo 1234435 1852235 := bstep (se 1 (by rfl) ⟨1389176, by rfl⟩ : syracuseStep 1852235 = 2778353) B2778353
theorem B10552139 : Blo 1234435 10552139 := bstep (se 1 (by rfl) ⟨7914104, by rfl⟩ : syracuseStep 10552139 = 15828209) B15828209
theorem B1852247 : Blo 1234435 1852247 := bstep (se 1 (by rfl) ⟨1389185, by rfl⟩ : syracuseStep 1852247 = 2778371) B2778371
theorem B38028133 : Blo 1234435 38028133 := bstep (se 4 (by rfl) ⟨3565137, by rfl⟩ : syracuseStep 38028133 = 7130275) B7130275
theorem B1852313 : Blo 1234435 1852313 := bstep (se 2 (by rfl) ⟨694617, by rfl⟩ : syracuseStep 1852313 = 1389235) B1389235
theorem B1319851 : Blo 1234435 1319851 := bstep (se 1 (by rfl) ⟨989888, by rfl⟩ : syracuseStep 1319851 = 1979777) B1979777
theorem B3515329 : Blo 1234435 3515329 := bstep (se 2 (by rfl) ⟨1318248, by rfl⟩ : syracuseStep 3515329 = 2636497) B2636497
theorem B4170689 : Blo 1234435 4170689 := bstep (se 2 (by rfl) ⟨1564008, by rfl⟩ : syracuseStep 4170689 = 3128017) B3128017
theorem B1852427 : Blo 1234435 1852427 := bstep (se 1 (by rfl) ⟨1389320, by rfl⟩ : syracuseStep 1852427 = 2778641) B2778641
theorem B1852439 : Blo 1234435 1852439 := bstep (se 1 (by rfl) ⟨1389329, by rfl⟩ : syracuseStep 1852439 = 2778659) B2778659
theorem B2778137 : Blo 1234435 2778137 := bstep (se 2 (by rfl) ⟨1041801, by rfl⟩ : syracuseStep 2778137 = 2083603) B2083603
theorem B5940269 : Blo 1234435 5940269 := bstep (se 3 (by rfl) ⟨1113800, by rfl⟩ : syracuseStep 5940269 = 2227601) B2227601
theorem B22848581 : Blo 1234435 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B23733323 : Blo 1234435 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B1852505 : Blo 1234435 1852505 := bstep (se 2 (by rfl) ⟨694689, by rfl⟩ : syracuseStep 1852505 = 1389379) B1389379
theorem B2778227 : Blo 1234435 2778227 := bstep (se 1 (by rfl) ⟨2083670, by rfl⟩ : syracuseStep 2778227 = 4167341) B4167341
theorem B2778263 : Blo 1234435 2778263 := bstep (se 1 (by rfl) ⟨2083697, by rfl⟩ : syracuseStep 2778263 = 4167395) B4167395
theorem B2344115 : Blo 1234435 2344115 := bstep (se 1 (by rfl) ⟨1758086, by rfl⟩ : syracuseStep 2344115 = 3516173) B3516173
theorem B1852619 : Blo 1234435 1852619 := bstep (se 1 (by rfl) ⟨1389464, by rfl⟩ : syracuseStep 1852619 = 2778929) B2778929
theorem B1852631 : Blo 1234435 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B2344153 : Blo 1234435 2344153 := bstep (se 2 (by rfl) ⟨879057, by rfl⟩ : syracuseStep 2344153 = 1758115) B1758115
theorem B2712793 : Blo 1234435 2712793 := bstep (se 2 (by rfl) ⟨1017297, by rfl⟩ : syracuseStep 2712793 = 2034595) B2034595
theorem B1852697 : Blo 1234435 1852697 := bstep (se 2 (by rfl) ⟨694761, by rfl⟩ : syracuseStep 1852697 = 1389523) B1389523
theorem B2639155 : Blo 1234435 2639155 := bstep (se 1 (by rfl) ⟨1979366, by rfl⟩ : syracuseStep 2639155 = 3958733) B3958733
theorem B2778443 : Blo 1234435 2778443 := bstep (se 1 (by rfl) ⟨2083832, by rfl⟩ : syracuseStep 2778443 = 4167665) B4167665
theorem B2778497 : Blo 1234435 2778497 := bstep (se 2 (by rfl) ⟨1041936, by rfl⟩ : syracuseStep 2778497 = 2083873) B2083873
theorem B1852811 : Blo 1234435 1852811 := bstep (se 1 (by rfl) ⟨1389608, by rfl⟩ : syracuseStep 1852811 = 2779217) B2779217
theorem B1852823 : Blo 1234435 1852823 := bstep (se 1 (by rfl) ⟨1389617, by rfl⟩ : syracuseStep 1852823 = 2779235) B2779235
theorem B7038359 : Blo 1234435 7038359 := bstep (se 1 (by rfl) ⟨5278769, by rfl⟩ : syracuseStep 7038359 = 10557539) B10557539
theorem B15820211 : Blo 1234435 15820211 := bstep (se 1 (by rfl) ⟨11865158, by rfl⟩ : syracuseStep 15820211 = 23730317) B23730317
theorem B1852889 : Blo 1234435 1852889 := bstep (se 2 (by rfl) ⟨694833, by rfl⟩ : syracuseStep 1852889 = 1389667) B1389667
theorem B4171229 : Blo 1234435 4171229 := bstep (se 3 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 4171229 = 1564211) B1564211
theorem B1853003 : Blo 1234435 1853003 := bstep (se 1 (by rfl) ⟨1389752, by rfl⟩ : syracuseStep 1853003 = 2779505) B2779505
theorem B1853015 : Blo 1234435 1853015 := bstep (se 1 (by rfl) ⟨1389761, by rfl⟩ : syracuseStep 1853015 = 2779523) B2779523
theorem B1484375 : Blo 1234435 1484375 := bstep (se 1 (by rfl) ⟨1113281, by rfl⟩ : syracuseStep 1484375 = 2226563) B2226563
theorem B1877593 : Blo 1234435 1877593 := bstep (se 2 (by rfl) ⟨704097, by rfl⟩ : syracuseStep 1877593 = 1408195) B1408195
theorem B2778713 : Blo 1234435 2778713 := bstep (se 2 (by rfl) ⟨1042017, by rfl⟩ : syracuseStep 2778713 = 2084035) B2084035
theorem B2344601 : Blo 1234435 2344601 := bstep (se 2 (by rfl) ⟨879225, by rfl⟩ : syracuseStep 2344601 = 1758451) B1758451
theorem B1853081 : Blo 1234435 1853081 := bstep (se 2 (by rfl) ⟨694905, by rfl⟩ : syracuseStep 1853081 = 1389811) B1389811
theorem B2778803 : Blo 1234435 2778803 := bstep (se 1 (by rfl) ⟨2084102, by rfl⟩ : syracuseStep 2778803 = 4168205) B4168205
theorem B2778839 : Blo 1234435 2778839 := bstep (se 1 (by rfl) ⟨2084129, by rfl⟩ : syracuseStep 2778839 = 4168259) B4168259
theorem B4687577 : Blo 1234435 4687577 := bstep (se 2 (by rfl) ⟨1757841, by rfl⟩ : syracuseStep 4687577 = 3515683) B3515683
theorem B1853195 : Blo 1234435 1853195 := bstep (se 1 (by rfl) ⟨1389896, by rfl⟩ : syracuseStep 1853195 = 2779793) B2779793
theorem B1853207 : Blo 1234435 1853207 := bstep (se 1 (by rfl) ⟨1389905, by rfl⟩ : syracuseStep 1853207 = 2779811) B2779811
theorem B2639641 : Blo 1234435 2639641 := bstep (se 2 (by rfl) ⟨989865, by rfl⟩ : syracuseStep 2639641 = 1979731) B1979731
theorem B1853273 : Blo 1234435 1853273 := bstep (se 2 (by rfl) ⟨694977, by rfl⟩ : syracuseStep 1853273 = 1389955) B1389955
theorem B25692005 : Blo 1234435 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B2779019 : Blo 1234435 2779019 := bstep (se 1 (by rfl) ⟨2084264, by rfl⟩ : syracuseStep 2779019 = 4168529) B4168529
theorem B2779073 : Blo 1234435 2779073 := bstep (se 2 (by rfl) ⟨1042152, by rfl⟩ : syracuseStep 2779073 = 2084305) B2084305
theorem B3172289 : Blo 1234435 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B1853387 : Blo 1234435 1853387 := bstep (se 1 (by rfl) ⟨1390040, by rfl⟩ : syracuseStep 1853387 = 2780081) B2780081
theorem B1853399 : Blo 1234435 1853399 := bstep (se 1 (by rfl) ⟨1390049, by rfl⟩ : syracuseStep 1853399 = 2780099) B2780099
theorem B4687895 : Blo 1234435 4687895 := bstep (se 1 (by rfl) ⟨3515921, by rfl⟩ : syracuseStep 4687895 = 7031843) B7031843
theorem B1853465 : Blo 1234435 1853465 := bstep (se 2 (by rfl) ⟨695049, by rfl⟩ : syracuseStep 1853465 = 1390099) B1390099
theorem B2967617 : Blo 1234435 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B4515905 : Blo 1234435 4515905 := bstep (se 2 (by rfl) ⟨1693464, by rfl⟩ : syracuseStep 4515905 = 3386929) B3386929
theorem B1484875 : Blo 1234435 1484875 := bstep (se 1 (by rfl) ⟨1113656, by rfl⟩ : syracuseStep 1484875 = 2227313) B2227313
theorem B1853579 : Blo 1234435 1853579 := bstep (se 1 (by rfl) ⟨1390184, by rfl⟩ : syracuseStep 1853579 = 2780369) B2780369
theorem B1853591 : Blo 1234435 1853591 := bstep (se 1 (by rfl) ⟨1390193, by rfl⟩ : syracuseStep 1853591 = 2780387) B2780387
theorem B2779289 : Blo 1234435 2779289 := bstep (se 2 (by rfl) ⟨1042233, by rfl⟩ : syracuseStep 2779289 = 2084467) B2084467
theorem B5277899 : Blo 1234435 5277899 := bstep (se 1 (by rfl) ⟨3958424, by rfl⟩ : syracuseStep 5277899 = 7916849) B7916849
theorem B1853657 : Blo 1234435 1853657 := bstep (se 2 (by rfl) ⟨695121, by rfl⟩ : syracuseStep 1853657 = 1390243) B1390243
theorem B2779379 : Blo 1234435 2779379 := bstep (se 1 (by rfl) ⟨2084534, by rfl⟩ : syracuseStep 2779379 = 4169069) B4169069
theorem B2779415 : Blo 1234435 2779415 := bstep (se 1 (by rfl) ⟨2084561, by rfl⟩ : syracuseStep 2779415 = 4169123) B4169123
theorem B6252875 : Blo 1234435 6252875 := bstep (se 1 (by rfl) ⟨4689656, by rfl⟩ : syracuseStep 6252875 = 9379313) B9379313
theorem B1853771 : Blo 1234435 1853771 := bstep (se 1 (by rfl) ⟨1390328, by rfl⟩ : syracuseStep 1853771 = 2780657) B2780657
theorem B1853783 : Blo 1234435 1853783 := bstep (se 1 (by rfl) ⟨1390337, by rfl⟩ : syracuseStep 1853783 = 2780675) B2780675
theorem B2345345 : Blo 1234435 2345345 := bstep (se 2 (by rfl) ⟨879504, by rfl⟩ : syracuseStep 2345345 = 1759009) B1759009
theorem B2083225 : Blo 1234435 2083225 := bstep (se 2 (by rfl) ⟨781209, by rfl⟩ : syracuseStep 2083225 = 1562419) B1562419
theorem B1853849 : Blo 1234435 1853849 := bstep (se 2 (by rfl) ⟨695193, by rfl⟩ : syracuseStep 1853849 = 1390387) B1390387
theorem B2779595 : Blo 1234435 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B3754457 : Blo 1234435 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B2779649 : Blo 1234435 2779649 := bstep (se 2 (by rfl) ⟨1042368, by rfl⟩ : syracuseStep 2779649 = 2084737) B2084737
theorem B1853963 : Blo 1234435 1853963 := bstep (se 1 (by rfl) ⟨1390472, by rfl⟩ : syracuseStep 1853963 = 2780945) B2780945
theorem B14068241 : Blo 1234435 14068241 := bstep (se 2 (by rfl) ⟨5275590, by rfl⟩ : syracuseStep 14068241 = 10551181) B10551181
theorem B1853975 : Blo 1234435 1853975 := bstep (se 1 (by rfl) ⟨1390481, by rfl⟩ : syracuseStep 1853975 = 2780963) B2780963
theorem B4172363 : Blo 1234435 4172363 := bstep (se 1 (by rfl) ⟨3129272, by rfl⟩ : syracuseStep 4172363 = 6258545) B6258545
theorem B1854041 : Blo 1234435 1854041 := bstep (se 2 (by rfl) ⟨695265, by rfl⟩ : syracuseStep 1854041 = 1390531) B1390531
theorem B2345611 : Blo 1234435 2345611 := bstep (se 1 (by rfl) ⟨1759208, by rfl⟩ : syracuseStep 2345611 = 3518417) B3518417
theorem B4688563 : Blo 1234435 4688563 := bstep (se 1 (by rfl) ⟨3516422, by rfl⟩ : syracuseStep 4688563 = 7032845) B7032845
theorem B5638835 : Blo 1234435 5638835 := bstep (se 1 (by rfl) ⟨4229126, by rfl⟩ : syracuseStep 5638835 = 8458253) B8458253
theorem B1854155 : Blo 1234435 1854155 := bstep (se 1 (by rfl) ⟨1390616, by rfl⟩ : syracuseStep 1854155 = 2781233) B2781233
theorem B1854167 : Blo 1234435 1854167 := bstep (se 1 (by rfl) ⟨1390625, by rfl⟩ : syracuseStep 1854167 = 2781251) B2781251
theorem B2779865 : Blo 1234435 2779865 := bstep (se 2 (by rfl) ⟨1042449, by rfl⟩ : syracuseStep 2779865 = 2084899) B2084899
theorem B3959513 : Blo 1234435 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B7031569 : Blo 1234435 7031569 := bstep (se 2 (by rfl) ⟨2636838, by rfl⟩ : syracuseStep 7031569 = 5273677) B5273677
theorem B1854233 : Blo 1234435 1854233 := bstep (se 2 (by rfl) ⟨695337, by rfl⟩ : syracuseStep 1854233 = 1390675) B1390675
theorem B2779955 : Blo 1234435 2779955 := bstep (se 1 (by rfl) ⟨2084966, by rfl⟩ : syracuseStep 2779955 = 4169933) B4169933
theorem B2779991 : Blo 1234435 2779991 := bstep (se 1 (by rfl) ⟨2084993, by rfl⟩ : syracuseStep 2779991 = 4169987) B4169987
theorem B4172633 : Blo 1234435 4172633 := bstep (se 2 (by rfl) ⟨1564737, by rfl⟩ : syracuseStep 4172633 = 3129475) B3129475
theorem B7129957 : Blo 1234435 7129957 := bstep (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) B1336867
theorem B1854347 : Blo 1234435 1854347 := bstep (se 1 (by rfl) ⟨1390760, by rfl⟩ : syracuseStep 1854347 = 2781521) B2781521
theorem B1854359 : Blo 1234435 1854359 := bstep (se 1 (by rfl) ⟨1390769, by rfl⟩ : syracuseStep 1854359 = 2781539) B2781539
theorem B2083799 : Blo 1234435 2083799 := bstep (se 1 (by rfl) ⟨1562849, by rfl⟩ : syracuseStep 2083799 = 3125699) B3125699
theorem B5639129 : Blo 1234435 5639129 := bstep (se 2 (by rfl) ⟨2114673, by rfl⟩ : syracuseStep 5639129 = 4229347) B4229347
theorem B1854425 : Blo 1234435 1854425 := bstep (se 2 (by rfl) ⟨695409, by rfl⟩ : syracuseStep 1854425 = 1390819) B1390819
theorem B2780171 : Blo 1234435 2780171 := bstep (se 1 (by rfl) ⟨2085128, by rfl⟩ : syracuseStep 2780171 = 4170257) B4170257
theorem B1977367 : Blo 1234435 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B2780225 : Blo 1234435 2780225 := bstep (se 2 (by rfl) ⟨1042584, by rfl⟩ : syracuseStep 2780225 = 2085169) B2085169
theorem B2346059 : Blo 1234435 2346059 := bstep (se 1 (by rfl) ⟨1759544, by rfl⟩ : syracuseStep 2346059 = 3519089) B3519089
theorem B1854539 : Blo 1234435 1854539 := bstep (se 1 (by rfl) ⟨1390904, by rfl⟩ : syracuseStep 1854539 = 2781809) B2781809
theorem B2083927 : Blo 1234435 2083927 := bstep (se 1 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 2083927 = 3125891) B3125891
theorem B1854551 : Blo 1234435 1854551 := bstep (se 1 (by rfl) ⟨1390913, by rfl⟩ : syracuseStep 1854551 = 2781827) B2781827
theorem B5278871 : Blo 1234435 5278871 := bstep (se 1 (by rfl) ⟨3959153, by rfl⟩ : syracuseStep 5278871 = 7918307) B7918307
theorem B1854617 : Blo 1234435 1854617 := bstep (se 2 (by rfl) ⟨695481, by rfl⟩ : syracuseStep 1854617 = 1390963) B1390963
theorem B4885697 : Blo 1234435 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B2346241 : Blo 1234435 2346241 := bstep (se 2 (by rfl) ⟨879840, by rfl⟩ : syracuseStep 2346241 = 1759681) B1759681
theorem B2780441 : Blo 1234435 2780441 := bstep (se 2 (by rfl) ⟨1042665, by rfl⟩ : syracuseStep 2780441 = 2085331) B2085331
theorem B17804609 : Blo 1234435 17804609 := bstep (se 2 (by rfl) ⟨6676728, by rfl⟩ : syracuseStep 17804609 = 13353457) B13353457
theorem B2780531 : Blo 1234435 2780531 := bstep (se 1 (by rfl) ⟨2085398, by rfl⟩ : syracuseStep 2780531 = 4170797) B4170797
theorem B2780567 : Blo 1234435 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B2379223 : Blo 1234435 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B2674201 : Blo 1234435 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B8449601 : Blo 1234435 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B2780747 : Blo 1234435 2780747 := bstep (se 1 (by rfl) ⟨2085560, by rfl⟩ : syracuseStep 2780747 = 4171121) B4171121
theorem B2346583 : Blo 1234435 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B2780801 : Blo 1234435 2780801 := bstep (se 2 (by rfl) ⟨1042800, by rfl⟩ : syracuseStep 2780801 = 2085601) B2085601
theorem B6016643 : Blo 1234435 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B77147845 : Blo 1234435 77147845 := bstep (se 4 (by rfl) ⟨7232610, by rfl⟩ : syracuseStep 77147845 = 14465221) B14465221
theorem B156446405 : Blo 1234435 156446405 := bstep (se 4 (by rfl) ⟨14666850, by rfl⟩ : syracuseStep 156446405 = 29333701) B29333701
theorem B3124939 : Blo 1234435 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B2084555 : Blo 1234435 2084555 := bstep (se 1 (by rfl) ⟨1563416, by rfl⟩ : syracuseStep 2084555 = 3126833) B3126833
theorem B5279539 : Blo 1234435 5279539 := bstep (se 1 (by rfl) ⟨3959654, by rfl⟩ : syracuseStep 5279539 = 7919309) B7919309
theorem B2346803 : Blo 1234435 2346803 := bstep (se 1 (by rfl) ⟨1760102, by rfl⟩ : syracuseStep 2346803 = 3520205) B3520205
theorem B1978187 : Blo 1234435 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B2084683 : Blo 1234435 2084683 := bstep (se 1 (by rfl) ⟨1563512, by rfl⟩ : syracuseStep 2084683 = 3127025) B3127025
theorem B7040843 : Blo 1234435 7040843 := bstep (se 1 (by rfl) ⟨5280632, by rfl⟩ : syracuseStep 7040843 = 10561265) B10561265
theorem B3125081 : Blo 1234435 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B2781017 : Blo 1234435 2781017 := bstep (se 2 (by rfl) ⟨1042881, by rfl⟩ : syracuseStep 2781017 = 2085763) B2085763
theorem B19009397 : Blo 1234435 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B4689809 : Blo 1234435 4689809 := bstep (se 2 (by rfl) ⟨1758678, by rfl⟩ : syracuseStep 4689809 = 3517357) B3517357
theorem B2781107 : Blo 1234435 2781107 := bstep (se 1 (by rfl) ⟨2085830, by rfl⟩ : syracuseStep 2781107 = 4171661) B4171661
theorem B2781143 : Blo 1234435 2781143 := bstep (se 1 (by rfl) ⟨2085857, by rfl⟩ : syracuseStep 2781143 = 4171715) B4171715
theorem B2084825 : Blo 1234435 2084825 := bstep (se 2 (by rfl) ⟨781809, by rfl⟩ : syracuseStep 2084825 = 1563619) B1563619
theorem B2347031 : Blo 1234435 2347031 := bstep (se 1 (by rfl) ⟨1760273, by rfl⟩ : syracuseStep 2347031 = 3520547) B3520547
theorem B6254657 : Blo 1234435 6254657 := bstep (se 2 (by rfl) ⟨2345496, by rfl⟩ : syracuseStep 6254657 = 4690993) B4690993
theorem B4755521 : Blo 1234435 4755521 := bstep (se 2 (by rfl) ⟨1783320, by rfl⟩ : syracuseStep 4755521 = 3566641) B3566641
theorem B2084953 : Blo 1234435 2084953 := bstep (se 2 (by rfl) ⟨781857, by rfl⟩ : syracuseStep 2084953 = 1563715) B1563715
theorem B2781323 : Blo 1234435 2781323 := bstep (se 1 (by rfl) ⟨2085992, by rfl⟩ : syracuseStep 2781323 = 4171985) B4171985
theorem B2781377 : Blo 1234435 2781377 := bstep (se 2 (by rfl) ⟨1043016, by rfl⟩ : syracuseStep 2781377 = 2086033) B2086033
theorem B2347289 : Blo 1234435 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B21401921 : Blo 1234435 21401921 := bstep (se 2 (by rfl) ⟨8025720, by rfl⟩ : syracuseStep 21401921 = 16051441) B16051441
theorem B1388875 : Blo 1234435 1388875 := bstep (se 1 (by rfl) ⟨1041656, by rfl⟩ : syracuseStep 1388875 = 2083313) B2083313
theorem B2781593 : Blo 1234435 2781593 := bstep (se 2 (by rfl) ⟨1043097, by rfl⟩ : syracuseStep 2781593 = 2086195) B2086195
theorem B1388983 : Blo 1234435 1388983 := bstep (se 1 (by rfl) ⟨1041737, by rfl⟩ : syracuseStep 1388983 = 2083475) B2083475
theorem B2970049 : Blo 1234435 2970049 := bstep (se 2 (by rfl) ⟨1113768, by rfl⟩ : syracuseStep 2970049 = 2227537) B2227537
theorem B2781683 : Blo 1234435 2781683 := bstep (se 1 (by rfl) ⟨2086262, by rfl⟩ : syracuseStep 2781683 = 4172525) B4172525
theorem B2781719 : Blo 1234435 2781719 := bstep (se 1 (by rfl) ⟨2086289, by rfl⟩ : syracuseStep 2781719 = 4172579) B4172579
theorem B4690507 : Blo 1234435 4690507 := bstep (se 1 (by rfl) ⟨3517880, by rfl⟩ : syracuseStep 4690507 = 7035761) B7035761
theorem B3519065 : Blo 1234435 3519065 := bstep (se 2 (by rfl) ⟨1319649, by rfl⟩ : syracuseStep 3519065 = 2639299) B2639299
theorem B1389163 : Blo 1234435 1389163 := bstep (se 1 (by rfl) ⟨1041872, by rfl⟩ : syracuseStep 1389163 = 2083745) B2083745
theorem B3125911 : Blo 1234435 3125911 := bstep (se 1 (by rfl) ⟨2344433, by rfl⟩ : syracuseStep 3125911 = 4688867) B4688867
theorem B2085527 : Blo 1234435 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B2781899 : Blo 1234435 2781899 := bstep (se 1 (by rfl) ⟨2086424, by rfl⟩ : syracuseStep 2781899 = 4172849) B4172849
theorem B1389271 : Blo 1234435 1389271 := bstep (se 1 (by rfl) ⟨1041953, by rfl⟩ : syracuseStep 1389271 = 2083907) B2083907
theorem B2781953 : Blo 1234435 2781953 := bstep (se 2 (by rfl) ⟨1043232, by rfl⟩ : syracuseStep 2781953 = 2086465) B2086465
theorem B6017809 : Blo 1234435 6017809 := bstep (se 2 (by rfl) ⟨2256678, by rfl⟩ : syracuseStep 6017809 = 4513357) B4513357
theorem B4166423 : Blo 1234435 4166423 := bstep (se 1 (by rfl) ⟨3124817, by rfl⟩ : syracuseStep 4166423 = 6249635) B6249635
theorem B2085655 : Blo 1234435 2085655 := bstep (se 1 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 2085655 = 3128483) B3128483
theorem B5010221 : Blo 1234435 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B6681419 : Blo 1234435 6681419 := bstep (se 1 (by rfl) ⟨5011064, by rfl⟩ : syracuseStep 6681419 = 10022129) B10022129
theorem B4690781 : Blo 1234435 4690781 := bstep (se 3 (by rfl) ⟨879521, by rfl⟩ : syracuseStep 4690781 = 1759043) B1759043
theorem B6017885 : Blo 1234435 6017885 := bstep (se 3 (by rfl) ⟨1128353, by rfl⟩ : syracuseStep 6017885 = 2256707) B2256707
theorem B1389451 : Blo 1234435 1389451 := bstep (se 1 (by rfl) ⟨1042088, by rfl⟩ : syracuseStep 1389451 = 2084177) B2084177
theorem B1389559 : Blo 1234435 1389559 := bstep (se 1 (by rfl) ⟨1042169, by rfl⟩ : syracuseStep 1389559 = 2084339) B2084339
theorem B5280785 : Blo 1234435 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B3126347 : Blo 1234435 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B1389739 : Blo 1234435 1389739 := bstep (se 1 (by rfl) ⟨1042304, by rfl⟩ : syracuseStep 1389739 = 2084609) B2084609
theorem B1389847 : Blo 1234435 1389847 := bstep (se 1 (by rfl) ⟨1042385, by rfl⟩ : syracuseStep 1389847 = 2084771) B2084771
theorem B4166963 : Blo 1234435 4166963 := bstep (se 1 (by rfl) ⟨3125222, by rfl⟩ : syracuseStep 4166963 = 6250445) B6250445
theorem B2225497 : Blo 1234435 2225497 := bstep (se 2 (by rfl) ⟨834561, by rfl⟩ : syracuseStep 2225497 = 1669123) B1669123
theorem B14071157 : Blo 1234435 14071157 := bstep (se 5 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 14071157 = 1319171) B1319171
theorem B2086283 : Blo 1234435 2086283 := bstep (se 1 (by rfl) ⟨1564712, by rfl⟩ : syracuseStep 2086283 = 3129425) B3129425
theorem B3126721 : Blo 1234435 3126721 := bstep (se 2 (by rfl) ⟨1172520, by rfl⟩ : syracuseStep 3126721 = 2345041) B2345041
theorem B1758667 : Blo 1234435 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1390027 : Blo 1234435 1390027 := bstep (se 1 (by rfl) ⟨1042520, by rfl⟩ : syracuseStep 1390027 = 2085041) B2085041
theorem B1234443 : Blo 1234435 1234443 := bstep (se 1 (by rfl) ⟨925832, by rfl⟩ : syracuseStep 1234443 = 1851665) B1851665
theorem B2086411 : Blo 1234435 2086411 := bstep (se 1 (by rfl) ⟨1564808, by rfl⟩ : syracuseStep 2086411 = 3129617) B3129617
theorem B1234455 : Blo 1234435 1234455 := bstep (se 1 (by rfl) ⟨925841, by rfl⟩ : syracuseStep 1234455 = 1851683) B1851683
theorem B4691479 : Blo 1234435 4691479 := bstep (se 1 (by rfl) ⟨3518609, by rfl⟩ : syracuseStep 4691479 = 7037219) B7037219
theorem B1234475 : Blo 1234435 1234475 := bstep (se 1 (by rfl) ⟨925856, by rfl⟩ : syracuseStep 1234475 = 1851713) B1851713
theorem B1234487 : Blo 1234435 1234487 := bstep (se 1 (by rfl) ⟨925865, by rfl⟩ : syracuseStep 1234487 = 1851731) B1851731
theorem B1390135 : Blo 1234435 1390135 := bstep (se 1 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 1390135 = 2085203) B2085203
theorem B4167233 : Blo 1234435 4167233 := bstep (se 2 (by rfl) ⟨1562712, by rfl⟩ : syracuseStep 4167233 = 3125425) B3125425
theorem B1234507 : Blo 1234435 1234507 := bstep (se 1 (by rfl) ⟨925880, by rfl⟩ : syracuseStep 1234507 = 1851761) B1851761
theorem B3757643 : Blo 1234435 3757643 := bstep (se 1 (by rfl) ⟨2818232, by rfl⟩ : syracuseStep 3757643 = 5636465) B5636465
theorem B1234519 : Blo 1234435 1234519 := bstep (se 1 (by rfl) ⟨925889, by rfl⟩ : syracuseStep 1234519 = 1851779) B1851779
theorem B1234539 : Blo 1234435 1234539 := bstep (se 1 (by rfl) ⟨925904, by rfl⟩ : syracuseStep 1234539 = 1851809) B1851809
theorem B1234551 : Blo 1234435 1234551 := bstep (se 1 (by rfl) ⟨925913, by rfl⟩ : syracuseStep 1234551 = 1851827) B1851827
theorem B1234571 : Blo 1234435 1234571 := bstep (se 1 (by rfl) ⟨925928, by rfl⟩ : syracuseStep 1234571 = 1851857) B1851857
theorem B1234583 : Blo 1234435 1234583 := bstep (se 1 (by rfl) ⟨925937, by rfl⟩ : syracuseStep 1234583 = 1851875) B1851875
theorem B1234603 : Blo 1234435 1234603 := bstep (se 1 (by rfl) ⟨925952, by rfl⟩ : syracuseStep 1234603 = 1851905) B1851905
theorem B1234615 : Blo 1234435 1234615 := bstep (se 1 (by rfl) ⟨925961, by rfl⟩ : syracuseStep 1234615 = 1851923) B1851923
theorem B1234635 : Blo 1234435 1234635 := bstep (se 1 (by rfl) ⟨925976, by rfl⟩ : syracuseStep 1234635 = 1851953) B1851953
theorem B1234647 : Blo 1234435 1234647 := bstep (se 1 (by rfl) ⟨925985, by rfl⟩ : syracuseStep 1234647 = 1851971) B1851971
theorem B1758935 : Blo 1234435 1758935 := bstep (se 1 (by rfl) ⟨1319201, by rfl⟩ : syracuseStep 1758935 = 2638403) B2638403
theorem B1234667 : Blo 1234435 1234667 := bstep (se 1 (by rfl) ⟨926000, by rfl⟩ : syracuseStep 1234667 = 1852001) B1852001
theorem B1390315 : Blo 1234435 1390315 := bstep (se 1 (by rfl) ⟨1042736, by rfl⟩ : syracuseStep 1390315 = 2085473) B2085473
theorem B1234679 : Blo 1234435 1234679 := bstep (se 1 (by rfl) ⟨926009, by rfl⟩ : syracuseStep 1234679 = 1852019) B1852019
theorem B1234699 : Blo 1234435 1234699 := bstep (se 1 (by rfl) ⟨926024, by rfl⟩ : syracuseStep 1234699 = 1852049) B1852049
theorem B1234711 : Blo 1234435 1234711 := bstep (se 1 (by rfl) ⟨926033, by rfl⟩ : syracuseStep 1234711 = 1852067) B1852067
theorem B2750233 : Blo 1234435 2750233 := bstep (se 2 (by rfl) ⟨1031337, by rfl⟩ : syracuseStep 2750233 = 2062675) B2062675
theorem B1234731 : Blo 1234435 1234731 := bstep (se 1 (by rfl) ⟨926048, by rfl⟩ : syracuseStep 1234731 = 1852097) B1852097
theorem B1234743 : Blo 1234435 1234743 := bstep (se 1 (by rfl) ⟨926057, by rfl⟩ : syracuseStep 1234743 = 1852115) B1852115
theorem B1234763 : Blo 1234435 1234763 := bstep (se 1 (by rfl) ⟨926072, by rfl⟩ : syracuseStep 1234763 = 1852145) B1852145
theorem B3520331 : Blo 1234435 3520331 := bstep (se 1 (by rfl) ⟨2640248, by rfl⟩ : syracuseStep 3520331 = 5280497) B5280497
theorem B1234775 : Blo 1234435 1234775 := bstep (se 1 (by rfl) ⟨926081, by rfl⟩ : syracuseStep 1234775 = 1852163) B1852163
theorem B1390423 : Blo 1234435 1390423 := bstep (se 1 (by rfl) ⟨1042817, by rfl⟩ : syracuseStep 1390423 = 2085635) B2085635
theorem B1234795 : Blo 1234435 1234795 := bstep (se 1 (by rfl) ⟨926096, by rfl⟩ : syracuseStep 1234795 = 1852193) B1852193
theorem B1234807 : Blo 1234435 1234807 := bstep (se 1 (by rfl) ⟨926105, by rfl⟩ : syracuseStep 1234807 = 1852211) B1852211
theorem B1234827 : Blo 1234435 1234827 := bstep (se 1 (by rfl) ⟨926120, by rfl⟩ : syracuseStep 1234827 = 1852241) B1852241
theorem B2226059 : Blo 1234435 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B1234839 : Blo 1234435 1234839 := bstep (se 1 (by rfl) ⟨926129, by rfl⟩ : syracuseStep 1234839 = 1852259) B1852259
theorem B1669015 : Blo 1234435 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B2815897 : Blo 1234435 2815897 := bstep (se 2 (by rfl) ⟨1055961, by rfl⟩ : syracuseStep 2815897 = 2111923) B2111923
theorem B1234859 : Blo 1234435 1234859 := bstep (se 1 (by rfl) ⟨926144, by rfl⟩ : syracuseStep 1234859 = 1852289) B1852289
theorem B1234871 : Blo 1234435 1234871 := bstep (se 1 (by rfl) ⟨926153, by rfl⟩ : syracuseStep 1234871 = 1852307) B1852307
theorem B1234891 : Blo 1234435 1234891 := bstep (se 1 (by rfl) ⟨926168, by rfl⟩ : syracuseStep 1234891 = 1852337) B1852337
theorem B1234903 : Blo 1234435 1234903 := bstep (se 1 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 1234903 = 1852355) B1852355
theorem B6256601 : Blo 1234435 6256601 := bstep (se 2 (by rfl) ⟨2346225, by rfl⟩ : syracuseStep 6256601 = 4692451) B4692451
theorem B1234923 : Blo 1234435 1234923 := bstep (se 1 (by rfl) ⟨926192, by rfl⟩ : syracuseStep 1234923 = 1852385) B1852385
theorem B1234935 : Blo 1234435 1234935 := bstep (se 1 (by rfl) ⟨926201, by rfl⟩ : syracuseStep 1234935 = 1852403) B1852403
theorem B1234955 : Blo 1234435 1234955 := bstep (se 1 (by rfl) ⟨926216, by rfl⟩ : syracuseStep 1234955 = 1852433) B1852433
theorem B1390603 : Blo 1234435 1390603 := bstep (se 1 (by rfl) ⟨1042952, by rfl⟩ : syracuseStep 1390603 = 2085905) B2085905
theorem B1562647 : Blo 1234435 1562647 := bstep (se 1 (by rfl) ⟨1171985, by rfl⟩ : syracuseStep 1562647 = 2343971) B2343971
theorem B1234967 : Blo 1234435 1234967 := bstep (se 1 (by rfl) ⟨926225, by rfl⟩ : syracuseStep 1234967 = 1852451) B1852451
theorem B3127319 : Blo 1234435 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B1234987 : Blo 1234435 1234987 := bstep (se 1 (by rfl) ⟨926240, by rfl⟩ : syracuseStep 1234987 = 1852481) B1852481
theorem B1234999 : Blo 1234435 1234999 := bstep (se 1 (by rfl) ⟨926249, by rfl⟩ : syracuseStep 1234999 = 1852499) B1852499
theorem B1235019 : Blo 1234435 1235019 := bstep (se 1 (by rfl) ⟨926264, by rfl⟩ : syracuseStep 1235019 = 1852529) B1852529
theorem B1235031 : Blo 1234435 1235031 := bstep (se 1 (by rfl) ⟨926273, by rfl⟩ : syracuseStep 1235031 = 1852547) B1852547
theorem B4167773 : Blo 1234435 4167773 := bstep (se 3 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 4167773 = 1562915) B1562915
theorem B1235051 : Blo 1234435 1235051 := bstep (se 1 (by rfl) ⟨926288, by rfl⟩ : syracuseStep 1235051 = 1852577) B1852577
theorem B1235063 : Blo 1234435 1235063 := bstep (se 1 (by rfl) ⟨926297, by rfl⟩ : syracuseStep 1235063 = 1852595) B1852595
theorem B1390711 : Blo 1234435 1390711 := bstep (se 1 (by rfl) ⟨1043033, by rfl⟩ : syracuseStep 1390711 = 2086067) B2086067
theorem B7035011 : Blo 1234435 7035011 := bstep (se 1 (by rfl) ⟨5276258, by rfl⟩ : syracuseStep 7035011 = 10552517) B10552517
theorem B1235083 : Blo 1234435 1235083 := bstep (se 1 (by rfl) ⟨926312, by rfl⟩ : syracuseStep 1235083 = 1852625) B1852625
theorem B1235095 : Blo 1234435 1235095 := bstep (se 1 (by rfl) ⟨926321, by rfl⟩ : syracuseStep 1235095 = 1852643) B1852643
theorem B11876503 : Blo 1234435 11876503 := bstep (se 1 (by rfl) ⟨8907377, by rfl⟩ : syracuseStep 11876503 = 17814755) B17814755
theorem B1235115 : Blo 1234435 1235115 := bstep (se 1 (by rfl) ⟨926336, by rfl⟩ : syracuseStep 1235115 = 1852673) B1852673
theorem B7919795 : Blo 1234435 7919795 := bstep (se 1 (by rfl) ⟨5939846, by rfl⟩ : syracuseStep 7919795 = 11879693) B11879693
theorem B1235127 : Blo 1234435 1235127 := bstep (se 1 (by rfl) ⟨926345, by rfl⟩ : syracuseStep 1235127 = 1852691) B1852691
theorem B1235147 : Blo 1234435 1235147 := bstep (se 1 (by rfl) ⟨926360, by rfl⟩ : syracuseStep 1235147 = 1852721) B1852721
theorem B1235159 : Blo 1234435 1235159 := bstep (se 1 (by rfl) ⟨926369, by rfl⟩ : syracuseStep 1235159 = 1852739) B1852739
theorem B1235179 : Blo 1234435 1235179 := bstep (se 1 (by rfl) ⟨926384, by rfl⟩ : syracuseStep 1235179 = 1852769) B1852769
theorem B1235191 : Blo 1234435 1235191 := bstep (se 1 (by rfl) ⟨926393, by rfl⟩ : syracuseStep 1235191 = 1852787) B1852787
theorem B1235211 : Blo 1234435 1235211 := bstep (se 1 (by rfl) ⟨926408, by rfl⟩ : syracuseStep 1235211 = 1852817) B1852817
theorem B5937425 : Blo 1234435 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B1235223 : Blo 1234435 1235223 := bstep (se 1 (by rfl) ⟨926417, by rfl⟩ : syracuseStep 1235223 = 1852835) B1852835
theorem B1235243 : Blo 1234435 1235243 := bstep (se 1 (by rfl) ⟨926432, by rfl⟩ : syracuseStep 1235243 = 1852865) B1852865
theorem B1390891 : Blo 1234435 1390891 := bstep (se 1 (by rfl) ⟨1043168, by rfl⟩ : syracuseStep 1390891 = 2086337) B2086337
theorem B4692269 : Blo 1234435 4692269 := bstep (se 3 (by rfl) ⟨879800, by rfl⟩ : syracuseStep 4692269 = 1759601) B1759601
theorem B1235255 : Blo 1234435 1235255 := bstep (se 1 (by rfl) ⟨926441, by rfl⟩ : syracuseStep 1235255 = 1852883) B1852883
theorem B1235275 : Blo 1234435 1235275 := bstep (se 1 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 1235275 = 1852913) B1852913
theorem B7919947 : Blo 1234435 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B1235287 : Blo 1234435 1235287 := bstep (se 1 (by rfl) ⟨926465, by rfl⟩ : syracuseStep 1235287 = 1852931) B1852931
theorem B2226521 : Blo 1234435 2226521 := bstep (se 2 (by rfl) ⟨834945, by rfl⟩ : syracuseStep 2226521 = 1669891) B1669891
theorem B1235307 : Blo 1234435 1235307 := bstep (se 1 (by rfl) ⟨926480, by rfl⟩ : syracuseStep 1235307 = 1852961) B1852961
theorem B1235319 : Blo 1234435 1235319 := bstep (se 1 (by rfl) ⟨926489, by rfl⟩ : syracuseStep 1235319 = 1852979) B1852979
theorem B1235339 : Blo 1234435 1235339 := bstep (se 1 (by rfl) ⟨926504, by rfl⟩ : syracuseStep 1235339 = 1853009) B1853009
theorem B1235351 : Blo 1234435 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B1235371 : Blo 1234435 1235371 := bstep (se 1 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 1235371 = 1853057) B1853057
theorem B1235383 : Blo 1234435 1235383 := bstep (se 1 (by rfl) ⟨926537, by rfl⟩ : syracuseStep 1235383 = 1853075) B1853075
theorem B1235403 : Blo 1234435 1235403 := bstep (se 1 (by rfl) ⟨926552, by rfl⟩ : syracuseStep 1235403 = 1853105) B1853105
theorem B1235415 : Blo 1234435 1235415 := bstep (se 1 (by rfl) ⟨926561, by rfl⟩ : syracuseStep 1235415 = 1853123) B1853123
theorem B1235435 : Blo 1234435 1235435 := bstep (se 1 (by rfl) ⟨926576, by rfl⟩ : syracuseStep 1235435 = 1853153) B1853153
theorem B1235447 : Blo 1234435 1235447 := bstep (se 1 (by rfl) ⟨926585, by rfl⟩ : syracuseStep 1235447 = 1853171) B1853171
theorem B1235467 : Blo 1234435 1235467 := bstep (se 1 (by rfl) ⟨926600, by rfl⟩ : syracuseStep 1235467 = 1853201) B1853201
theorem B1235479 : Blo 1234435 1235479 := bstep (se 1 (by rfl) ⟨926609, by rfl⟩ : syracuseStep 1235479 = 1853219) B1853219
theorem B1235499 : Blo 1234435 1235499 := bstep (se 1 (by rfl) ⟨926624, by rfl⟩ : syracuseStep 1235499 = 1853249) B1853249
theorem B1235511 : Blo 1234435 1235511 := bstep (se 1 (by rfl) ⟨926633, by rfl⟩ : syracuseStep 1235511 = 1853267) B1853267
theorem B1235531 : Blo 1234435 1235531 := bstep (se 1 (by rfl) ⟨926648, by rfl⟩ : syracuseStep 1235531 = 1853297) B1853297
theorem B1235543 : Blo 1234435 1235543 := bstep (se 1 (by rfl) ⟨926657, by rfl⟩ : syracuseStep 1235543 = 1853315) B1853315
theorem B7223909 : Blo 1234435 7223909 := bstep (se 4 (by rfl) ⟨677241, by rfl⟩ : syracuseStep 7223909 = 1354483) B1354483
theorem B1235563 : Blo 1234435 1235563 := bstep (se 1 (by rfl) ⟨926672, by rfl⟩ : syracuseStep 1235563 = 1853345) B1853345
theorem B1235575 : Blo 1234435 1235575 := bstep (se 1 (by rfl) ⟨926681, by rfl⟩ : syracuseStep 1235575 = 1853363) B1853363
theorem B1235595 : Blo 1234435 1235595 := bstep (se 1 (by rfl) ⟨926696, by rfl⟩ : syracuseStep 1235595 = 1853393) B1853393
theorem B1235607 : Blo 1234435 1235607 := bstep (se 1 (by rfl) ⟨926705, by rfl⟩ : syracuseStep 1235607 = 1853411) B1853411
theorem B1759897 : Blo 1234435 1759897 := bstep (se 2 (by rfl) ⟨659961, by rfl⟩ : syracuseStep 1759897 = 1319923) B1319923
theorem B1235627 : Blo 1234435 1235627 := bstep (se 1 (by rfl) ⟨926720, by rfl⟩ : syracuseStep 1235627 = 1853441) B1853441
theorem B1235639 : Blo 1234435 1235639 := bstep (se 1 (by rfl) ⟨926729, by rfl⟩ : syracuseStep 1235639 = 1853459) B1853459
theorem B1235659 : Blo 1234435 1235659 := bstep (se 1 (by rfl) ⟨926744, by rfl⟩ : syracuseStep 1235659 = 1853489) B1853489
theorem B1235671 : Blo 1234435 1235671 := bstep (se 1 (by rfl) ⟨926753, by rfl⟩ : syracuseStep 1235671 = 1853507) B1853507
theorem B1235691 : Blo 1234435 1235691 := bstep (se 1 (by rfl) ⟨926768, by rfl⟩ : syracuseStep 1235691 = 1853537) B1853537
theorem B1235703 : Blo 1234435 1235703 := bstep (se 1 (by rfl) ⟨926777, by rfl⟩ : syracuseStep 1235703 = 1853555) B1853555
theorem B1235723 : Blo 1234435 1235723 := bstep (se 1 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 1235723 = 1853585) B1853585
theorem B1235735 : Blo 1234435 1235735 := bstep (se 1 (by rfl) ⟨926801, by rfl⟩ : syracuseStep 1235735 = 1853603) B1853603
theorem B8903459 : Blo 1234435 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B1235755 : Blo 1234435 1235755 := bstep (se 1 (by rfl) ⟨926816, by rfl⟩ : syracuseStep 1235755 = 1853633) B1853633
theorem B1235767 : Blo 1234435 1235767 := bstep (se 1 (by rfl) ⟨926825, by rfl⟩ : syracuseStep 1235767 = 1853651) B1853651
theorem B3128129 : Blo 1234435 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B1235787 : Blo 1234435 1235787 := bstep (se 1 (by rfl) ⟨926840, by rfl⟩ : syracuseStep 1235787 = 1853681) B1853681
theorem B1235799 : Blo 1234435 1235799 := bstep (se 1 (by rfl) ⟨926849, by rfl⟩ : syracuseStep 1235799 = 1853699) B1853699
theorem B1235819 : Blo 1234435 1235819 := bstep (se 1 (by rfl) ⟨926864, by rfl⟩ : syracuseStep 1235819 = 1853729) B1853729
theorem B1235831 : Blo 1234435 1235831 := bstep (se 1 (by rfl) ⟨926873, by rfl⟩ : syracuseStep 1235831 = 1853747) B1853747
theorem B1235851 : Blo 1234435 1235851 := bstep (se 1 (by rfl) ⟨926888, by rfl⟩ : syracuseStep 1235851 = 1853777) B1853777
theorem B1252247 : Blo 1234435 1252247 := bstep (se 1 (by rfl) ⟨939185, by rfl⟩ : syracuseStep 1252247 = 1878371) B1878371
theorem B1235863 : Blo 1234435 1235863 := bstep (se 1 (by rfl) ⟨926897, by rfl⟩ : syracuseStep 1235863 = 1853795) B1853795
theorem B1235883 : Blo 1234435 1235883 := bstep (se 1 (by rfl) ⟨926912, by rfl⟩ : syracuseStep 1235883 = 1853825) B1853825
theorem B1235895 : Blo 1234435 1235895 := bstep (se 1 (by rfl) ⟨926921, by rfl⟩ : syracuseStep 1235895 = 1853843) B1853843
theorem B1235915 : Blo 1234435 1235915 := bstep (se 1 (by rfl) ⟨926936, by rfl⟩ : syracuseStep 1235915 = 1853873) B1853873
theorem B11262925 : Blo 1234435 11262925 := bstep (se 3 (by rfl) ⟨2111798, by rfl⟩ : syracuseStep 11262925 = 4223597) B4223597
theorem B1235927 : Blo 1234435 1235927 := bstep (se 1 (by rfl) ⟨926945, by rfl⟩ : syracuseStep 1235927 = 1853891) B1853891
theorem B1235947 : Blo 1234435 1235947 := bstep (se 1 (by rfl) ⟨926960, by rfl⟩ : syracuseStep 1235947 = 1853921) B1853921
theorem B2817011 : Blo 1234435 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B1235959 : Blo 1234435 1235959 := bstep (se 1 (by rfl) ⟨926969, by rfl⟩ : syracuseStep 1235959 = 1853939) B1853939
theorem B1235979 : Blo 1234435 1235979 := bstep (se 1 (by rfl) ⟨926984, by rfl⟩ : syracuseStep 1235979 = 1853969) B1853969
theorem B1235991 : Blo 1234435 1235991 := bstep (se 1 (by rfl) ⟨926993, by rfl⟩ : syracuseStep 1235991 = 1853987) B1853987
theorem B1236011 : Blo 1234435 1236011 := bstep (se 1 (by rfl) ⟨927008, by rfl⟩ : syracuseStep 1236011 = 1854017) B1854017
theorem B1236023 : Blo 1234435 1236023 := bstep (se 1 (by rfl) ⟨927017, by rfl⟩ : syracuseStep 1236023 = 1854035) B1854035
theorem B1236043 : Blo 1234435 1236043 := bstep (se 1 (by rfl) ⟨927032, by rfl⟩ : syracuseStep 1236043 = 1854065) B1854065
theorem B1236055 : Blo 1234435 1236055 := bstep (se 1 (by rfl) ⟨927041, by rfl⟩ : syracuseStep 1236055 = 1854083) B1854083
theorem B1236075 : Blo 1234435 1236075 := bstep (se 1 (by rfl) ⟨927056, by rfl⟩ : syracuseStep 1236075 = 1854113) B1854113
theorem B1236087 : Blo 1234435 1236087 := bstep (se 1 (by rfl) ⟨927065, by rfl⟩ : syracuseStep 1236087 = 1854131) B1854131
theorem B1236107 : Blo 1234435 1236107 := bstep (se 1 (by rfl) ⟨927080, by rfl⟩ : syracuseStep 1236107 = 1854161) B1854161
theorem B1236119 : Blo 1234435 1236119 := bstep (se 1 (by rfl) ⟨927089, by rfl⟩ : syracuseStep 1236119 = 1854179) B1854179
theorem B1236139 : Blo 1234435 1236139 := bstep (se 1 (by rfl) ⟨927104, by rfl⟩ : syracuseStep 1236139 = 1854209) B1854209
theorem B1236151 : Blo 1234435 1236151 := bstep (se 1 (by rfl) ⟨927113, by rfl⟩ : syracuseStep 1236151 = 1854227) B1854227
theorem B4168907 : Blo 1234435 4168907 := bstep (se 1 (by rfl) ⟨3126680, by rfl⟩ : syracuseStep 4168907 = 6253361) B6253361
theorem B1236171 : Blo 1234435 1236171 := bstep (se 1 (by rfl) ⟨927128, by rfl⟩ : syracuseStep 1236171 = 1854257) B1854257
theorem B1236183 : Blo 1234435 1236183 := bstep (se 1 (by rfl) ⟨927137, by rfl⟩ : syracuseStep 1236183 = 1854275) B1854275
theorem B1236203 : Blo 1234435 1236203 := bstep (se 1 (by rfl) ⟨927152, by rfl⟩ : syracuseStep 1236203 = 1854305) B1854305
theorem B1236215 : Blo 1234435 1236215 := bstep (se 1 (by rfl) ⟨927161, by rfl⟩ : syracuseStep 1236215 = 1854323) B1854323
theorem B2227457 : Blo 1234435 2227457 := bstep (se 2 (by rfl) ⟨835296, by rfl⟩ : syracuseStep 2227457 = 1670593) B1670593
theorem B1236235 : Blo 1234435 1236235 := bstep (se 1 (by rfl) ⟨927176, by rfl⟩ : syracuseStep 1236235 = 1854353) B1854353
theorem B1236247 : Blo 1234435 1236247 := bstep (se 1 (by rfl) ⟨927185, by rfl⟩ : syracuseStep 1236247 = 1854371) B1854371
theorem B1236267 : Blo 1234435 1236267 := bstep (se 1 (by rfl) ⟨927200, by rfl⟩ : syracuseStep 1236267 = 1854401) B1854401
theorem B1236279 : Blo 1234435 1236279 := bstep (se 1 (by rfl) ⟨927209, by rfl⟩ : syracuseStep 1236279 = 1854419) B1854419
theorem B1236299 : Blo 1234435 1236299 := bstep (se 1 (by rfl) ⟨927224, by rfl⟩ : syracuseStep 1236299 = 1854449) B1854449
theorem B2227543 : Blo 1234435 2227543 := bstep (se 1 (by rfl) ⟨1670657, by rfl⟩ : syracuseStep 2227543 = 3341315) B3341315
theorem B1236311 : Blo 1234435 1236311 := bstep (se 1 (by rfl) ⟨927233, by rfl⟩ : syracuseStep 1236311 = 1854467) B1854467
theorem B3128665 : Blo 1234435 3128665 := bstep (se 2 (by rfl) ⟨1173249, by rfl⟩ : syracuseStep 3128665 = 2346499) B2346499
theorem B1236331 : Blo 1234435 1236331 := bstep (se 1 (by rfl) ⟨927248, by rfl⟩ : syracuseStep 1236331 = 1854497) B1854497
theorem B1236343 : Blo 1234435 1236343 := bstep (se 1 (by rfl) ⟨927257, by rfl⟩ : syracuseStep 1236343 = 1854515) B1854515
theorem B1236363 : Blo 1234435 1236363 := bstep (se 1 (by rfl) ⟨927272, by rfl⟩ : syracuseStep 1236363 = 1854545) B1854545
theorem B1236375 : Blo 1234435 1236375 := bstep (se 1 (by rfl) ⟨927281, by rfl⟩ : syracuseStep 1236375 = 1854563) B1854563
theorem B1236395 : Blo 1234435 1236395 := bstep (se 1 (by rfl) ⟨927296, by rfl⟩ : syracuseStep 1236395 = 1854593) B1854593
theorem B1236407 : Blo 1234435 1236407 := bstep (se 1 (by rfl) ⟨927305, by rfl⟩ : syracuseStep 1236407 = 1854611) B1854611
theorem B1236427 : Blo 1234435 1236427 := bstep (se 1 (by rfl) ⟨927320, by rfl⟩ : syracuseStep 1236427 = 1854641) B1854641
theorem B4169177 : Blo 1234435 4169177 := bstep (se 2 (by rfl) ⟨1563441, by rfl⟩ : syracuseStep 4169177 = 3126883) B3126883
theorem B2637335 : Blo 1234435 2637335 := bstep (se 1 (by rfl) ⟨1978001, by rfl⟩ : syracuseStep 2637335 = 3956003) B3956003
theorem B5275181 : Blo 1234435 5275181 := bstep (se 3 (by rfl) ⟨989096, by rfl⟩ : syracuseStep 5275181 = 1978193) B1978193
theorem B6258221 : Blo 1234435 6258221 := bstep (se 3 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 6258221 = 2346833) B2346833
theorem B4693697 : Blo 1234435 4693697 := bstep (se 2 (by rfl) ⟨1760136, by rfl⟩ : syracuseStep 4693697 = 3520273) B3520273
theorem B2637515 : Blo 1234435 2637515 := bstep (se 1 (by rfl) ⟨1978136, by rfl⟩ : syracuseStep 2637515 = 3956273) B3956273
theorem B1564363 : Blo 1234435 1564363 := bstep (se 1 (by rfl) ⟨1173272, by rfl⟩ : syracuseStep 1564363 = 2346545) B2346545
theorem B10149725 : Blo 1234435 10149725 := bstep (se 3 (by rfl) ⟨1903073, by rfl⟩ : syracuseStep 10149725 = 3806147) B3806147
theorem B5275523 : Blo 1234435 5275523 := bstep (se 1 (by rfl) ⟨3956642, by rfl⟩ : syracuseStep 5275523 = 7913285) B7913285
theorem B1564687 : Blo 1234435 1564687 := bstep (se 1 (by rfl) ⟨1173515, by rfl⟩ : syracuseStep 1564687 = 2347031) B2347031
theorem B4169771 : Blo 1234435 4169771 := bstep (se 1 (by rfl) ⟨3127328, by rfl⟩ : syracuseStep 4169771 = 6254657) B6254657
theorem B3170347 : Blo 1234435 3170347 := bstep (se 1 (by rfl) ⟨2377760, by rfl⟩ : syracuseStep 3170347 = 4755521) B4755521
theorem B7913645 : Blo 1234435 7913645 := bstep (se 3 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 7913645 = 2967617) B2967617
theorem B1564859 : Blo 1234435 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B15835337 : Blo 1234435 15835337 := bstep (se 2 (by rfl) ⟨5938251, by rfl⟩ : syracuseStep 15835337 = 11876503) B11876503
theorem B1851707 : Blo 1234435 1851707 := bstep (se 1 (by rfl) ⟨1388780, by rfl⟩ : syracuseStep 1851707 = 2777561) B2777561
theorem B1851767 : Blo 1234435 1851767 := bstep (se 1 (by rfl) ⟨1388825, by rfl⟩ : syracuseStep 1851767 = 2777651) B2777651
theorem B1851791 : Blo 1234435 1851791 := bstep (se 1 (by rfl) ⟨1388843, by rfl⟩ : syracuseStep 1851791 = 2777687) B2777687
theorem B1851833 : Blo 1234435 1851833 := bstep (se 2 (by rfl) ⟨694437, by rfl⟩ : syracuseStep 1851833 = 1388875) B1388875
theorem B10559929 : Blo 1234435 10559929 := bstep (se 2 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 10559929 = 7919947) B7919947
theorem B9388547 : Blo 1234435 9388547 := bstep (se 1 (by rfl) ⟨7041410, by rfl⟩ : syracuseStep 9388547 = 14082821) B14082821
theorem B1851911 : Blo 1234435 1851911 := bstep (se 1 (by rfl) ⟨1388933, by rfl⟩ : syracuseStep 1851911 = 2777867) B2777867
theorem B2777615 : Blo 1234435 2777615 := bstep (se 1 (by rfl) ⟨2083211, by rfl⟩ : syracuseStep 2777615 = 4166423) B4166423
theorem B2777633 : Blo 1234435 2777633 := bstep (se 2 (by rfl) ⟨1041612, by rfl⟩ : syracuseStep 2777633 = 2083225) B2083225
theorem B1851947 : Blo 1234435 1851947 := bstep (se 1 (by rfl) ⟨1388960, by rfl⟩ : syracuseStep 1851947 = 2777921) B2777921
theorem B1851977 : Blo 1234435 1851977 := bstep (se 2 (by rfl) ⟨694491, by rfl⟩ : syracuseStep 1851977 = 1388983) B1388983
theorem B5939885 : Blo 1234435 5939885 := bstep (se 3 (by rfl) ⟨1113728, by rfl⟩ : syracuseStep 5939885 = 2227457) B2227457
theorem B76030645 : Blo 1234435 76030645 := bstep (se 5 (by rfl) ⟨3563936, by rfl⟩ : syracuseStep 76030645 = 7127873) B7127873
theorem B1852091 : Blo 1234435 1852091 := bstep (se 1 (by rfl) ⟨1389068, by rfl⟩ : syracuseStep 1852091 = 2778137) B2778137
theorem B1852151 : Blo 1234435 1852151 := bstep (se 1 (by rfl) ⟨1389113, by rfl⟩ : syracuseStep 1852151 = 2778227) B2778227
theorem B1852175 : Blo 1234435 1852175 := bstep (se 1 (by rfl) ⟨1389131, by rfl⟩ : syracuseStep 1852175 = 2778263) B2778263
theorem B1852217 : Blo 1234435 1852217 := bstep (se 2 (by rfl) ⟨694581, by rfl⟩ : syracuseStep 1852217 = 1389163) B1389163
theorem B2777975 : Blo 1234435 2777975 := bstep (se 1 (by rfl) ⟨2083481, by rfl⟩ : syracuseStep 2777975 = 4166963) B4166963
theorem B1852295 : Blo 1234435 1852295 := bstep (se 1 (by rfl) ⟨1389221, by rfl⟩ : syracuseStep 1852295 = 2778443) B2778443
theorem B6251417 : Blo 1234435 6251417 := bstep (se 2 (by rfl) ⟨2344281, by rfl⟩ : syracuseStep 6251417 = 4688563) B4688563
theorem B9380771 : Blo 1234435 9380771 := bstep (se 1 (by rfl) ⟨7035578, by rfl⟩ : syracuseStep 9380771 = 14071157) B14071157
theorem B1852331 : Blo 1234435 1852331 := bstep (se 1 (by rfl) ⟨1389248, by rfl⟩ : syracuseStep 1852331 = 2778497) B2778497
theorem B1852361 : Blo 1234435 1852361 := bstep (se 2 (by rfl) ⟨694635, by rfl⟩ : syracuseStep 1852361 = 1389271) B1389271
theorem B2778155 : Blo 1234435 2778155 := bstep (se 1 (by rfl) ⟨2083616, by rfl⟩ : syracuseStep 2778155 = 4167233) B4167233
theorem B1852475 : Blo 1234435 1852475 := bstep (se 1 (by rfl) ⟨1389356, by rfl⟩ : syracuseStep 1852475 = 2778713) B2778713
theorem B1852535 : Blo 1234435 1852535 := bstep (se 1 (by rfl) ⟨1389401, by rfl⟩ : syracuseStep 1852535 = 2778803) B2778803
theorem B1852559 : Blo 1234435 1852559 := bstep (se 1 (by rfl) ⟨1389419, by rfl⟩ : syracuseStep 1852559 = 2778839) B2778839
theorem B1852601 : Blo 1234435 1852601 := bstep (se 2 (by rfl) ⟨694725, by rfl⟩ : syracuseStep 1852601 = 1389451) B1389451
theorem B4687105 : Blo 1234435 4687105 := bstep (se 2 (by rfl) ⟨1757664, by rfl⟩ : syracuseStep 4687105 = 3515329) B3515329
theorem B1852679 : Blo 1234435 1852679 := bstep (se 1 (by rfl) ⟨1389509, by rfl⟩ : syracuseStep 1852679 = 2779019) B2779019
theorem B1484039 : Blo 1234435 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B15017233 : Blo 1234435 15017233 := bstep (se 2 (by rfl) ⟨5631462, by rfl⟩ : syracuseStep 15017233 = 11262925) B11262925
theorem B1852715 : Blo 1234435 1852715 := bstep (se 1 (by rfl) ⟨1389536, by rfl⟩ : syracuseStep 1852715 = 2779073) B2779073
theorem B4171067 : Blo 1234435 4171067 := bstep (se 1 (by rfl) ⟨3128300, by rfl⟩ : syracuseStep 4171067 = 6256601) B6256601
theorem B1852745 : Blo 1234435 1852745 := bstep (se 2 (by rfl) ⟨694779, by rfl⟩ : syracuseStep 1852745 = 1389559) B1389559
theorem B2778515 : Blo 1234435 2778515 := bstep (se 1 (by rfl) ⟨2083886, by rfl⟩ : syracuseStep 2778515 = 4167773) B4167773
theorem B1852859 : Blo 1234435 1852859 := bstep (se 1 (by rfl) ⟨1389644, by rfl⟩ : syracuseStep 1852859 = 2779289) B2779289
theorem B2778569 : Blo 1234435 2778569 := bstep (se 2 (by rfl) ⟨1041963, by rfl⟩ : syracuseStep 2778569 = 2083927) B2083927
theorem B1852919 : Blo 1234435 1852919 := bstep (se 1 (by rfl) ⟨1389689, by rfl⟩ : syracuseStep 1852919 = 2779379) B2779379
theorem B3958283 : Blo 1234435 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B1852943 : Blo 1234435 1852943 := bstep (se 1 (by rfl) ⟨1389707, by rfl⟩ : syracuseStep 1852943 = 2779415) B2779415
theorem B1852985 : Blo 1234435 1852985 := bstep (se 2 (by rfl) ⟨694869, by rfl⟩ : syracuseStep 1852985 = 1389739) B1389739
theorem B1484347 : Blo 1234435 1484347 := bstep (se 1 (by rfl) ⟨1113260, by rfl⟩ : syracuseStep 1484347 = 2226521) B2226521
theorem B1853063 : Blo 1234435 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B1853099 : Blo 1234435 1853099 := bstep (se 1 (by rfl) ⟨1389824, by rfl⟩ : syracuseStep 1853099 = 2779649) B2779649
theorem B1853129 : Blo 1234435 1853129 := bstep (se 2 (by rfl) ⟨694923, by rfl⟩ : syracuseStep 1853129 = 1389847) B1389847
theorem B2967329 : Blo 1234435 2967329 := bstep (se 2 (by rfl) ⟨1112748, by rfl⟩ : syracuseStep 2967329 = 2225497) B2225497
theorem B4171553 : Blo 1234435 4171553 := bstep (se 2 (by rfl) ⟨1564332, by rfl⟩ : syracuseStep 4171553 = 3128665) B3128665
theorem B11880229 : Blo 1234435 11880229 := bstep (se 4 (by rfl) ⟨1113771, by rfl⟩ : syracuseStep 11880229 = 2227543) B2227543
theorem B1853243 : Blo 1234435 1853243 := bstep (se 1 (by rfl) ⟨1389932, by rfl⟩ : syracuseStep 1853243 = 2779865) B2779865
theorem B2639675 : Blo 1234435 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B1853303 : Blo 1234435 1853303 := bstep (se 1 (by rfl) ⟨1389977, by rfl⟩ : syracuseStep 1853303 = 2779955) B2779955
theorem B1853327 : Blo 1234435 1853327 := bstep (se 1 (by rfl) ⟨1389995, by rfl⟩ : syracuseStep 1853327 = 2779991) B2779991
theorem B2344889 : Blo 1234435 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B1853369 : Blo 1234435 1853369 := bstep (se 2 (by rfl) ⟨695013, by rfl⟩ : syracuseStep 1853369 = 1390027) B1390027
theorem B3172297 : Blo 1234435 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B1878007 : Blo 1234435 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B1853447 : Blo 1234435 1853447 := bstep (se 1 (by rfl) ⟨1390085, by rfl⟩ : syracuseStep 1853447 = 2780171) B2780171
theorem B3565601 : Blo 1234435 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B1853483 : Blo 1234435 1853483 := bstep (se 1 (by rfl) ⟨1390112, by rfl⟩ : syracuseStep 1853483 = 2780225) B2780225
theorem B1853513 : Blo 1234435 1853513 := bstep (se 2 (by rfl) ⟨695067, by rfl⟩ : syracuseStep 1853513 = 1390135) B1390135
theorem B2779271 : Blo 1234435 2779271 := bstep (se 1 (by rfl) ⟨2084453, by rfl⟩ : syracuseStep 2779271 = 4168907) B4168907
theorem B1853627 : Blo 1234435 1853627 := bstep (se 1 (by rfl) ⟨1390220, by rfl⟩ : syracuseStep 1853627 = 2780441) B2780441
theorem B1853687 : Blo 1234435 1853687 := bstep (se 1 (by rfl) ⟨1390265, by rfl⟩ : syracuseStep 1853687 = 2780531) B2780531
theorem B68512013 : Blo 1234435 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B1853711 : Blo 1234435 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B1853753 : Blo 1234435 1853753 := bstep (se 2 (by rfl) ⟨695157, by rfl⟩ : syracuseStep 1853753 = 1390315) B1390315
theorem B2779451 : Blo 1234435 2779451 := bstep (se 1 (by rfl) ⟨2084588, by rfl⟩ : syracuseStep 2779451 = 4169177) B4169177
theorem B3516787 : Blo 1234435 3516787 := bstep (se 1 (by rfl) ⟨2637590, by rfl⟩ : syracuseStep 3516787 = 5275181) B5275181
theorem B4172147 : Blo 1234435 4172147 := bstep (se 1 (by rfl) ⟨3129110, by rfl⟩ : syracuseStep 4172147 = 6258221) B6258221
theorem B1853831 : Blo 1234435 1853831 := bstep (se 1 (by rfl) ⟨1390373, by rfl⟩ : syracuseStep 1853831 = 2780747) B2780747
theorem B7039385 : Blo 1234435 7039385 := bstep (se 2 (by rfl) ⟨2639769, by rfl⟩ : syracuseStep 7039385 = 5279539) B5279539
theorem B1853867 : Blo 1234435 1853867 := bstep (se 1 (by rfl) ⟨1390400, by rfl⟩ : syracuseStep 1853867 = 2780801) B2780801
theorem B2779577 : Blo 1234435 2779577 := bstep (se 2 (by rfl) ⟨1042341, by rfl⟩ : syracuseStep 2779577 = 2084683) B2084683
theorem B1853897 : Blo 1234435 1853897 := bstep (se 2 (by rfl) ⟨695211, by rfl⟩ : syracuseStep 1853897 = 1390423) B1390423
theorem B3754529 : Blo 1234435 3754529 := bstep (se 2 (by rfl) ⟨1407948, by rfl⟩ : syracuseStep 3754529 = 2815897) B2815897
theorem B2083387 : Blo 1234435 2083387 := bstep (se 1 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 2083387 = 3125081) B3125081
theorem B1854011 : Blo 1234435 1854011 := bstep (se 1 (by rfl) ⟨1390508, by rfl⟩ : syracuseStep 1854011 = 2781017) B2781017
theorem B3517015 : Blo 1234435 3517015 := bstep (se 1 (by rfl) ⟨2637761, by rfl⟩ : syracuseStep 3517015 = 5275523) B5275523
theorem B1854071 : Blo 1234435 1854071 := bstep (se 1 (by rfl) ⟨1390553, by rfl⟩ : syracuseStep 1854071 = 2781107) B2781107
theorem B1854095 : Blo 1234435 1854095 := bstep (se 1 (by rfl) ⟨1390571, by rfl⟩ : syracuseStep 1854095 = 2781143) B2781143
theorem B1854137 : Blo 1234435 1854137 := bstep (se 2 (by rfl) ⟨695301, by rfl⟩ : syracuseStep 1854137 = 1390603) B1390603
theorem B2083529 : Blo 1234435 2083529 := bstep (se 2 (by rfl) ⟨781323, by rfl⟩ : syracuseStep 2083529 = 1562647) B1562647
theorem B1854215 : Blo 1234435 1854215 := bstep (se 1 (by rfl) ⟨1390661, by rfl⟩ : syracuseStep 1854215 = 2781323) B2781323
theorem B2779919 : Blo 1234435 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B2779937 : Blo 1234435 2779937 := bstep (se 2 (by rfl) ⟨1042476, by rfl⟩ : syracuseStep 2779937 = 2084953) B2084953
theorem B1854251 : Blo 1234435 1854251 := bstep (se 1 (by rfl) ⟨1390688, by rfl⟩ : syracuseStep 1854251 = 2781377) B2781377
theorem B1854281 : Blo 1234435 1854281 := bstep (se 2 (by rfl) ⟨695355, by rfl⟩ : syracuseStep 1854281 = 1390711) B1390711
theorem B1854395 : Blo 1234435 1854395 := bstep (se 1 (by rfl) ⟨1390796, by rfl⟩ : syracuseStep 1854395 = 2781593) B2781593
theorem B1854455 : Blo 1234435 1854455 := bstep (se 1 (by rfl) ⟨1390841, by rfl⟩ : syracuseStep 1854455 = 2781683) B2781683
theorem B1854479 : Blo 1234435 1854479 := bstep (se 1 (by rfl) ⟨1390859, by rfl⟩ : syracuseStep 1854479 = 2781719) B2781719
theorem B1854521 : Blo 1234435 1854521 := bstep (se 2 (by rfl) ⟨695445, by rfl⟩ : syracuseStep 1854521 = 1390891) B1390891
theorem B14076989 : Blo 1234435 14076989 := bstep (se 3 (by rfl) ⟨2639435, by rfl⟩ : syracuseStep 14076989 = 5278871) B5278871
theorem B2780279 : Blo 1234435 2780279 := bstep (se 1 (by rfl) ⟨2085209, by rfl⟩ : syracuseStep 2780279 = 4170419) B4170419
theorem B1854599 : Blo 1234435 1854599 := bstep (se 1 (by rfl) ⟨1390949, by rfl⟩ : syracuseStep 1854599 = 2781899) B2781899
theorem B1854635 : Blo 1234435 1854635 := bstep (se 1 (by rfl) ⟨1390976, by rfl⟩ : syracuseStep 1854635 = 2781953) B2781953
theorem B13028525 : Blo 1234435 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B3960065 : Blo 1234435 3960065 := bstep (se 2 (by rfl) ⟨1485024, by rfl⟩ : syracuseStep 3960065 = 2970049) B2970049
theorem B9383201 : Blo 1234435 9383201 := bstep (se 2 (by rfl) ⟨3518700, by rfl⟩ : syracuseStep 9383201 = 7037401) B7037401
theorem B2780459 : Blo 1234435 2780459 := bstep (se 1 (by rfl) ⟨2085344, by rfl⟩ : syracuseStep 2780459 = 4170689) B4170689
theorem B3960179 : Blo 1234435 3960179 := bstep (se 1 (by rfl) ⟨2970134, by rfl⟩ : syracuseStep 3960179 = 5940269) B5940269
theorem B15232387 : Blo 1234435 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B15822215 : Blo 1234435 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B2084231 : Blo 1234435 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B6254009 : Blo 1234435 6254009 := bstep (se 2 (by rfl) ⟨2345253, by rfl⟩ : syracuseStep 6254009 = 4690507) B4690507
theorem B10546807 : Blo 1234435 10546807 := bstep (se 1 (by rfl) ⟨7910105, by rfl⟩ : syracuseStep 10546807 = 15820211) B15820211
theorem B2780819 : Blo 1234435 2780819 := bstep (se 1 (by rfl) ⟨2085614, by rfl⟩ : syracuseStep 2780819 = 4171229) B4171229
theorem B3124889 : Blo 1234435 3124889 := bstep (se 2 (by rfl) ⟨1171833, by rfl⟩ : syracuseStep 3124889 = 2343667) B2343667
theorem B9375425 : Blo 1234435 9375425 := bstep (se 2 (by rfl) ⟨3515784, by rfl⟩ : syracuseStep 9375425 = 7031569) B7031569
theorem B8023745 : Blo 1234435 8023745 := bstep (se 2 (by rfl) ⟨3008904, by rfl⟩ : syracuseStep 8023745 = 6017809) B6017809
theorem B411455173 : Blo 1234435 411455173 := bstep (se 4 (by rfl) ⟨38573922, by rfl⟩ : syracuseStep 411455173 = 77147845) B77147845
theorem B2780873 : Blo 1234435 2780873 := bstep (se 2 (by rfl) ⟨1042827, by rfl⟩ : syracuseStep 2780873 = 2085655) B2085655
theorem B9506609 : Blo 1234435 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B3125051 : Blo 1234435 3125051 := bstep (se 1 (by rfl) ⟨2343788, by rfl⟩ : syracuseStep 3125051 = 4687577) B4687577
theorem B2346887 : Blo 1234435 2346887 := bstep (se 1 (by rfl) ⟨1760165, by rfl⟩ : syracuseStep 2346887 = 3520331) B3520331
theorem B30060557 : Blo 1234435 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B3125263 : Blo 1234435 3125263 := bstep (se 1 (by rfl) ⟨2343947, by rfl⟩ : syracuseStep 3125263 = 4687895) B4687895
theorem B2084879 : Blo 1234435 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B3010603 : Blo 1234435 3010603 := bstep (se 1 (by rfl) ⟨2257952, by rfl⟩ : syracuseStep 3010603 = 4515905) B4515905
theorem B4690007 : Blo 1234435 4690007 := bstep (se 1 (by rfl) ⟨3517505, by rfl⟩ : syracuseStep 4690007 = 7035011) B7035011
theorem B5279863 : Blo 1234435 5279863 := bstep (se 1 (by rfl) ⟨3959897, by rfl⟩ : syracuseStep 5279863 = 7919795) B7919795
theorem B3518599 : Blo 1234435 3518599 := bstep (se 1 (by rfl) ⟨2638949, by rfl⟩ : syracuseStep 3518599 = 5277899) B5277899
theorem B22532269 : Blo 1234435 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B9384173 : Blo 1234435 9384173 := bstep (se 3 (by rfl) ⟨1759532, by rfl⟩ : syracuseStep 9384173 = 3519065) B3519065
theorem B19263757 : Blo 1234435 19263757 := bstep (se 3 (by rfl) ⟨3611954, by rfl⟩ : syracuseStep 19263757 = 7223909) B7223909
theorem B3125537 : Blo 1234435 3125537 := bstep (se 2 (by rfl) ⟨1172076, by rfl⟩ : syracuseStep 3125537 = 2344153) B2344153
theorem B3617057 : Blo 1234435 3617057 := bstep (se 2 (by rfl) ⟨1356396, by rfl⟩ : syracuseStep 3617057 = 2712793) B2712793
theorem B2502971 : Blo 1234435 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B2781575 : Blo 1234435 2781575 := bstep (se 1 (by rfl) ⟨2086181, by rfl⟩ : syracuseStep 2781575 = 4172363) B4172363
theorem B3518873 : Blo 1234435 3518873 := bstep (se 2 (by rfl) ⟨1319577, by rfl⟩ : syracuseStep 3518873 = 2639155) B2639155
theorem B20034013 : Blo 1234435 20034013 := bstep (se 3 (by rfl) ⟨3756377, by rfl⟩ : syracuseStep 20034013 = 7512755) B7512755
theorem B5935639 : Blo 1234435 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B2085419 : Blo 1234435 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B2781755 : Blo 1234435 2781755 := bstep (se 1 (by rfl) ⟨2086316, by rfl⟩ : syracuseStep 2781755 = 4172633) B4172633
theorem B4690493 : Blo 1234435 4690493 := bstep (se 3 (by rfl) ⟨879467, by rfl⟩ : syracuseStep 4690493 = 1758935) B1758935
theorem B1389199 : Blo 1234435 1389199 := bstep (se 1 (by rfl) ⟨1041899, by rfl⟩ : syracuseStep 1389199 = 2083799) B2083799
theorem B2781881 : Blo 1234435 2781881 := bstep (se 2 (by rfl) ⟨1043205, by rfl⟩ : syracuseStep 2781881 = 2086411) B2086411
theorem B6255305 : Blo 1234435 6255305 := bstep (se 2 (by rfl) ⟨2345739, by rfl⟩ : syracuseStep 6255305 = 4691479) B4691479
theorem B2503457 : Blo 1234435 2503457 := bstep (se 2 (by rfl) ⟨938796, by rfl⟩ : syracuseStep 2503457 = 1877593) B1877593
theorem B4166585 : Blo 1234435 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B2085817 : Blo 1234435 2085817 := bstep (se 2 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 2085817 = 1564363) B1564363
theorem B1758223 : Blo 1234435 1758223 := bstep (se 1 (by rfl) ⟨1318667, by rfl⟩ : syracuseStep 1758223 = 2637335) B2637335
theorem B3519521 : Blo 1234435 3519521 := bstep (se 2 (by rfl) ⟨1319820, by rfl⟩ : syracuseStep 3519521 = 2639641) B2639641
theorem B3666977 : Blo 1234435 3666977 := bstep (se 2 (by rfl) ⟨1375116, by rfl⟩ : syracuseStep 3666977 = 2750233) B2750233
theorem B3339325 : Blo 1234435 3339325 := bstep (se 3 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 3339325 = 1252247) B1252247
theorem B4011095 : Blo 1234435 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B104297603 : Blo 1234435 104297603 := bstep (se 1 (by rfl) ⟨78223202, by rfl⟩ : syracuseStep 104297603 = 156446405) B156446405
theorem B1758343 : Blo 1234435 1758343 := bstep (se 1 (by rfl) ⟨1318757, by rfl⟩ : syracuseStep 1758343 = 2637515) B2637515
theorem B1389703 : Blo 1234435 1389703 := bstep (se 1 (by rfl) ⟨1042277, by rfl⟩ : syracuseStep 1389703 = 2084555) B2084555
theorem B8459437 : Blo 1234435 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B2225353 : Blo 1234435 2225353 := bstep (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) B1669015
theorem B3126539 : Blo 1234435 3126539 := bstep (se 1 (by rfl) ⟨2344904, by rfl⟩ : syracuseStep 3126539 = 4689809) B4689809
theorem B1389883 : Blo 1234435 1389883 := bstep (se 1 (by rfl) ⟨1042412, by rfl⟩ : syracuseStep 1389883 = 2084825) B2084825
theorem B1234439 : Blo 1234435 1234439 := bstep (se 1 (by rfl) ⟨925829, by rfl⟩ : syracuseStep 1234439 = 1851659) B1851659
theorem B4167179 : Blo 1234435 4167179 := bstep (se 1 (by rfl) ⟨3125384, by rfl⟩ : syracuseStep 4167179 = 6250769) B6250769
theorem B1234447 : Blo 1234435 1234447 := bstep (se 1 (by rfl) ⟨925835, by rfl⟩ : syracuseStep 1234447 = 1851671) B1851671
theorem B14267947 : Blo 1234435 14267947 := bstep (se 1 (by rfl) ⟨10700960, by rfl⟩ : syracuseStep 14267947 = 21401921) B21401921
theorem B1234491 : Blo 1234435 1234491 := bstep (se 1 (by rfl) ⟨925868, by rfl⟩ : syracuseStep 1234491 = 1851737) B1851737
theorem B4167287 : Blo 1234435 4167287 := bstep (se 1 (by rfl) ⟨3125465, by rfl⟩ : syracuseStep 4167287 = 6250931) B6250931
theorem B1234567 : Blo 1234435 1234567 := bstep (se 1 (by rfl) ⟨925925, by rfl⟩ : syracuseStep 1234567 = 1851851) B1851851
theorem B1234575 : Blo 1234435 1234575 := bstep (se 1 (by rfl) ⟨925931, by rfl⟩ : syracuseStep 1234575 = 1851863) B1851863
theorem B3757715 : Blo 1234435 3757715 := bstep (se 1 (by rfl) ⟨2818286, by rfl⟩ : syracuseStep 3757715 = 5636573) B5636573
theorem B1234619 : Blo 1234435 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B7919333 : Blo 1234435 7919333 := bstep (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) B1484875
theorem B1234695 : Blo 1234435 1234695 := bstep (se 1 (by rfl) ⟨926021, by rfl⟩ : syracuseStep 1234695 = 1852043) B1852043
theorem B1234703 : Blo 1234435 1234703 := bstep (se 1 (by rfl) ⟨926027, by rfl⟩ : syracuseStep 1234703 = 1852055) B1852055
theorem B1390351 : Blo 1234435 1390351 := bstep (se 1 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 1390351 = 2085527) B2085527
theorem B1234747 : Blo 1234435 1234747 := bstep (se 1 (by rfl) ⟨926060, by rfl⟩ : syracuseStep 1234747 = 1852121) B1852121
theorem B1234823 : Blo 1234435 1234823 := bstep (se 1 (by rfl) ⟨926117, by rfl⟩ : syracuseStep 1234823 = 1852235) B1852235
theorem B7034759 : Blo 1234435 7034759 := bstep (se 1 (by rfl) ⟨5276069, by rfl⟩ : syracuseStep 7034759 = 10552139) B10552139
theorem B4454279 : Blo 1234435 4454279 := bstep (se 1 (by rfl) ⟨3340709, by rfl⟩ : syracuseStep 4454279 = 6681419) B6681419
theorem B1234831 : Blo 1234435 1234831 := bstep (se 1 (by rfl) ⟨926123, by rfl⟩ : syracuseStep 1234831 = 1852247) B1852247
theorem B3127187 : Blo 1234435 3127187 := bstep (se 1 (by rfl) ⟨2345390, by rfl⟩ : syracuseStep 3127187 = 4690781) B4690781
theorem B4011923 : Blo 1234435 4011923 := bstep (se 1 (by rfl) ⟨3008942, by rfl⟩ : syracuseStep 4011923 = 6017885) B6017885
theorem B1234875 : Blo 1234435 1234875 := bstep (se 1 (by rfl) ⟨926156, by rfl⟩ : syracuseStep 1234875 = 1852313) B1852313
theorem B1234951 : Blo 1234435 1234951 := bstep (se 1 (by rfl) ⟨926213, by rfl⟩ : syracuseStep 1234951 = 1852427) B1852427
theorem B3520523 : Blo 1234435 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B1234959 : Blo 1234435 1234959 := bstep (se 1 (by rfl) ⟨926219, by rfl⟩ : syracuseStep 1234959 = 1852439) B1852439
theorem B1235003 : Blo 1234435 1235003 := bstep (se 1 (by rfl) ⟨926252, by rfl⟩ : syracuseStep 1235003 = 1852505) B1852505
theorem B1562743 : Blo 1234435 1562743 := bstep (se 1 (by rfl) ⟨1172057, by rfl⟩ : syracuseStep 1562743 = 2344115) B2344115
theorem B9386117 : Blo 1234435 9386117 := bstep (se 4 (by rfl) ⟨879948, by rfl⟩ : syracuseStep 9386117 = 1759897) B1759897
theorem B1235079 : Blo 1234435 1235079 := bstep (se 1 (by rfl) ⟨926309, by rfl⟩ : syracuseStep 1235079 = 1852619) B1852619
theorem B1235087 : Blo 1234435 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B3127481 : Blo 1234435 3127481 := bstep (se 2 (by rfl) ⟨1172805, by rfl⟩ : syracuseStep 3127481 = 2345611) B2345611
theorem B1235131 : Blo 1234435 1235131 := bstep (se 1 (by rfl) ⟨926348, by rfl⟩ : syracuseStep 1235131 = 1852697) B1852697
theorem B4167881 : Blo 1234435 4167881 := bstep (se 2 (by rfl) ⟨1562955, by rfl⟩ : syracuseStep 4167881 = 3125911) B3125911
theorem B15833333 : Blo 1234435 15833333 := bstep (se 5 (by rfl) ⟨742187, by rfl⟩ : syracuseStep 15833333 = 1484375) B1484375
theorem B1235207 : Blo 1234435 1235207 := bstep (se 1 (by rfl) ⟨926405, by rfl⟩ : syracuseStep 1235207 = 1852811) B1852811
theorem B1390855 : Blo 1234435 1390855 := bstep (se 1 (by rfl) ⟨1043141, by rfl⟩ : syracuseStep 1390855 = 2086283) B2086283
theorem B1235215 : Blo 1234435 1235215 := bstep (se 1 (by rfl) ⟨926411, by rfl⟩ : syracuseStep 1235215 = 1852823) B1852823
theorem B4692239 : Blo 1234435 4692239 := bstep (se 1 (by rfl) ⟨3519179, by rfl⟩ : syracuseStep 4692239 = 7038359) B7038359
theorem B3954977 : Blo 1234435 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B1235259 : Blo 1234435 1235259 := bstep (se 1 (by rfl) ⟨926444, by rfl⟩ : syracuseStep 1235259 = 1852889) B1852889
theorem B1235335 : Blo 1234435 1235335 := bstep (se 1 (by rfl) ⟨926501, by rfl⟩ : syracuseStep 1235335 = 1853003) B1853003
theorem B2505095 : Blo 1234435 2505095 := bstep (se 1 (by rfl) ⟨1878821, by rfl⟩ : syracuseStep 2505095 = 3757643) B3757643
theorem B1235343 : Blo 1234435 1235343 := bstep (se 1 (by rfl) ⟨926507, by rfl⟩ : syracuseStep 1235343 = 1853015) B1853015
theorem B1563067 : Blo 1234435 1563067 := bstep (se 1 (by rfl) ⟨1172300, by rfl⟩ : syracuseStep 1563067 = 2344601) B2344601
theorem B1235387 : Blo 1234435 1235387 := bstep (se 1 (by rfl) ⟨926540, by rfl⟩ : syracuseStep 1235387 = 1853081) B1853081
theorem B13720013 : Blo 1234435 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B1235463 : Blo 1234435 1235463 := bstep (se 1 (by rfl) ⟨926597, by rfl⟩ : syracuseStep 1235463 = 1853195) B1853195
theorem B1235471 : Blo 1234435 1235471 := bstep (se 1 (by rfl) ⟨926603, by rfl⟩ : syracuseStep 1235471 = 1853207) B1853207
theorem B1759801 : Blo 1234435 1759801 := bstep (se 2 (by rfl) ⟨659925, by rfl⟩ : syracuseStep 1759801 = 1319851) B1319851
theorem B1235515 : Blo 1234435 1235515 := bstep (se 1 (by rfl) ⟨926636, by rfl⟩ : syracuseStep 1235515 = 1853273) B1853273
theorem B1235591 : Blo 1234435 1235591 := bstep (se 1 (by rfl) ⟨926693, by rfl⟩ : syracuseStep 1235591 = 1853387) B1853387
theorem B1235599 : Blo 1234435 1235599 := bstep (se 1 (by rfl) ⟨926699, by rfl⟩ : syracuseStep 1235599 = 1853399) B1853399
theorem B1235643 : Blo 1234435 1235643 := bstep (se 1 (by rfl) ⟨926732, by rfl⟩ : syracuseStep 1235643 = 1853465) B1853465
theorem B2636489 : Blo 1234435 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B1235719 : Blo 1234435 1235719 := bstep (se 1 (by rfl) ⟨926789, by rfl⟩ : syracuseStep 1235719 = 1853579) B1853579
theorem B1235727 : Blo 1234435 1235727 := bstep (se 1 (by rfl) ⟨926795, by rfl⟩ : syracuseStep 1235727 = 1853591) B1853591
theorem B1235771 : Blo 1234435 1235771 := bstep (se 1 (by rfl) ⟨926828, by rfl⟩ : syracuseStep 1235771 = 1853657) B1853657
theorem B3128179 : Blo 1234435 3128179 := bstep (se 1 (by rfl) ⟨2346134, by rfl⟩ : syracuseStep 3128179 = 4692269) B4692269
theorem B4168583 : Blo 1234435 4168583 := bstep (se 1 (by rfl) ⟨3126437, by rfl⟩ : syracuseStep 4168583 = 6252875) B6252875
theorem B1235847 : Blo 1234435 1235847 := bstep (se 1 (by rfl) ⟨926885, by rfl⟩ : syracuseStep 1235847 = 1853771) B1853771
theorem B1235855 : Blo 1234435 1235855 := bstep (se 1 (by rfl) ⟨926891, by rfl⟩ : syracuseStep 1235855 = 1853783) B1853783
theorem B1563563 : Blo 1234435 1563563 := bstep (se 1 (by rfl) ⟨1172672, by rfl⟩ : syracuseStep 1563563 = 2345345) B2345345
theorem B1235899 : Blo 1234435 1235899 := bstep (se 1 (by rfl) ⟨926924, by rfl⟩ : syracuseStep 1235899 = 1853849) B1853849
theorem B3128321 : Blo 1234435 3128321 := bstep (se 2 (by rfl) ⟨1173120, by rfl⟩ : syracuseStep 3128321 = 2346241) B2346241
theorem B1235975 : Blo 1234435 1235975 := bstep (se 1 (by rfl) ⟨926981, by rfl⟩ : syracuseStep 1235975 = 1853963) B1853963
theorem B9378827 : Blo 1234435 9378827 := bstep (se 1 (by rfl) ⟨7034120, by rfl⟩ : syracuseStep 9378827 = 14068241) B14068241
theorem B1235983 : Blo 1234435 1235983 := bstep (se 1 (by rfl) ⟨926987, by rfl⟩ : syracuseStep 1235983 = 1853975) B1853975
theorem B1236027 : Blo 1234435 1236027 := bstep (se 1 (by rfl) ⟨927020, by rfl⟩ : syracuseStep 1236027 = 1854041) B1854041
theorem B3759223 : Blo 1234435 3759223 := bstep (se 1 (by rfl) ⟨2819417, by rfl⟩ : syracuseStep 3759223 = 5638835) B5638835
theorem B1236103 : Blo 1234435 1236103 := bstep (se 1 (by rfl) ⟨927077, by rfl⟩ : syracuseStep 1236103 = 1854155) B1854155
theorem B1236111 : Blo 1234435 1236111 := bstep (se 1 (by rfl) ⟨927083, by rfl⟩ : syracuseStep 1236111 = 1854167) B1854167
theorem B1236155 : Blo 1234435 1236155 := bstep (se 1 (by rfl) ⟨927116, by rfl⟩ : syracuseStep 1236155 = 1854233) B1854233
theorem B202816709 : Blo 1234435 202816709 := bstep (se 4 (by rfl) ⟨19014066, by rfl⟩ : syracuseStep 202816709 = 38028133) B38028133
theorem B4168961 : Blo 1234435 4168961 := bstep (se 2 (by rfl) ⟨1563360, by rfl⟩ : syracuseStep 4168961 = 3126721) B3126721
theorem B1236231 : Blo 1234435 1236231 := bstep (se 1 (by rfl) ⟨927173, by rfl⟩ : syracuseStep 1236231 = 1854347) B1854347
theorem B1236239 : Blo 1234435 1236239 := bstep (se 1 (by rfl) ⟨927179, by rfl⟩ : syracuseStep 1236239 = 1854359) B1854359
theorem B3759419 : Blo 1234435 3759419 := bstep (se 1 (by rfl) ⟨2819564, by rfl⟩ : syracuseStep 3759419 = 5639129) B5639129
theorem B1236283 : Blo 1234435 1236283 := bstep (se 1 (by rfl) ⟨927212, by rfl⟩ : syracuseStep 1236283 = 1854425) B1854425
theorem B1564039 : Blo 1234435 1564039 := bstep (se 1 (by rfl) ⟨1173029, by rfl⟩ : syracuseStep 1564039 = 2346059) B2346059
theorem B1236359 : Blo 1234435 1236359 := bstep (se 1 (by rfl) ⟨927269, by rfl⟩ : syracuseStep 1236359 = 1854539) B1854539
theorem B1236367 : Blo 1234435 1236367 := bstep (se 1 (by rfl) ⟨927275, by rfl⟩ : syracuseStep 1236367 = 1854551) B1854551
theorem B1236411 : Blo 1234435 1236411 := bstep (se 1 (by rfl) ⟨927308, by rfl⟩ : syracuseStep 1236411 = 1854617) B1854617
theorem B3128777 : Blo 1234435 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B13360589 : Blo 1234435 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B5275165 : Blo 1234435 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B11869739 : Blo 1234435 11869739 := bstep (se 1 (by rfl) ⟨8902304, by rfl⟩ : syracuseStep 11869739 = 17804609) B17804609
theorem B27065933 : Blo 1234435 27065933 := bstep (se 3 (by rfl) ⟨5074862, by rfl⟩ : syracuseStep 27065933 = 10149725) B10149725
theorem B3129131 : Blo 1234435 3129131 := bstep (se 1 (by rfl) ⟨2346848, by rfl⟩ : syracuseStep 3129131 = 4693697) B4693697
theorem B1564535 : Blo 1234435 1564535 := bstep (se 1 (by rfl) ⟨1173401, by rfl⟩ : syracuseStep 1564535 = 2346803) B2346803
theorem B4693895 : Blo 1234435 4693895 := bstep (se 1 (by rfl) ⟨3520421, by rfl⟩ : syracuseStep 4693895 = 7040843) B7040843
theorem B12672931 : Blo 1234435 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B9388061 : Blo 1234435 9388061 := bstep (se 3 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 9388061 = 3520523) B3520523
theorem B4014137 : Blo 1234435 4014137 := bstep (se 2 (by rfl) ⟨1505301, by rfl⟩ : syracuseStep 4014137 = 3010603) B3010603
theorem B5275763 : Blo 1234435 5275763 := bstep (se 1 (by rfl) ⟨3956822, by rfl⟩ : syracuseStep 5275763 = 7913645) B7913645
theorem B16908517 : Blo 1234435 16908517 := bstep (se 4 (by rfl) ⟨1585173, by rfl⟩ : syracuseStep 16908517 = 3170347) B3170347
theorem B17809733 : Blo 1234435 17809733 := bstep (se 4 (by rfl) ⟨1669662, by rfl⟩ : syracuseStep 17809733 = 3339325) B3339325
theorem B6259031 : Blo 1234435 6259031 := bstep (se 1 (by rfl) ⟨4694273, by rfl⟩ : syracuseStep 6259031 = 9388547) B9388547
theorem B278126941 : Blo 1234435 278126941 := bstep (se 3 (by rfl) ⟨52148801, by rfl⟩ : syracuseStep 278126941 = 104297603) B104297603
theorem B1851743 : Blo 1234435 1851743 := bstep (se 1 (by rfl) ⟨1388807, by rfl⟩ : syracuseStep 1851743 = 2777615) B2777615
theorem B1851755 : Blo 1234435 1851755 := bstep (se 1 (by rfl) ⟨1388816, by rfl⟩ : syracuseStep 1851755 = 2777633) B2777633
theorem B4170203 : Blo 1234435 4170203 := bstep (se 1 (by rfl) ⟨3127652, by rfl⟩ : syracuseStep 4170203 = 6255305) B6255305
theorem B1851983 : Blo 1234435 1851983 := bstep (se 1 (by rfl) ⟨1388987, by rfl⟩ : syracuseStep 1851983 = 2777975) B2777975
theorem B2777723 : Blo 1234435 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B3957437 : Blo 1234435 3957437 := bstep (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) B1484039
theorem B1852103 : Blo 1234435 1852103 := bstep (se 1 (by rfl) ⟨1389077, by rfl⟩ : syracuseStep 1852103 = 2778155) B2778155
theorem B7914185 : Blo 1234435 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B2777849 : Blo 1234435 2777849 := bstep (se 2 (by rfl) ⟨1041693, by rfl⟩ : syracuseStep 2777849 = 2083387) B2083387
theorem B1852265 : Blo 1234435 1852265 := bstep (se 2 (by rfl) ⟨694599, by rfl⟩ : syracuseStep 1852265 = 1389199) B1389199
theorem B1852343 : Blo 1234435 1852343 := bstep (se 1 (by rfl) ⟨1389257, by rfl⟩ : syracuseStep 1852343 = 2778515) B2778515
theorem B1852379 : Blo 1234435 1852379 := bstep (se 1 (by rfl) ⟨1389284, by rfl⟩ : syracuseStep 1852379 = 2778569) B2778569
theorem B2778119 : Blo 1234435 2778119 := bstep (se 1 (by rfl) ⟨2083589, by rfl⟩ : syracuseStep 2778119 = 4167179) B4167179
theorem B2638855 : Blo 1234435 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B2778191 : Blo 1234435 2778191 := bstep (se 1 (by rfl) ⟨2083643, by rfl⟩ : syracuseStep 2778191 = 4167287) B4167287
theorem B4170905 : Blo 1234435 4170905 := bstep (se 2 (by rfl) ⟨1564089, by rfl⟩ : syracuseStep 4170905 = 3128179) B3128179
theorem B2344297 : Blo 1234435 2344297 := bstep (se 2 (by rfl) ⟨879111, by rfl⟩ : syracuseStep 2344297 = 1758223) B1758223
theorem B2377067 : Blo 1234435 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B1852847 : Blo 1234435 1852847 := bstep (se 1 (by rfl) ⟨1389635, by rfl⟩ : syracuseStep 1852847 = 2779271) B2779271
theorem B2778587 : Blo 1234435 2778587 := bstep (se 1 (by rfl) ⟨2083940, by rfl⟩ : syracuseStep 2778587 = 4167881) B4167881
theorem B2344457 : Blo 1234435 2344457 := bstep (se 2 (by rfl) ⟨879171, by rfl⟩ : syracuseStep 2344457 = 1758343) B1758343
theorem B1852937 : Blo 1234435 1852937 := bstep (se 2 (by rfl) ⟨694851, by rfl⟩ : syracuseStep 1852937 = 1389703) B1389703
theorem B1852967 : Blo 1234435 1852967 := bstep (se 1 (by rfl) ⟨1389725, by rfl⟩ : syracuseStep 1852967 = 2779451) B2779451
theorem B2967137 : Blo 1234435 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B1853051 : Blo 1234435 1853051 := bstep (se 1 (by rfl) ⟨1389788, by rfl⟩ : syracuseStep 1853051 = 2779577) B2779577
theorem B20022977 : Blo 1234435 20022977 := bstep (se 2 (by rfl) ⟨7508616, by rfl⟩ : syracuseStep 20022977 = 15017233) B15017233
theorem B1853177 : Blo 1234435 1853177 := bstep (se 2 (by rfl) ⟨694941, by rfl⟩ : syracuseStep 1853177 = 1389883) B1389883
theorem B20309849 : Blo 1234435 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B1853279 : Blo 1234435 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B1853291 : Blo 1234435 1853291 := bstep (se 1 (by rfl) ⟨1389968, by rfl⟩ : syracuseStep 1853291 = 2779937) B2779937
theorem B7030637 : Blo 1234435 7030637 := bstep (se 3 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 7030637 = 2636489) B2636489
theorem B2779055 : Blo 1234435 2779055 := bstep (se 1 (by rfl) ⟨2084291, by rfl⟩ : syracuseStep 2779055 = 4168583) B4168583
theorem B6252551 : Blo 1234435 6252551 := bstep (se 1 (by rfl) ⟨4689413, by rfl⟩ : syracuseStep 6252551 = 9378827) B9378827
theorem B19023929 : Blo 1234435 19023929 := bstep (se 2 (by rfl) ⟨7133973, by rfl⟩ : syracuseStep 19023929 = 14267947) B14267947
theorem B1853519 : Blo 1234435 1853519 := bstep (se 1 (by rfl) ⟨1390139, by rfl⟩ : syracuseStep 1853519 = 2780279) B2780279
theorem B8685683 : Blo 1234435 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B135211139 : Blo 1234435 135211139 := bstep (se 1 (by rfl) ⟨101408354, by rfl⟩ : syracuseStep 135211139 = 202816709) B202816709
theorem B7039133 : Blo 1234435 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B2779307 : Blo 1234435 2779307 := bstep (se 1 (by rfl) ⟨2084480, by rfl⟩ : syracuseStep 2779307 = 4168961) B4168961
theorem B2640043 : Blo 1234435 2640043 := bstep (se 1 (by rfl) ⟨1980032, by rfl⟩ : syracuseStep 2640043 = 3960065) B3960065
theorem B1853639 : Blo 1234435 1853639 := bstep (se 1 (by rfl) ⟨1390229, by rfl⟩ : syracuseStep 1853639 = 2780459) B2780459
theorem B2640119 : Blo 1234435 2640119 := bstep (se 1 (by rfl) ⟨1980089, by rfl⟩ : syracuseStep 2640119 = 3960179) B3960179
theorem B8907059 : Blo 1234435 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B4172093 : Blo 1234435 4172093 := bstep (se 3 (by rfl) ⟨782267, by rfl⟩ : syracuseStep 4172093 = 1564535) B1564535
theorem B1853801 : Blo 1234435 1853801 := bstep (se 2 (by rfl) ⟨695175, by rfl⟩ : syracuseStep 1853801 = 1390351) B1390351
theorem B1853879 : Blo 1234435 1853879 := bstep (se 1 (by rfl) ⟨1390409, by rfl⟩ : syracuseStep 1853879 = 2780819) B2780819
theorem B2083259 : Blo 1234435 2083259 := bstep (se 1 (by rfl) ⟨1562444, by rfl⟩ : syracuseStep 2083259 = 3124889) B3124889
theorem B1853915 : Blo 1234435 1853915 := bstep (se 1 (by rfl) ⟨1390436, by rfl⟩ : syracuseStep 1853915 = 2780873) B2780873
theorem B6253037 : Blo 1234435 6253037 := bstep (se 3 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 6253037 = 2344889) B2344889
theorem B2083367 : Blo 1234435 2083367 := bstep (se 1 (by rfl) ⟨1562525, by rfl⟩ : syracuseStep 2083367 = 3125051) B3125051
theorem B4229729 : Blo 1234435 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B20040371 : Blo 1234435 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B2779847 : Blo 1234435 2779847 := bstep (se 1 (by rfl) ⟨2084885, by rfl⟩ : syracuseStep 2779847 = 4169771) B4169771
theorem B2083657 : Blo 1234435 2083657 := bstep (se 2 (by rfl) ⟨781371, by rfl⟩ : syracuseStep 2083657 = 1562743) B1562743
theorem B7039817 : Blo 1234435 7039817 := bstep (se 2 (by rfl) ⟨2639931, by rfl⟩ : syracuseStep 7039817 = 5279863) B5279863
theorem B2083691 : Blo 1234435 2083691 := bstep (se 1 (by rfl) ⟨1562768, by rfl⟩ : syracuseStep 2083691 = 3125537) B3125537
theorem B2411371 : Blo 1234435 2411371 := bstep (se 1 (by rfl) ⟨1808528, by rfl⟩ : syracuseStep 2411371 = 3617057) B3617057
theorem B30043025 : Blo 1234435 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B1854383 : Blo 1234435 1854383 := bstep (se 1 (by rfl) ⟨1390787, by rfl⟩ : syracuseStep 1854383 = 2781575) B2781575
theorem B2345915 : Blo 1234435 2345915 := bstep (se 1 (by rfl) ⟨1759436, by rfl⟩ : syracuseStep 2345915 = 3518873) B3518873
theorem B1854473 : Blo 1234435 1854473 := bstep (se 2 (by rfl) ⟨695427, by rfl⟩ : syracuseStep 1854473 = 1390855) B1390855
theorem B25685009 : Blo 1234435 25685009 := bstep (se 2 (by rfl) ⟨9631878, by rfl⟩ : syracuseStep 25685009 = 19263757) B19263757
theorem B1854503 : Blo 1234435 1854503 := bstep (se 1 (by rfl) ⟨1390877, by rfl⟩ : syracuseStep 1854503 = 2781755) B2781755
theorem B3959923 : Blo 1234435 3959923 := bstep (se 1 (by rfl) ⟨2969942, by rfl⟩ : syracuseStep 3959923 = 5939885) B5939885
theorem B1854587 : Blo 1234435 1854587 := bstep (se 1 (by rfl) ⟨1390940, by rfl⟩ : syracuseStep 1854587 = 2781881) B2781881
theorem B4689049 : Blo 1234435 4689049 := bstep (se 2 (by rfl) ⟨1758393, by rfl⟩ : syracuseStep 4689049 = 3516787) B3516787
theorem B4172957 : Blo 1234435 4172957 := bstep (se 3 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 4172957 = 1564859) B1564859
theorem B2084089 : Blo 1234435 2084089 := bstep (se 2 (by rfl) ⟨781533, by rfl⟩ : syracuseStep 2084089 = 1563067) B1563067
theorem B6253847 : Blo 1234435 6253847 := bstep (se 1 (by rfl) ⟨4690385, by rfl⟩ : syracuseStep 6253847 = 9380771) B9380771
theorem B2346347 : Blo 1234435 2346347 := bstep (se 1 (by rfl) ⟨1759760, by rfl⟩ : syracuseStep 2346347 = 3519521) B3519521
theorem B2444651 : Blo 1234435 2444651 := bstep (se 1 (by rfl) ⟨1833488, by rfl⟩ : syracuseStep 2444651 = 3666977) B3666977
theorem B2674063 : Blo 1234435 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B2346401 : Blo 1234435 2346401 := bstep (se 2 (by rfl) ⟨879900, by rfl⟩ : syracuseStep 2346401 = 1759801) B1759801
theorem B4689353 : Blo 1234435 4689353 := bstep (se 2 (by rfl) ⟨1758507, by rfl⟩ : syracuseStep 4689353 = 3517015) B3517015
theorem B2084359 : Blo 1234435 2084359 := bstep (se 1 (by rfl) ⟨1563269, by rfl⟩ : syracuseStep 2084359 = 3126539) B3126539
theorem B2780711 : Blo 1234435 2780711 := bstep (se 1 (by rfl) ⟨2085533, by rfl⟩ : syracuseStep 2780711 = 4171067) B4171067
theorem B5279555 : Blo 1234435 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B1978219 : Blo 1234435 1978219 := bstep (se 1 (by rfl) ⟨1483664, by rfl⟩ : syracuseStep 1978219 = 2967329) B2967329
theorem B2781035 : Blo 1234435 2781035 := bstep (se 1 (by rfl) ⟨2085776, by rfl⟩ : syracuseStep 2781035 = 4171553) B4171553
theorem B2781089 : Blo 1234435 2781089 := bstep (se 2 (by rfl) ⟨1042908, by rfl⟩ : syracuseStep 2781089 = 2085817) B2085817
theorem B4689839 : Blo 1234435 4689839 := bstep (se 1 (by rfl) ⟨3517379, by rfl⟩ : syracuseStep 4689839 = 7034759) B7034759
theorem B2969519 : Blo 1234435 2969519 := bstep (se 1 (by rfl) ⟨2227139, by rfl⟩ : syracuseStep 2969519 = 4454279) B4454279
theorem B2084791 : Blo 1234435 2084791 := bstep (se 1 (by rfl) ⟨1563593, by rfl⟩ : syracuseStep 2084791 = 3127187) B3127187
theorem B2084987 : Blo 1234435 2084987 := bstep (se 1 (by rfl) ⟨1563740, by rfl⟩ : syracuseStep 2084987 = 3127481) B3127481
theorem B10555555 : Blo 1234435 10555555 := bstep (se 1 (by rfl) ⟨7916666, by rfl⟩ : syracuseStep 10555555 = 15833333) B15833333
theorem B45674675 : Blo 1234435 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B2781431 : Blo 1234435 2781431 := bstep (se 1 (by rfl) ⟨2086073, by rfl⟩ : syracuseStep 2781431 = 4172147) B4172147
theorem B9146675 : Blo 1234435 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B2503019 : Blo 1234435 2503019 := bstep (se 1 (by rfl) ⟨1877264, by rfl⟩ : syracuseStep 2503019 = 3754529) B3754529
theorem B1389019 : Blo 1234435 1389019 := bstep (se 1 (by rfl) ⟨1041764, by rfl⟩ : syracuseStep 1389019 = 2083529) B2083529
theorem B2085385 : Blo 1234435 2085385 := bstep (se 2 (by rfl) ⟨782019, by rfl⟩ : syracuseStep 2085385 = 1564039) B1564039
theorem B2085547 : Blo 1234435 2085547 := bstep (se 1 (by rfl) ⟨1564160, by rfl⟩ : syracuseStep 2085547 = 3128321) B3128321
theorem B7033553 : Blo 1234435 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B9384659 : Blo 1234435 9384659 := bstep (se 1 (by rfl) ⟨7038494, by rfl⟩ : syracuseStep 9384659 = 14076989) B14076989
theorem B1979129 : Blo 1234435 1979129 := bstep (se 2 (by rfl) ⟨742173, by rfl⟩ : syracuseStep 1979129 = 1484347) B1484347
theorem B14062409 : Blo 1234435 14062409 := bstep (se 2 (by rfl) ⟨5273403, by rfl⟩ : syracuseStep 14062409 = 10546807) B10546807
theorem B6255467 : Blo 1234435 6255467 := bstep (se 1 (by rfl) ⟨4691600, by rfl⟩ : syracuseStep 6255467 = 9383201) B9383201
theorem B10548143 : Blo 1234435 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B1389487 : Blo 1234435 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B548606897 : Blo 1234435 548606897 := bstep (se 2 (by rfl) ⟨205727586, by rfl⟩ : syracuseStep 548606897 = 411455173) B411455173
theorem B2085851 : Blo 1234435 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B15840305 : Blo 1234435 15840305 := bstep (se 2 (by rfl) ⟨5940114, by rfl⟩ : syracuseStep 15840305 = 11880229) B11880229
theorem B18043955 : Blo 1234435 18043955 := bstep (se 1 (by rfl) ⟨13532966, by rfl⟩ : syracuseStep 18043955 = 27065933) B27065933
theorem B2086087 : Blo 1234435 2086087 := bstep (se 1 (by rfl) ⟨1564565, by rfl⟩ : syracuseStep 2086087 = 3129131) B3129131
theorem B6337739 : Blo 1234435 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B16897241 : Blo 1234435 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B2504009 : Blo 1234435 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B1389919 : Blo 1234435 1389919 := bstep (se 1 (by rfl) ⟨1042439, by rfl⟩ : syracuseStep 1389919 = 2084879) B2084879
theorem B4167017 : Blo 1234435 4167017 := bstep (se 2 (by rfl) ⟨1562631, by rfl⟩ : syracuseStep 4167017 = 3125263) B3125263
theorem B2086249 : Blo 1234435 2086249 := bstep (se 2 (by rfl) ⟨782343, by rfl⟩ : syracuseStep 2086249 = 1564687) B1564687
theorem B3126671 : Blo 1234435 3126671 := bstep (se 1 (by rfl) ⟨2345003, by rfl⟩ : syracuseStep 3126671 = 4690007) B4690007
theorem B10556891 : Blo 1234435 10556891 := bstep (se 1 (by rfl) ⟨7917668, by rfl⟩ : syracuseStep 10556891 = 15835337) B15835337
theorem B6256115 : Blo 1234435 6256115 := bstep (se 1 (by rfl) ⟨4692086, by rfl⟩ : syracuseStep 6256115 = 9384173) B9384173
theorem B4691465 : Blo 1234435 4691465 := bstep (se 2 (by rfl) ⟨1759299, by rfl⟩ : syracuseStep 4691465 = 3518599) B3518599
theorem B1234471 : Blo 1234435 1234471 := bstep (se 1 (by rfl) ⟨925853, by rfl⟩ : syracuseStep 1234471 = 1851707) B1851707
theorem B1668647 : Blo 1234435 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B1234511 : Blo 1234435 1234511 := bstep (se 1 (by rfl) ⟨925883, by rfl⟩ : syracuseStep 1234511 = 1851767) B1851767
theorem B1234527 : Blo 1234435 1234527 := bstep (se 1 (by rfl) ⟨925895, by rfl⟩ : syracuseStep 1234527 = 1851791) B1851791
theorem B1234555 : Blo 1234435 1234555 := bstep (se 1 (by rfl) ⟨925916, by rfl⟩ : syracuseStep 1234555 = 1851833) B1851833
theorem B1234607 : Blo 1234435 1234607 := bstep (se 1 (by rfl) ⟨925955, by rfl⟩ : syracuseStep 1234607 = 1851911) B1851911
theorem B1234631 : Blo 1234435 1234631 := bstep (se 1 (by rfl) ⟨925973, by rfl⟩ : syracuseStep 1234631 = 1851947) B1851947
theorem B1390279 : Blo 1234435 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B3126995 : Blo 1234435 3126995 := bstep (se 1 (by rfl) ⟨2345246, by rfl⟩ : syracuseStep 3126995 = 4690493) B4690493
theorem B1234651 : Blo 1234435 1234651 := bstep (se 1 (by rfl) ⟨925988, by rfl⟩ : syracuseStep 1234651 = 1851977) B1851977
theorem B1234727 : Blo 1234435 1234727 := bstep (se 1 (by rfl) ⟨926045, by rfl⟩ : syracuseStep 1234727 = 1852091) B1852091
theorem B1234767 : Blo 1234435 1234767 := bstep (se 1 (by rfl) ⟨926075, by rfl⟩ : syracuseStep 1234767 = 1852151) B1852151
theorem B1234783 : Blo 1234435 1234783 := bstep (se 1 (by rfl) ⟨926087, by rfl⟩ : syracuseStep 1234783 = 1852175) B1852175
theorem B1668971 : Blo 1234435 1668971 := bstep (se 1 (by rfl) ⟨1251728, by rfl⟩ : syracuseStep 1668971 = 2503457) B2503457
theorem B1234811 : Blo 1234435 1234811 := bstep (se 1 (by rfl) ⟨926108, by rfl⟩ : syracuseStep 1234811 = 1852217) B1852217
theorem B14079905 : Blo 1234435 14079905 := bstep (se 2 (by rfl) ⟨5279964, by rfl⟩ : syracuseStep 14079905 = 10559929) B10559929
theorem B1234863 : Blo 1234435 1234863 := bstep (se 1 (by rfl) ⟨926147, by rfl⟩ : syracuseStep 1234863 = 1852295) B1852295
theorem B4167611 : Blo 1234435 4167611 := bstep (se 1 (by rfl) ⟨3125708, by rfl⟩ : syracuseStep 4167611 = 6251417) B6251417
theorem B1234887 : Blo 1234435 1234887 := bstep (se 1 (by rfl) ⟨926165, by rfl⟩ : syracuseStep 1234887 = 1852331) B1852331
theorem B26712017 : Blo 1234435 26712017 := bstep (se 2 (by rfl) ⟨10017006, by rfl⟩ : syracuseStep 26712017 = 20034013) B20034013
theorem B1234907 : Blo 1234435 1234907 := bstep (se 1 (by rfl) ⟨926180, by rfl⟩ : syracuseStep 1234907 = 1852361) B1852361
theorem B1234983 : Blo 1234435 1234983 := bstep (se 1 (by rfl) ⟨926237, by rfl⟩ : syracuseStep 1234983 = 1852475) B1852475
theorem B1235023 : Blo 1234435 1235023 := bstep (se 1 (by rfl) ⟨926267, by rfl⟩ : syracuseStep 1235023 = 1852535) B1852535
theorem B1235039 : Blo 1234435 1235039 := bstep (se 1 (by rfl) ⟨926279, by rfl⟩ : syracuseStep 1235039 = 1852559) B1852559
theorem B1235067 : Blo 1234435 1235067 := bstep (se 1 (by rfl) ⟨926300, by rfl⟩ : syracuseStep 1235067 = 1852601) B1852601
theorem B10025117 : Blo 1234435 10025117 := bstep (se 3 (by rfl) ⟨1879709, by rfl⟩ : syracuseStep 10025117 = 3759419) B3759419
theorem B1235119 : Blo 1234435 1235119 := bstep (se 1 (by rfl) ⟨926339, by rfl⟩ : syracuseStep 1235119 = 1852679) B1852679
theorem B1235143 : Blo 1234435 1235143 := bstep (se 1 (by rfl) ⟨926357, by rfl⟩ : syracuseStep 1235143 = 1852715) B1852715
theorem B1235163 : Blo 1234435 1235163 := bstep (se 1 (by rfl) ⟨926372, by rfl⟩ : syracuseStep 1235163 = 1852745) B1852745
theorem B101374193 : Blo 1234435 101374193 := bstep (se 2 (by rfl) ⟨38015322, by rfl⟩ : syracuseStep 101374193 = 76030645) B76030645
theorem B1235239 : Blo 1234435 1235239 := bstep (se 1 (by rfl) ⟨926429, by rfl⟩ : syracuseStep 1235239 = 1852859) B1852859
theorem B1235279 : Blo 1234435 1235279 := bstep (se 1 (by rfl) ⟨926459, by rfl⟩ : syracuseStep 1235279 = 1852919) B1852919
theorem B1235295 : Blo 1234435 1235295 := bstep (se 1 (by rfl) ⟨926471, by rfl⟩ : syracuseStep 1235295 = 1852943) B1852943
theorem B1235323 : Blo 1234435 1235323 := bstep (se 1 (by rfl) ⟨926492, by rfl⟩ : syracuseStep 1235323 = 1852985) B1852985
theorem B1235375 : Blo 1234435 1235375 := bstep (se 1 (by rfl) ⟨926531, by rfl⟩ : syracuseStep 1235375 = 1853063) B1853063
theorem B2505143 : Blo 1234435 2505143 := bstep (se 1 (by rfl) ⟨1878857, by rfl⟩ : syracuseStep 2505143 = 3757715) B3757715
theorem B1235399 : Blo 1234435 1235399 := bstep (se 1 (by rfl) ⟨926549, by rfl⟩ : syracuseStep 1235399 = 1853099) B1853099
theorem B1235419 : Blo 1234435 1235419 := bstep (se 1 (by rfl) ⟨926564, by rfl⟩ : syracuseStep 1235419 = 1853129) B1853129
theorem B1235495 : Blo 1234435 1235495 := bstep (se 1 (by rfl) ⟨926621, by rfl⟩ : syracuseStep 1235495 = 1853243) B1853243
theorem B1235535 : Blo 1234435 1235535 := bstep (se 1 (by rfl) ⟨926651, by rfl⟩ : syracuseStep 1235535 = 1853303) B1853303
theorem B1235551 : Blo 1234435 1235551 := bstep (se 1 (by rfl) ⟨926663, by rfl⟩ : syracuseStep 1235551 = 1853327) B1853327
theorem B1235579 : Blo 1234435 1235579 := bstep (se 1 (by rfl) ⟨926684, by rfl⟩ : syracuseStep 1235579 = 1853369) B1853369
theorem B1235631 : Blo 1234435 1235631 := bstep (se 1 (by rfl) ⟨926723, by rfl⟩ : syracuseStep 1235631 = 1853447) B1853447
theorem B1235655 : Blo 1234435 1235655 := bstep (se 1 (by rfl) ⟨926741, by rfl⟩ : syracuseStep 1235655 = 1853483) B1853483
theorem B1235675 : Blo 1234435 1235675 := bstep (se 1 (by rfl) ⟨926756, by rfl⟩ : syracuseStep 1235675 = 1853513) B1853513
theorem B6257411 : Blo 1234435 6257411 := bstep (se 1 (by rfl) ⟨4693058, by rfl⟩ : syracuseStep 6257411 = 9386117) B9386117
theorem B1235751 : Blo 1234435 1235751 := bstep (se 1 (by rfl) ⟨926813, by rfl⟩ : syracuseStep 1235751 = 1853627) B1853627
theorem B5012297 : Blo 1234435 5012297 := bstep (se 2 (by rfl) ⟨1879611, by rfl⟩ : syracuseStep 5012297 = 3759223) B3759223
theorem B1235791 : Blo 1234435 1235791 := bstep (se 1 (by rfl) ⟨926843, by rfl⟩ : syracuseStep 1235791 = 1853687) B1853687
theorem B1235807 : Blo 1234435 1235807 := bstep (se 1 (by rfl) ⟨926855, by rfl⟩ : syracuseStep 1235807 = 1853711) B1853711
theorem B3128159 : Blo 1234435 3128159 := bstep (se 1 (by rfl) ⟨2346119, by rfl⟩ : syracuseStep 3128159 = 4692239) B4692239
theorem B2636651 : Blo 1234435 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B1235835 : Blo 1234435 1235835 := bstep (se 1 (by rfl) ⟨926876, by rfl⟩ : syracuseStep 1235835 = 1853753) B1853753
theorem B11279249 : Blo 1234435 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B1670063 : Blo 1234435 1670063 := bstep (se 1 (by rfl) ⟨1252547, by rfl⟩ : syracuseStep 1670063 = 2505095) B2505095
theorem B1235887 : Blo 1234435 1235887 := bstep (se 1 (by rfl) ⟨926915, by rfl⟩ : syracuseStep 1235887 = 1853831) B1853831
theorem B4692923 : Blo 1234435 4692923 := bstep (se 1 (by rfl) ⟨3519692, by rfl⟩ : syracuseStep 4692923 = 7039385) B7039385
theorem B1235911 : Blo 1234435 1235911 := bstep (se 1 (by rfl) ⟨926933, by rfl⟩ : syracuseStep 1235911 = 1853867) B1853867
theorem B1235931 : Blo 1234435 1235931 := bstep (se 1 (by rfl) ⟨926948, by rfl⟩ : syracuseStep 1235931 = 1853897) B1853897
theorem B6249473 : Blo 1234435 6249473 := bstep (se 2 (by rfl) ⟨2343552, by rfl⟩ : syracuseStep 6249473 = 4687105) B4687105
theorem B1236007 : Blo 1234435 1236007 := bstep (se 1 (by rfl) ⟨927005, by rfl⟩ : syracuseStep 1236007 = 1854011) B1854011
theorem B1236047 : Blo 1234435 1236047 := bstep (se 1 (by rfl) ⟨927035, by rfl⟩ : syracuseStep 1236047 = 1854071) B1854071
theorem B1236063 : Blo 1234435 1236063 := bstep (se 1 (by rfl) ⟨927047, by rfl⟩ : syracuseStep 1236063 = 1854095) B1854095
theorem B1236091 : Blo 1234435 1236091 := bstep (se 1 (by rfl) ⟨927068, by rfl⟩ : syracuseStep 1236091 = 1854137) B1854137
theorem B1236143 : Blo 1234435 1236143 := bstep (se 1 (by rfl) ⟨927107, by rfl⟩ : syracuseStep 1236143 = 1854215) B1854215
theorem B1236167 : Blo 1234435 1236167 := bstep (se 1 (by rfl) ⟨927125, by rfl⟩ : syracuseStep 1236167 = 1854251) B1854251
theorem B1236187 : Blo 1234435 1236187 := bstep (se 1 (by rfl) ⟨927140, by rfl⟩ : syracuseStep 1236187 = 1854281) B1854281
theorem B1236263 : Blo 1234435 1236263 := bstep (se 1 (by rfl) ⟨927197, by rfl⟩ : syracuseStep 1236263 = 1854395) B1854395
theorem B1236303 : Blo 1234435 1236303 := bstep (se 1 (by rfl) ⟨927227, by rfl⟩ : syracuseStep 1236303 = 1854455) B1854455
theorem B1236319 : Blo 1234435 1236319 := bstep (se 1 (by rfl) ⟨927239, by rfl⟩ : syracuseStep 1236319 = 1854479) B1854479
theorem B1236347 : Blo 1234435 1236347 := bstep (se 1 (by rfl) ⟨927260, by rfl⟩ : syracuseStep 1236347 = 1854521) B1854521
theorem B1236399 : Blo 1234435 1236399 := bstep (se 1 (by rfl) ⟨927299, by rfl⟩ : syracuseStep 1236399 = 1854599) B1854599
theorem B1236423 : Blo 1234435 1236423 := bstep (se 1 (by rfl) ⟨927317, by rfl⟩ : syracuseStep 1236423 = 1854635) B1854635
theorem B4169339 : Blo 1234435 4169339 := bstep (se 1 (by rfl) ⟨3127004, by rfl⟩ : syracuseStep 4169339 = 6254009) B6254009
theorem B7913159 : Blo 1234435 7913159 := bstep (se 1 (by rfl) ⟨5934869, by rfl⟩ : syracuseStep 7913159 = 11869739) B11869739
theorem B10698461 : Blo 1234435 10698461 := bstep (se 3 (by rfl) ⟨2005961, by rfl⟩ : syracuseStep 10698461 = 4011923) B4011923
theorem B4169501 : Blo 1234435 4169501 := bstep (se 3 (by rfl) ⟨781781, by rfl⟩ : syracuseStep 4169501 = 1563563) B1563563
theorem B6250283 : Blo 1234435 6250283 := bstep (se 1 (by rfl) ⟨4687712, by rfl⟩ : syracuseStep 6250283 = 9375425) B9375425
theorem B5349163 : Blo 1234435 5349163 := bstep (se 1 (by rfl) ⟨4011872, by rfl⟩ : syracuseStep 5349163 = 8023745) B8023745
theorem B1564591 : Blo 1234435 1564591 := bstep (se 1 (by rfl) ⟨1173443, by rfl⟩ : syracuseStep 1564591 = 2346887) B2346887
theorem B3129263 : Blo 1234435 3129263 := bstep (se 1 (by rfl) ⟨2346947, by rfl⟩ : syracuseStep 3129263 = 4693895) B4693895
theorem B6258707 : Blo 1234435 6258707 := bstep (se 1 (by rfl) ⟨4694030, by rfl⟩ : syracuseStep 6258707 = 9388061) B9388061
theorem B30449783 : Blo 1234435 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B14074073 : Blo 1234435 14074073 := bstep (se 2 (by rfl) ⟨5277777, by rfl⟩ : syracuseStep 14074073 = 10555555) B10555555
theorem B22544689 : Blo 1234435 22544689 := bstep (se 2 (by rfl) ⟨8454258, by rfl⟩ : syracuseStep 22544689 = 16908517) B16908517
theorem B1851815 : Blo 1234435 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B370835921 : Blo 1234435 370835921 := bstep (se 2 (by rfl) ⟨139063470, by rfl⟩ : syracuseStep 370835921 = 278126941) B278126941
theorem B5276123 : Blo 1234435 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B1851899 : Blo 1234435 1851899 := bstep (se 1 (by rfl) ⟨1388924, by rfl⟩ : syracuseStep 1851899 = 2777849) B2777849
theorem B1319419 : Blo 1234435 1319419 := bstep (se 1 (by rfl) ⟨989564, by rfl⟩ : syracuseStep 1319419 = 1979129) B1979129
theorem B4170311 : Blo 1234435 4170311 := bstep (se 1 (by rfl) ⟨3127733, by rfl⟩ : syracuseStep 4170311 = 6255467) B6255467
theorem B1852025 : Blo 1234435 1852025 := bstep (se 2 (by rfl) ⟨694509, by rfl⟩ : syracuseStep 1852025 = 1389019) B1389019
theorem B1852079 : Blo 1234435 1852079 := bstep (se 1 (by rfl) ⟨1389059, by rfl⟩ : syracuseStep 1852079 = 2778119) B2778119
theorem B10560203 : Blo 1234435 10560203 := bstep (se 1 (by rfl) ⟨7920152, by rfl⟩ : syracuseStep 10560203 = 15840305) B15840305
theorem B1852127 : Blo 1234435 1852127 := bstep (se 1 (by rfl) ⟨1389095, by rfl⟩ : syracuseStep 1852127 = 2778191) B2778191
theorem B11264827 : Blo 1234435 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B2778011 : Blo 1234435 2778011 := bstep (se 1 (by rfl) ⟨2083508, by rfl⟩ : syracuseStep 2778011 = 4167017) B4167017
theorem B1852391 : Blo 1234435 1852391 := bstep (se 1 (by rfl) ⟨1389293, by rfl⟩ : syracuseStep 1852391 = 2778587) B2778587
theorem B7037927 : Blo 1234435 7037927 := bstep (se 1 (by rfl) ⟨5278445, by rfl⟩ : syracuseStep 7037927 = 10556891) B10556891
theorem B4170743 : Blo 1234435 4170743 := bstep (se 1 (by rfl) ⟨3128057, by rfl⟩ : syracuseStep 4170743 = 6256115) B6256115
theorem B2778209 : Blo 1234435 2778209 := bstep (se 2 (by rfl) ⟨1041828, by rfl⟩ : syracuseStep 2778209 = 2083657) B2083657
theorem B1852649 : Blo 1234435 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B4687091 : Blo 1234435 4687091 := bstep (se 1 (by rfl) ⟨3515318, by rfl⟩ : syracuseStep 4687091 = 7030637) B7030637
theorem B1852703 : Blo 1234435 1852703 := bstep (se 1 (by rfl) ⟨1389527, by rfl⟩ : syracuseStep 1852703 = 2779055) B2779055
theorem B2778407 : Blo 1234435 2778407 := bstep (se 1 (by rfl) ⟨2083805, by rfl⟩ : syracuseStep 2778407 = 4167611) B4167611
theorem B12682619 : Blo 1234435 12682619 := bstep (se 1 (by rfl) ⟨9511964, by rfl⟩ : syracuseStep 12682619 = 19023929) B19023929
theorem B4449725 : Blo 1234435 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B1852871 : Blo 1234435 1852871 := bstep (se 1 (by rfl) ⟨1389653, by rfl⟩ : syracuseStep 1852871 = 2779307) B2779307
theorem B6252065 : Blo 1234435 6252065 := bstep (se 2 (by rfl) ⟨2344524, by rfl⟩ : syracuseStep 6252065 = 4689049) B4689049
theorem B2778785 : Blo 1234435 2778785 := bstep (se 2 (by rfl) ⟨1042044, by rfl⟩ : syracuseStep 2778785 = 2084089) B2084089
theorem B2819819 : Blo 1234435 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B1853225 : Blo 1234435 1853225 := bstep (se 2 (by rfl) ⟨694959, by rfl⟩ : syracuseStep 1853225 = 1389919) B1389919
theorem B1853231 : Blo 1234435 1853231 := bstep (se 1 (by rfl) ⟨1389923, by rfl⟩ : syracuseStep 1853231 = 2779847) B2779847
theorem B10553165 : Blo 1234435 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B4171607 : Blo 1234435 4171607 := bstep (se 1 (by rfl) ⟨3128705, by rfl⟩ : syracuseStep 4171607 = 6257411) B6257411
theorem B3565417 : Blo 1234435 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B2779145 : Blo 1234435 2779145 := bstep (se 2 (by rfl) ⟨1042179, by rfl⟩ : syracuseStep 2779145 = 2084359) B2084359
theorem B17123339 : Blo 1234435 17123339 := bstep (se 1 (by rfl) ⟨12842504, by rfl⟩ : syracuseStep 17123339 = 25685009) B25685009
theorem B1853705 : Blo 1234435 1853705 := bstep (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) B1390279
theorem B7031069 : Blo 1234435 7031069 := bstep (se 3 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 7031069 = 2636651) B2636651
theorem B4450589 : Blo 1234435 4450589 := bstep (se 3 (by rfl) ⟨834485, by rfl⟩ : syracuseStep 4450589 = 1668971) B1668971
theorem B1853807 : Blo 1234435 1853807 := bstep (se 1 (by rfl) ⟨1390355, by rfl⟩ : syracuseStep 1853807 = 2780711) B2780711
theorem B2779559 : Blo 1234435 2779559 := bstep (se 1 (by rfl) ⟨2084669, by rfl⟩ : syracuseStep 2779559 = 4169339) B4169339
theorem B2779667 : Blo 1234435 2779667 := bstep (se 1 (by rfl) ⟨2084750, by rfl⟩ : syracuseStep 2779667 = 4169501) B4169501
theorem B1854023 : Blo 1234435 1854023 := bstep (se 1 (by rfl) ⟨1390517, by rfl⟩ : syracuseStep 1854023 = 2781035) B2781035
theorem B2779721 : Blo 1234435 2779721 := bstep (se 2 (by rfl) ⟨1042395, by rfl⟩ : syracuseStep 2779721 = 2084791) B2084791
theorem B1854059 : Blo 1234435 1854059 := bstep (se 1 (by rfl) ⟨1390544, by rfl⟩ : syracuseStep 1854059 = 2781089) B2781089
theorem B3517175 : Blo 1234435 3517175 := bstep (se 1 (by rfl) ⟨2637881, by rfl⟩ : syracuseStep 3517175 = 5275763) B5275763
theorem B1854287 : Blo 1234435 1854287 := bstep (se 1 (by rfl) ⟨1390715, by rfl⟩ : syracuseStep 1854287 = 2781431) B2781431
theorem B6097783 : Blo 1234435 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B11873155 : Blo 1234435 11873155 := bstep (se 1 (by rfl) ⟨8904866, by rfl⟩ : syracuseStep 11873155 = 17809733) B17809733
theorem B4172687 : Blo 1234435 4172687 := bstep (se 1 (by rfl) ⟨3129515, by rfl⟩ : syracuseStep 4172687 = 6259031) B6259031
theorem B2780135 : Blo 1234435 2780135 := bstep (se 1 (by rfl) ⟨2085101, by rfl⟩ : syracuseStep 2780135 = 4170203) B4170203
theorem B4689035 : Blo 1234435 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B9374939 : Blo 1234435 9374939 := bstep (se 1 (by rfl) ⟨7031204, by rfl⟩ : syracuseStep 9374939 = 14062409) B14062409
theorem B7032095 : Blo 1234435 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B7040317 : Blo 1234435 7040317 := bstep (se 3 (by rfl) ⟨1320059, by rfl⟩ : syracuseStep 7040317 = 2640119) B2640119
theorem B2780513 : Blo 1234435 2780513 := bstep (se 2 (by rfl) ⟨1042692, by rfl⟩ : syracuseStep 2780513 = 2085385) B2085385
theorem B12029303 : Blo 1234435 12029303 := bstep (se 1 (by rfl) ⟨9021977, by rfl⟩ : syracuseStep 12029303 = 18043955) B18043955
theorem B2780603 : Blo 1234435 2780603 := bstep (se 1 (by rfl) ⟨2085452, by rfl⟩ : syracuseStep 2780603 = 4170905) B4170905
theorem B2780729 : Blo 1234435 2780729 := bstep (se 2 (by rfl) ⟨1042773, by rfl⟩ : syracuseStep 2780729 = 2085547) B2085547
theorem B2084447 : Blo 1234435 2084447 := bstep (se 1 (by rfl) ⟨1563335, by rfl⟩ : syracuseStep 2084447 = 3126671) B3126671
theorem B1978091 : Blo 1234435 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B13348651 : Blo 1234435 13348651 := bstep (se 1 (by rfl) ⟨10011488, by rfl⟩ : syracuseStep 13348651 = 20022977) B20022977
theorem B2084663 : Blo 1234435 2084663 := bstep (se 1 (by rfl) ⟨1563497, by rfl⟩ : syracuseStep 2084663 = 3126995) B3126995
theorem B3215161 : Blo 1234435 3215161 := bstep (se 2 (by rfl) ⟨1205685, by rfl⟩ : syracuseStep 3215161 = 2411371) B2411371
theorem B3518473 : Blo 1234435 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B90140759 : Blo 1234435 90140759 := bstep (se 1 (by rfl) ⟨67605569, by rfl⟩ : syracuseStep 90140759 = 135211139) B135211139
theorem B5279897 : Blo 1234435 5279897 := bstep (se 2 (by rfl) ⟨1979961, by rfl⟩ : syracuseStep 5279897 = 3959923) B3959923
theorem B2781395 : Blo 1234435 2781395 := bstep (se 1 (by rfl) ⟨2086046, by rfl⟩ : syracuseStep 2781395 = 4172093) B4172093
theorem B2781449 : Blo 1234435 2781449 := bstep (se 2 (by rfl) ⟨1043043, by rfl⟩ : syracuseStep 2781449 = 2086087) B2086087
theorem B1388839 : Blo 1234435 1388839 := bstep (se 1 (by rfl) ⟨1041629, by rfl⟩ : syracuseStep 1388839 = 2083259) B2083259
theorem B1388911 : Blo 1234435 1388911 := bstep (se 1 (by rfl) ⟨1041683, by rfl⟩ : syracuseStep 1388911 = 2083367) B2083367
theorem B3125729 : Blo 1234435 3125729 := bstep (se 2 (by rfl) ⟨1172148, by rfl⟩ : syracuseStep 3125729 = 2344297) B2344297
theorem B2781665 : Blo 1234435 2781665 := bstep (se 2 (by rfl) ⟨1043124, by rfl⟩ : syracuseStep 2781665 = 2086249) B2086249
theorem B17814005 : Blo 1234435 17814005 := bstep (se 5 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 17814005 = 1670063) B1670063
theorem B2085439 : Blo 1234435 2085439 := bstep (se 1 (by rfl) ⟨1564079, by rfl⟩ : syracuseStep 2085439 = 3128159) B3128159
theorem B1389127 : Blo 1234435 1389127 := bstep (se 1 (by rfl) ⟨1041845, by rfl⟩ : syracuseStep 1389127 = 2083691) B2083691
theorem B4166315 : Blo 1234435 4166315 := bstep (se 1 (by rfl) ⟨3124736, by rfl⟩ : syracuseStep 4166315 = 6249473) B6249473
theorem B2781971 : Blo 1234435 2781971 := bstep (se 1 (by rfl) ⟨2086478, by rfl⟩ : syracuseStep 2781971 = 4172957) B4172957
theorem B3126235 : Blo 1234435 3126235 := bstep (se 1 (by rfl) ⟨2344676, by rfl⟩ : syracuseStep 3126235 = 4689353) B4689353
theorem B7132217 : Blo 1234435 7132217 := bstep (se 2 (by rfl) ⟨2674581, by rfl⟩ : syracuseStep 7132217 = 5349163) B5349163
theorem B7918717 : Blo 1234435 7918717 := bstep (se 3 (by rfl) ⟨1484759, by rfl⟩ : syracuseStep 7918717 = 2969519) B2969519
theorem B7132307 : Blo 1234435 7132307 := bstep (se 1 (by rfl) ⟨5349230, by rfl⟩ : syracuseStep 7132307 = 10698461) B10698461
theorem B4166855 : Blo 1234435 4166855 := bstep (se 1 (by rfl) ⟨3125141, by rfl⟩ : syracuseStep 4166855 = 6250283) B6250283
theorem B3519703 : Blo 1234435 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B2086121 : Blo 1234435 2086121 := bstep (se 2 (by rfl) ⟨782295, by rfl⟩ : syracuseStep 2086121 = 1564591) B1564591
theorem B3126559 : Blo 1234435 3126559 := bstep (se 1 (by rfl) ⟨2344919, by rfl⟩ : syracuseStep 3126559 = 4689839) B4689839
theorem B2086175 : Blo 1234435 2086175 := bstep (se 1 (by rfl) ⟨1564631, by rfl⟩ : syracuseStep 2086175 = 3129263) B3129263
theorem B2676091 : Blo 1234435 2676091 := bstep (se 1 (by rfl) ⟨2007068, by rfl⟩ : syracuseStep 2676091 = 4014137) B4014137
theorem B1389991 : Blo 1234435 1389991 := bstep (se 1 (by rfl) ⟨1042493, by rfl⟩ : syracuseStep 1389991 = 2084987) B2084987
theorem B3520057 : Blo 1234435 3520057 := bstep (se 2 (by rfl) ⟨1320021, by rfl⟩ : syracuseStep 3520057 = 2640043) B2640043
theorem B1234495 : Blo 1234435 1234495 := bstep (se 1 (by rfl) ⟨925871, by rfl⟩ : syracuseStep 1234495 = 1851743) B1851743
theorem B1234503 : Blo 1234435 1234503 := bstep (se 1 (by rfl) ⟨925877, by rfl⟩ : syracuseStep 1234503 = 1851755) B1851755
theorem B1234655 : Blo 1234435 1234655 := bstep (se 1 (by rfl) ⟨925991, by rfl⟩ : syracuseStep 1234655 = 1851983) B1851983
theorem B1234735 : Blo 1234435 1234735 := bstep (se 1 (by rfl) ⟨926051, by rfl⟩ : syracuseStep 1234735 = 1852103) B1852103
theorem B6256439 : Blo 1234435 6256439 := bstep (se 1 (by rfl) ⟨4692329, by rfl⟩ : syracuseStep 6256439 = 9384659) B9384659
theorem B1234843 : Blo 1234435 1234843 := bstep (se 1 (by rfl) ⟨926132, by rfl⟩ : syracuseStep 1234843 = 1852265) B1852265
theorem B365737931 : Blo 1234435 365737931 := bstep (se 1 (by rfl) ⟨274303448, by rfl⟩ : syracuseStep 365737931 = 548606897) B548606897
theorem B1234895 : Blo 1234435 1234895 := bstep (se 1 (by rfl) ⟨926171, by rfl⟩ : syracuseStep 1234895 = 1852343) B1852343
theorem B1234919 : Blo 1234435 1234919 := bstep (se 1 (by rfl) ⟨926189, by rfl⟩ : syracuseStep 1234919 = 1852379) B1852379
theorem B1390567 : Blo 1234435 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B4225159 : Blo 1234435 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B1669339 : Blo 1234435 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B6674717 : Blo 1234435 6674717 := bstep (se 3 (by rfl) ⟨1251509, by rfl⟩ : syracuseStep 6674717 = 2503019) B2503019
theorem B6338845 : Blo 1234435 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B1235231 : Blo 1234435 1235231 := bstep (se 1 (by rfl) ⟨926423, by rfl⟩ : syracuseStep 1235231 = 1852847) B1852847
theorem B6256925 : Blo 1234435 6256925 := bstep (se 3 (by rfl) ⟨1173173, by rfl⟩ : syracuseStep 6256925 = 2346347) B2346347
theorem B1562971 : Blo 1234435 1562971 := bstep (se 1 (by rfl) ⟨1172228, by rfl⟩ : syracuseStep 1562971 = 2344457) B2344457
theorem B1235291 : Blo 1234435 1235291 := bstep (se 1 (by rfl) ⟨926468, by rfl⟩ : syracuseStep 1235291 = 1852937) B1852937
theorem B3127643 : Blo 1234435 3127643 := bstep (se 1 (by rfl) ⟨2345732, by rfl⟩ : syracuseStep 3127643 = 4691465) B4691465
theorem B1235311 : Blo 1234435 1235311 := bstep (se 1 (by rfl) ⟨926483, by rfl⟩ : syracuseStep 1235311 = 1852967) B1852967
theorem B1235367 : Blo 1234435 1235367 := bstep (se 1 (by rfl) ⟨926525, by rfl⟩ : syracuseStep 1235367 = 1853051) B1853051
theorem B1235451 : Blo 1234435 1235451 := bstep (se 1 (by rfl) ⟨926588, by rfl⟩ : syracuseStep 1235451 = 1853177) B1853177
theorem B13539899 : Blo 1234435 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B1235519 : Blo 1234435 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B1235527 : Blo 1234435 1235527 := bstep (se 1 (by rfl) ⟨926645, by rfl⟩ : syracuseStep 1235527 = 1853291) B1853291
theorem B9386603 : Blo 1234435 9386603 := bstep (se 1 (by rfl) ⟨7039952, by rfl⟩ : syracuseStep 9386603 = 14079905) B14079905
theorem B17808011 : Blo 1234435 17808011 := bstep (se 1 (by rfl) ⟨13356008, by rfl⟩ : syracuseStep 17808011 = 26712017) B26712017
theorem B4168367 : Blo 1234435 4168367 := bstep (se 1 (by rfl) ⟨3126275, by rfl⟩ : syracuseStep 4168367 = 6252551) B6252551
theorem B1235679 : Blo 1234435 1235679 := bstep (se 1 (by rfl) ⟨926759, by rfl⟩ : syracuseStep 1235679 = 1853519) B1853519
theorem B5790455 : Blo 1234435 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B4692755 : Blo 1234435 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B6683411 : Blo 1234435 6683411 := bstep (se 1 (by rfl) ⟨5012558, by rfl⟩ : syracuseStep 6683411 = 10025117) B10025117
theorem B1235759 : Blo 1234435 1235759 := bstep (se 1 (by rfl) ⟨926819, by rfl⟩ : syracuseStep 1235759 = 1853639) B1853639
theorem B67582795 : Blo 1234435 67582795 := bstep (se 1 (by rfl) ⟨50687096, by rfl⟩ : syracuseStep 67582795 = 101374193) B101374193
theorem B5938039 : Blo 1234435 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B1235867 : Blo 1234435 1235867 := bstep (se 1 (by rfl) ⟨926900, by rfl⟩ : syracuseStep 1235867 = 1853801) B1853801
theorem B1670095 : Blo 1234435 1670095 := bstep (se 1 (by rfl) ⟨1252571, by rfl⟩ : syracuseStep 1670095 = 2505143) B2505143
theorem B1235919 : Blo 1234435 1235919 := bstep (se 1 (by rfl) ⟨926939, by rfl⟩ : syracuseStep 1235919 = 1853879) B1853879
theorem B1235943 : Blo 1234435 1235943 := bstep (se 1 (by rfl) ⟨926957, by rfl⟩ : syracuseStep 1235943 = 1853915) B1853915
theorem B4168691 : Blo 1234435 4168691 := bstep (se 1 (by rfl) ⟨3126518, by rfl⟩ : syracuseStep 4168691 = 6253037) B6253037
theorem B13360247 : Blo 1234435 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B4693211 : Blo 1234435 4693211 := bstep (se 1 (by rfl) ⟨3519908, by rfl⟩ : syracuseStep 4693211 = 7039817) B7039817
theorem B3341531 : Blo 1234435 3341531 := bstep (se 1 (by rfl) ⟨2506148, by rfl⟩ : syracuseStep 3341531 = 5012297) B5012297
theorem B20028683 : Blo 1234435 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B7519499 : Blo 1234435 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B1236255 : Blo 1234435 1236255 := bstep (se 1 (by rfl) ⟨927191, by rfl⟩ : syracuseStep 1236255 = 1854383) B1854383
theorem B1563943 : Blo 1234435 1563943 := bstep (se 1 (by rfl) ⟨1172957, by rfl⟩ : syracuseStep 1563943 = 2345915) B2345915
theorem B3128615 : Blo 1234435 3128615 := bstep (se 1 (by rfl) ⟨2346461, by rfl⟩ : syracuseStep 3128615 = 4692923) B4692923
theorem B1236315 : Blo 1234435 1236315 := bstep (se 1 (by rfl) ⟨927236, by rfl⟩ : syracuseStep 1236315 = 1854473) B1854473
theorem B1236335 : Blo 1234435 1236335 := bstep (se 1 (by rfl) ⟨927251, by rfl⟩ : syracuseStep 1236335 = 1854503) B1854503
theorem B1236391 : Blo 1234435 1236391 := bstep (se 1 (by rfl) ⟨927293, by rfl⟩ : syracuseStep 1236391 = 1854587) B1854587
theorem B4169231 : Blo 1234435 4169231 := bstep (se 1 (by rfl) ⟨3126923, by rfl⟩ : syracuseStep 4169231 = 6253847) B6253847
theorem B1629767 : Blo 1234435 1629767 := bstep (se 1 (by rfl) ⟨1222325, by rfl⟩ : syracuseStep 1629767 = 2444651) B2444651
theorem B1564267 : Blo 1234435 1564267 := bstep (se 1 (by rfl) ⟨1173200, by rfl⟩ : syracuseStep 1564267 = 2346401) B2346401
theorem B5275439 : Blo 1234435 5275439 := bstep (se 1 (by rfl) ⟨3956579, by rfl⟩ : syracuseStep 5275439 = 7913159) B7913159
theorem B2637625 : Blo 1234435 2637625 := bstep (se 2 (by rfl) ⟨989109, by rfl⟩ : syracuseStep 2637625 = 1978219) B1978219
theorem B45662237 : Blo 1234435 45662237 := bstep (se 3 (by rfl) ⟨8561669, by rfl⟩ : syracuseStep 45662237 = 17123339) B17123339
theorem B20299855 : Blo 1234435 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B1851785 : Blo 1234435 1851785 := bstep (se 2 (by rfl) ⟨694419, by rfl⟩ : syracuseStep 1851785 = 1388839) B1388839
theorem B2777543 : Blo 1234435 2777543 := bstep (se 1 (by rfl) ⟨2083157, by rfl⟩ : syracuseStep 2777543 = 4166315) B4166315
theorem B1851881 : Blo 1234435 1851881 := bstep (se 2 (by rfl) ⟨694455, by rfl⟩ : syracuseStep 1851881 = 1388911) B1388911
theorem B1852007 : Blo 1234435 1852007 := bstep (se 1 (by rfl) ⟨1389005, by rfl⟩ : syracuseStep 1852007 = 2778011) B2778011
theorem B1852139 : Blo 1234435 1852139 := bstep (se 1 (by rfl) ⟨1389104, by rfl⟩ : syracuseStep 1852139 = 2778209) B2778209
theorem B1852169 : Blo 1234435 1852169 := bstep (se 2 (by rfl) ⟨694563, by rfl⟩ : syracuseStep 1852169 = 1389127) B1389127
theorem B2777903 : Blo 1234435 2777903 := bstep (se 1 (by rfl) ⟨2083427, by rfl⟩ : syracuseStep 2777903 = 4166855) B4166855
theorem B1852271 : Blo 1234435 1852271 := bstep (se 1 (by rfl) ⟨1389203, by rfl⟩ : syracuseStep 1852271 = 2778407) B2778407
theorem B8455079 : Blo 1234435 8455079 := bstep (se 1 (by rfl) ⟨6341309, by rfl⟩ : syracuseStep 8455079 = 12682619) B12682619
theorem B2966483 : Blo 1234435 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B1852523 : Blo 1234435 1852523 := bstep (se 1 (by rfl) ⟨1389392, by rfl⟩ : syracuseStep 1852523 = 2778785) B2778785
theorem B4170959 : Blo 1234435 4170959 := bstep (se 1 (by rfl) ⟨3128219, by rfl⟩ : syracuseStep 4170959 = 6256439) B6256439
theorem B1852763 : Blo 1234435 1852763 := bstep (se 1 (by rfl) ⟨1389572, by rfl⟩ : syracuseStep 1852763 = 2779145) B2779145
theorem B4687379 : Blo 1234435 4687379 := bstep (se 1 (by rfl) ⟨3515534, by rfl⟩ : syracuseStep 4687379 = 7031069) B7031069
theorem B4449811 : Blo 1234435 4449811 := bstep (se 1 (by rfl) ⟨3337358, by rfl⟩ : syracuseStep 4449811 = 6674717) B6674717
theorem B2967059 : Blo 1234435 2967059 := bstep (se 1 (by rfl) ⟨2225294, by rfl⟩ : syracuseStep 2967059 = 4450589) B4450589
theorem B4171283 : Blo 1234435 4171283 := bstep (se 1 (by rfl) ⟨3128462, by rfl⟩ : syracuseStep 4171283 = 6256925) B6256925
theorem B1853039 : Blo 1234435 1853039 := bstep (se 1 (by rfl) ⟨1389779, by rfl⟩ : syracuseStep 1853039 = 2779559) B2779559
theorem B1853111 : Blo 1234435 1853111 := bstep (se 1 (by rfl) ⟨1389833, by rfl⟩ : syracuseStep 1853111 = 2779667) B2779667
theorem B1853147 : Blo 1234435 1853147 := bstep (se 1 (by rfl) ⟨1389860, by rfl⟩ : syracuseStep 1853147 = 2779721) B2779721
theorem B11872007 : Blo 1234435 11872007 := bstep (se 1 (by rfl) ⟨8904005, by rfl⟩ : syracuseStep 11872007 = 17808011) B17808011
theorem B2778911 : Blo 1234435 2778911 := bstep (se 1 (by rfl) ⟨2084183, by rfl⟩ : syracuseStep 2778911 = 4168367) B4168367
theorem B2344783 : Blo 1234435 2344783 := bstep (se 1 (by rfl) ⟨1758587, by rfl⟩ : syracuseStep 2344783 = 3517175) B3517175
theorem B3860303 : Blo 1234435 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B1853321 : Blo 1234435 1853321 := bstep (se 2 (by rfl) ⟨694995, by rfl⟩ : syracuseStep 1853321 = 1389991) B1389991
theorem B1853423 : Blo 1234435 1853423 := bstep (se 1 (by rfl) ⟨1390067, by rfl⟩ : syracuseStep 1853423 = 2780135) B2780135
theorem B2779127 : Blo 1234435 2779127 := bstep (se 1 (by rfl) ⟨2084345, by rfl⟩ : syracuseStep 2779127 = 4168691) B4168691
theorem B8906831 : Blo 1234435 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B4688063 : Blo 1234435 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B1853675 : Blo 1234435 1853675 := bstep (se 1 (by rfl) ⟨1390256, by rfl⟩ : syracuseStep 1853675 = 2780513) B2780513
theorem B1853735 : Blo 1234435 1853735 := bstep (se 1 (by rfl) ⟨1390301, by rfl⟩ : syracuseStep 1853735 = 2780603) B2780603
theorem B2779487 : Blo 1234435 2779487 := bstep (se 1 (by rfl) ⟨2084615, by rfl⟩ : syracuseStep 2779487 = 4169231) B4169231
theorem B1853819 : Blo 1234435 1853819 := bstep (se 1 (by rfl) ⟨1390364, by rfl⟩ : syracuseStep 1853819 = 2780729) B2780729
theorem B3516833 : Blo 1234435 3516833 := bstep (se 2 (by rfl) ⟨1318812, by rfl⟩ : syracuseStep 3516833 = 2637625) B2637625
theorem B4286881 : Blo 1234435 4286881 := bstep (se 2 (by rfl) ⟨1607580, by rfl⟩ : syracuseStep 4286881 = 3215161) B3215161
theorem B8907173 : Blo 1234435 8907173 := bstep (se 4 (by rfl) ⟨835047, by rfl⟩ : syracuseStep 8907173 = 1670095) B1670095
theorem B4753889 : Blo 1234435 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B3516959 : Blo 1234435 3516959 := bstep (se 1 (by rfl) ⟨2637719, by rfl⟩ : syracuseStep 3516959 = 5275439) B5275439
theorem B1854089 : Blo 1234435 1854089 := bstep (se 2 (by rfl) ⟨695283, by rfl⟩ : syracuseStep 1854089 = 1390567) B1390567
theorem B4172471 : Blo 1234435 4172471 := bstep (se 1 (by rfl) ⟨3129353, by rfl⟩ : syracuseStep 4172471 = 6258707) B6258707
theorem B1854263 : Blo 1234435 1854263 := bstep (se 1 (by rfl) ⟨1390697, by rfl⟩ : syracuseStep 1854263 = 2781395) B2781395
theorem B9382715 : Blo 1234435 9382715 := bstep (se 1 (by rfl) ⟨7037036, by rfl⟩ : syracuseStep 9382715 = 14074073) B14074073
theorem B1854299 : Blo 1234435 1854299 := bstep (se 1 (by rfl) ⟨1390724, by rfl⟩ : syracuseStep 1854299 = 2781449) B2781449
theorem B3517415 : Blo 1234435 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B2083819 : Blo 1234435 2083819 := bstep (se 1 (by rfl) ⟨1562864, by rfl⟩ : syracuseStep 2083819 = 3125729) B3125729
theorem B1854443 : Blo 1234435 1854443 := bstep (se 1 (by rfl) ⟨1390832, by rfl⟩ : syracuseStep 1854443 = 2781665) B2781665
theorem B2780207 : Blo 1234435 2780207 := bstep (se 1 (by rfl) ⟨2085155, by rfl⟩ : syracuseStep 2780207 = 4170311) B4170311
theorem B30059585 : Blo 1234435 30059585 := bstep (se 2 (by rfl) ⟨11272344, by rfl⟩ : syracuseStep 30059585 = 22544689) B22544689
theorem B2083961 : Blo 1234435 2083961 := bstep (se 2 (by rfl) ⟨781485, by rfl⟩ : syracuseStep 2083961 = 1562971) B1562971
theorem B7040135 : Blo 1234435 7040135 := bstep (se 1 (by rfl) ⟨5280101, by rfl⟩ : syracuseStep 7040135 = 10560203) B10560203
theorem B1854647 : Blo 1234435 1854647 := bstep (se 1 (by rfl) ⟨1390985, by rfl⟩ : syracuseStep 1854647 = 2781971) B2781971
theorem B2780495 : Blo 1234435 2780495 := bstep (se 1 (by rfl) ⟨2085371, by rfl⟩ : syracuseStep 2780495 = 4170743) B4170743
theorem B2780585 : Blo 1234435 2780585 := bstep (se 2 (by rfl) ⟨1042719, by rfl⟩ : syracuseStep 2780585 = 2085439) B2085439
theorem B3124727 : Blo 1234435 3124727 := bstep (se 1 (by rfl) ⟨2343545, by rfl⟩ : syracuseStep 3124727 = 4687091) B4687091
theorem B15019769 : Blo 1234435 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B8130377 : Blo 1234435 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B7917385 : Blo 1234435 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B15830873 : Blo 1234435 15830873 := bstep (se 2 (by rfl) ⟨5936577, by rfl⟩ : syracuseStep 15830873 = 11873155) B11873155
theorem B2781071 : Blo 1234435 2781071 := bstep (se 1 (by rfl) ⟨2085803, by rfl⟩ : syracuseStep 2781071 = 4171607) B4171607
theorem B4346045 : Blo 1234435 4346045 := bstep (se 3 (by rfl) ⟨814883, by rfl⟩ : syracuseStep 4346045 = 1629767) B1629767
theorem B2085095 : Blo 1234435 2085095 := bstep (se 1 (by rfl) ⟨1563821, by rfl⟩ : syracuseStep 2085095 = 3127643) B3127643
theorem B2085257 : Blo 1234435 2085257 := bstep (se 2 (by rfl) ⟨781971, by rfl⟩ : syracuseStep 2085257 = 1563943) B1563943
theorem B3568121 : Blo 1234435 3568121 := bstep (se 2 (by rfl) ⟨1338045, by rfl⟩ : syracuseStep 3568121 = 2676091) B2676091
theorem B2781791 : Blo 1234435 2781791 := bstep (se 1 (by rfl) ⟨2086343, by rfl⟩ : syracuseStep 2781791 = 4172687) B4172687
theorem B3126023 : Blo 1234435 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B2085689 : Blo 1234435 2085689 := bstep (se 2 (by rfl) ⟨782133, by rfl⟩ : syracuseStep 2085689 = 1564267) B1564267
theorem B2085743 : Blo 1234435 2085743 := bstep (se 1 (by rfl) ⟨1564307, by rfl⟩ : syracuseStep 2085743 = 3128615) B3128615
theorem B17798201 : Blo 1234435 17798201 := bstep (se 2 (by rfl) ⟨6674325, by rfl⟩ : syracuseStep 17798201 = 13348651) B13348651
theorem B1389631 : Blo 1234435 1389631 := bstep (se 1 (by rfl) ⟨1042223, by rfl⟩ : syracuseStep 1389631 = 2084447) B2084447
theorem B1389775 : Blo 1234435 1389775 := bstep (se 1 (by rfl) ⟨1042331, by rfl⟩ : syracuseStep 1389775 = 2084663) B2084663
theorem B4691297 : Blo 1234435 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B60093839 : Blo 1234435 60093839 := bstep (se 1 (by rfl) ⟨45070379, by rfl⟩ : syracuseStep 60093839 = 90140759) B90140759
theorem B3519931 : Blo 1234435 3519931 := bstep (se 1 (by rfl) ⟨2639948, by rfl⟩ : syracuseStep 3519931 = 5279897) B5279897
theorem B5633545 : Blo 1234435 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B1234543 : Blo 1234435 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B11876003 : Blo 1234435 11876003 := bstep (se 1 (by rfl) ⟨8907002, by rfl⟩ : syracuseStep 11876003 = 17814005) B17814005
theorem B1234599 : Blo 1234435 1234599 := bstep (se 1 (by rfl) ⟨925949, by rfl⟩ : syracuseStep 1234599 = 1851899) B1851899
theorem B8451793 : Blo 1234435 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B19019485 : Blo 1234435 19019485 := bstep (se 3 (by rfl) ⟨3566153, by rfl⟩ : syracuseStep 19019485 = 7132307) B7132307
theorem B1234683 : Blo 1234435 1234683 := bstep (se 1 (by rfl) ⟨926012, by rfl⟩ : syracuseStep 1234683 = 1852025) B1852025
theorem B1234719 : Blo 1234435 1234719 := bstep (se 1 (by rfl) ⟨926039, by rfl⟩ : syracuseStep 1234719 = 1852079) B1852079
theorem B1234751 : Blo 1234435 1234751 := bstep (se 1 (by rfl) ⟨926063, by rfl⟩ : syracuseStep 1234751 = 1852127) B1852127
theorem B8910749 : Blo 1234435 8910749 := bstep (se 3 (by rfl) ⟨1670765, by rfl⟩ : syracuseStep 8910749 = 3341531) B3341531
theorem B76076981 : Blo 1234435 76076981 := bstep (se 5 (by rfl) ⟨3566108, by rfl⟩ : syracuseStep 76076981 = 7132217) B7132217
theorem B1234927 : Blo 1234435 1234927 := bstep (se 1 (by rfl) ⟨926195, by rfl⟩ : syracuseStep 1234927 = 1852391) B1852391
theorem B4691951 : Blo 1234435 4691951 := bstep (se 1 (by rfl) ⟨3518963, by rfl⟩ : syracuseStep 4691951 = 7037927) B7037927
theorem B1235099 : Blo 1234435 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B1390747 : Blo 1234435 1390747 := bstep (se 1 (by rfl) ⟨1043060, by rfl⟩ : syracuseStep 1390747 = 2086121) B2086121
theorem B1235135 : Blo 1234435 1235135 := bstep (se 1 (by rfl) ⟨926351, by rfl⟩ : syracuseStep 1235135 = 1852703) B1852703
theorem B1390783 : Blo 1234435 1390783 := bstep (se 1 (by rfl) ⟨1043087, by rfl⟩ : syracuseStep 1390783 = 2086175) B2086175
theorem B1235247 : Blo 1234435 1235247 := bstep (se 1 (by rfl) ⟨926435, by rfl⟩ : syracuseStep 1235247 = 1852871) B1852871
theorem B4168043 : Blo 1234435 4168043 := bstep (se 1 (by rfl) ⟨3126032, by rfl⟩ : syracuseStep 4168043 = 6252065) B6252065
theorem B90110393 : Blo 1234435 90110393 := bstep (se 2 (by rfl) ⟨33791397, by rfl⟩ : syracuseStep 90110393 = 67582795) B67582795
theorem B8903141 : Blo 1234435 8903141 := bstep (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) B1669339
theorem B1235483 : Blo 1234435 1235483 := bstep (se 1 (by rfl) ⟨926612, by rfl⟩ : syracuseStep 1235483 = 1853225) B1853225
theorem B1235487 : Blo 1234435 1235487 := bstep (se 1 (by rfl) ⟨926615, by rfl⟩ : syracuseStep 1235487 = 1853231) B1853231
theorem B988895789 : Blo 1234435 988895789 := bstep (se 3 (by rfl) ⟨185417960, by rfl⟩ : syracuseStep 988895789 = 370835921) B370835921
theorem B7035443 : Blo 1234435 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B4168313 : Blo 1234435 4168313 := bstep (se 2 (by rfl) ⟨1563117, by rfl⟩ : syracuseStep 4168313 = 3126235) B3126235
theorem B243825287 : Blo 1234435 243825287 := bstep (se 1 (by rfl) ⟨182868965, by rfl⟩ : syracuseStep 243825287 = 365737931) B365737931
theorem B10558289 : Blo 1234435 10558289 := bstep (se 2 (by rfl) ⟨3959358, by rfl⟩ : syracuseStep 10558289 = 7918717) B7918717
theorem B1235803 : Blo 1234435 1235803 := bstep (se 1 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 1235803 = 1853705) B1853705
theorem B1235871 : Blo 1234435 1235871 := bstep (se 1 (by rfl) ⟨926903, by rfl⟩ : syracuseStep 1235871 = 1853807) B1853807
theorem B4692937 : Blo 1234435 4692937 := bstep (se 2 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 4692937 = 3519703) B3519703
theorem B9026599 : Blo 1234435 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B4168745 : Blo 1234435 4168745 := bstep (se 2 (by rfl) ⟨1563279, by rfl⟩ : syracuseStep 4168745 = 3126559) B3126559
theorem B1236015 : Blo 1234435 1236015 := bstep (se 1 (by rfl) ⟨927011, by rfl⟩ : syracuseStep 1236015 = 1854023) B1854023
theorem B1236039 : Blo 1234435 1236039 := bstep (se 1 (by rfl) ⟨927029, by rfl⟩ : syracuseStep 1236039 = 1854059) B1854059
theorem B6257735 : Blo 1234435 6257735 := bstep (se 1 (by rfl) ⟨4693301, by rfl⟩ : syracuseStep 6257735 = 9386603) B9386603
theorem B9387089 : Blo 1234435 9387089 := bstep (se 2 (by rfl) ⟨3520158, by rfl⟩ : syracuseStep 9387089 = 7040317) B7040317
theorem B3128503 : Blo 1234435 3128503 := bstep (se 1 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 3128503 = 4692755) B4692755
theorem B4455607 : Blo 1234435 4455607 := bstep (se 1 (by rfl) ⟨3341705, by rfl⟩ : syracuseStep 4455607 = 6683411) B6683411
theorem B1236191 : Blo 1234435 1236191 := bstep (se 1 (by rfl) ⟨927143, by rfl⟩ : syracuseStep 1236191 = 1854287) B1854287
theorem B7519517 : Blo 1234435 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B4693409 : Blo 1234435 4693409 := bstep (se 2 (by rfl) ⟨1760028, by rfl⟩ : syracuseStep 4693409 = 3520057) B3520057
theorem B6249959 : Blo 1234435 6249959 := bstep (se 1 (by rfl) ⟨4687469, by rfl⟩ : syracuseStep 6249959 = 9374939) B9374939
theorem B3128807 : Blo 1234435 3128807 := bstep (se 1 (by rfl) ⟨2346605, by rfl⟩ : syracuseStep 3128807 = 4693211) B4693211
theorem B13352455 : Blo 1234435 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B5012999 : Blo 1234435 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B8019535 : Blo 1234435 8019535 := bstep (se 1 (by rfl) ⟨6014651, by rfl⟩ : syracuseStep 8019535 = 12029303) B12029303
theorem B1318727 : Blo 1234435 1318727 := bstep (se 1 (by rfl) ⟨989045, by rfl⟩ : syracuseStep 1318727 = 1978091) B1978091
theorem B7036901 : Blo 1234435 7036901 := bstep (se 4 (by rfl) ⟨659709, by rfl⟩ : syracuseStep 7036901 = 1319419) B1319419
theorem B30441491 : Blo 1234435 30441491 := bstep (se 1 (by rfl) ⟨22831118, by rfl⟩ : syracuseStep 30441491 = 45662237) B45662237
theorem B71213093 : Blo 1234435 71213093 := bstep (se 4 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 71213093 = 13352455) B13352455
theorem B27066473 : Blo 1234435 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B1851695 : Blo 1234435 1851695 := bstep (se 1 (by rfl) ⟨1388771, by rfl⟩ : syracuseStep 1851695 = 2777543) B2777543
theorem B1851935 : Blo 1234435 1851935 := bstep (se 1 (by rfl) ⟨1388951, by rfl⟩ : syracuseStep 1851935 = 2777903) B2777903
theorem B5636719 : Blo 1234435 5636719 := bstep (se 1 (by rfl) ⟨4227539, by rfl⟩ : syracuseStep 5636719 = 8455079) B8455079
theorem B7914671 : Blo 1234435 7914671 := bstep (se 1 (by rfl) ⟨5936003, by rfl⟩ : syracuseStep 7914671 = 11872007) B11872007
theorem B1852607 : Blo 1234435 1852607 := bstep (se 1 (by rfl) ⟨1389455, by rfl⟩ : syracuseStep 1852607 = 2778911) B2778911
theorem B50717987 : Blo 1234435 50717987 := bstep (se 1 (by rfl) ⟨38038490, by rfl⟩ : syracuseStep 50717987 = 76076981) B76076981
theorem B2778425 : Blo 1234435 2778425 := bstep (se 2 (by rfl) ⟨1041909, by rfl⟩ : syracuseStep 2778425 = 2083819) B2083819
theorem B1852751 : Blo 1234435 1852751 := bstep (se 1 (by rfl) ⟨1389563, by rfl⟩ : syracuseStep 1852751 = 2779127) B2779127
theorem B12035465 : Blo 1234435 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B1852841 : Blo 1234435 1852841 := bstep (se 2 (by rfl) ⟨694815, by rfl⟩ : syracuseStep 1852841 = 1389631) B1389631
theorem B1852991 : Blo 1234435 1852991 := bstep (se 1 (by rfl) ⟨1389743, by rfl⟩ : syracuseStep 1852991 = 2779487) B2779487
theorem B2778695 : Blo 1234435 2778695 := bstep (se 1 (by rfl) ⟨2084021, by rfl⟩ : syracuseStep 2778695 = 4168043) B4168043
theorem B4171337 : Blo 1234435 4171337 := bstep (se 2 (by rfl) ⟨1564251, by rfl⟩ : syracuseStep 4171337 = 3128503) B3128503
theorem B5940809 : Blo 1234435 5940809 := bstep (se 2 (by rfl) ⟨2227803, by rfl⟩ : syracuseStep 5940809 = 4455607) B4455607
theorem B1853033 : Blo 1234435 1853033 := bstep (se 2 (by rfl) ⟨694887, by rfl⟩ : syracuseStep 1853033 = 1389775) B1389775
theorem B2344555 : Blo 1234435 2344555 := bstep (se 1 (by rfl) ⟨1758416, by rfl⟩ : syracuseStep 2344555 = 3516833) B3516833
theorem B60073595 : Blo 1234435 60073595 := bstep (se 1 (by rfl) ⟨45055196, by rfl⟩ : syracuseStep 60073595 = 90110393) B90110393
theorem B650200765 : Blo 1234435 650200765 := bstep (se 3 (by rfl) ⟨121912643, by rfl⟩ : syracuseStep 650200765 = 243825287) B243825287
theorem B2344639 : Blo 1234435 2344639 := bstep (se 1 (by rfl) ⟨1758479, by rfl⟩ : syracuseStep 2344639 = 3516959) B3516959
theorem B2778875 : Blo 1234435 2778875 := bstep (se 1 (by rfl) ⟨2084156, by rfl⟩ : syracuseStep 2778875 = 4168313) B4168313
theorem B7038859 : Blo 1234435 7038859 := bstep (se 1 (by rfl) ⟨5279144, by rfl⟩ : syracuseStep 7038859 = 10558289) B10558289
theorem B2344943 : Blo 1234435 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B5933081 : Blo 1234435 5933081 := bstep (se 2 (by rfl) ⟨2224905, by rfl⟩ : syracuseStep 5933081 = 4449811) B4449811
theorem B2779163 : Blo 1234435 2779163 := bstep (se 1 (by rfl) ⟨2084372, by rfl⟩ : syracuseStep 2779163 = 4168745) B4168745
theorem B1853471 : Blo 1234435 1853471 := bstep (se 1 (by rfl) ⟨1390103, by rfl⟩ : syracuseStep 1853471 = 2780207) B2780207
theorem B20039723 : Blo 1234435 20039723 := bstep (se 1 (by rfl) ⟨15029792, by rfl⟩ : syracuseStep 20039723 = 30059585) B30059585
theorem B4171823 : Blo 1234435 4171823 := bstep (se 1 (by rfl) ⟨3128867, by rfl⟩ : syracuseStep 4171823 = 6257735) B6257735
theorem B10692713 : Blo 1234435 10692713 := bstep (se 2 (by rfl) ⟨4009767, by rfl⟩ : syracuseStep 10692713 = 8019535) B8019535
theorem B3516605 : Blo 1234435 3516605 := bstep (se 3 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 3516605 = 1318727) B1318727
theorem B1853663 : Blo 1234435 1853663 := bstep (se 1 (by rfl) ⟨1390247, by rfl⟩ : syracuseStep 1853663 = 2780495) B2780495
theorem B1853723 : Blo 1234435 1853723 := bstep (se 1 (by rfl) ⟨1390292, by rfl⟩ : syracuseStep 1853723 = 2780585) B2780585
theorem B2083151 : Blo 1234435 2083151 := bstep (se 1 (by rfl) ⟨1562363, by rfl⟩ : syracuseStep 2083151 = 3124727) B3124727
theorem B10013179 : Blo 1234435 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B10553915 : Blo 1234435 10553915 := bstep (se 1 (by rfl) ⟨7915436, by rfl⟩ : syracuseStep 10553915 = 15830873) B15830873
theorem B1854047 : Blo 1234435 1854047 := bstep (se 1 (by rfl) ⟨1390535, by rfl⟩ : syracuseStep 1854047 = 2781071) B2781071
theorem B1854329 : Blo 1234435 1854329 := bstep (se 2 (by rfl) ⟨695373, by rfl⟩ : syracuseStep 1854329 = 1390747) B1390747
theorem B1854377 : Blo 1234435 1854377 := bstep (se 2 (by rfl) ⟨695391, by rfl⟩ : syracuseStep 1854377 = 1390783) B1390783
theorem B2378747 : Blo 1234435 2378747 := bstep (se 1 (by rfl) ⟨1784060, by rfl⟩ : syracuseStep 2378747 = 3568121) B3568121
theorem B1854527 : Blo 1234435 1854527 := bstep (se 1 (by rfl) ⟨1390895, by rfl⟩ : syracuseStep 1854527 = 2781791) B2781791
theorem B2084015 : Blo 1234435 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B11865467 : Blo 1234435 11865467 := bstep (se 1 (by rfl) ⟨8899100, by rfl⟩ : syracuseStep 11865467 = 17798201) B17798201
theorem B2780639 : Blo 1234435 2780639 := bstep (se 1 (by rfl) ⟨2085479, by rfl⟩ : syracuseStep 2780639 = 4170959) B4170959
theorem B40062559 : Blo 1234435 40062559 := bstep (se 1 (by rfl) ⟨30046919, by rfl⟩ : syracuseStep 40062559 = 60093839) B60093839
theorem B3124919 : Blo 1234435 3124919 := bstep (se 1 (by rfl) ⟨2343689, by rfl⟩ : syracuseStep 3124919 = 4687379) B4687379
theorem B1978039 : Blo 1234435 1978039 := bstep (se 1 (by rfl) ⟨1483529, by rfl⟩ : syracuseStep 1978039 = 2967059) B2967059
theorem B2780855 : Blo 1234435 2780855 := bstep (se 1 (by rfl) ⟨2085641, by rfl⟩ : syracuseStep 2780855 = 4171283) B4171283
theorem B7917335 : Blo 1234435 7917335 := bstep (se 1 (by rfl) ⟨5938001, by rfl⟩ : syracuseStep 7917335 = 11876003) B11876003
theorem B3125375 : Blo 1234435 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B5935427 : Blo 1234435 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B659263859 : Blo 1234435 659263859 := bstep (se 1 (by rfl) ⟨494447894, by rfl⟩ : syracuseStep 659263859 = 988895789) B988895789
theorem B4690295 : Blo 1234435 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B2781647 : Blo 1234435 2781647 := bstep (se 1 (by rfl) ⟨2086235, by rfl⟩ : syracuseStep 2781647 = 4172471) B4172471
theorem B6255143 : Blo 1234435 6255143 := bstep (se 1 (by rfl) ⟨4691357, by rfl⟩ : syracuseStep 6255143 = 9382715) B9382715
theorem B1389307 : Blo 1234435 1389307 := bstep (se 1 (by rfl) ⟨1041980, by rfl⟩ : syracuseStep 1389307 = 2083961) B2083961
theorem B10294141 : Blo 1234435 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B11269057 : Blo 1234435 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B25359313 : Blo 1234435 25359313 := bstep (se 2 (by rfl) ⟨9509742, by rfl⟩ : syracuseStep 25359313 = 19019485) B19019485
theorem B4166639 : Blo 1234435 4166639 := bstep (se 1 (by rfl) ⟨3124979, by rfl⟩ : syracuseStep 4166639 = 6249959) B6249959
theorem B2085871 : Blo 1234435 2085871 := bstep (se 1 (by rfl) ⟨1564403, by rfl⟩ : syracuseStep 2085871 = 3128807) B3128807
theorem B23761997 : Blo 1234435 23761997 := bstep (se 3 (by rfl) ⟨4455374, by rfl⟩ : syracuseStep 23761997 = 8910749) B8910749
theorem B10556513 : Blo 1234435 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B3126377 : Blo 1234435 3126377 := bstep (se 2 (by rfl) ⟨1172391, by rfl⟩ : syracuseStep 3126377 = 2344783) B2344783
theorem B5420251 : Blo 1234435 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B7910621 : Blo 1234435 7910621 := bstep (se 3 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 7910621 = 2966483) B2966483
theorem B4691267 : Blo 1234435 4691267 := bstep (se 1 (by rfl) ⟨3518450, by rfl⟩ : syracuseStep 4691267 = 7036901) B7036901
theorem B2897363 : Blo 1234435 2897363 := bstep (se 1 (by rfl) ⟨2173022, by rfl⟩ : syracuseStep 2897363 = 4346045) B4346045
theorem B1390063 : Blo 1234435 1390063 := bstep (se 1 (by rfl) ⟨1042547, by rfl⟩ : syracuseStep 1390063 = 2085095) B2085095
theorem B1234523 : Blo 1234435 1234523 := bstep (se 1 (by rfl) ⟨925892, by rfl⟩ : syracuseStep 1234523 = 1851785) B1851785
theorem B1390171 : Blo 1234435 1390171 := bstep (se 1 (by rfl) ⟨1042628, by rfl⟩ : syracuseStep 1390171 = 2085257) B2085257
theorem B1234587 : Blo 1234435 1234587 := bstep (se 1 (by rfl) ⟨925940, by rfl⟩ : syracuseStep 1234587 = 1851881) B1851881
theorem B1234671 : Blo 1234435 1234671 := bstep (se 1 (by rfl) ⟨926003, by rfl⟩ : syracuseStep 1234671 = 1852007) B1852007
theorem B1234759 : Blo 1234435 1234759 := bstep (se 1 (by rfl) ⟨926069, by rfl⟩ : syracuseStep 1234759 = 1852139) B1852139
theorem B1234779 : Blo 1234435 1234779 := bstep (se 1 (by rfl) ⟨926084, by rfl⟩ : syracuseStep 1234779 = 1852169) B1852169
theorem B1390459 : Blo 1234435 1390459 := bstep (se 1 (by rfl) ⟨1042844, by rfl⟩ : syracuseStep 1390459 = 2085689) B2085689
theorem B5715841 : Blo 1234435 5715841 := bstep (se 2 (by rfl) ⟨2143440, by rfl⟩ : syracuseStep 5715841 = 4286881) B4286881
theorem B1234847 : Blo 1234435 1234847 := bstep (se 1 (by rfl) ⟨926135, by rfl⟩ : syracuseStep 1234847 = 1852271) B1852271
theorem B1390495 : Blo 1234435 1390495 := bstep (se 1 (by rfl) ⟨1042871, by rfl⟩ : syracuseStep 1390495 = 2085743) B2085743
theorem B1235015 : Blo 1234435 1235015 := bstep (se 1 (by rfl) ⟨926261, by rfl⟩ : syracuseStep 1235015 = 1852523) B1852523
theorem B1235175 : Blo 1234435 1235175 := bstep (se 1 (by rfl) ⟨926381, by rfl⟩ : syracuseStep 1235175 = 1852763) B1852763
theorem B3127531 : Blo 1234435 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B1235359 : Blo 1234435 1235359 := bstep (se 1 (by rfl) ⟨926519, by rfl⟩ : syracuseStep 1235359 = 1853039) B1853039
theorem B1235407 : Blo 1234435 1235407 := bstep (se 1 (by rfl) ⟨926555, by rfl⟩ : syracuseStep 1235407 = 1853111) B1853111
theorem B1235431 : Blo 1234435 1235431 := bstep (se 1 (by rfl) ⟨926573, by rfl⟩ : syracuseStep 1235431 = 1853147) B1853147
theorem B1235547 : Blo 1234435 1235547 := bstep (se 1 (by rfl) ⟨926660, by rfl⟩ : syracuseStep 1235547 = 1853321) B1853321
theorem B6257249 : Blo 1234435 6257249 := bstep (se 2 (by rfl) ⟨2346468, by rfl⟩ : syracuseStep 6257249 = 4692937) B4692937
theorem B1235615 : Blo 1234435 1235615 := bstep (se 1 (by rfl) ⟨926711, by rfl⟩ : syracuseStep 1235615 = 1853423) B1853423
theorem B3127967 : Blo 1234435 3127967 := bstep (se 1 (by rfl) ⟨2345975, by rfl⟩ : syracuseStep 3127967 = 4691951) B4691951
theorem B5937887 : Blo 1234435 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B1235783 : Blo 1234435 1235783 := bstep (se 1 (by rfl) ⟨926837, by rfl⟩ : syracuseStep 1235783 = 1853675) B1853675
theorem B1235823 : Blo 1234435 1235823 := bstep (se 1 (by rfl) ⟨926867, by rfl⟩ : syracuseStep 1235823 = 1853735) B1853735
theorem B1235879 : Blo 1234435 1235879 := bstep (se 1 (by rfl) ⟨926909, by rfl⟩ : syracuseStep 1235879 = 1853819) B1853819
theorem B5938115 : Blo 1234435 5938115 := bstep (se 1 (by rfl) ⟨4453586, by rfl⟩ : syracuseStep 5938115 = 8907173) B8907173
theorem B3169259 : Blo 1234435 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B1236059 : Blo 1234435 1236059 := bstep (se 1 (by rfl) ⟨927044, by rfl⟩ : syracuseStep 1236059 = 1854089) B1854089
theorem B1236175 : Blo 1234435 1236175 := bstep (se 1 (by rfl) ⟨927131, by rfl⟩ : syracuseStep 1236175 = 1854263) B1854263
theorem B1236199 : Blo 1234435 1236199 := bstep (se 1 (by rfl) ⟨927149, by rfl⟩ : syracuseStep 1236199 = 1854299) B1854299
theorem B4693241 : Blo 1234435 4693241 := bstep (se 2 (by rfl) ⟨1759965, by rfl⟩ : syracuseStep 4693241 = 3519931) B3519931
theorem B1236295 : Blo 1234435 1236295 := bstep (se 1 (by rfl) ⟨927221, by rfl⟩ : syracuseStep 1236295 = 1854443) B1854443
theorem B7511393 : Blo 1234435 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B6258059 : Blo 1234435 6258059 := bstep (se 1 (by rfl) ⟨4693544, by rfl⟩ : syracuseStep 6258059 = 9387089) B9387089
theorem B4693423 : Blo 1234435 4693423 := bstep (se 1 (by rfl) ⟨3520067, by rfl⟩ : syracuseStep 4693423 = 7040135) B7040135
theorem B1236431 : Blo 1234435 1236431 := bstep (se 1 (by rfl) ⟨927323, by rfl⟩ : syracuseStep 1236431 = 1854647) B1854647
theorem B5013011 : Blo 1234435 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B3128939 : Blo 1234435 3128939 := bstep (se 1 (by rfl) ⟨2346704, by rfl⟩ : syracuseStep 3128939 = 4693409) B4693409
theorem B3341999 : Blo 1234435 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B3956951 : Blo 1234435 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B439509239 : Blo 1234435 439509239 := bstep (se 1 (by rfl) ⟨329631929, by rfl⟩ : syracuseStep 439509239 = 659263859) B659263859
theorem B4170041 : Blo 1234435 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B4170095 : Blo 1234435 4170095 := bstep (se 1 (by rfl) ⟨3127571, by rfl⟩ : syracuseStep 4170095 = 6255143) B6255143
theorem B2777759 : Blo 1234435 2777759 := bstep (se 1 (by rfl) ⟨2083319, by rfl⟩ : syracuseStep 2777759 = 4166639) B4166639
theorem B7037675 : Blo 1234435 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B5276447 : Blo 1234435 5276447 := bstep (se 1 (by rfl) ⟨3957335, by rfl⟩ : syracuseStep 5276447 = 7914671) B7914671
theorem B1852283 : Blo 1234435 1852283 := bstep (se 1 (by rfl) ⟨1389212, by rfl⟩ : syracuseStep 1852283 = 2778425) B2778425
theorem B1852409 : Blo 1234435 1852409 := bstep (se 2 (by rfl) ⟨694653, by rfl⟩ : syracuseStep 1852409 = 1389307) B1389307
theorem B1852463 : Blo 1234435 1852463 := bstep (se 1 (by rfl) ⟨1389347, by rfl⟩ : syracuseStep 1852463 = 2778695) B2778695
theorem B1852583 : Blo 1234435 1852583 := bstep (se 1 (by rfl) ⟨1389437, by rfl⟩ : syracuseStep 1852583 = 2778875) B2778875
theorem B15025409 : Blo 1234435 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B1852775 : Blo 1234435 1852775 := bstep (se 1 (by rfl) ⟨1389581, by rfl⟩ : syracuseStep 1852775 = 2779163) B2779163
theorem B2344403 : Blo 1234435 2344403 := bstep (se 1 (by rfl) ⟨1758302, by rfl⟩ : syracuseStep 2344403 = 3516605) B3516605
theorem B7227001 : Blo 1234435 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B4171499 : Blo 1234435 4171499 := bstep (se 1 (by rfl) ⟨3128624, by rfl⟩ : syracuseStep 4171499 = 6257249) B6257249
theorem B3958591 : Blo 1234435 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B1853417 : Blo 1234435 1853417 := bstep (se 2 (by rfl) ⟨695031, by rfl⟩ : syracuseStep 1853417 = 1390063) B1390063
theorem B1853561 : Blo 1234435 1853561 := bstep (se 2 (by rfl) ⟨695085, by rfl⟩ : syracuseStep 1853561 = 1390171) B1390171
theorem B5007595 : Blo 1234435 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B4172039 : Blo 1234435 4172039 := bstep (se 1 (by rfl) ⟨3129029, by rfl⟩ : syracuseStep 4172039 = 6258059) B6258059
theorem B1853759 : Blo 1234435 1853759 := bstep (se 1 (by rfl) ⟨1390319, by rfl⟩ : syracuseStep 1853759 = 2780639) B2780639
theorem B2083279 : Blo 1234435 2083279 := bstep (se 1 (by rfl) ⟨1562459, by rfl⟩ : syracuseStep 2083279 = 3124919) B3124919
theorem B1853903 : Blo 1234435 1853903 := bstep (se 1 (by rfl) ⟨1390427, by rfl⟩ : syracuseStep 1853903 = 2780855) B2780855
theorem B1853945 : Blo 1234435 1853945 := bstep (se 2 (by rfl) ⟨695229, by rfl⟩ : syracuseStep 1853945 = 1390459) B1390459
theorem B7621121 : Blo 1234435 7621121 := bstep (se 2 (by rfl) ⟨2857920, by rfl⟩ : syracuseStep 7621121 = 5715841) B5715841
theorem B5278223 : Blo 1234435 5278223 := bstep (se 1 (by rfl) ⟨3958667, by rfl⟩ : syracuseStep 5278223 = 7917335) B7917335
theorem B1853993 : Blo 1234435 1853993 := bstep (se 2 (by rfl) ⟨695247, by rfl⟩ : syracuseStep 1853993 = 1390495) B1390495
theorem B20294327 : Blo 1234435 20294327 := bstep (se 1 (by rfl) ⟨15220745, by rfl⟩ : syracuseStep 20294327 = 30441491) B30441491
theorem B47475395 : Blo 1234435 47475395 := bstep (se 1 (by rfl) ⟨35606546, by rfl⟩ : syracuseStep 47475395 = 71213093) B71213093
theorem B2083583 : Blo 1234435 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B1854431 : Blo 1234435 1854431 := bstep (se 1 (by rfl) ⟨1390823, by rfl⟩ : syracuseStep 1854431 = 2781647) B2781647
theorem B2084251 : Blo 1234435 2084251 := bstep (se 1 (by rfl) ⟨1563188, by rfl⟩ : syracuseStep 2084251 = 3126377) B3126377
theorem B33811991 : Blo 1234435 33811991 := bstep (se 1 (by rfl) ⟨25358993, by rfl⟩ : syracuseStep 33811991 = 50717987) B50717987
theorem B8023643 : Blo 1234435 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B2780891 : Blo 1234435 2780891 := bstep (se 1 (by rfl) ⟨2085668, by rfl⟩ : syracuseStep 2780891 = 4171337) B4171337
theorem B3960539 : Blo 1234435 3960539 := bstep (se 1 (by rfl) ⟨2970404, by rfl⟩ : syracuseStep 3960539 = 5940809) B5940809
theorem B13725521 : Blo 1234435 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B33812417 : Blo 1234435 33812417 := bstep (se 2 (by rfl) ⟨12679656, by rfl⟩ : syracuseStep 33812417 = 25359313) B25359313
theorem B2781161 : Blo 1234435 2781161 := bstep (se 2 (by rfl) ⟨1042935, by rfl⟩ : syracuseStep 2781161 = 2085871) B2085871
theorem B2781215 : Blo 1234435 2781215 := bstep (se 1 (by rfl) ⟨2085911, by rfl⟩ : syracuseStep 2781215 = 4171823) B4171823
theorem B1388767 : Blo 1234435 1388767 := bstep (se 1 (by rfl) ⟨1041575, by rfl⟩ : syracuseStep 1388767 = 2083151) B2083151
theorem B2085311 : Blo 1234435 2085311 := bstep (se 1 (by rfl) ⟨1563983, by rfl⟩ : syracuseStep 2085311 = 3127967) B3127967
theorem B1585831 : Blo 1234435 1585831 := bstep (se 1 (by rfl) ⟨1189373, by rfl⟩ : syracuseStep 1585831 = 2378747) B2378747
theorem B1389343 : Blo 1234435 1389343 := bstep (se 1 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 1389343 = 2084015) B2084015
theorem B53416745 : Blo 1234435 53416745 := bstep (se 2 (by rfl) ⟨20031279, by rfl⟩ : syracuseStep 53416745 = 40062559) B40062559
theorem B3126073 : Blo 1234435 3126073 := bstep (se 2 (by rfl) ⟨1172277, by rfl⟩ : syracuseStep 3126073 = 2344555) B2344555
theorem B7910311 : Blo 1234435 7910311 := bstep (se 1 (by rfl) ⟨5932733, by rfl⟩ : syracuseStep 7910311 = 11865467) B11865467
theorem B3126185 : Blo 1234435 3126185 := bstep (se 2 (by rfl) ⟨1172319, by rfl⟩ : syracuseStep 3126185 = 2344639) B2344639
theorem B2085959 : Blo 1234435 2085959 := bstep (se 1 (by rfl) ⟨1564469, by rfl⟩ : syracuseStep 2085959 = 3128939) B3128939
theorem B9385145 : Blo 1234435 9385145 := bstep (se 2 (by rfl) ⟨3519429, by rfl⟩ : syracuseStep 9385145 = 7038859) B7038859
theorem B18044315 : Blo 1234435 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B1234463 : Blo 1234435 1234463 := bstep (se 1 (by rfl) ⟨925847, by rfl⟩ : syracuseStep 1234463 = 1851695) B1851695
theorem B3126863 : Blo 1234435 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B28513901 : Blo 1234435 28513901 := bstep (se 3 (by rfl) ⟨5346356, by rfl⟩ : syracuseStep 28513901 = 10692713) B10692713
theorem B1234623 : Blo 1234435 1234623 := bstep (se 1 (by rfl) ⟨925967, by rfl⟩ : syracuseStep 1234623 = 1851935) B1851935
theorem B30062501 : Blo 1234435 30062501 := bstep (se 4 (by rfl) ⟨2818359, by rfl⟩ : syracuseStep 30062501 = 5636719) B5636719
theorem B13350905 : Blo 1234435 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B15841331 : Blo 1234435 15841331 := bstep (se 1 (by rfl) ⟨11880998, by rfl⟩ : syracuseStep 15841331 = 23761997) B23761997
theorem B1235071 : Blo 1234435 1235071 := bstep (se 1 (by rfl) ⟨926303, by rfl⟩ : syracuseStep 1235071 = 1852607) B1852607
theorem B5273747 : Blo 1234435 5273747 := bstep (se 1 (by rfl) ⟨3955310, by rfl⟩ : syracuseStep 5273747 = 7910621) B7910621
theorem B3127511 : Blo 1234435 3127511 := bstep (se 1 (by rfl) ⟨2345633, by rfl⟩ : syracuseStep 3127511 = 4691267) B4691267
theorem B1235167 : Blo 1234435 1235167 := bstep (se 1 (by rfl) ⟨926375, by rfl⟩ : syracuseStep 1235167 = 1852751) B1852751
theorem B1235227 : Blo 1234435 1235227 := bstep (se 1 (by rfl) ⟨926420, by rfl⟩ : syracuseStep 1235227 = 1852841) B1852841
theorem B10549541 : Blo 1234435 10549541 := bstep (se 4 (by rfl) ⟨989019, by rfl⟩ : syracuseStep 10549541 = 1978039) B1978039
theorem B1931575 : Blo 1234435 1931575 := bstep (se 1 (by rfl) ⟨1448681, by rfl⟩ : syracuseStep 1931575 = 2897363) B2897363
theorem B1235327 : Blo 1234435 1235327 := bstep (se 1 (by rfl) ⟨926495, by rfl⟩ : syracuseStep 1235327 = 1852991) B1852991
theorem B1235355 : Blo 1234435 1235355 := bstep (se 1 (by rfl) ⟨926516, by rfl⟩ : syracuseStep 1235355 = 1853033) B1853033
theorem B40049063 : Blo 1234435 40049063 := bstep (se 1 (by rfl) ⟨30036797, by rfl⟩ : syracuseStep 40049063 = 60073595) B60073595
theorem B1563295 : Blo 1234435 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B3955387 : Blo 1234435 3955387 := bstep (se 1 (by rfl) ⟨2966540, by rfl⟩ : syracuseStep 3955387 = 5933081) B5933081
theorem B1235647 : Blo 1234435 1235647 := bstep (se 1 (by rfl) ⟨926735, by rfl⟩ : syracuseStep 1235647 = 1853471) B1853471
theorem B13359815 : Blo 1234435 13359815 := bstep (se 1 (by rfl) ⟨10019861, by rfl⟩ : syracuseStep 13359815 = 20039723) B20039723
theorem B1235775 : Blo 1234435 1235775 := bstep (se 1 (by rfl) ⟨926831, by rfl⟩ : syracuseStep 1235775 = 1853663) B1853663
theorem B1235815 : Blo 1234435 1235815 := bstep (se 1 (by rfl) ⟨926861, by rfl⟩ : syracuseStep 1235815 = 1853723) B1853723
theorem B7035943 : Blo 1234435 7035943 := bstep (se 1 (by rfl) ⟨5276957, by rfl⟩ : syracuseStep 7035943 = 10553915) B10553915
theorem B1236031 : Blo 1234435 1236031 := bstep (se 1 (by rfl) ⟨927023, by rfl⟩ : syracuseStep 1236031 = 1854047) B1854047
theorem B6257897 : Blo 1234435 6257897 := bstep (se 2 (by rfl) ⟨2346711, by rfl⟩ : syracuseStep 6257897 = 4693423) B4693423
theorem B1236219 : Blo 1234435 1236219 := bstep (se 1 (by rfl) ⟨927164, by rfl⟩ : syracuseStep 1236219 = 1854329) B1854329
theorem B1236251 : Blo 1234435 1236251 := bstep (se 1 (by rfl) ⟨927188, by rfl⟩ : syracuseStep 1236251 = 1854377) B1854377
theorem B2112839 : Blo 1234435 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B1236351 : Blo 1234435 1236351 := bstep (se 1 (by rfl) ⟨927263, by rfl⟩ : syracuseStep 1236351 = 1854527) B1854527
theorem B3128827 : Blo 1234435 3128827 := bstep (se 1 (by rfl) ⟨2346620, by rfl⟩ : syracuseStep 3128827 = 4693241) B4693241
theorem B866934353 : Blo 1234435 866934353 := bstep (se 2 (by rfl) ⟨325100382, by rfl⟩ : syracuseStep 866934353 = 650200765) B650200765
theorem B3342007 : Blo 1234435 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B2227999 : Blo 1234435 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B15834973 : Blo 1234435 15834973 := bstep (se 3 (by rfl) ⟨2969057, by rfl⟩ : syracuseStep 15834973 = 5938115) B5938115
theorem B2637967 : Blo 1234435 2637967 := bstep (se 1 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 2637967 = 3956951) B3956951
theorem B1851689 : Blo 1234435 1851689 := bstep (se 2 (by rfl) ⟨694383, by rfl⟩ : syracuseStep 1851689 = 1388767) B1388767
theorem B6676793 : Blo 1234435 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B1851839 : Blo 1234435 1851839 := bstep (se 1 (by rfl) ⟨1388879, by rfl⟩ : syracuseStep 1851839 = 2777759) B2777759
theorem B35611163 : Blo 1234435 35611163 := bstep (se 1 (by rfl) ⟨26708372, by rfl⟩ : syracuseStep 35611163 = 53416745) B53416745
theorem B2777705 : Blo 1234435 2777705 := bstep (se 2 (by rfl) ⟨1041639, by rfl⟩ : syracuseStep 2777705 = 2083279) B2083279
theorem B38544005 : Blo 1234435 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B2114441 : Blo 1234435 2114441 := bstep (se 2 (by rfl) ⟨792915, by rfl⟩ : syracuseStep 2114441 = 1585831) B1585831
theorem B1852457 : Blo 1234435 1852457 := bstep (se 2 (by rfl) ⟨694671, by rfl⟩ : syracuseStep 1852457 = 1389343) B1389343
theorem B6251741 : Blo 1234435 6251741 := bstep (se 3 (by rfl) ⟨1172201, by rfl⟩ : syracuseStep 6251741 = 2344403) B2344403
theorem B10560887 : Blo 1234435 10560887 := bstep (se 1 (by rfl) ⟨7920665, by rfl⟩ : syracuseStep 10560887 = 15841331) B15841331
theorem B9381257 : Blo 1234435 9381257 := bstep (se 2 (by rfl) ⟨3517971, by rfl⟩ : syracuseStep 9381257 = 7035943) B7035943
theorem B3515831 : Blo 1234435 3515831 := bstep (se 1 (by rfl) ⟨2636873, by rfl⟩ : syracuseStep 3515831 = 5273747) B5273747
theorem B26699375 : Blo 1234435 26699375 := bstep (se 1 (by rfl) ⟨20024531, by rfl⟩ : syracuseStep 26699375 = 40049063) B40049063
theorem B5080747 : Blo 1234435 5080747 := bstep (se 1 (by rfl) ⟨3810560, by rfl⟩ : syracuseStep 5080747 = 7621121) B7621121
theorem B8906543 : Blo 1234435 8906543 := bstep (se 1 (by rfl) ⟨6679907, by rfl⟩ : syracuseStep 8906543 = 13359815) B13359815
theorem B54118205 : Blo 1234435 54118205 := bstep (se 3 (by rfl) ⟨10147163, by rfl⟩ : syracuseStep 54118205 = 20294327) B20294327
theorem B2779001 : Blo 1234435 2779001 := bstep (se 2 (by rfl) ⟨1042125, by rfl⟩ : syracuseStep 2779001 = 2084251) B2084251
theorem B4171769 : Blo 1234435 4171769 := bstep (se 2 (by rfl) ⟨1564413, by rfl⟩ : syracuseStep 4171769 = 3128827) B3128827
theorem B4171931 : Blo 1234435 4171931 := bstep (se 1 (by rfl) ⟨3128948, by rfl⟩ : syracuseStep 4171931 = 6257897) B6257897
theorem B577956235 : Blo 1234435 577956235 := bstep (se 1 (by rfl) ⟨433467176, by rfl⟩ : syracuseStep 577956235 = 866934353) B866934353
theorem B5278121 : Blo 1234435 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B21113297 : Blo 1234435 21113297 := bstep (se 2 (by rfl) ⟨7917486, by rfl⟩ : syracuseStep 21113297 = 15834973) B15834973
theorem B1853927 : Blo 1234435 1853927 := bstep (se 1 (by rfl) ⟨1390445, by rfl⟩ : syracuseStep 1853927 = 2780891) B2780891
theorem B2640359 : Blo 1234435 2640359 := bstep (se 1 (by rfl) ⟨1980269, by rfl⟩ : syracuseStep 2640359 = 3960539) B3960539
theorem B1854107 : Blo 1234435 1854107 := bstep (se 1 (by rfl) ⟨1390580, by rfl⟩ : syracuseStep 1854107 = 2781161) B2781161
theorem B1854143 : Blo 1234435 1854143 := bstep (se 1 (by rfl) ⟨1390607, by rfl⟩ : syracuseStep 1854143 = 2781215) B2781215
theorem B293006159 : Blo 1234435 293006159 := bstep (se 1 (by rfl) ⟨219754619, by rfl⟩ : syracuseStep 293006159 = 439509239) B439509239
theorem B2780027 : Blo 1234435 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B2780063 : Blo 1234435 2780063 := bstep (se 1 (by rfl) ⟨2085047, by rfl⟩ : syracuseStep 2780063 = 4170095) B4170095
theorem B2575433 : Blo 1234435 2575433 := bstep (se 2 (by rfl) ⟨965787, by rfl⟩ : syracuseStep 2575433 = 1931575) B1931575
theorem B3517631 : Blo 1234435 3517631 := bstep (se 1 (by rfl) ⟨2638223, by rfl⟩ : syracuseStep 3517631 = 5276447) B5276447
theorem B2084123 : Blo 1234435 2084123 := bstep (se 1 (by rfl) ⟨1563092, by rfl⟩ : syracuseStep 2084123 = 3126185) B3126185
theorem B2084393 : Blo 1234435 2084393 := bstep (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) B1563295
theorem B12029543 : Blo 1234435 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B2084575 : Blo 1234435 2084575 := bstep (se 1 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 2084575 = 3126863) B3126863
theorem B2780999 : Blo 1234435 2780999 := bstep (se 1 (by rfl) ⟨2085749, by rfl⟩ : syracuseStep 2780999 = 4171499) B4171499
theorem B10547081 : Blo 1234435 10547081 := bstep (se 2 (by rfl) ⟨3955155, by rfl⟩ : syracuseStep 10547081 = 7910311) B7910311
theorem B20041667 : Blo 1234435 20041667 := bstep (se 1 (by rfl) ⟨15031250, by rfl⟩ : syracuseStep 20041667 = 30062501) B30062501
theorem B8900603 : Blo 1234435 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B2085007 : Blo 1234435 2085007 := bstep (se 1 (by rfl) ⟨1563755, by rfl⟩ : syracuseStep 2085007 = 3127511) B3127511
theorem B2781359 : Blo 1234435 2781359 := bstep (se 1 (by rfl) ⟨2086019, by rfl⟩ : syracuseStep 2781359 = 4172039) B4172039
theorem B7033027 : Blo 1234435 7033027 := bstep (se 1 (by rfl) ⟨5274770, by rfl⟩ : syracuseStep 7033027 = 10549541) B10549541
theorem B3518815 : Blo 1234435 3518815 := bstep (se 1 (by rfl) ⟨2639111, by rfl⟩ : syracuseStep 3518815 = 5278223) B5278223
theorem B31650263 : Blo 1234435 31650263 := bstep (se 1 (by rfl) ⟨23737697, by rfl⟩ : syracuseStep 31650263 = 47475395) B47475395
theorem B1389055 : Blo 1234435 1389055 := bstep (se 1 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 1389055 = 2083583) B2083583
theorem B22541327 : Blo 1234435 22541327 := bstep (se 1 (by rfl) ⟨16905995, by rfl⟩ : syracuseStep 22541327 = 33811991) B33811991
theorem B2970665 : Blo 1234435 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B22541611 : Blo 1234435 22541611 := bstep (se 1 (by rfl) ⟨16906208, by rfl⟩ : syracuseStep 22541611 = 33812417) B33812417
theorem B1390207 : Blo 1234435 1390207 := bstep (se 1 (by rfl) ⟨1042655, by rfl⟩ : syracuseStep 1390207 = 2085311) B2085311
theorem B4691783 : Blo 1234435 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B1234855 : Blo 1234435 1234855 := bstep (se 1 (by rfl) ⟨926141, by rfl⟩ : syracuseStep 1234855 = 1852283) B1852283
theorem B1234939 : Blo 1234435 1234939 := bstep (se 1 (by rfl) ⟨926204, by rfl⟩ : syracuseStep 1234939 = 1852409) B1852409
theorem B1234975 : Blo 1234435 1234975 := bstep (se 1 (by rfl) ⟨926231, by rfl⟩ : syracuseStep 1234975 = 1852463) B1852463
theorem B1390639 : Blo 1234435 1390639 := bstep (se 1 (by rfl) ⟨1042979, by rfl⟩ : syracuseStep 1390639 = 2085959) B2085959
theorem B1235055 : Blo 1234435 1235055 := bstep (se 1 (by rfl) ⟨926291, by rfl⟩ : syracuseStep 1235055 = 1852583) B1852583
theorem B6256763 : Blo 1234435 6256763 := bstep (se 1 (by rfl) ⟨4692572, by rfl⟩ : syracuseStep 6256763 = 9385145) B9385145
theorem B10016939 : Blo 1234435 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1235183 : Blo 1234435 1235183 := bstep (se 1 (by rfl) ⟨926387, by rfl⟩ : syracuseStep 1235183 = 1852775) B1852775
theorem B5273849 : Blo 1234435 5273849 := bstep (se 2 (by rfl) ⟨1977693, by rfl⟩ : syracuseStep 5273849 = 3955387) B3955387
theorem B4168097 : Blo 1234435 4168097 := bstep (se 2 (by rfl) ⟨1563036, by rfl⟩ : syracuseStep 4168097 = 3126073) B3126073
theorem B1235611 : Blo 1234435 1235611 := bstep (se 1 (by rfl) ⟨926708, by rfl⟩ : syracuseStep 1235611 = 1853417) B1853417
theorem B1235707 : Blo 1234435 1235707 := bstep (se 1 (by rfl) ⟨926780, by rfl⟩ : syracuseStep 1235707 = 1853561) B1853561
theorem B1235839 : Blo 1234435 1235839 := bstep (se 1 (by rfl) ⟨926879, by rfl⟩ : syracuseStep 1235839 = 1853759) B1853759
theorem B76037069 : Blo 1234435 76037069 := bstep (se 3 (by rfl) ⟨14256950, by rfl⟩ : syracuseStep 76037069 = 28513901) B28513901
theorem B1235935 : Blo 1234435 1235935 := bstep (se 1 (by rfl) ⟨926951, by rfl⟩ : syracuseStep 1235935 = 1853903) B1853903
theorem B1235963 : Blo 1234435 1235963 := bstep (se 1 (by rfl) ⟨926972, by rfl⟩ : syracuseStep 1235963 = 1853945) B1853945
theorem B1235995 : Blo 1234435 1235995 := bstep (se 1 (by rfl) ⟨926996, by rfl⟩ : syracuseStep 1235995 = 1853993) B1853993
theorem B1236287 : Blo 1234435 1236287 := bstep (se 1 (by rfl) ⟨927215, by rfl⟩ : syracuseStep 1236287 = 1854431) B1854431
theorem B1408559 : Blo 1234435 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B4456009 : Blo 1234435 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B5349095 : Blo 1234435 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B9150347 : Blo 1234435 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B23740775 : Blo 1234435 23740775 := bstep (se 1 (by rfl) ⟨17805581, by rfl⟩ : syracuseStep 23740775 = 35611163) B35611163
theorem B1851803 : Blo 1234435 1851803 := bstep (se 1 (by rfl) ⟨1388852, by rfl⟩ : syracuseStep 1851803 = 2777705) B2777705
theorem B15024629 : Blo 1234435 15024629 := bstep (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) B1408559
theorem B1409627 : Blo 1234435 1409627 := bstep (se 1 (by rfl) ⟨1057220, by rfl⟩ : syracuseStep 1409627 = 2114441) B2114441
theorem B1852073 : Blo 1234435 1852073 := bstep (se 2 (by rfl) ⟨694527, by rfl⟩ : syracuseStep 1852073 = 1389055) B1389055
theorem B2343887 : Blo 1234435 2343887 := bstep (se 1 (by rfl) ⟨1757915, by rfl⟩ : syracuseStep 2343887 = 3515831) B3515831
theorem B36078803 : Blo 1234435 36078803 := bstep (se 1 (by rfl) ⟨27059102, by rfl⟩ : syracuseStep 36078803 = 54118205) B54118205
theorem B1852667 : Blo 1234435 1852667 := bstep (se 1 (by rfl) ⟨1389500, by rfl⟩ : syracuseStep 1852667 = 2779001) B2779001
theorem B4171175 : Blo 1234435 4171175 := bstep (se 1 (by rfl) ⟨3128381, by rfl⟩ : syracuseStep 4171175 = 6256763) B6256763
theorem B6677959 : Blo 1234435 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B3515899 : Blo 1234435 3515899 := bstep (se 1 (by rfl) ⟨2636924, by rfl⟩ : syracuseStep 3515899 = 5273849) B5273849
theorem B2778731 : Blo 1234435 2778731 := bstep (se 1 (by rfl) ⟨2084048, by rfl⟩ : syracuseStep 2778731 = 4168097) B4168097
theorem B14075531 : Blo 1234435 14075531 := bstep (se 1 (by rfl) ⟨10556648, by rfl⟩ : syracuseStep 14075531 = 21113297) B21113297
theorem B1853351 : Blo 1234435 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B1853375 : Blo 1234435 1853375 := bstep (se 1 (by rfl) ⟨1390031, by rfl⟩ : syracuseStep 1853375 = 2780063) B2780063
theorem B5941345 : Blo 1234435 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B2345087 : Blo 1234435 2345087 := bstep (se 1 (by rfl) ⟨1758815, by rfl⟩ : syracuseStep 2345087 = 3517631) B3517631
theorem B1853609 : Blo 1234435 1853609 := bstep (se 2 (by rfl) ⟨695103, by rfl⟩ : syracuseStep 1853609 = 1390207) B1390207
theorem B2779433 : Blo 1234435 2779433 := bstep (se 2 (by rfl) ⟨1042287, by rfl⟩ : syracuseStep 2779433 = 2084575) B2084575
theorem B3566063 : Blo 1234435 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B1853999 : Blo 1234435 1853999 := bstep (se 1 (by rfl) ⟨1390499, by rfl⟩ : syracuseStep 1853999 = 2780999) B2780999
theorem B7031387 : Blo 1234435 7031387 := bstep (se 1 (by rfl) ⟨5273540, by rfl⟩ : syracuseStep 7031387 = 10547081) B10547081
theorem B5933735 : Blo 1234435 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B1854185 : Blo 1234435 1854185 := bstep (se 2 (by rfl) ⟨695319, by rfl⟩ : syracuseStep 1854185 = 1390639) B1390639
theorem B1854239 : Blo 1234435 1854239 := bstep (se 1 (by rfl) ⟨1390679, by rfl⟩ : syracuseStep 1854239 = 2781359) B2781359
theorem B3517289 : Blo 1234435 3517289 := bstep (se 2 (by rfl) ⟨1318983, by rfl⟩ : syracuseStep 3517289 = 2637967) B2637967
theorem B2780009 : Blo 1234435 2780009 := bstep (se 2 (by rfl) ⟨1042503, by rfl⟩ : syracuseStep 2780009 = 2085007) B2085007
theorem B4451195 : Blo 1234435 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B770608313 : Blo 1234435 770608313 := bstep (se 2 (by rfl) ⟨288978117, by rfl⟩ : syracuseStep 770608313 = 577956235) B577956235
theorem B15027551 : Blo 1234435 15027551 := bstep (se 1 (by rfl) ⟨11270663, by rfl⟩ : syracuseStep 15027551 = 22541327) B22541327
theorem B7040591 : Blo 1234435 7040591 := bstep (se 1 (by rfl) ⟨5280443, by rfl⟩ : syracuseStep 7040591 = 10560887) B10560887
theorem B6254171 : Blo 1234435 6254171 := bstep (se 1 (by rfl) ⟨4690628, by rfl⟩ : syracuseStep 6254171 = 9381257) B9381257
theorem B2781179 : Blo 1234435 2781179 := bstep (se 1 (by rfl) ⟨2085884, by rfl⟩ : syracuseStep 2781179 = 4171769) B4171769
theorem B2781287 : Blo 1234435 2781287 := bstep (se 1 (by rfl) ⟨2085965, by rfl⟩ : syracuseStep 2781287 = 4171931) B4171931
theorem B3518747 : Blo 1234435 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B1716955 : Blo 1234435 1716955 := bstep (se 1 (by rfl) ⟨1287716, by rfl⟩ : syracuseStep 1716955 = 2575433) B2575433
theorem B1389415 : Blo 1234435 1389415 := bstep (se 1 (by rfl) ⟨1042061, by rfl⟩ : syracuseStep 1389415 = 2084123) B2084123
theorem B1389595 : Blo 1234435 1389595 := bstep (se 1 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 1389595 = 2084393) B2084393
theorem B24400925 : Blo 1234435 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B1234459 : Blo 1234435 1234459 := bstep (se 1 (by rfl) ⟨925844, by rfl⟩ : syracuseStep 1234459 = 1851689) B1851689
theorem B9377369 : Blo 1234435 9377369 := bstep (se 2 (by rfl) ⟨3516513, by rfl⟩ : syracuseStep 9377369 = 7033027) B7033027
theorem B1234559 : Blo 1234435 1234559 := bstep (se 1 (by rfl) ⟨925919, by rfl⟩ : syracuseStep 1234559 = 1851839) B1851839
theorem B21100175 : Blo 1234435 21100175 := bstep (se 1 (by rfl) ⟨15825131, by rfl⟩ : syracuseStep 21100175 = 31650263) B31650263
theorem B25696003 : Blo 1234435 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B4691753 : Blo 1234435 4691753 := bstep (se 2 (by rfl) ⟨1759407, by rfl⟩ : syracuseStep 4691753 = 3518815) B3518815
theorem B1234971 : Blo 1234435 1234971 := bstep (se 1 (by rfl) ⟨926228, by rfl⟩ : syracuseStep 1234971 = 1852457) B1852457
theorem B1980443 : Blo 1234435 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B4167827 : Blo 1234435 4167827 := bstep (se 1 (by rfl) ⟨3125870, by rfl⟩ : syracuseStep 4167827 = 6251741) B6251741
theorem B17799583 : Blo 1234435 17799583 := bstep (se 1 (by rfl) ⟨13349687, by rfl⟩ : syracuseStep 17799583 = 26699375) B26699375
theorem B5937695 : Blo 1234435 5937695 := bstep (se 1 (by rfl) ⟨4453271, by rfl⟩ : syracuseStep 5937695 = 8906543) B8906543
theorem B3127855 : Blo 1234435 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B1235951 : Blo 1234435 1235951 := bstep (se 1 (by rfl) ⟨926963, by rfl⟩ : syracuseStep 1235951 = 1853927) B1853927
theorem B1760239 : Blo 1234435 1760239 := bstep (se 1 (by rfl) ⟨1320179, by rfl⟩ : syracuseStep 1760239 = 2640359) B2640359
theorem B30055481 : Blo 1234435 30055481 := bstep (se 2 (by rfl) ⟨11270805, by rfl⟩ : syracuseStep 30055481 = 22541611) B22541611
theorem B1236071 : Blo 1234435 1236071 := bstep (se 1 (by rfl) ⟨927053, by rfl⟩ : syracuseStep 1236071 = 1854107) B1854107
theorem B1236095 : Blo 1234435 1236095 := bstep (se 1 (by rfl) ⟨927071, by rfl⟩ : syracuseStep 1236095 = 1854143) B1854143
theorem B195337439 : Blo 1234435 195337439 := bstep (se 1 (by rfl) ⟨146503079, by rfl⟩ : syracuseStep 195337439 = 293006159) B293006159
theorem B50691379 : Blo 1234435 50691379 := bstep (se 1 (by rfl) ⟨38018534, by rfl⟩ : syracuseStep 50691379 = 76037069) B76037069
theorem B6774329 : Blo 1234435 6774329 := bstep (se 2 (by rfl) ⟨2540373, by rfl⟩ : syracuseStep 6774329 = 5080747) B5080747
theorem B8019695 : Blo 1234435 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B13361111 : Blo 1234435 13361111 := bstep (se 1 (by rfl) ⟨10020833, by rfl⟩ : syracuseStep 13361111 = 20041667) B20041667
theorem B7921793 : Blo 1234435 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B15827183 : Blo 1234435 15827183 := bstep (se 1 (by rfl) ⟨11870387, by rfl⟩ : syracuseStep 15827183 = 23740775) B23740775
theorem B23732777 : Blo 1234435 23732777 := bstep (se 2 (by rfl) ⟨8899791, by rfl⟩ : syracuseStep 23732777 = 17799583) B17799583
theorem B4170473 : Blo 1234435 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B24052535 : Blo 1234435 24052535 := bstep (se 1 (by rfl) ⟨18039401, by rfl⟩ : syracuseStep 24052535 = 36078803) B36078803
theorem B6251579 : Blo 1234435 6251579 := bstep (se 1 (by rfl) ⟨4688684, by rfl⟩ : syracuseStep 6251579 = 9377369) B9377369
theorem B1852487 : Blo 1234435 1852487 := bstep (se 1 (by rfl) ⟨1389365, by rfl⟩ : syracuseStep 1852487 = 2778731) B2778731
theorem B14066783 : Blo 1234435 14066783 := bstep (se 1 (by rfl) ⟨10550087, by rfl⟩ : syracuseStep 14066783 = 21100175) B21100175
theorem B1852553 : Blo 1234435 1852553 := bstep (se 2 (by rfl) ⟨694707, by rfl⟩ : syracuseStep 1852553 = 1389415) B1389415
theorem B1320295 : Blo 1234435 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B1852793 : Blo 1234435 1852793 := bstep (se 2 (by rfl) ⟨694797, by rfl⟩ : syracuseStep 1852793 = 1389595) B1389595
theorem B2778551 : Blo 1234435 2778551 := bstep (se 1 (by rfl) ⟨2083913, by rfl⟩ : syracuseStep 2778551 = 4167827) B4167827
theorem B1852955 : Blo 1234435 1852955 := bstep (se 1 (by rfl) ⟨1389716, by rfl⟩ : syracuseStep 1852955 = 2779433) B2779433
theorem B3958463 : Blo 1234435 3958463 := bstep (se 1 (by rfl) ⟨2968847, by rfl⟩ : syracuseStep 3958463 = 5937695) B5937695
theorem B4687591 : Blo 1234435 4687591 := bstep (se 1 (by rfl) ⟨3515693, by rfl⟩ : syracuseStep 4687591 = 7031387) B7031387
theorem B2344859 : Blo 1234435 2344859 := bstep (se 1 (by rfl) ⟨1758644, by rfl⟩ : syracuseStep 2344859 = 3517289) B3517289
theorem B1853339 : Blo 1234435 1853339 := bstep (se 1 (by rfl) ⟨1390004, by rfl⟩ : syracuseStep 1853339 = 2780009) B2780009
theorem B2967463 : Blo 1234435 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B4687865 : Blo 1234435 4687865 := bstep (se 2 (by rfl) ⟨1757949, by rfl⟩ : syracuseStep 4687865 = 3515899) B3515899
theorem B513738875 : Blo 1234435 513738875 := bstep (se 1 (by rfl) ⟨385304156, by rfl⟩ : syracuseStep 513738875 = 770608313) B770608313
theorem B34261337 : Blo 1234435 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B4516219 : Blo 1234435 4516219 := bstep (se 1 (by rfl) ⟨3387164, by rfl⟩ : syracuseStep 4516219 = 6774329) B6774329
theorem B8907407 : Blo 1234435 8907407 := bstep (se 1 (by rfl) ⟨6680555, by rfl⟩ : syracuseStep 8907407 = 13361111) B13361111
theorem B1854119 : Blo 1234435 1854119 := bstep (se 1 (by rfl) ⟨1390589, by rfl⟩ : syracuseStep 1854119 = 2781179) B2781179
theorem B1854191 : Blo 1234435 1854191 := bstep (se 1 (by rfl) ⟨1390643, by rfl⟩ : syracuseStep 1854191 = 2781287) B2781287
theorem B2345831 : Blo 1234435 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B2780783 : Blo 1234435 2780783 := bstep (se 1 (by rfl) ⟨2085587, by rfl⟩ : syracuseStep 2780783 = 4171175) B4171175
theorem B9383687 : Blo 1234435 9383687 := bstep (se 1 (by rfl) ⟨7037765, by rfl⟩ : syracuseStep 9383687 = 14075531) B14075531
theorem B2346985 : Blo 1234435 2346985 := bstep (se 2 (by rfl) ⟨880119, by rfl⟩ : syracuseStep 2346985 = 1760239) B1760239
theorem B67588505 : Blo 1234435 67588505 := bstep (se 2 (by rfl) ⟨25345689, by rfl⟩ : syracuseStep 67588505 = 50691379) B50691379
theorem B21385853 : Blo 1234435 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B130224959 : Blo 1234435 130224959 := bstep (se 1 (by rfl) ⟨97668719, by rfl⟩ : syracuseStep 130224959 = 195337439) B195337439
theorem B1234535 : Blo 1234435 1234535 := bstep (se 1 (by rfl) ⟨925901, by rfl⟩ : syracuseStep 1234535 = 1851803) B1851803
theorem B10016419 : Blo 1234435 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B1234715 : Blo 1234435 1234715 := bstep (se 1 (by rfl) ⟨926036, by rfl⟩ : syracuseStep 1234715 = 1852073) B1852073
theorem B1562591 : Blo 1234435 1562591 := bstep (se 1 (by rfl) ⟨1171943, by rfl⟩ : syracuseStep 1562591 = 2343887) B2343887
theorem B16267283 : Blo 1234435 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B1235111 : Blo 1234435 1235111 := bstep (se 1 (by rfl) ⟨926333, by rfl⟩ : syracuseStep 1235111 = 1852667) B1852667
theorem B9157093 : Blo 1234435 9157093 := bstep (se 4 (by rfl) ⟨858477, by rfl⟩ : syracuseStep 9157093 = 1716955) B1716955
theorem B3127835 : Blo 1234435 3127835 := bstep (se 1 (by rfl) ⟨2345876, by rfl⟩ : syracuseStep 3127835 = 4691753) B4691753
theorem B1235567 : Blo 1234435 1235567 := bstep (se 1 (by rfl) ⟨926675, by rfl⟩ : syracuseStep 1235567 = 1853351) B1853351
theorem B9509501 : Blo 1234435 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B1235583 : Blo 1234435 1235583 := bstep (se 1 (by rfl) ⟨926687, by rfl⟩ : syracuseStep 1235583 = 1853375) B1853375
theorem B1563391 : Blo 1234435 1563391 := bstep (se 1 (by rfl) ⟨1172543, by rfl⟩ : syracuseStep 1563391 = 2345087) B2345087
theorem B1235739 : Blo 1234435 1235739 := bstep (se 1 (by rfl) ⟨926804, by rfl⟩ : syracuseStep 1235739 = 1853609) B1853609
theorem B3759005 : Blo 1234435 3759005 := bstep (se 3 (by rfl) ⟨704813, by rfl⟩ : syracuseStep 3759005 = 1409627) B1409627
theorem B1235999 : Blo 1234435 1235999 := bstep (se 1 (by rfl) ⟨926999, by rfl⟩ : syracuseStep 1235999 = 1853999) B1853999
theorem B3955823 : Blo 1234435 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B1236123 : Blo 1234435 1236123 := bstep (se 1 (by rfl) ⟨927092, by rfl⟩ : syracuseStep 1236123 = 1854185) B1854185
theorem B1236159 : Blo 1234435 1236159 := bstep (se 1 (by rfl) ⟨927119, by rfl⟩ : syracuseStep 1236159 = 1854239) B1854239
theorem B8903945 : Blo 1234435 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B20036987 : Blo 1234435 20036987 := bstep (se 1 (by rfl) ⟨15027740, by rfl⟩ : syracuseStep 20036987 = 30055481) B30055481
theorem B10018367 : Blo 1234435 10018367 := bstep (se 1 (by rfl) ⟨7513775, by rfl⟩ : syracuseStep 10018367 = 15027551) B15027551
theorem B4693727 : Blo 1234435 4693727 := bstep (se 1 (by rfl) ⟨3520295, by rfl⟩ : syracuseStep 4693727 = 7040591) B7040591
theorem B4169447 : Blo 1234435 4169447 := bstep (se 1 (by rfl) ⟨3127085, by rfl⟩ : syracuseStep 4169447 = 6254171) B6254171
theorem B10551455 : Blo 1234435 10551455 := bstep (se 1 (by rfl) ⟨7913591, by rfl⟩ : syracuseStep 10551455 = 15827183) B15827183
theorem B1852367 : Blo 1234435 1852367 := bstep (se 1 (by rfl) ⟨1389275, by rfl⟩ : syracuseStep 1852367 = 2778551) B2778551
theorem B2638975 : Blo 1234435 2638975 := bstep (se 1 (by rfl) ⟨1979231, by rfl⟩ : syracuseStep 2638975 = 3958463) B3958463
theorem B342492583 : Blo 1234435 342492583 := bstep (se 1 (by rfl) ⟨256869437, by rfl⟩ : syracuseStep 342492583 = 513738875) B513738875
theorem B24086501 : Blo 1234435 24086501 := bstep (se 4 (by rfl) ⟨2258109, by rfl⟩ : syracuseStep 24086501 = 4516219) B4516219
theorem B13355225 : Blo 1234435 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B6678911 : Blo 1234435 6678911 := bstep (se 1 (by rfl) ⟨5009183, by rfl⟩ : syracuseStep 6678911 = 10018367) B10018367
theorem B1853855 : Blo 1234435 1853855 := bstep (se 1 (by rfl) ⟨1390391, by rfl⟩ : syracuseStep 1853855 = 2780783) B2780783
theorem B2779631 : Blo 1234435 2779631 := bstep (se 1 (by rfl) ⟨2084723, by rfl⟩ : syracuseStep 2779631 = 4169447) B4169447
theorem B45059003 : Blo 1234435 45059003 := bstep (se 1 (by rfl) ⟨33794252, by rfl⟩ : syracuseStep 45059003 = 67588505) B67588505
theorem B15821851 : Blo 1234435 15821851 := bstep (se 1 (by rfl) ⟨11866388, by rfl⟩ : syracuseStep 15821851 = 23732777) B23732777
theorem B14257235 : Blo 1234435 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B2780315 : Blo 1234435 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B16035023 : Blo 1234435 16035023 := bstep (se 1 (by rfl) ⟨12026267, by rfl⟩ : syracuseStep 16035023 = 24052535) B24052535
theorem B2084521 : Blo 1234435 2084521 := bstep (se 2 (by rfl) ⟨781695, by rfl⟩ : syracuseStep 2084521 = 1563391) B1563391
theorem B3125243 : Blo 1234435 3125243 := bstep (se 1 (by rfl) ⟨2343932, by rfl⟩ : syracuseStep 3125243 = 4687865) B4687865
theorem B2085223 : Blo 1234435 2085223 := bstep (se 1 (by rfl) ⟨1563917, by rfl⟩ : syracuseStep 2085223 = 3127835) B3127835
theorem B5935963 : Blo 1234435 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B13357991 : Blo 1234435 13357991 := bstep (se 1 (by rfl) ⟨10018493, by rfl⟩ : syracuseStep 13357991 = 20036987) B20036987
theorem B10024013 : Blo 1234435 10024013 := bstep (se 3 (by rfl) ⟨1879502, by rfl⟩ : syracuseStep 10024013 = 3759005) B3759005
theorem B6255791 : Blo 1234435 6255791 := bstep (se 1 (by rfl) ⟨4691843, by rfl⟩ : syracuseStep 6255791 = 9383687) B9383687
theorem B48837829 : Blo 1234435 48837829 := bstep (se 4 (by rfl) ⟨4578546, by rfl⟩ : syracuseStep 48837829 = 9157093) B9157093
theorem B4166909 : Blo 1234435 4166909 := bstep (se 3 (by rfl) ⟨781295, by rfl⟩ : syracuseStep 4166909 = 1562591) B1562591
theorem B5281195 : Blo 1234435 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B86816639 : Blo 1234435 86816639 := bstep (se 1 (by rfl) ⟨65112479, by rfl⟩ : syracuseStep 86816639 = 130224959) B130224959
theorem B4167719 : Blo 1234435 4167719 := bstep (se 1 (by rfl) ⟨3125789, by rfl⟩ : syracuseStep 4167719 = 6251579) B6251579
theorem B1234991 : Blo 1234435 1234991 := bstep (se 1 (by rfl) ⟨926243, by rfl⟩ : syracuseStep 1234991 = 1852487) B1852487
theorem B9377855 : Blo 1234435 9377855 := bstep (se 1 (by rfl) ⟨7033391, by rfl⟩ : syracuseStep 9377855 = 14066783) B14066783
theorem B1235035 : Blo 1234435 1235035 := bstep (se 1 (by rfl) ⟨926276, by rfl⟩ : syracuseStep 1235035 = 1852553) B1852553
theorem B91363565 : Blo 1234435 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B1235195 : Blo 1234435 1235195 := bstep (se 1 (by rfl) ⟨926396, by rfl⟩ : syracuseStep 1235195 = 1852793) B1852793
theorem B1235303 : Blo 1234435 1235303 := bstep (se 1 (by rfl) ⟨926477, by rfl⟩ : syracuseStep 1235303 = 1852955) B1852955
theorem B1563239 : Blo 1234435 1563239 := bstep (se 1 (by rfl) ⟨1172429, by rfl⟩ : syracuseStep 1563239 = 2344859) B2344859
theorem B1235559 : Blo 1234435 1235559 := bstep (se 1 (by rfl) ⟨926669, by rfl⟩ : syracuseStep 1235559 = 1853339) B1853339
theorem B10844855 : Blo 1234435 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B6339667 : Blo 1234435 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B5938271 : Blo 1234435 5938271 := bstep (se 1 (by rfl) ⟨4453703, by rfl⟩ : syracuseStep 5938271 = 8907407) B8907407
theorem B1236079 : Blo 1234435 1236079 := bstep (se 1 (by rfl) ⟨927059, by rfl⟩ : syracuseStep 1236079 = 1854119) B1854119
theorem B1760393 : Blo 1234435 1760393 := bstep (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) B1320295
theorem B1236127 : Blo 1234435 1236127 := bstep (se 1 (by rfl) ⟨927095, by rfl⟩ : syracuseStep 1236127 = 1854191) B1854191
theorem B1563887 : Blo 1234435 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B2637215 : Blo 1234435 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B6250121 : Blo 1234435 6250121 := bstep (se 2 (by rfl) ⟨2343795, by rfl⟩ : syracuseStep 6250121 = 4687591) B4687591
theorem B3129151 : Blo 1234435 3129151 := bstep (se 1 (by rfl) ⟨2346863, by rfl⟩ : syracuseStep 3129151 = 4693727) B4693727
theorem B3956617 : Blo 1234435 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B3129313 : Blo 1234435 3129313 := bstep (se 2 (by rfl) ⟨1173492, by rfl⟩ : syracuseStep 3129313 = 2346985) B2346985
theorem B4694381 : Blo 1234435 4694381 := bstep (se 3 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 4694381 = 1760393) B1760393
theorem B4170365 : Blo 1234435 4170365 := bstep (se 3 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 4170365 = 1563887) B1563887
theorem B4170527 : Blo 1234435 4170527 := bstep (se 1 (by rfl) ⟨3127895, by rfl⟩ : syracuseStep 4170527 = 6255791) B6255791
theorem B2777939 : Blo 1234435 2777939 := bstep (se 1 (by rfl) ⟨2083454, by rfl⟩ : syracuseStep 2777939 = 4166909) B4166909
theorem B7914617 : Blo 1234435 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B57877759 : Blo 1234435 57877759 := bstep (se 1 (by rfl) ⟨43408319, by rfl⟩ : syracuseStep 57877759 = 86816639) B86816639
theorem B16057667 : Blo 1234435 16057667 := bstep (se 1 (by rfl) ⟨12043250, by rfl⟩ : syracuseStep 16057667 = 24086501) B24086501
theorem B2778479 : Blo 1234435 2778479 := bstep (se 1 (by rfl) ⟨2083859, by rfl⟩ : syracuseStep 2778479 = 4167719) B4167719
theorem B21095801 : Blo 1234435 21095801 := bstep (se 2 (by rfl) ⟨7910925, by rfl⟩ : syracuseStep 21095801 = 15821851) B15821851
theorem B6251903 : Blo 1234435 6251903 := bstep (se 1 (by rfl) ⟨4688927, by rfl⟩ : syracuseStep 6251903 = 9377855) B9377855
theorem B60909043 : Blo 1234435 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B1853087 : Blo 1234435 1853087 := bstep (se 1 (by rfl) ⟨1389815, by rfl⟩ : syracuseStep 1853087 = 2779631) B2779631
theorem B456656777 : Blo 1234435 456656777 := bstep (se 2 (by rfl) ⟨171246291, by rfl⟩ : syracuseStep 456656777 = 342492583) B342492583
theorem B9504823 : Blo 1234435 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B3958847 : Blo 1234435 3958847 := bstep (se 1 (by rfl) ⟨2969135, by rfl⟩ : syracuseStep 3958847 = 5938271) B5938271
theorem B1853543 : Blo 1234435 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B2779361 : Blo 1234435 2779361 := bstep (se 2 (by rfl) ⟨1042260, by rfl⟩ : syracuseStep 2779361 = 2084521) B2084521
theorem B4172201 : Blo 1234435 4172201 := bstep (se 2 (by rfl) ⟨1564575, by rfl⟩ : syracuseStep 4172201 = 3129151) B3129151
theorem B35621309 : Blo 1234435 35621309 := bstep (se 3 (by rfl) ⟨6678995, by rfl⟩ : syracuseStep 35621309 = 13357991) B13357991
theorem B4172417 : Blo 1234435 4172417 := bstep (se 2 (by rfl) ⟨1564656, by rfl⟩ : syracuseStep 4172417 = 3129313) B3129313
theorem B2083495 : Blo 1234435 2083495 := bstep (se 1 (by rfl) ⟨1562621, by rfl⟩ : syracuseStep 2083495 = 3125243) B3125243
theorem B2780297 : Blo 1234435 2780297 := bstep (se 2 (by rfl) ⟨1042611, by rfl⟩ : syracuseStep 2780297 = 2085223) B2085223
theorem B3518633 : Blo 1234435 3518633 := bstep (se 2 (by rfl) ⟨1319487, by rfl⟩ : syracuseStep 3518633 = 2638975) B2638975
theorem B4452607 : Blo 1234435 4452607 := bstep (se 1 (by rfl) ⟨3339455, by rfl⟩ : syracuseStep 4452607 = 6678911) B6678911
theorem B7229903 : Blo 1234435 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B7041593 : Blo 1234435 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B1758143 : Blo 1234435 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B4166747 : Blo 1234435 4166747 := bstep (se 1 (by rfl) ⟨3125060, by rfl⟩ : syracuseStep 4166747 = 6250121) B6250121
theorem B7034303 : Blo 1234435 7034303 := bstep (se 1 (by rfl) ⟨5275727, by rfl⟩ : syracuseStep 7034303 = 10551455) B10551455
theorem B1234911 : Blo 1234435 1234911 := bstep (se 1 (by rfl) ⟨926183, by rfl⟩ : syracuseStep 1234911 = 1852367) B1852367
theorem B6682675 : Blo 1234435 6682675 := bstep (se 1 (by rfl) ⟨5012006, by rfl⟩ : syracuseStep 6682675 = 10024013) B10024013
theorem B8452889 : Blo 1234435 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B8903483 : Blo 1234435 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B65117105 : Blo 1234435 65117105 := bstep (se 2 (by rfl) ⟨24418914, by rfl⟩ : syracuseStep 65117105 = 48837829) B48837829
theorem B4168637 : Blo 1234435 4168637 := bstep (se 3 (by rfl) ⟨781619, by rfl⟩ : syracuseStep 4168637 = 1563239) B1563239
theorem B1235903 : Blo 1234435 1235903 := bstep (se 1 (by rfl) ⟨926927, by rfl⟩ : syracuseStep 1235903 = 1853855) B1853855
theorem B30039335 : Blo 1234435 30039335 := bstep (se 1 (by rfl) ⟨22529501, by rfl⟩ : syracuseStep 30039335 = 45059003) B45059003
theorem B10690015 : Blo 1234435 10690015 := bstep (se 1 (by rfl) ⟨8017511, by rfl⟩ : syracuseStep 10690015 = 16035023) B16035023
theorem B5275489 : Blo 1234435 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B12673097 : Blo 1234435 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B3129587 : Blo 1234435 3129587 := bstep (se 1 (by rfl) ⟨2347190, by rfl⟩ : syracuseStep 3129587 = 4694381) B4694381
theorem B4694395 : Blo 1234435 4694395 := bstep (se 1 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 4694395 = 7041593) B7041593
theorem B1851959 : Blo 1234435 1851959 := bstep (se 1 (by rfl) ⟨1388969, by rfl⟩ : syracuseStep 1851959 = 2777939) B2777939
theorem B2777831 : Blo 1234435 2777831 := bstep (se 1 (by rfl) ⟨2083373, by rfl⟩ : syracuseStep 2777831 = 4166747) B4166747
theorem B5276411 : Blo 1234435 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2777993 : Blo 1234435 2777993 := bstep (se 2 (by rfl) ⟨1041747, by rfl⟩ : syracuseStep 2777993 = 2083495) B2083495
theorem B1852319 : Blo 1234435 1852319 := bstep (se 1 (by rfl) ⟨1389239, by rfl⟩ : syracuseStep 1852319 = 2778479) B2778479
theorem B2639231 : Blo 1234435 2639231 := bstep (se 1 (by rfl) ⟨1979423, by rfl⟩ : syracuseStep 2639231 = 3958847) B3958847
theorem B1852907 : Blo 1234435 1852907 := bstep (se 1 (by rfl) ⟨1389680, by rfl⟩ : syracuseStep 1852907 = 2779361) B2779361
theorem B43411403 : Blo 1234435 43411403 := bstep (se 1 (by rfl) ⟨32558552, by rfl⟩ : syracuseStep 43411403 = 65117105) B65117105
theorem B2779091 : Blo 1234435 2779091 := bstep (se 1 (by rfl) ⟨2084318, by rfl⟩ : syracuseStep 2779091 = 4168637) B4168637
theorem B1853531 : Blo 1234435 1853531 := bstep (se 1 (by rfl) ⟨1390148, by rfl⟩ : syracuseStep 1853531 = 2780297) B2780297
theorem B4688381 : Blo 1234435 4688381 := bstep (se 3 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 4688381 = 1758143) B1758143
theorem B2345755 : Blo 1234435 2345755 := bstep (se 1 (by rfl) ⟨1759316, by rfl⟩ : syracuseStep 2345755 = 3518633) B3518633
theorem B2780243 : Blo 1234435 2780243 := bstep (se 1 (by rfl) ⟨2085182, by rfl⟩ : syracuseStep 2780243 = 4170365) B4170365
theorem B2780351 : Blo 1234435 2780351 := bstep (se 1 (by rfl) ⟨2085263, by rfl⟩ : syracuseStep 2780351 = 4170527) B4170527
theorem B4689535 : Blo 1234435 4689535 := bstep (se 1 (by rfl) ⟨3517151, by rfl⟩ : syracuseStep 4689535 = 7034303) B7034303
theorem B19279741 : Blo 1234435 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B2781467 : Blo 1234435 2781467 := bstep (se 1 (by rfl) ⟨2086100, by rfl⟩ : syracuseStep 2781467 = 4172201) B4172201
theorem B2781611 : Blo 1234435 2781611 := bstep (se 1 (by rfl) ⟨2086208, by rfl⟩ : syracuseStep 2781611 = 4172417) B4172417
theorem B5935655 : Blo 1234435 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B81212057 : Blo 1234435 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B20026223 : Blo 1234435 20026223 := bstep (se 1 (by rfl) ⟨15019667, by rfl⟩ : syracuseStep 20026223 = 30039335) B30039335
theorem B7033985 : Blo 1234435 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B8910233 : Blo 1234435 8910233 := bstep (se 2 (by rfl) ⟨3341337, by rfl⟩ : syracuseStep 8910233 = 6682675) B6682675
theorem B5936809 : Blo 1234435 5936809 := bstep (se 2 (by rfl) ⟨2226303, by rfl⟩ : syracuseStep 5936809 = 4452607) B4452607
theorem B10705111 : Blo 1234435 10705111 := bstep (se 1 (by rfl) ⟨8028833, by rfl⟩ : syracuseStep 10705111 = 16057667) B16057667
theorem B14063867 : Blo 1234435 14063867 := bstep (se 1 (by rfl) ⟨10547900, by rfl⟩ : syracuseStep 14063867 = 21095801) B21095801
theorem B4167935 : Blo 1234435 4167935 := bstep (se 1 (by rfl) ⟨3125951, by rfl⟩ : syracuseStep 4167935 = 6251903) B6251903
theorem B1235391 : Blo 1234435 1235391 := bstep (se 1 (by rfl) ⟨926543, by rfl⟩ : syracuseStep 1235391 = 1853087) B1853087
theorem B304437851 : Blo 1234435 304437851 := bstep (se 1 (by rfl) ⟨228328388, by rfl⟩ : syracuseStep 304437851 = 456656777) B456656777
theorem B308681381 : Blo 1234435 308681381 := bstep (se 4 (by rfl) ⟨28938879, by rfl⟩ : syracuseStep 308681381 = 57877759) B57877759
theorem B1235695 : Blo 1234435 1235695 := bstep (se 1 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 1235695 = 1853543) B1853543
theorem B23747539 : Blo 1234435 23747539 := bstep (se 1 (by rfl) ⟨17810654, by rfl⟩ : syracuseStep 23747539 = 35621309) B35621309
theorem B5635259 : Blo 1234435 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B14253353 : Blo 1234435 14253353 := bstep (se 2 (by rfl) ⟨5345007, by rfl⟩ : syracuseStep 14253353 = 10690015) B10690015
theorem B3957103 : Blo 1234435 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B54141371 : Blo 1234435 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B1851887 : Blo 1234435 1851887 := bstep (se 1 (by rfl) ⟨1388915, by rfl⟩ : syracuseStep 1851887 = 2777831) B2777831
theorem B6259193 : Blo 1234435 6259193 := bstep (se 2 (by rfl) ⟨2347197, by rfl⟩ : syracuseStep 6259193 = 4694395) B4694395
theorem B1851995 : Blo 1234435 1851995 := bstep (se 1 (by rfl) ⟨1388996, by rfl⟩ : syracuseStep 1851995 = 2777993) B2777993
theorem B5940155 : Blo 1234435 5940155 := bstep (se 1 (by rfl) ⟨4455116, by rfl⟩ : syracuseStep 5940155 = 8910233) B8910233
theorem B31663385 : Blo 1234435 31663385 := bstep (se 2 (by rfl) ⟨11873769, by rfl⟩ : syracuseStep 31663385 = 23747539) B23747539
theorem B1852727 : Blo 1234435 1852727 := bstep (se 1 (by rfl) ⟨1389545, by rfl⟩ : syracuseStep 1852727 = 2779091) B2779091
theorem B2778623 : Blo 1234435 2778623 := bstep (se 1 (by rfl) ⟨2083967, by rfl⟩ : syracuseStep 2778623 = 4167935) B4167935
theorem B202958567 : Blo 1234435 202958567 := bstep (se 1 (by rfl) ⟨152218925, by rfl⟩ : syracuseStep 202958567 = 304437851) B304437851
theorem B1853495 : Blo 1234435 1853495 := bstep (se 1 (by rfl) ⟨1390121, by rfl⟩ : syracuseStep 1853495 = 2780243) B2780243
theorem B1853567 : Blo 1234435 1853567 := bstep (se 1 (by rfl) ⟨1390175, by rfl⟩ : syracuseStep 1853567 = 2780351) B2780351
theorem B6252713 : Blo 1234435 6252713 := bstep (se 2 (by rfl) ⟨2344767, by rfl⟩ : syracuseStep 6252713 = 4689535) B4689535
theorem B7915745 : Blo 1234435 7915745 := bstep (se 2 (by rfl) ⟨2968404, by rfl⟩ : syracuseStep 7915745 = 5936809) B5936809
theorem B115763741 : Blo 1234435 115763741 := bstep (se 3 (by rfl) ⟨21705701, by rfl⟩ : syracuseStep 115763741 = 43411403) B43411403
theorem B8448731 : Blo 1234435 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B1854311 : Blo 1234435 1854311 := bstep (se 1 (by rfl) ⟨1390733, by rfl⟩ : syracuseStep 1854311 = 2781467) B2781467
theorem B1854407 : Blo 1234435 1854407 := bstep (se 1 (by rfl) ⟨1390805, by rfl⟩ : syracuseStep 1854407 = 2781611) B2781611
theorem B3517607 : Blo 1234435 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B4689323 : Blo 1234435 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B57093925 : Blo 1234435 57093925 := bstep (se 4 (by rfl) ⟨5352555, by rfl⟩ : syracuseStep 57093925 = 10705111) B10705111
theorem B9375911 : Blo 1234435 9375911 := bstep (se 1 (by rfl) ⟨7031933, by rfl⟩ : syracuseStep 9375911 = 14063867) B14063867
theorem B3125587 : Blo 1234435 3125587 := bstep (se 1 (by rfl) ⟨2344190, by rfl⟩ : syracuseStep 3125587 = 4688381) B4688381
theorem B205787587 : Blo 1234435 205787587 := bstep (se 1 (by rfl) ⟨154340690, by rfl⟩ : syracuseStep 205787587 = 308681381) B308681381
theorem B3756839 : Blo 1234435 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B2086391 : Blo 1234435 2086391 := bstep (se 1 (by rfl) ⟨1564793, by rfl⟩ : syracuseStep 2086391 = 3129587) B3129587
theorem B1234639 : Blo 1234435 1234639 := bstep (se 1 (by rfl) ⟨925979, by rfl⟩ : syracuseStep 1234639 = 1851959) B1851959
theorem B13350815 : Blo 1234435 13350815 := bstep (se 1 (by rfl) ⟨10013111, by rfl⟩ : syracuseStep 13350815 = 20026223) B20026223
theorem B1234879 : Blo 1234435 1234879 := bstep (se 1 (by rfl) ⟨926159, by rfl⟩ : syracuseStep 1234879 = 1852319) B1852319
theorem B1759487 : Blo 1234435 1759487 := bstep (se 1 (by rfl) ⟨1319615, by rfl⟩ : syracuseStep 1759487 = 2639231) B2639231
theorem B1235271 : Blo 1234435 1235271 := bstep (se 1 (by rfl) ⟨926453, by rfl⟩ : syracuseStep 1235271 = 1852907) B1852907
theorem B3127673 : Blo 1234435 3127673 := bstep (se 2 (by rfl) ⟨1172877, by rfl⟩ : syracuseStep 3127673 = 2345755) B2345755
theorem B1235687 : Blo 1234435 1235687 := bstep (se 1 (by rfl) ⟨926765, by rfl⟩ : syracuseStep 1235687 = 1853531) B1853531
theorem B9502235 : Blo 1234435 9502235 := bstep (se 1 (by rfl) ⟨7126676, by rfl⟩ : syracuseStep 9502235 = 14253353) B14253353
theorem B25706321 : Blo 1234435 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B6250607 : Blo 1234435 6250607 := bstep (se 1 (by rfl) ⟨4687955, by rfl⟩ : syracuseStep 6250607 = 9375911) B9375911
theorem B36094247 : Blo 1234435 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B9380285 : Blo 1234435 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B274383449 : Blo 1234435 274383449 := bstep (se 2 (by rfl) ⟨102893793, by rfl⟩ : syracuseStep 274383449 = 205787587) B205787587
theorem B1852415 : Blo 1234435 1852415 := bstep (se 1 (by rfl) ⟨1389311, by rfl⟩ : syracuseStep 1852415 = 2778623) B2778623
theorem B5277163 : Blo 1234435 5277163 := bstep (se 1 (by rfl) ⟨3957872, by rfl⟩ : syracuseStep 5277163 = 7915745) B7915745
theorem B21104549 : Blo 1234435 21104549 := bstep (se 4 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 21104549 = 3957103) B3957103
theorem B6334823 : Blo 1234435 6334823 := bstep (se 1 (by rfl) ⟨4751117, by rfl⟩ : syracuseStep 6334823 = 9502235) B9502235
theorem B4172795 : Blo 1234435 4172795 := bstep (se 1 (by rfl) ⟨3129596, by rfl⟩ : syracuseStep 4172795 = 6259193) B6259193
theorem B3960103 : Blo 1234435 3960103 := bstep (se 1 (by rfl) ⟨2970077, by rfl⟩ : syracuseStep 3960103 = 5940155) B5940155
theorem B8900543 : Blo 1234435 8900543 := bstep (se 1 (by rfl) ⟨6675407, by rfl⟩ : syracuseStep 8900543 = 13350815) B13350815
theorem B2085115 : Blo 1234435 2085115 := bstep (se 1 (by rfl) ⟨1563836, by rfl⟩ : syracuseStep 2085115 = 3127673) B3127673
theorem B5632487 : Blo 1234435 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B3126215 : Blo 1234435 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B76125233 : Blo 1234435 76125233 := bstep (se 2 (by rfl) ⟨28546962, by rfl⟩ : syracuseStep 76125233 = 57093925) B57093925
theorem B1234591 : Blo 1234435 1234591 := bstep (se 1 (by rfl) ⟨925943, by rfl⟩ : syracuseStep 1234591 = 1851887) B1851887
theorem B1234663 : Blo 1234435 1234663 := bstep (se 1 (by rfl) ⟨925997, by rfl⟩ : syracuseStep 1234663 = 1851995) B1851995
theorem B4167449 : Blo 1234435 4167449 := bstep (se 2 (by rfl) ⟨1562793, by rfl⟩ : syracuseStep 4167449 = 3125587) B3125587
theorem B4691965 : Blo 1234435 4691965 := bstep (se 3 (by rfl) ⟨879743, by rfl⟩ : syracuseStep 4691965 = 1759487) B1759487
theorem B21108923 : Blo 1234435 21108923 := bstep (se 1 (by rfl) ⟨15831692, by rfl⟩ : syracuseStep 21108923 = 31663385) B31663385
theorem B1235151 : Blo 1234435 1235151 := bstep (se 1 (by rfl) ⟨926363, by rfl⟩ : syracuseStep 1235151 = 1852727) B1852727
theorem B1390927 : Blo 1234435 1390927 := bstep (se 1 (by rfl) ⟨1043195, by rfl⟩ : syracuseStep 1390927 = 2086391) B2086391
theorem B135305711 : Blo 1234435 135305711 := bstep (se 1 (by rfl) ⟨101479283, by rfl⟩ : syracuseStep 135305711 = 202958567) B202958567
theorem B1235663 : Blo 1234435 1235663 := bstep (se 1 (by rfl) ⟨926747, by rfl⟩ : syracuseStep 1235663 = 1853495) B1853495
theorem B1235711 : Blo 1234435 1235711 := bstep (se 1 (by rfl) ⟨926783, by rfl⟩ : syracuseStep 1235711 = 1853567) B1853567
theorem B4168475 : Blo 1234435 4168475 := bstep (se 1 (by rfl) ⟨3126356, by rfl⟩ : syracuseStep 4168475 = 6252713) B6252713
theorem B77175827 : Blo 1234435 77175827 := bstep (se 1 (by rfl) ⟨57881870, by rfl⟩ : syracuseStep 77175827 = 115763741) B115763741
theorem B1236207 : Blo 1234435 1236207 := bstep (se 1 (by rfl) ⟨927155, by rfl⟩ : syracuseStep 1236207 = 1854311) B1854311
theorem B1236271 : Blo 1234435 1236271 := bstep (se 1 (by rfl) ⟨927203, by rfl⟩ : syracuseStep 1236271 = 1854407) B1854407
theorem B10018237 : Blo 1234435 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B17137547 : Blo 1234435 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B50750155 : Blo 1234435 50750155 := bstep (se 1 (by rfl) ⟨38062616, by rfl⟩ : syracuseStep 50750155 = 76125233) B76125233
theorem B2778299 : Blo 1234435 2778299 := bstep (se 1 (by rfl) ⟨2083724, by rfl⟩ : syracuseStep 2778299 = 4167449) B4167449
theorem B90203807 : Blo 1234435 90203807 := bstep (se 1 (by rfl) ⟨67652855, by rfl⟩ : syracuseStep 90203807 = 135305711) B135305711
theorem B2778983 : Blo 1234435 2778983 := bstep (se 1 (by rfl) ⟨2084237, by rfl⟩ : syracuseStep 2778983 = 4168475) B4168475
theorem B23734781 : Blo 1234435 23734781 := bstep (se 3 (by rfl) ⟨4450271, by rfl⟩ : syracuseStep 23734781 = 8900543) B8900543
theorem B24062831 : Blo 1234435 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B6253523 : Blo 1234435 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B3754991 : Blo 1234435 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B2780153 : Blo 1234435 2780153 := bstep (se 2 (by rfl) ⟨1042557, by rfl⟩ : syracuseStep 2780153 = 2085115) B2085115
theorem B182922299 : Blo 1234435 182922299 := bstep (se 1 (by rfl) ⟨137191724, by rfl⟩ : syracuseStep 182922299 = 274383449) B274383449
theorem B1854569 : Blo 1234435 1854569 := bstep (se 2 (by rfl) ⟨695463, by rfl⟩ : syracuseStep 1854569 = 1390927) B1390927
theorem B2084143 : Blo 1234435 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B14069699 : Blo 1234435 14069699 := bstep (se 1 (by rfl) ⟨10552274, by rfl⟩ : syracuseStep 14069699 = 21104549) B21104549
theorem B4223215 : Blo 1234435 4223215 := bstep (se 1 (by rfl) ⟨3167411, by rfl⟩ : syracuseStep 4223215 = 6334823) B6334823
theorem B5280137 : Blo 1234435 5280137 := bstep (se 2 (by rfl) ⟨1980051, by rfl⟩ : syracuseStep 5280137 = 3960103) B3960103
theorem B13357649 : Blo 1234435 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B2781863 : Blo 1234435 2781863 := bstep (se 1 (by rfl) ⟨2086397, by rfl⟩ : syracuseStep 2781863 = 4172795) B4172795
theorem B51450551 : Blo 1234435 51450551 := bstep (se 1 (by rfl) ⟨38587913, by rfl⟩ : syracuseStep 51450551 = 77175827) B77175827
theorem B11425031 : Blo 1234435 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B6255953 : Blo 1234435 6255953 := bstep (se 2 (by rfl) ⟨2345982, by rfl⟩ : syracuseStep 6255953 = 4691965) B4691965
theorem B4167071 : Blo 1234435 4167071 := bstep (se 1 (by rfl) ⟨3125303, by rfl⟩ : syracuseStep 4167071 = 6250607) B6250607
theorem B1234943 : Blo 1234435 1234943 := bstep (se 1 (by rfl) ⟨926207, by rfl⟩ : syracuseStep 1234943 = 1852415) B1852415
theorem B14072615 : Blo 1234435 14072615 := bstep (se 1 (by rfl) ⟨10554461, by rfl⟩ : syracuseStep 14072615 = 21108923) B21108923
theorem B7036217 : Blo 1234435 7036217 := bstep (se 2 (by rfl) ⟨2638581, by rfl⟩ : syracuseStep 7036217 = 5277163) B5277163
theorem B8905099 : Blo 1234435 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B34300367 : Blo 1234435 34300367 := bstep (se 1 (by rfl) ⟨25725275, by rfl⟩ : syracuseStep 34300367 = 51450551) B51450551
theorem B1852199 : Blo 1234435 1852199 := bstep (se 1 (by rfl) ⟨1389149, by rfl⟩ : syracuseStep 1852199 = 2778299) B2778299
theorem B4170635 : Blo 1234435 4170635 := bstep (se 1 (by rfl) ⟨3127976, by rfl⟩ : syracuseStep 4170635 = 6255953) B6255953
theorem B67666873 : Blo 1234435 67666873 := bstep (se 2 (by rfl) ⟨25375077, by rfl⟩ : syracuseStep 67666873 = 50750155) B50750155
theorem B2778047 : Blo 1234435 2778047 := bstep (se 1 (by rfl) ⟨2083535, by rfl⟩ : syracuseStep 2778047 = 4167071) B4167071
theorem B1852655 : Blo 1234435 1852655 := bstep (se 1 (by rfl) ⟨1389491, by rfl⟩ : syracuseStep 1852655 = 2778983) B2778983
theorem B2778857 : Blo 1234435 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B9381743 : Blo 1234435 9381743 := bstep (se 1 (by rfl) ⟨7036307, by rfl⟩ : syracuseStep 9381743 = 14072615) B14072615
theorem B16041887 : Blo 1234435 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B1853435 : Blo 1234435 1853435 := bstep (se 1 (by rfl) ⟨1390076, by rfl⟩ : syracuseStep 1853435 = 2780153) B2780153
theorem B121948199 : Blo 1234435 121948199 := bstep (se 1 (by rfl) ⟨91461149, by rfl⟩ : syracuseStep 121948199 = 182922299) B182922299
theorem B5630953 : Blo 1234435 5630953 := bstep (se 2 (by rfl) ⟨2111607, by rfl⟩ : syracuseStep 5630953 = 4223215) B4223215
theorem B1854575 : Blo 1234435 1854575 := bstep (se 1 (by rfl) ⟨1390931, by rfl⟩ : syracuseStep 1854575 = 2781863) B2781863
theorem B15823187 : Blo 1234435 15823187 := bstep (se 1 (by rfl) ⟨11867390, by rfl⟩ : syracuseStep 15823187 = 23734781) B23734781
theorem B2503327 : Blo 1234435 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B4690811 : Blo 1234435 4690811 := bstep (se 1 (by rfl) ⟨3518108, by rfl⟩ : syracuseStep 4690811 = 7036217) B7036217
theorem B3520091 : Blo 1234435 3520091 := bstep (se 1 (by rfl) ⟨2640068, by rfl⟩ : syracuseStep 3520091 = 5280137) B5280137
theorem B7616687 : Blo 1234435 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B60135871 : Blo 1234435 60135871 := bstep (se 1 (by rfl) ⟨45101903, by rfl⟩ : syracuseStep 60135871 = 90203807) B90203807
theorem B4169015 : Blo 1234435 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B1236379 : Blo 1234435 1236379 := bstep (se 1 (by rfl) ⟨927284, by rfl⟩ : syracuseStep 1236379 = 1854569) B1854569
theorem B9379799 : Blo 1234435 9379799 := bstep (se 1 (by rfl) ⟨7034849, by rfl⟩ : syracuseStep 9379799 = 14069699) B14069699
theorem B1852031 : Blo 1234435 1852031 := bstep (se 1 (by rfl) ⟨1389023, by rfl⟩ : syracuseStep 1852031 = 2778047) B2778047
theorem B1852571 : Blo 1234435 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B81298799 : Blo 1234435 81298799 := bstep (se 1 (by rfl) ⟨60974099, by rfl⟩ : syracuseStep 81298799 = 121948199) B121948199
theorem B2779343 : Blo 1234435 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B6253199 : Blo 1234435 6253199 := bstep (se 1 (by rfl) ⟨4689899, by rfl⟩ : syracuseStep 6253199 = 9379799) B9379799
theorem B22866911 : Blo 1234435 22866911 := bstep (se 1 (by rfl) ⟨17150183, by rfl⟩ : syracuseStep 22866911 = 34300367) B34300367
theorem B20311165 : Blo 1234435 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B11873465 : Blo 1234435 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B2780423 : Blo 1234435 2780423 := bstep (se 1 (by rfl) ⟨2085317, by rfl⟩ : syracuseStep 2780423 = 4170635) B4170635
theorem B3337769 : Blo 1234435 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B2346727 : Blo 1234435 2346727 := bstep (se 1 (by rfl) ⟨1760045, by rfl⟩ : syracuseStep 2346727 = 3520091) B3520091
theorem B6254495 : Blo 1234435 6254495 := bstep (se 1 (by rfl) ⟨4690871, by rfl⟩ : syracuseStep 6254495 = 9381743) B9381743
theorem B90222497 : Blo 1234435 90222497 := bstep (se 2 (by rfl) ⟨33833436, by rfl⟩ : syracuseStep 90222497 = 67666873) B67666873
theorem B10694591 : Blo 1234435 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B7507937 : Blo 1234435 7507937 := bstep (se 2 (by rfl) ⟨2815476, by rfl⟩ : syracuseStep 7507937 = 5630953) B5630953
theorem B10548791 : Blo 1234435 10548791 := bstep (se 1 (by rfl) ⟨7911593, by rfl⟩ : syracuseStep 10548791 = 15823187) B15823187
theorem B1234799 : Blo 1234435 1234799 := bstep (se 1 (by rfl) ⟨926099, by rfl⟩ : syracuseStep 1234799 = 1852199) B1852199
theorem B3127207 : Blo 1234435 3127207 := bstep (se 1 (by rfl) ⟨2345405, by rfl⟩ : syracuseStep 3127207 = 4690811) B4690811
theorem B80181161 : Blo 1234435 80181161 := bstep (se 2 (by rfl) ⟨30067935, by rfl⟩ : syracuseStep 80181161 = 60135871) B60135871
theorem B1235103 : Blo 1234435 1235103 := bstep (se 1 (by rfl) ⟨926327, by rfl⟩ : syracuseStep 1235103 = 1852655) B1852655
theorem B1235623 : Blo 1234435 1235623 := bstep (se 1 (by rfl) ⟨926717, by rfl⟩ : syracuseStep 1235623 = 1853435) B1853435
theorem B1236383 : Blo 1234435 1236383 := bstep (se 1 (by rfl) ⟨927287, by rfl⟩ : syracuseStep 1236383 = 1854575) B1854575
theorem B54199199 : Blo 1234435 54199199 := bstep (se 1 (by rfl) ⟨40649399, by rfl⟩ : syracuseStep 54199199 = 81298799) B81298799
theorem B53454107 : Blo 1234435 53454107 := bstep (se 1 (by rfl) ⟨40090580, by rfl⟩ : syracuseStep 53454107 = 80181161) B80181161
theorem B1852895 : Blo 1234435 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B7915643 : Blo 1234435 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B1853615 : Blo 1234435 1853615 := bstep (se 1 (by rfl) ⟨1390211, by rfl⟩ : syracuseStep 1853615 = 2780423) B2780423
theorem B60148331 : Blo 1234435 60148331 := bstep (se 1 (by rfl) ⟨45111248, by rfl⟩ : syracuseStep 60148331 = 90222497) B90222497
theorem B7129727 : Blo 1234435 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B7032527 : Blo 1234435 7032527 := bstep (se 1 (by rfl) ⟨5274395, by rfl⟩ : syracuseStep 7032527 = 10548791) B10548791
theorem B2225179 : Blo 1234435 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B1234687 : Blo 1234435 1234687 := bstep (se 1 (by rfl) ⟨926015, by rfl⟩ : syracuseStep 1234687 = 1852031) B1852031
theorem B1235047 : Blo 1234435 1235047 := bstep (se 1 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 1235047 = 1852571) B1852571
theorem B27081553 : Blo 1234435 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B4168799 : Blo 1234435 4168799 := bstep (se 1 (by rfl) ⟨3126599, by rfl⟩ : syracuseStep 4168799 = 6253199) B6253199
theorem B15244607 : Blo 1234435 15244607 := bstep (se 1 (by rfl) ⟨11433455, by rfl⟩ : syracuseStep 15244607 = 22866911) B22866911
theorem B3128969 : Blo 1234435 3128969 := bstep (se 2 (by rfl) ⟨1173363, by rfl⟩ : syracuseStep 3128969 = 2346727) B2346727
theorem B4169609 : Blo 1234435 4169609 := bstep (se 2 (by rfl) ⟨1563603, by rfl⟩ : syracuseStep 4169609 = 3127207) B3127207
theorem B20021165 : Blo 1234435 20021165 := bstep (se 3 (by rfl) ⟨3753968, by rfl⟩ : syracuseStep 20021165 = 7507937) B7507937
theorem B4169663 : Blo 1234435 4169663 := bstep (se 1 (by rfl) ⟨3127247, by rfl⟩ : syracuseStep 4169663 = 6254495) B6254495
theorem B35636071 : Blo 1234435 35636071 := bstep (se 1 (by rfl) ⟨26727053, by rfl⟩ : syracuseStep 35636071 = 53454107) B53454107
theorem B2966905 : Blo 1234435 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B5277095 : Blo 1234435 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B4753151 : Blo 1234435 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B2779199 : Blo 1234435 2779199 := bstep (se 1 (by rfl) ⟨2084399, by rfl⟩ : syracuseStep 2779199 = 4168799) B4168799
theorem B4688351 : Blo 1234435 4688351 := bstep (se 1 (by rfl) ⟨3516263, by rfl⟩ : syracuseStep 4688351 = 7032527) B7032527
theorem B2779739 : Blo 1234435 2779739 := bstep (se 1 (by rfl) ⟨2084804, by rfl⟩ : syracuseStep 2779739 = 4169609) B4169609
theorem B13347443 : Blo 1234435 13347443 := bstep (se 1 (by rfl) ⟨10010582, by rfl⟩ : syracuseStep 13347443 = 20021165) B20021165
theorem B2779775 : Blo 1234435 2779775 := bstep (se 1 (by rfl) ⟨2084831, by rfl⟩ : syracuseStep 2779775 = 4169663) B4169663
theorem B10163071 : Blo 1234435 10163071 := bstep (se 1 (by rfl) ⟨7622303, by rfl⟩ : syracuseStep 10163071 = 15244607) B15244607
theorem B2085979 : Blo 1234435 2085979 := bstep (se 1 (by rfl) ⟨1564484, by rfl⟩ : syracuseStep 2085979 = 3128969) B3128969
theorem B36132799 : Blo 1234435 36132799 := bstep (se 1 (by rfl) ⟨27099599, by rfl⟩ : syracuseStep 36132799 = 54199199) B54199199
theorem B1235263 : Blo 1234435 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B36108737 : Blo 1234435 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B1235743 : Blo 1234435 1235743 := bstep (se 1 (by rfl) ⟨926807, by rfl⟩ : syracuseStep 1235743 = 1853615) B1853615
theorem B40098887 : Blo 1234435 40098887 := bstep (se 1 (by rfl) ⟨30074165, by rfl⟩ : syracuseStep 40098887 = 60148331) B60148331
theorem B47514761 : Blo 1234435 47514761 := bstep (se 2 (by rfl) ⟨17818035, by rfl⟩ : syracuseStep 47514761 = 35636071) B35636071
theorem B13550761 : Blo 1234435 13550761 := bstep (se 2 (by rfl) ⟨5081535, by rfl⟩ : syracuseStep 13550761 = 10163071) B10163071
theorem B1852799 : Blo 1234435 1852799 := bstep (se 1 (by rfl) ⟨1389599, by rfl⟩ : syracuseStep 1852799 = 2779199) B2779199
theorem B1853159 : Blo 1234435 1853159 := bstep (se 1 (by rfl) ⟨1389869, by rfl⟩ : syracuseStep 1853159 = 2779739) B2779739
theorem B8898295 : Blo 1234435 8898295 := bstep (se 1 (by rfl) ⟨6673721, by rfl⟩ : syracuseStep 8898295 = 13347443) B13347443
theorem B1853183 : Blo 1234435 1853183 := bstep (se 1 (by rfl) ⟨1389887, by rfl⟩ : syracuseStep 1853183 = 2779775) B2779775
theorem B26732591 : Blo 1234435 26732591 := bstep (se 1 (by rfl) ⟨20049443, by rfl⟩ : syracuseStep 26732591 = 40098887) B40098887
theorem B3518063 : Blo 1234435 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B2781305 : Blo 1234435 2781305 := bstep (se 2 (by rfl) ⟨1042989, by rfl⟩ : syracuseStep 2781305 = 2085979) B2085979
theorem B24072491 : Blo 1234435 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B3125567 : Blo 1234435 3125567 := bstep (se 1 (by rfl) ⟨2344175, by rfl⟩ : syracuseStep 3125567 = 4688351) B4688351
theorem B3168767 : Blo 1234435 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B3955873 : Blo 1234435 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B48177065 : Blo 1234435 48177065 := bstep (se 2 (by rfl) ⟨18066399, by rfl⟩ : syracuseStep 48177065 = 36132799) B36132799
theorem B16048327 : Blo 1234435 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B11864393 : Blo 1234435 11864393 := bstep (se 2 (by rfl) ⟨4449147, by rfl⟩ : syracuseStep 11864393 = 8898295) B8898295
theorem B2345375 : Blo 1234435 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B1854203 : Blo 1234435 1854203 := bstep (se 1 (by rfl) ⟨1390652, by rfl⟩ : syracuseStep 1854203 = 2781305) B2781305
theorem B2083711 : Blo 1234435 2083711 := bstep (se 1 (by rfl) ⟨1562783, by rfl⟩ : syracuseStep 2083711 = 3125567) B3125567
theorem B8450045 : Blo 1234435 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B17821727 : Blo 1234435 17821727 := bstep (se 1 (by rfl) ⟨13366295, by rfl⟩ : syracuseStep 17821727 = 26732591) B26732591
theorem B18067681 : Blo 1234435 18067681 := bstep (se 2 (by rfl) ⟨6775380, by rfl⟩ : syracuseStep 18067681 = 13550761) B13550761
theorem B32118043 : Blo 1234435 32118043 := bstep (se 1 (by rfl) ⟨24088532, by rfl⟩ : syracuseStep 32118043 = 48177065) B48177065
theorem B31676507 : Blo 1234435 31676507 := bstep (se 1 (by rfl) ⟨23757380, by rfl⟩ : syracuseStep 31676507 = 47514761) B47514761
theorem B1235199 : Blo 1234435 1235199 := bstep (se 1 (by rfl) ⟨926399, by rfl⟩ : syracuseStep 1235199 = 1852799) B1852799
theorem B1235439 : Blo 1234435 1235439 := bstep (se 1 (by rfl) ⟨926579, by rfl⟩ : syracuseStep 1235439 = 1853159) B1853159
theorem B1235455 : Blo 1234435 1235455 := bstep (se 1 (by rfl) ⟨926591, by rfl⟩ : syracuseStep 1235455 = 1853183) B1853183
theorem B5274497 : Blo 1234435 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B21397769 : Blo 1234435 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B2778281 : Blo 1234435 2778281 := bstep (se 2 (by rfl) ⟨1041855, by rfl⟩ : syracuseStep 2778281 = 2083711) B2083711
theorem B11881151 : Blo 1234435 11881151 := bstep (se 1 (by rfl) ⟨8910863, by rfl⟩ : syracuseStep 11881151 = 17821727) B17821727
theorem B6254333 : Blo 1234435 6254333 := bstep (se 3 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 6254333 = 2345375) B2345375
theorem B7909595 : Blo 1234435 7909595 := bstep (se 1 (by rfl) ⟨5932196, by rfl⟩ : syracuseStep 7909595 = 11864393) B11864393
theorem B42824057 : Blo 1234435 42824057 := bstep (se 2 (by rfl) ⟨16059021, by rfl⟩ : syracuseStep 42824057 = 32118043) B32118043
theorem B5633363 : Blo 1234435 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B24090241 : Blo 1234435 24090241 := bstep (se 2 (by rfl) ⟨9033840, by rfl⟩ : syracuseStep 24090241 = 18067681) B18067681
theorem B21117671 : Blo 1234435 21117671 := bstep (se 1 (by rfl) ⟨15838253, by rfl⟩ : syracuseStep 21117671 = 31676507) B31676507
theorem B1236135 : Blo 1234435 1236135 := bstep (se 1 (by rfl) ⟨927101, by rfl⟩ : syracuseStep 1236135 = 1854203) B1854203
theorem B14065325 : Blo 1234435 14065325 := bstep (se 3 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 14065325 = 5274497) B5274497
theorem B1852187 : Blo 1234435 1852187 := bstep (se 1 (by rfl) ⟨1389140, by rfl⟩ : syracuseStep 1852187 = 2778281) B2778281
theorem B114197485 : Blo 1234435 114197485 := bstep (se 3 (by rfl) ⟨21412028, by rfl⟩ : syracuseStep 114197485 = 42824057) B42824057
theorem B14265179 : Blo 1234435 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B3755575 : Blo 1234435 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B14078447 : Blo 1234435 14078447 := bstep (se 1 (by rfl) ⟨10558835, by rfl⟩ : syracuseStep 14078447 = 21117671) B21117671
theorem B9376883 : Blo 1234435 9376883 := bstep (se 1 (by rfl) ⟨7032662, by rfl⟩ : syracuseStep 9376883 = 14065325) B14065325
theorem B5273063 : Blo 1234435 5273063 := bstep (se 1 (by rfl) ⟨3954797, by rfl⟩ : syracuseStep 5273063 = 7909595) B7909595
theorem B7920767 : Blo 1234435 7920767 := bstep (se 1 (by rfl) ⟨5940575, by rfl⟩ : syracuseStep 7920767 = 11881151) B11881151
theorem B32120321 : Blo 1234435 32120321 := bstep (se 2 (by rfl) ⟨12045120, by rfl⟩ : syracuseStep 32120321 = 24090241) B24090241
theorem B4169555 : Blo 1234435 4169555 := bstep (se 1 (by rfl) ⟨3127166, by rfl⟩ : syracuseStep 4169555 = 6254333) B6254333
theorem B6251255 : Blo 1234435 6251255 := bstep (se 1 (by rfl) ⟨4688441, by rfl⟩ : syracuseStep 6251255 = 9376883) B9376883
theorem B3515375 : Blo 1234435 3515375 := bstep (se 1 (by rfl) ⟨2636531, by rfl⟩ : syracuseStep 3515375 = 5273063) B5273063
theorem B5007433 : Blo 1234435 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B2779703 : Blo 1234435 2779703 := bstep (se 1 (by rfl) ⟨2084777, by rfl⟩ : syracuseStep 2779703 = 4169555) B4169555
theorem B21122045 : Blo 1234435 21122045 := bstep (se 3 (by rfl) ⟨3960383, by rfl⟩ : syracuseStep 21122045 = 7920767) B7920767
theorem B9385631 : Blo 1234435 9385631 := bstep (se 1 (by rfl) ⟨7039223, by rfl⟩ : syracuseStep 9385631 = 14078447) B14078447
theorem B1234791 : Blo 1234435 1234791 := bstep (se 1 (by rfl) ⟨926093, by rfl⟩ : syracuseStep 1234791 = 1852187) B1852187
theorem B152263313 : Blo 1234435 152263313 := bstep (se 2 (by rfl) ⟨57098742, by rfl⟩ : syracuseStep 152263313 = 114197485) B114197485
theorem B85654189 : Blo 1234435 85654189 := bstep (se 3 (by rfl) ⟨16060160, by rfl⟩ : syracuseStep 85654189 = 32120321) B32120321
theorem B9510119 : Blo 1234435 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B6676577 : Blo 1234435 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B2343583 : Blo 1234435 2343583 := bstep (se 1 (by rfl) ⟨1757687, by rfl⟩ : syracuseStep 2343583 = 3515375) B3515375
theorem B114205585 : Blo 1234435 114205585 := bstep (se 2 (by rfl) ⟨42827094, by rfl⟩ : syracuseStep 114205585 = 85654189) B85654189
theorem B1853135 : Blo 1234435 1853135 := bstep (se 1 (by rfl) ⟨1389851, by rfl⟩ : syracuseStep 1853135 = 2779703) B2779703
theorem B101508875 : Blo 1234435 101508875 := bstep (se 1 (by rfl) ⟨76131656, by rfl⟩ : syracuseStep 101508875 = 152263313) B152263313
theorem B4167503 : Blo 1234435 4167503 := bstep (se 1 (by rfl) ⟨3125627, by rfl⟩ : syracuseStep 4167503 = 6251255) B6251255
theorem B6257087 : Blo 1234435 6257087 := bstep (se 1 (by rfl) ⟨4692815, by rfl⟩ : syracuseStep 6257087 = 9385631) B9385631
theorem B14081363 : Blo 1234435 14081363 := bstep (se 1 (by rfl) ⟨10561022, by rfl⟩ : syracuseStep 14081363 = 21122045) B21122045
theorem B6340079 : Blo 1234435 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B152274113 : Blo 1234435 152274113 := bstep (se 2 (by rfl) ⟨57102792, by rfl⟩ : syracuseStep 152274113 = 114205585) B114205585
theorem B2778335 : Blo 1234435 2778335 := bstep (se 1 (by rfl) ⟨2083751, by rfl⟩ : syracuseStep 2778335 = 4167503) B4167503
theorem B4171391 : Blo 1234435 4171391 := bstep (se 1 (by rfl) ⟨3128543, by rfl⟩ : syracuseStep 4171391 = 6257087) B6257087
theorem B4451051 : Blo 1234435 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B3124777 : Blo 1234435 3124777 := bstep (se 2 (by rfl) ⟨1171791, by rfl⟩ : syracuseStep 3124777 = 2343583) B2343583
theorem B1235423 : Blo 1234435 1235423 := bstep (se 1 (by rfl) ⟨926567, by rfl⟩ : syracuseStep 1235423 = 1853135) B1853135
theorem B67672583 : Blo 1234435 67672583 := bstep (se 1 (by rfl) ⟨50754437, by rfl⟩ : syracuseStep 67672583 = 101508875) B101508875
theorem B16906877 : Blo 1234435 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B9387575 : Blo 1234435 9387575 := bstep (se 1 (by rfl) ⟨7040681, by rfl⟩ : syracuseStep 9387575 = 14081363) B14081363
theorem B101516075 : Blo 1234435 101516075 := bstep (se 1 (by rfl) ⟨76137056, by rfl⟩ : syracuseStep 101516075 = 152274113) B152274113
theorem B1852223 : Blo 1234435 1852223 := bstep (se 1 (by rfl) ⟨1389167, by rfl⟩ : syracuseStep 1852223 = 2778335) B2778335
theorem B45115055 : Blo 1234435 45115055 := bstep (se 1 (by rfl) ⟨33836291, by rfl⟩ : syracuseStep 45115055 = 67672583) B67672583
theorem B2967367 : Blo 1234435 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B2780927 : Blo 1234435 2780927 := bstep (se 1 (by rfl) ⟨2085695, by rfl⟩ : syracuseStep 2780927 = 4171391) B4171391
theorem B4166369 : Blo 1234435 4166369 := bstep (se 2 (by rfl) ⟨1562388, by rfl⟩ : syracuseStep 4166369 = 3124777) B3124777
theorem B11271251 : Blo 1234435 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B6258383 : Blo 1234435 6258383 := bstep (se 1 (by rfl) ⟨4693787, by rfl⟩ : syracuseStep 6258383 = 9387575) B9387575
theorem B2777579 : Blo 1234435 2777579 := bstep (se 1 (by rfl) ⟨2083184, by rfl⟩ : syracuseStep 2777579 = 4166369) B4166369
theorem B7514167 : Blo 1234435 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B4172255 : Blo 1234435 4172255 := bstep (se 1 (by rfl) ⟨3129191, by rfl⟩ : syracuseStep 4172255 = 6258383) B6258383
theorem B1853951 : Blo 1234435 1853951 := bstep (se 1 (by rfl) ⟨1390463, by rfl⟩ : syracuseStep 1853951 = 2780927) B2780927
theorem B67677383 : Blo 1234435 67677383 := bstep (se 1 (by rfl) ⟨50758037, by rfl⟩ : syracuseStep 67677383 = 101516075) B101516075
theorem B30076703 : Blo 1234435 30076703 := bstep (se 1 (by rfl) ⟨22557527, by rfl⟩ : syracuseStep 30076703 = 45115055) B45115055
theorem B1234815 : Blo 1234435 1234815 := bstep (se 1 (by rfl) ⟨926111, by rfl⟩ : syracuseStep 1234815 = 1852223) B1852223
theorem B3956489 : Blo 1234435 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B10018889 : Blo 1234435 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B1851719 : Blo 1234435 1851719 := bstep (se 1 (by rfl) ⟨1388789, by rfl⟩ : syracuseStep 1851719 = 2777579) B2777579
theorem B2781503 : Blo 1234435 2781503 := bstep (se 1 (by rfl) ⟨2086127, by rfl⟩ : syracuseStep 2781503 = 4172255) B4172255
theorem B45118255 : Blo 1234435 45118255 := bstep (se 1 (by rfl) ⟨33838691, by rfl⟩ : syracuseStep 45118255 = 67677383) B67677383
theorem B20051135 : Blo 1234435 20051135 := bstep (se 1 (by rfl) ⟨15038351, by rfl⟩ : syracuseStep 20051135 = 30076703) B30076703
theorem B1235967 : Blo 1234435 1235967 := bstep (se 1 (by rfl) ⟨926975, by rfl⟩ : syracuseStep 1235967 = 1853951) B1853951
theorem B2637659 : Blo 1234435 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B6679259 : Blo 1234435 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B1854335 : Blo 1234435 1854335 := bstep (se 1 (by rfl) ⟨1390751, by rfl⟩ : syracuseStep 1854335 = 2781503) B2781503
theorem B60157673 : Blo 1234435 60157673 := bstep (se 2 (by rfl) ⟨22559127, by rfl⟩ : syracuseStep 60157673 = 45118255) B45118255
theorem B1758439 : Blo 1234435 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B1234479 : Blo 1234435 1234479 := bstep (se 1 (by rfl) ⟨925859, by rfl⟩ : syracuseStep 1234479 = 1851719) B1851719
theorem B13367423 : Blo 1234435 13367423 := bstep (se 1 (by rfl) ⟨10025567, by rfl⟩ : syracuseStep 13367423 = 20051135) B20051135
theorem B4452839 : Blo 1234435 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B40105115 : Blo 1234435 40105115 := bstep (se 1 (by rfl) ⟨30078836, by rfl⟩ : syracuseStep 40105115 = 60157673) B60157673
theorem B9378341 : Blo 1234435 9378341 := bstep (se 4 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 9378341 = 1758439) B1758439
theorem B8911615 : Blo 1234435 8911615 := bstep (se 1 (by rfl) ⟨6683711, by rfl⟩ : syracuseStep 8911615 = 13367423) B13367423
theorem B1236223 : Blo 1234435 1236223 := bstep (se 1 (by rfl) ⟨927167, by rfl⟩ : syracuseStep 1236223 = 1854335) B1854335
theorem B6252227 : Blo 1234435 6252227 := bstep (se 1 (by rfl) ⟨4689170, by rfl⟩ : syracuseStep 6252227 = 9378341) B9378341
theorem B2968559 : Blo 1234435 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B11882153 : Blo 1234435 11882153 := bstep (se 2 (by rfl) ⟨4455807, by rfl⟩ : syracuseStep 11882153 = 8911615) B8911615
theorem B26736743 : Blo 1234435 26736743 := bstep (se 1 (by rfl) ⟨20052557, by rfl⟩ : syracuseStep 26736743 = 40105115) B40105115
theorem B1979039 : Blo 1234435 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B4168151 : Blo 1234435 4168151 := bstep (se 1 (by rfl) ⟨3126113, by rfl⟩ : syracuseStep 4168151 = 6252227) B6252227
theorem B17824495 : Blo 1234435 17824495 := bstep (se 1 (by rfl) ⟨13368371, by rfl⟩ : syracuseStep 17824495 = 26736743) B26736743
theorem B7921435 : Blo 1234435 7921435 := bstep (se 1 (by rfl) ⟨5941076, by rfl⟩ : syracuseStep 7921435 = 11882153) B11882153
theorem B23765993 : Blo 1234435 23765993 := bstep (se 2 (by rfl) ⟨8912247, by rfl⟩ : syracuseStep 23765993 = 17824495) B17824495
theorem B2778767 : Blo 1234435 2778767 := bstep (se 1 (by rfl) ⟨2084075, by rfl⟩ : syracuseStep 2778767 = 4168151) B4168151
theorem B5277437 : Blo 1234435 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B10561913 : Blo 1234435 10561913 := bstep (se 2 (by rfl) ⟨3960717, by rfl⟩ : syracuseStep 10561913 = 7921435) B7921435
theorem B15843995 : Blo 1234435 15843995 := bstep (se 1 (by rfl) ⟨11882996, by rfl⟩ : syracuseStep 15843995 = 23765993) B23765993
theorem B1852511 : Blo 1234435 1852511 := bstep (se 1 (by rfl) ⟨1389383, by rfl⟩ : syracuseStep 1852511 = 2778767) B2778767
theorem B3518291 : Blo 1234435 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B7041275 : Blo 1234435 7041275 := bstep (se 1 (by rfl) ⟨5280956, by rfl⟩ : syracuseStep 7041275 = 10561913) B10561913
theorem B4694183 : Blo 1234435 4694183 := bstep (se 1 (by rfl) ⟨3520637, by rfl⟩ : syracuseStep 4694183 = 7041275) B7041275
theorem B2345527 : Blo 1234435 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B10562663 : Blo 1234435 10562663 := bstep (se 1 (by rfl) ⟨7921997, by rfl⟩ : syracuseStep 10562663 = 15843995) B15843995
theorem B1235007 : Blo 1234435 1235007 := bstep (se 1 (by rfl) ⟨926255, by rfl⟩ : syracuseStep 1235007 = 1852511) B1852511
theorem B3129455 : Blo 1234435 3129455 := bstep (se 1 (by rfl) ⟨2347091, by rfl⟩ : syracuseStep 3129455 = 4694183) B4694183
theorem B7041775 : Blo 1234435 7041775 := bstep (se 1 (by rfl) ⟨5281331, by rfl⟩ : syracuseStep 7041775 = 10562663) B10562663
theorem B3127369 : Blo 1234435 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B4169825 : Blo 1234435 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B9389033 : Blo 1234435 9389033 := bstep (se 2 (by rfl) ⟨3520887, by rfl⟩ : syracuseStep 9389033 = 7041775) B7041775
theorem B2086303 : Blo 1234435 2086303 := bstep (se 1 (by rfl) ⟨1564727, by rfl⟩ : syracuseStep 2086303 = 3129455) B3129455
theorem B6259355 : Blo 1234435 6259355 := bstep (se 1 (by rfl) ⟨4694516, by rfl⟩ : syracuseStep 6259355 = 9389033) B9389033
theorem B2779883 : Blo 1234435 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B2781737 : Blo 1234435 2781737 := bstep (se 2 (by rfl) ⟨1043151, by rfl⟩ : syracuseStep 2781737 = 2086303) B2086303
theorem B1853255 : Blo 1234435 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B1854491 : Blo 1234435 1854491 := bstep (se 1 (by rfl) ⟨1390868, by rfl⟩ : syracuseStep 1854491 = 2781737) B2781737
theorem B4172903 : Blo 1234435 4172903 := bstep (se 1 (by rfl) ⟨3129677, by rfl⟩ : syracuseStep 4172903 = 6259355) B6259355
theorem B2781935 : Blo 1234435 2781935 := bstep (se 1 (by rfl) ⟨2086451, by rfl⟩ : syracuseStep 2781935 = 4172903) B4172903
theorem B1235503 : Blo 1234435 1235503 := bstep (se 1 (by rfl) ⟨926627, by rfl⟩ : syracuseStep 1235503 = 1853255) B1853255
theorem B1236327 : Blo 1234435 1236327 := bstep (se 1 (by rfl) ⟨927245, by rfl⟩ : syracuseStep 1236327 = 1854491) B1854491
theorem B1854623 : Blo 1234435 1854623 := bstep (se 1 (by rfl) ⟨1390967, by rfl⟩ : syracuseStep 1854623 = 2781935) B2781935
theorem B1236415 : Blo 1234435 1236415 := bstep (se 1 (by rfl) ⟨927311, by rfl⟩ : syracuseStep 1236415 = 1854623) B1854623

theorem C0 (j : ℕ) (h1 : 308608 ≤ j) (h2 : j ≤ 309108) : Blo 1234435 (4 * j + 3) := by
  interval_cases j
  · exact B1234435
  · exact B1234439
  · exact B1234443
  · exact B1234447
  · exact B1234451
  · exact B1234455
  · exact B1234459
  · exact B1234463
  · exact B1234467
  · exact B1234471
  · exact B1234475
  · exact B1234479
  · exact B1234483
  · exact B1234487
  · exact B1234491
  · exact B1234495
  · exact B1234499
  · exact B1234503
  · exact B1234507
  · exact B1234511
  · exact B1234515
  · exact B1234519
  · exact B1234523
  · exact B1234527
  · exact B1234531
  · exact B1234535
  · exact B1234539
  · exact B1234543
  · exact B1234547
  · exact B1234551
  · exact B1234555
  · exact B1234559
  · exact B1234563
  · exact B1234567
  · exact B1234571
  · exact B1234575
  · exact B1234579
  · exact B1234583
  · exact B1234587
  · exact B1234591
  · exact B1234595
  · exact B1234599
  · exact B1234603
  · exact B1234607
  · exact B1234611
  · exact B1234615
  · exact B1234619
  · exact B1234623
  · exact B1234627
  · exact B1234631
  · exact B1234635
  · exact B1234639
  · exact B1234643
  · exact B1234647
  · exact B1234651
  · exact B1234655
  · exact B1234659
  · exact B1234663
  · exact B1234667
  · exact B1234671
  · exact B1234675
  · exact B1234679
  · exact B1234683
  · exact B1234687
  · exact B1234691
  · exact B1234695
  · exact B1234699
  · exact B1234703
  · exact B1234707
  · exact B1234711
  · exact B1234715
  · exact B1234719
  · exact B1234723
  · exact B1234727
  · exact B1234731
  · exact B1234735
  · exact B1234739
  · exact B1234743
  · exact B1234747
  · exact B1234751
  · exact B1234755
  · exact B1234759
  · exact B1234763
  · exact B1234767
  · exact B1234771
  · exact B1234775
  · exact B1234779
  · exact B1234783
  · exact B1234787
  · exact B1234791
  · exact B1234795
  · exact B1234799
  · exact B1234803
  · exact B1234807
  · exact B1234811
  · exact B1234815
  · exact B1234819
  · exact B1234823
  · exact B1234827
  · exact B1234831
  · exact B1234835
  · exact B1234839
  · exact B1234843
  · exact B1234847
  · exact B1234851
  · exact B1234855
  · exact B1234859
  · exact B1234863
  · exact B1234867
  · exact B1234871
  · exact B1234875
  · exact B1234879
  · exact B1234883
  · exact B1234887
  · exact B1234891
  · exact B1234895
  · exact B1234899
  · exact B1234903
  · exact B1234907
  · exact B1234911
  · exact B1234915
  · exact B1234919
  · exact B1234923
  · exact B1234927
  · exact B1234931
  · exact B1234935
  · exact B1234939
  · exact B1234943
  · exact B1234947
  · exact B1234951
  · exact B1234955
  · exact B1234959
  · exact B1234963
  · exact B1234967
  · exact B1234971
  · exact B1234975
  · exact B1234979
  · exact B1234983
  · exact B1234987
  · exact B1234991
  · exact B1234995
  · exact B1234999
  · exact B1235003
  · exact B1235007
  · exact B1235011
  · exact B1235015
  · exact B1235019
  · exact B1235023
  · exact B1235027
  · exact B1235031
  · exact B1235035
  · exact B1235039
  · exact B1235043
  · exact B1235047
  · exact B1235051
  · exact B1235055
  · exact B1235059
  · exact B1235063
  · exact B1235067
  · exact B1235071
  · exact B1235075
  · exact B1235079
  · exact B1235083
  · exact B1235087
  · exact B1235091
  · exact B1235095
  · exact B1235099
  · exact B1235103
  · exact B1235107
  · exact B1235111
  · exact B1235115
  · exact B1235119
  · exact B1235123
  · exact B1235127
  · exact B1235131
  · exact B1235135
  · exact B1235139
  · exact B1235143
  · exact B1235147
  · exact B1235151
  · exact B1235155
  · exact B1235159
  · exact B1235163
  · exact B1235167
  · exact B1235171
  · exact B1235175
  · exact B1235179
  · exact B1235183
  · exact B1235187
  · exact B1235191
  · exact B1235195
  · exact B1235199
  · exact B1235203
  · exact B1235207
  · exact B1235211
  · exact B1235215
  · exact B1235219
  · exact B1235223
  · exact B1235227
  · exact B1235231
  · exact B1235235
  · exact B1235239
  · exact B1235243
  · exact B1235247
  · exact B1235251
  · exact B1235255
  · exact B1235259
  · exact B1235263
  · exact B1235267
  · exact B1235271
  · exact B1235275
  · exact B1235279
  · exact B1235283
  · exact B1235287
  · exact B1235291
  · exact B1235295
  · exact B1235299
  · exact B1235303
  · exact B1235307
  · exact B1235311
  · exact B1235315
  · exact B1235319
  · exact B1235323
  · exact B1235327
  · exact B1235331
  · exact B1235335
  · exact B1235339
  · exact B1235343
  · exact B1235347
  · exact B1235351
  · exact B1235355
  · exact B1235359
  · exact B1235363
  · exact B1235367
  · exact B1235371
  · exact B1235375
  · exact B1235379
  · exact B1235383
  · exact B1235387
  · exact B1235391
  · exact B1235395
  · exact B1235399
  · exact B1235403
  · exact B1235407
  · exact B1235411
  · exact B1235415
  · exact B1235419
  · exact B1235423
  · exact B1235427
  · exact B1235431
  · exact B1235435
  · exact B1235439
  · exact B1235443
  · exact B1235447
  · exact B1235451
  · exact B1235455
  · exact B1235459
  · exact B1235463
  · exact B1235467
  · exact B1235471
  · exact B1235475
  · exact B1235479
  · exact B1235483
  · exact B1235487
  · exact B1235491
  · exact B1235495
  · exact B1235499
  · exact B1235503
  · exact B1235507
  · exact B1235511
  · exact B1235515
  · exact B1235519
  · exact B1235523
  · exact B1235527
  · exact B1235531
  · exact B1235535
  · exact B1235539
  · exact B1235543
  · exact B1235547
  · exact B1235551
  · exact B1235555
  · exact B1235559
  · exact B1235563
  · exact B1235567
  · exact B1235571
  · exact B1235575
  · exact B1235579
  · exact B1235583
  · exact B1235587
  · exact B1235591
  · exact B1235595
  · exact B1235599
  · exact B1235603
  · exact B1235607
  · exact B1235611
  · exact B1235615
  · exact B1235619
  · exact B1235623
  · exact B1235627
  · exact B1235631
  · exact B1235635
  · exact B1235639
  · exact B1235643
  · exact B1235647
  · exact B1235651
  · exact B1235655
  · exact B1235659
  · exact B1235663
  · exact B1235667
  · exact B1235671
  · exact B1235675
  · exact B1235679
  · exact B1235683
  · exact B1235687
  · exact B1235691
  · exact B1235695
  · exact B1235699
  · exact B1235703
  · exact B1235707
  · exact B1235711
  · exact B1235715
  · exact B1235719
  · exact B1235723
  · exact B1235727
  · exact B1235731
  · exact B1235735
  · exact B1235739
  · exact B1235743
  · exact B1235747
  · exact B1235751
  · exact B1235755
  · exact B1235759
  · exact B1235763
  · exact B1235767
  · exact B1235771
  · exact B1235775
  · exact B1235779
  · exact B1235783
  · exact B1235787
  · exact B1235791
  · exact B1235795
  · exact B1235799
  · exact B1235803
  · exact B1235807
  · exact B1235811
  · exact B1235815
  · exact B1235819
  · exact B1235823
  · exact B1235827
  · exact B1235831
  · exact B1235835
  · exact B1235839
  · exact B1235843
  · exact B1235847
  · exact B1235851
  · exact B1235855
  · exact B1235859
  · exact B1235863
  · exact B1235867
  · exact B1235871
  · exact B1235875
  · exact B1235879
  · exact B1235883
  · exact B1235887
  · exact B1235891
  · exact B1235895
  · exact B1235899
  · exact B1235903
  · exact B1235907
  · exact B1235911
  · exact B1235915
  · exact B1235919
  · exact B1235923
  · exact B1235927
  · exact B1235931
  · exact B1235935
  · exact B1235939
  · exact B1235943
  · exact B1235947
  · exact B1235951
  · exact B1235955
  · exact B1235959
  · exact B1235963
  · exact B1235967
  · exact B1235971
  · exact B1235975
  · exact B1235979
  · exact B1235983
  · exact B1235987
  · exact B1235991
  · exact B1235995
  · exact B1235999
  · exact B1236003
  · exact B1236007
  · exact B1236011
  · exact B1236015
  · exact B1236019
  · exact B1236023
  · exact B1236027
  · exact B1236031
  · exact B1236035
  · exact B1236039
  · exact B1236043
  · exact B1236047
  · exact B1236051
  · exact B1236055
  · exact B1236059
  · exact B1236063
  · exact B1236067
  · exact B1236071
  · exact B1236075
  · exact B1236079
  · exact B1236083
  · exact B1236087
  · exact B1236091
  · exact B1236095
  · exact B1236099
  · exact B1236103
  · exact B1236107
  · exact B1236111
  · exact B1236115
  · exact B1236119
  · exact B1236123
  · exact B1236127
  · exact B1236131
  · exact B1236135
  · exact B1236139
  · exact B1236143
  · exact B1236147
  · exact B1236151
  · exact B1236155
  · exact B1236159
  · exact B1236163
  · exact B1236167
  · exact B1236171
  · exact B1236175
  · exact B1236179
  · exact B1236183
  · exact B1236187
  · exact B1236191
  · exact B1236195
  · exact B1236199
  · exact B1236203
  · exact B1236207
  · exact B1236211
  · exact B1236215
  · exact B1236219
  · exact B1236223
  · exact B1236227
  · exact B1236231
  · exact B1236235
  · exact B1236239
  · exact B1236243
  · exact B1236247
  · exact B1236251
  · exact B1236255
  · exact B1236259
  · exact B1236263
  · exact B1236267
  · exact B1236271
  · exact B1236275
  · exact B1236279
  · exact B1236283
  · exact B1236287
  · exact B1236291
  · exact B1236295
  · exact B1236299
  · exact B1236303
  · exact B1236307
  · exact B1236311
  · exact B1236315
  · exact B1236319
  · exact B1236323
  · exact B1236327
  · exact B1236331
  · exact B1236335
  · exact B1236339
  · exact B1236343
  · exact B1236347
  · exact B1236351
  · exact B1236355
  · exact B1236359
  · exact B1236363
  · exact B1236367
  · exact B1236371
  · exact B1236375
  · exact B1236379
  · exact B1236383
  · exact B1236387
  · exact B1236391
  · exact B1236395
  · exact B1236399
  · exact B1236403
  · exact B1236407
  · exact B1236411
  · exact B1236415
  · exact B1236419
  · exact B1236423
  · exact B1236427
  · exact B1236431
  · exact B1236435

theorem solution (m : ℕ) (hlo : 1234435 ≤ m) (hhi : m ≤ 1236435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 308608 ≤ j := by omega
    have hj2 : j ≤ 309108 := by omega
    have hb : Blo 1234435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
